#include "src/prove/system.h"

#include <array>
#include <deque>
#include <set>
#include <functional>
#include <optional>
#include <stdexcept>

#include "src/prove/facts.h"

namespace sys2fol::prove {

namespace {

// ---- The writer's shapes, read from named formulas ----

struct Bound {
    std::string v;
    FmP body;
};

std::optional<Bound> as_some(const FmP& f) {
    if (f->k != Fm::Exists || f->a->k != Fm::And || f->a->a->k != Fm::Atom || f->a->a->name != "set" ||
        f->a->a->args != std::vector<std::string>{f->name})
        return {};
    return Bound{f->name, f->a->b};
}

std::optional<Bound> as_all(const FmP& f) {
    if (f->k != Fm::Forall || f->a->k != Fm::Imp || f->a->a->k != Fm::Atom || f->a->a->name != "set" ||
        f->a->a->args != std::vector<std::string>{f->name})
        return {};
    return Bound{f->name, f->a->b};
}

std::vector<FmP> disjuncts(const FmP& f) {
    if (f->k == Fm::False) return {};
    std::vector<FmP> out;
    FmP g = f;
    for (; g->k == Fm::Or; g = g->b) out.push_back(g->a);
    out.push_back(g);
    return out;
}

std::vector<FmP> conjuncts(const FmP& f, size_t n) {
    std::vector<FmP> out;
    FmP g = f;
    while (out.size() + 1 < n) {
        if (g->k != Fm::And) throw std::runtime_error("expected " + std::to_string(n) + " conjuncts: " + print(f).substr(0, 200));
        out.push_back(g->a);
        g = g->b;
    }
    out.push_back(g);
    return out;
}

bool is_atom(const FmP& f, const char* p, const std::vector<std::string>& args) {
    return f->k == Fm::Atom && f->name == p && f->args == args;
}

// The numbers a proof has named, by name: its claim's own, from its top, and any it built after them (decision 23).
using Nums = std::map<std::string, uint64_t>;

std::optional<uint64_t> number(const Nums& nums, const std::string& v) {
    auto it = nums.find(v);
    if (it == nums.end()) return {};
    return it->second;
}

// x is the number c: eq(x, z_c), or zero(x) for 0.
std::optional<std::pair<uint64_t, std::string>> as_num(const FmP& f, const Nums& nums) {
    if (f->k != Fm::Atom) return {};
    if (f->name == "zero" && f->args.size() == 1) return {{0, f->args[0]}};
    if (f->name != "eq" || f->args.size() != 2) return {};
    auto c = number(nums, f->args[1]);
    if (!c) return {};
    return {{*c, f->args[0]}};
}

struct AtP {
    uint32_t i;
    std::string v, r;
};

// v is r's entry at i: pmem(z_i, v, r).
std::optional<AtP> as_at(const FmP& f, const Nums& nums) {
    if (f->k != Fm::Atom || f->name != "pmem" || f->args.size() != 3) return {};
    auto i = number(nums, f->args[0]);
    if (!i) return {};
    return AtP{static_cast<uint32_t>(*i), f->args[1], f->args[2]};
}

// Rec_k(t; x0, ..., x(k-1)), k >= 1: tuple(t, z_k) and pmem(z_i, x_i, t) for each i, nested to the right.
struct RecP {
    std::string t;
    std::vector<std::string> xs;
};

std::optional<RecP> as_rec(const FmP& f, const Nums& nums) {
    if (f->k != Fm::And || f->a->k != Fm::Atom || f->a->name != "tuple" || f->a->args.size() != 2) return {};
    auto k = number(nums, f->a->args[1]);
    if (!k || *k == 0) return {};
    RecP r{f->a->args[0], {}};
    FmP in = f->b;
    for (uint64_t i = 0; i < *k; ++i) {
        FmP c = i + 1 < *k ? (in->k == Fm::And ? in->a : nullptr) : in;
        if (!c || c->k != Fm::Atom || c->name != "pmem" || c->args.size() != 3 || number(nums, c->args[0]) != i || c->args[2] != r.t)
            return {};
        r.xs.push_back(c->args[1]);
        if (i + 1 < *k) in = in->b;
    }
    return r;
}

// A record pattern: (exists x1 ... xk. (Rec_k(t; x) & rest)).
struct RecordP {
    std::string t;
    std::vector<std::string> xs;
    FmP rest;
};

std::optional<RecordP> as_record(const FmP& f, const Nums& nums) {
    std::vector<std::string> xs;
    FmP g = f;
    while (auto b = as_some(g)) {
        xs.push_back(b->v);
        g = b->body;
        if (g->k != Fm::Exists) break;
    }
    if (xs.empty() || g->k != Fm::And) return {};
    auto r = as_rec(g->a, nums);
    if (!r || r->xs != xs) return {};
    return RecordP{r->t, xs, g->b};
}

// eq(v, x_i) from Rec_k(r; x) and pmem(z_i, v, r): a tuple is a function, by tuple_def.
H entry_unique(Tac& t, const std::string& r, H rec, size_t k, size_t i, const std::string& v, H at_v) {
    std::vector<H> parts = t.split(rec, k + 1);
    const FmP& pi = t.p.fm(parts[i + 1]);
    H td = t.p.iff_l(t.inst(t.p.use("tuple_def"), {r, t.p.fm(parts[0])->args[1]}), parts[0]);
    return t.mp(t.inst(t.split(td, 4)[3], {pi->args[0], v, pi->args[1]}), {at_v, parts[i + 1]});
}

// rest(v) = r as the writer puts it: (exists n m. (nsucc(m, n) & (tuple(v, n) & (tuple(r, m) & shifted)))).
struct RestP {
    std::string v, r;
};

std::optional<RestP> as_rest(const FmP& f) {
    auto n = as_some(f);
    auto m = n ? as_some(n->body) : std::nullopt;
    if (!m || m->body->k != Fm::And || !is_atom(m->body->a, "nsucc", {m->v, n->v})) return {};
    FmP g = m->body->b;
    if (g->k != Fm::And || g->a->k != Fm::Atom || g->a->name != "tuple" || g->a->args.size() != 2 || g->a->args[1] != n->v)
        return {};
    std::string v = g->a->args[0];
    g = g->b;
    if (g->k != Fm::And || g->a->k != Fm::Atom || g->a->name != "tuple" || g->a->args.size() != 2 || g->a->args[1] != m->v)
        return {};
    return RestP{v, g->a->args[0]};
}

// v ++ [y] = r as the writer puts it: (exists n. (tuple(v, n) & snoc(v, n, y, r))).
struct AppendP {
    std::string v, y, r;
};

std::optional<AppendP> as_append(const FmP& f) {
    auto n = as_some(f);
    if (!n || n->body->k != Fm::And) return {};
    const FmP &a = n->body->a, &b = n->body->b;
    if (a->k != Fm::Atom || a->name != "tuple" || a->args.size() != 2 || a->args[1] != n->v) return {};
    if (b->k != Fm::Atom || b->name != "snoc" || b->args.size() != 4 || b->args[0] != a->args[0] || b->args[1] != n->v) return {};
    return AppendP{a->args[0], b->args[2], b->args[3]};
}

// Whether p occurs in f other than as a membership's right side, pmem(u, v, p) being one by pmem_def.
bool misplaced(const FmP& f, const std::string& p) {
    if (f->k == Fm::Atom) {
        for (size_t i = 0; i < f->args.size(); ++i)
            if (f->args[i] == p && !(f->name == "elem" && i == 1) && !(f->name == "pmem" && i == 2)) return true;
        return false;
    }
    if ((f->k == Fm::Forall || f->k == Fm::Exists) && f->name == p) return false;
    return (f->a && misplaced(f->a, p)) || (f->b && misplaced(f->b, p));
}

// (forall z. (elem(z, c) <-> elem(z, p))): c has p's members, so is p.
FmP same_members(const std::string& c, const std::string& p) {
    return all("z", iff(atom("elem", {"z", c}), atom("elem", {"z", p})));
}

// p in a (same_members(c, p) & body) form: its other side, or "".
std::string members_of(const FmP& f, const std::string& c) {
    auto z = as_all(f);
    if (!z || z->body->k != Fm::Iff || !is_atom(z->body->a, "elem", {z->v, c})) return "";
    const FmP& r = z->body->b;
    if (r->k != Fm::Atom || r->name != "elem" || r->args.size() != 2 || r->args[0] != z->v) return "";
    return r->args[1];
}

// f with each (elem(x, c) | eq(x, c)) written elem(x, s): x <= c is x in s, s the successor of c, by nsucc_def. The class
// machine takes a parameter only on a membership's right side.
FmP below_succ(const FmP& f, const std::string& c, const std::string& s) {
    if (f->k == Fm::Or && f->a->k == Fm::Atom && f->a->name == "elem" && f->b->k == Fm::Atom && f->b->name == "eq" &&
        f->a->args == f->b->args && f->a->args[1] == c)
        return atom("elem", {f->a->args[0], s});
    switch (f->k) {
        case Fm::Atom:
        case Fm::False: return f;
        case Fm::Not: return neg(below_succ(f->a, c, s));
        case Fm::Forall: return forall(f->name, below_succ(f->a, c, s));
        case Fm::Exists: return exists(f->name, below_succ(f->a, c, s));
        case Fm::And: return conj(below_succ(f->a, c, s), below_succ(f->b, c, s));
        case Fm::Or: return disj(below_succ(f->a, c, s), below_succ(f->b, c, s));
        case Fm::Imp: return imp(below_succ(f->a, c, s), below_succ(f->b, c, s));
        case Fm::Iff: return iff(below_succ(f->a, c, s), below_succ(f->b, c, s));
    }
    return f;
}

// ---- Values: what each variable's entries and numerals are, and the steps that say so ----

struct Entries {
    std::vector<std::string> xs;
    H rec;
};

class Eval {
public:
    Eval(Tac& t, Lemmas& lm, std::vector<std::string> z, std::vector<H> gz) : t(t), lm(lm), z(std::move(z)), gz(std::move(gz)) {
        for (size_t c = 0; c < this->z.size(); ++c) {
            val[this->z[c]] = c;
            eqz[this->z[c]] = refl(t, this->z[c]);
            nums[this->z[c]] = c;
        }
    }

    Tac& t;
    Lemmas& lm;
    std::vector<std::string> z;
    std::vector<H> gz;
    std::map<std::string, uint64_t> val;
    std::map<std::string, H> eqz, num;
    std::map<std::string, Entries> recs;
    std::map<std::string, H> rng;   // an entry's range, as its component writes it
    Nums nums;                       // the numbers, by name

    std::vector<std::string> zs(uint64_t c) const { return {z.begin(), z.begin() + c + 1}; }
    std::vector<H> gs(uint64_t c) const { return {gz.begin(), gz.begin() + c + 1}; }

    // x is the number c, by numc: eq(x, z_c), or zero(x).
    void value(const std::string& x, uint64_t c, H numc) {
        need(c);
        val[x] = c;
        num[x] = numc;
        eqz[x] = as_eq(x, numc);
    }

    H as_eq(const std::string& x, H numc) {
        if (!is_atom(t.p.fm(numc), "zero", {x})) return numc;
        return t.mp(t.inst(t.p.use("zero_UNIQ"), {x, z[0]}), {numc, gz[0]});
    }

    void same_as(const std::string& w, const std::string& x, H eq_w_x) {
        uint64_t c = known(x);
        val[w] = c;
        eqz[w] = t.mp(t.inst(t.p.use("eq_trans"), {w, x, z[c]}), {eq_w_x, eqz[x]});
        num.erase(w);
    }

    uint64_t known(const std::string& x) const {
        auto it = val.find(x);
        if (it == val.end()) throw std::runtime_error("the value of " + x + " is not known");
        return it->second;
    }

    // zero(x), x of value 0.
    H zero_of(const std::string& x) {
        if (auto it = num.find(x); it != num.end() && t.p.in_scope(x) && is_atom(t.p.fm(it->second), "zero", {x}))
            return it->second;
        if (x == z[0]) return gz[0];
        return t.mp(t.inst(t.p.use(lm.zero_cong()), {z[0], x}), {t.p.eq_sym(eqz.at(x)), gz[0]});
    }

    H eq_known(const std::string& x, const std::string& y) {
        uint64_t c = known(x);
        return t.mp(t.inst(t.p.use("eq_join"), {x, z[c], y}), {eqz.at(x), eqz.at(y)});
    }

    // false from eq(z_c, z_d), c != d.
    H apart(uint64_t c, uint64_t d, H e) {
        if (c > d) return apart(d, c, t.p.eq_sym(e));
        return t.p.not_elim(use_chain(t, t.p.use(lm.distinct(c, d)), zs(d), gs(d)), e);
    }

    // false from eq(x, y), x and y of different values.
    H clash(const std::string& x, const std::string& y, H e) {
        uint64_t c = known(x), d = known(y);
        H e1 = t.mp(t.inst(t.p.use("eq_trans"), {z[c], x, y}), {t.p.eq_sym(eqz.at(x)), e});
        H e2 = t.mp(t.inst(t.p.use("eq_trans"), {z[c], y, z[d]}), {e1, eqz.at(y)});
        return apart(c, d, e2);
    }

    // false from x being the number c, eq(x, z_c) or zero(x), x of another value.
    H clash_num(const std::string& x, uint64_t c, H h) {
        need(c);
        H e = as_eq(x, h);
        uint64_t d = known(x);
        H e2 = t.mp(t.inst(t.p.use("eq_trans"), {z[c], x, z[d]}), {t.p.eq_sym(e), eqz.at(x)});
        return apart(c, d, e2);
    }

    H at_of(const std::string& r, size_t i) {
        const Entries& e = recs.at(r);
        return t.split(e.rec, e.xs.size() + 1)[i + 1];
    }

    // eq(v, entry i of r), from pmem(z_i, v, r).
    H entry_eq(const std::string& r, size_t i, const std::string& v, H at_v) {
        const Entries& e = recs.at(r);
        return entry_unique(t, r, e.rec, e.xs.size(), i, v, at_v);
    }

    bool truth(const FmP& f) {
        switch (f->k) {
            case Fm::Imp:
                if (f->a->k == Fm::False && f->b->k == Fm::False) return true;
                return !truth(f->a) || truth(f->b);
            case Fm::Not: return !truth(f->a);
            case Fm::And: return truth(f->a) && truth(f->b);
            case Fm::Or: return truth(f->a) || truth(f->b);
            case Fm::Iff: return truth(f->a) == truth(f->b);
            case Fm::Atom:
                if (f->name == "eq" && f->args.size() == 2) return known(f->args[0]) == known(f->args[1]);
                if (f->name == "zero" && f->args.size() == 1) return known(f->args[0]) == 0;
                break;
            case Fm::Exists: {
                auto s = as_some(f);
                if (s && s->body->k == Fm::And)
                    if (auto a = as_at(s->body->a, nums); a && a->v == s->v && recs.count(a->r))
                        return truth(subst(s->body->b, {{s->v, recs.at(a->r).xs.at(a->i)}}));
                if (auto r = as_record(f, nums); r && recs.count(r->t)) return truth(subst(r->rest, rename(r->xs, recs.at(r->t).xs)));
                break;
            }
            default: break;
        }
        throw std::runtime_error("sysprove cannot evaluate " + print(f).substr(0, 300));
    }

    H prove(const FmP& f) {
        if (!truth(f)) throw std::runtime_error("asked to prove what is false: " + print(f).substr(0, 300));
        switch (f->k) {
            case Fm::Imp: {
                if (f->a->k == Fm::False && f->b->k == Fm::False) return t.assume(falsum(), [](H h) { return h; });
                if (!truth(f->a)) {
                    H na = disprove(f->a);
                    return t.assume(f->a, [&](H h) { return t.p.bottom_elim(t.p.not_elim(na, h), f->b); });
                }
                H hb = prove(f->b);
                return t.assume(f->a, [&](H) { return hb; });
            }
            case Fm::Not: return disprove(f->a);
            case Fm::And: return t.p.and_intro(prove(f->a), prove(f->b));
            case Fm::Or: return truth(f->a) ? t.p.or_intro_l(prove(f->a), f->b) : t.p.or_intro_r(f->a, prove(f->b));
            case Fm::Iff:
                if (truth(f->a)) {
                    H hb = prove(f->b), ha = prove(f->a);
                    return t.p.iff_intro(t.assume(f->a, [&](H) { return hb; }), t.assume(f->b, [&](H) { return ha; }));
                } else {
                    H na = disprove(f->a), nb = disprove(f->b);
                    return t.p.iff_intro(t.assume(f->a, [&](H h) { return t.p.bottom_elim(t.p.not_elim(na, h), f->b); }),
                                         t.assume(f->b, [&](H h) { return t.p.bottom_elim(t.p.not_elim(nb, h), f->a); }));
                }
            case Fm::Atom:
                if (f->name == "eq") return eq_known(f->args[0], f->args[1]);
                return zero_of(f->args[0]);
            case Fm::Exists: {
                auto s = as_some(f);
                if (s && s->body->k == Fm::And)
                    if (auto a = as_at(s->body->a, nums); a && a->v == s->v && recs.count(a->r)) {
                        const std::string& e = recs.at(a->r).xs.at(a->i);
                        H k = prove(subst(s->body->b, {{s->v, e}}));
                        return t.witness(f, e, t.p.and_intro(at_of(a->r, a->i), k));
                    }
                if (auto r = as_record(f, nums); r && recs.count(r->t)) return prove_record(f, recs.at(r->t));
                break;
            }
            default: break;
        }
        throw std::runtime_error("sysprove cannot prove " + print(f).substr(0, 300));
    }

    H disprove(const FmP& f) {
        if (truth(f)) throw std::runtime_error("asked to refute what is true: " + print(f).substr(0, 300));
        switch (f->k) {
            case Fm::Imp: {
                H ha = prove(f->a), nb = disprove(f->b);
                return t.refute(f, [&](H h) { return t.p.not_elim(nb, t.p.implies_elim(h, ha)); });
            }
            case Fm::Not: {
                H ha = prove(f->a);
                return t.refute(f, [&](H h) { return t.p.not_elim(h, ha); });
            }
            case Fm::And:
                if (!truth(f->a)) {
                    H na = disprove(f->a);
                    return t.refute(f, [&](H h) { return t.p.not_elim(na, t.p.and_l(h)); });
                } else {
                    H nb = disprove(f->b);
                    return t.refute(f, [&](H h) { return t.p.not_elim(nb, t.p.and_r(h)); });
                }
            case Fm::Or: {
                H na = disprove(f->a), nb = disprove(f->b);
                return t.refute(f, [&](H h) {
                    return t.cases(h, [&](H l) { return t.p.not_elim(na, l); }, [&](H r) { return t.p.not_elim(nb, r); });
                });
            }
            case Fm::Iff:
                if (truth(f->a)) {
                    H ha = prove(f->a), nb = disprove(f->b);
                    return t.refute(f, [&](H h) { return t.p.not_elim(nb, t.p.iff_l(h, ha)); });
                } else {
                    H hb = prove(f->b), na = disprove(f->a);
                    return t.refute(f, [&](H h) { return t.p.not_elim(na, t.p.iff_r(h, hb)); });
                }
            case Fm::Atom:
                if (f->name == "eq") return t.refute(f, [&](H h) { return clash(f->args[0], f->args[1], h); });
                return t.refute(f, [&](H h) { return clash_num(f->args[0], 0, h); });
            case Fm::Exists: {
                auto s = as_some(f);
                if (s && s->body->k == Fm::And) {
                    if (auto a = as_at(s->body->a, nums); a && a->v == s->v && recs.count(a->r)) {
                        return t.refute(f, [&](H h) {
                            return t.obtain(h, "w", [&](const std::string& w, H body) {
                                std::vector<H> lk = t.split(body, 2);
                                same_as(w, recs.at(a->r).xs.at(a->i), entry_eq(a->r, a->i, w, lk[0]));
                                return t.p.not_elim(disprove(subst(s->body->b, {{s->v, w}})), lk[1]);
                            });
                        });
                    }
                }
                if (auto r = as_record(f, nums); r && recs.count(r->t)) {
                    return t.refute(f, [&](H h) { return refute_record(h, *r, 0, {}); });
                }
                break;
            }
            default: break;
        }
        throw std::runtime_error("sysprove cannot refute " + print(f).substr(0, 300));
    }

    // Under the record pattern's witnesses w, its rest refuted.
    H refute_record(H h, const RecordP& r, size_t i, std::vector<std::string> ws) {
        return t.obtain(h, "w", [&](const std::string& w, H body) -> H {
            ws.push_back(w);
            if (i + 1 < r.xs.size()) return refute_record(body, r, i + 1, ws);
            std::vector<H> rb = t.split(body, 2);
            const Entries& known = recs.at(r.t);
            for (size_t j = 0; j < ws.size(); ++j) {
                H at = t.split(rb[0], ws.size() + 1)[j + 1];
                same_as(ws[j], known.xs[j], entry_eq(r.t, j, ws[j], at));
            }
            return t.p.not_elim(disprove(subst(r.rest, rename(r.xs, ws))), rb[1]);
        });
    }

    H prove_record(const FmP& f, const Entries& e) {
        std::function<H(const FmP&, size_t)> go = [&](const FmP& g, size_t i) -> H {
            if (i == e.xs.size()) {
                FmP rest = g->b;
                return t.p.and_intro(e.rec, prove(rest));
            }
            auto s = as_some(g);
            H inner = go(subst(s->body, {{s->v, e.xs[i]}}), i + 1);
            return t.witness(g, e.xs[i], inner);
        };
        return go(f, 0);
    }

    static std::map<std::string, std::string> rename(const std::vector<std::string>& from, const std::vector<std::string>& to) {
        std::map<std::string, std::string> m;
        for (size_t i = 0; i < from.size(); ++i) m[from[i]] = to[i];
        return m;
    }

    void need(uint64_t c) const {
        if (c >= z.size()) throw std::runtime_error("a numeral beyond the proof's " + std::to_string(z.size()));
    }
};

// ---- Components: their characterizations and notations ----

struct Comp {
    std::string label;
    ComponentDef::Kind kind;
    size_t of = 0;          // Condition: the component its elements come from
    size_t roles[3] = {0, 0, 0};  // Rules: state, input, output
};

std::vector<Comp> comps_of(const Program& p, NameId inst) {
    std::vector<Comp> out;
    NameId sid = p.name(inst).structure;
    const std::vector<FieldId>& fs = p.name(sid).fields;
    auto index = [&](FieldId f) {
        for (size_t i = 0; i < fs.size(); ++i)
            if (fs[i] == f) return i;
        throw std::runtime_error("a field outside its structure");
    };
    for (FieldId f : fs) {
        Comp c{p.field(f).label, ComponentDef::Parts};
        const NodeP& type = p.field(f).type;
        if (type && type->k == K::SetType && type->kids[0]->k == K::Comp) {
            c.kind = ComponentDef::Condition;
            c.of = index(type->kids[0]->field);
        } else if (type && type->k == K::SetType && type->kids[0]->k == K::Tuple) {
            c.kind = ComponentDef::Rules;
            for (int i = 0; i < 3; ++i) c.roles[i] = index(type->kids[0]->kids[i]->field);
        } else if (type) {
            throw std::runtime_error("no proof route for the field " + c.label);
        }
        out.push_back(c);
    }
    return out;
}

// The prefix of a claim: its n components, each a set, then each one's characterization; body proves the rest.
H with_components(Tac& t, FmP f, size_t n,
                  const std::function<H(const std::vector<std::string>&, const std::vector<H>&, FmP)>& body) {
    std::vector<std::string> names;
    std::vector<H> chars;
    std::function<H(FmP, size_t)> go = [&](FmP g, size_t i) -> H {
        if (i < n) {
            auto b = as_all(g);
            if (!b) throw std::runtime_error("a claim without its components");
            FmP rest = b->body;
            std::string bv = b->v;
            return t.all("C", [&](const std::string& x) {
                names.push_back(x);
                H h = go(subst(rest, {{bv, x}}), i + 1);
                names.pop_back();
                return h;
            });
        }
        if (i < 2 * n) {
            if (g->k != Fm::Imp) throw std::runtime_error("a claim without its characterizations");
            return t.assume(g->a, [&](H c) {
                chars.push_back(c);
                H h = go(g->b, i + 1);
                chars.pop_back();
                return h;
            });
        }
        return body(names, chars, g);
    };
    return go(std::move(f), 0);
}

// The characterization's right side at q: elem(q, C) <-> it.
FmP member_at(Tac& t, H chr, const std::string& q) {
    auto b = as_all(t.p.fm(chr));
    return subst(b->body, {{b->v, q}})->b;
}

H member_iff(Tac& t, H chr, const std::string& q) { return t.inst(chr, {q}); }

std::string sets_name(const std::map<std::string, std::string>& sets, const std::string& purpose) {
    auto it = sets.find(purpose);
    if (it == sets.end()) throw std::runtime_error("no class machine claim for " + purpose);
    return it->second;
}

// The step relation's pieces: its bound names and rules, from its characterization's right side.
struct StepShape {
    std::string s, a, b, t;
    std::vector<FmP> rules;
};

StepShape step_shape(const FmP& m) {
    StepShape sh;
    auto s = as_some(m);
    sh.s = s->v;
    auto a = as_some(s->body->b);
    sh.a = a->v;
    auto b = as_some(a->body->b);
    sh.b = b->v;
    auto tt = as_some(b->body);
    sh.t = tt->v;
    sh.rules = disjuncts(tt->body->b);
    return sh;
}

class ClaimProofs {
public:
    ClaimProofs(const Program& p, std::map<std::string, FmP>& known, Lemmas& lm, const std::map<std::string, std::string>& sets,
                std::string ns)
        : p_(p), known_(known), lm_(lm), sets_(sets), ns_(std::move(ns)) {}

    std::string prove(const std::string& name, const FmP& claim) {
        Proof pr(name, known_);
        Tac t(pr);
        H h = dispatch(t, name, claim);
        if (!alpha_eq(pr.fm(h), claim)) throw std::runtime_error("the proof of " + name + " ends with another formula");
        pr.qed(h);
        return pr.text();
    }

private:
    const Program& p_;
    std::map<std::string, FmP>& known_;
    Lemmas& lm_;
    const std::map<std::string, std::string>& sets_;
    std::string ns_;
    static constexpr size_t N = 4;

    // The numbers each proof under way names: its claim's own, from its top, then any built after them. A lemma's proof
    // runs inside a claim's, so each proof has its own.
    struct Numbers {
        std::vector<std::string> z;
        std::vector<H> gz;
    };
    std::deque<Numbers> nums_;

    Nums zv() const {
        Nums m;
        const Numbers& n = nums_.back();
        for (size_t c = 0; c < n.z.size(); ++c) m[n.z[c]] = c;
        return m;
    }

    // The numbers a formula names at its top, each fixed with its defining atom; body proves the rest.
    H with_numbers(Tac& t, const FmP& f, const std::function<H(FmP)>& body) {
        nums_.push_back({});
        std::function<H(FmP)> go = [&](FmP g) -> H {
            auto b = as_all(g);
            const Numbers& n = nums_.back();
            if (!b || b->body->k != Fm::Imp ||
                !(n.z.empty() ? is_atom(b->body->a, "zero", {b->v}) : is_atom(b->body->a, "nsucc", {n.z.back(), b->v})))
                return body(g);
            FmP rest = b->body;
            std::string bv = b->v;
            return t.all("z", [&](const std::string& x) {
                FmP r = subst(rest, {{bv, x}});
                return t.assume(r->a, [&](H g0) {
                    nums_.back().z.push_back(x);
                    nums_.back().gz.push_back(g0);
                    H h = go(r->b);
                    nums_.back().z.pop_back();
                    nums_.back().gz.pop_back();
                    return h;
                });
            });
        };
        H h = go(f);
        nums_.pop_back();
        return h;
    }

    // The proof's numbers, at least z_0, ..., z_n, any past its claim's built from the last as its successor.
    H numerals(Tac& t, size_t n, const std::function<H(const std::vector<std::string>&, const std::vector<H>&)>& body) {
        const Numbers& ns = nums_.back();
        if (ns.z.size() > n) return body(ns.z, ns.gz);
        H ex = ns.z.empty() ? t.p.use("zero_EX") : t.inst(t.p.use("nsucc_EX"), {ns.z.back()});
        return t.obtain(ex, "z", [&](const std::string& z, H g) {
            nums_.back().z.push_back(z);
            nums_.back().gz.push_back(g);
            H h = numerals(t, n, body);
            nums_.back().z.pop_back();
            nums_.back().gz.pop_back();
            return h;
        });
    }

    // f closed over the proof's numbers it uses, named at its top as a claim names them; k their count.
    FmP close_numbers(const FmP& f, size_t& k) const {
        const Numbers& n = nums_.back();
        std::set<std::string> fv = free_vars(f);
        k = 0;
        for (size_t c = 0; c < n.z.size(); ++c)
            if (fv.count(n.z[c])) k = c + 1;
        FmP g = f;
        for (size_t c = k; c-- > 0;) g = all(n.z[c], imp(c == 0 ? atom("zero", {n.z[0]}) : atom("nsucc", {n.z[c - 1], n.z[c]}), g));
        return g;
    }

    // A claim stated over the first k numbers, at the proof's own.
    H at_numbers(Tac& t, H h, size_t k) {
        const Numbers& n = nums_.back();
        if (n.z.size() < k) throw std::runtime_error("a claim over more numbers than the proof names");
        return use_chain(t, h, {n.z.begin(), n.z.begin() + k}, {n.gz.begin(), n.gz.begin() + k});
    }

    // The numbers a formula names at its top.
    static size_t number_binders(FmP f) {
        size_t k = 0;
        std::string prev;
        while (auto b = as_all(f)) {
            if (b->body->k != Fm::Imp || !(k == 0 ? is_atom(b->body->a, "zero", {b->v}) : is_atom(b->body->a, "nsucc", {prev, b->v})))
                break;
            prev = b->v;
            ++k;
            f = b->body->b;
        }
        return k;
    }

    // A claim, its numbers at the proof's own.
    H cite(Tac& t, const std::string& name) { return at_numbers(t, t.p.use(name), number_binders(known_.at(name))); }

    // Sys.tuple4(q, x0, x1, x2, x3) <-> Rec_4(q; x), at the proof's numbers.
    H tuple4_iff(Tac& t, const std::vector<std::string>& args) { return t.inst(at_numbers(t, t.p.use(lm_.tuple4_at()), 5), args); }

    H dispatch(Tac& t, const std::string& name, const FmP& claim) {
        return with_numbers(t, claim, [&](FmP rest) { return dispatch_body(t, name, rest); });
    }

    H dispatch_body(Tac& t, const std::string& name, const FmP& claim) {
        for (NameId i : p_.instances) {
            const std::string& in = p_.name(i).text;
            std::vector<Comp> cs = comps_of(p_, i);
            bool own = name == ns_ + "." + in + "_wellformed";
            for (size_t f = 0; f < cs.size(); ++f) own = own || name == ns_ + "." + in + "_" + cs[f].label + "_exists";
            if (own && !p_.name(i).params.empty()) {
                if (name == ns_ + "." + in + "_wellformed") return wellformed_params(t, claim, cs, i, in);
                for (size_t f = 0; f < cs.size(); ++f)
                    if (name == ns_ + "." + in + "_" + cs[f].label + "_exists") return exists_params(t, claim, cs, f, i);
            }
            if (name == ns_ + "." + in + "_wellformed") return wellformed(t, claim, cs, in);
            for (size_t f = 0; f < cs.size(); ++f)
                if (name == ns_ + "." + in + "_" + cs[f].label + "_exists") return exists(t, claim, cs, f, in);
        }
        for (const Theorem& th : p_.theorems)
            if (name == ns_ + "." + th.name) return th.params.empty() ? theorem(t, claim, th.name) : length_theorem(t, claim, th);
        throw std::runtime_error("no proof route for " + name);
    }

    // A record's entries from its membership in a component written as parts, then k.
    H entries(Tac& t, Eval& ev, const std::string& q, H member, size_t k, bool split, const std::function<H()>& k_) {
        if (k == 0) {
            ev.value(q, 0, member);
            return k_();
        }
        std::vector<std::string> xs;
        std::function<H(H, size_t)> go = [&](H h, size_t i) -> H {
            return t.obtain(h, "e", [&](const std::string& x, H body) -> H {
                xs.push_back(x);
                H r = i + 1 < k ? go(body, i + 1) : [&] {
                    std::vector<H> rb = t.split(body, 2);
                    ev.recs[q] = {xs, rb[0]};
                    std::vector<H> rngs = t.split(rb[1], k);
                    for (size_t j = 0; j < k; ++j) ev.rng[xs[j]] = rngs[j];
                    if (!split) return k_();
                    return values(t, ev, xs, rngs, 0, k_);
                }();
                xs.pop_back();
                return r;
            });
        };
        return go(member, 0);
    }

    H values(Tac& t, Eval& ev, const std::vector<std::string>& xs, const std::vector<H>& rngs, size_t j,
             const std::function<H()>& k) {
        if (j == xs.size()) return k();
        size_t n = disjuncts(t.p.fm(rngs[j])).size();
        if (n == 1) {
            ev.value(xs[j], 0, rngs[j]);
            return values(t, ev, xs, rngs, j + 1, k);
        }
        return t.cases(rngs[j], n, [&](size_t c, H h) {
            ev.value(xs[j], c, h);
            return values(t, ev, xs, rngs, j + 1, k);
        });
    }

    size_t arity(const FmP& m) {
        if (m->k == Fm::Atom) return 0;
        size_t k = 0;
        FmP g = m;
        while (auto b = as_some(g)) {
            ++k;
            g = b->body;
            if (g->k != Fm::Exists) break;
        }
        return k;
    }

    // Learns x's value from a record-of value fact: a numeral, or a copy of an entry of a known record.
    H learn(Tac& t, Eval& ev, const std::string& x, H fact, const std::function<H()>& k) {
        const FmP& f = t.p.fm(fact);
        if (auto n = as_num(f, ev.nums); n && n->second == x) {
            ev.value(x, n->first, fact);
            return k();
        }
        auto s = as_some(f);
        if (s && s->body->k == Fm::And)
            if (auto a = as_at(s->body->a, ev.nums); a && a->v == s->v && ev.recs.count(a->r)) {
                return t.obtain(fact, "w", [&](const std::string& w, H body) {
                    std::vector<H> lk = t.split(body, 2);
                    const std::string& e = ev.recs.at(a->r).xs.at(a->i);
                    H we = ev.entry_eq(a->r, a->i, w, lk[0]);
                    H xw = lk[1];
                    if (!is_atom(t.p.fm(xw), "eq", {x, w})) throw std::runtime_error("a copied value of another shape");
                    H xe = t.mp(t.inst(t.p.use("eq_trans"), {x, w, e}), {xw, we});
                    ev.same_as(x, e, xe);
                    return k();
                });
            }
        throw std::runtime_error("sysprove cannot read the value " + print(f).substr(0, 200));
    }

    // From a record-of fact (exists x. Rec(r; x) & values): r's entries and their values, then k.
    H learn_record(Tac& t, Eval& ev, const std::string& r, H fact, size_t k, const std::function<H()>& k_) {
        if (k == 0) {
            ev.value(r, 0, fact);
            return k_();
        }
        std::vector<std::string> xs;
        std::function<H(H, size_t)> go = [&](H h, size_t i) -> H {
            return t.obtain(h, "y", [&](const std::string& x, H body) -> H {
                xs.push_back(x);
                H res;
                if (i + 1 < k) {
                    res = go(body, i + 1);
                } else {
                    std::vector<H> rb = t.split(body, 2);
                    ev.recs[r] = {xs, rb[0]};
                    std::vector<H> vs = t.split(rb[1], k);
                    std::function<H(size_t)> each = [&](size_t j) -> H {
                        if (j == k) return k_();
                        return learn(t, ev, xs[j], vs[j], [&] { return each(j + 1); });
                    };
                    res = each(0);
                }
                xs.pop_back();
                return res;
            });
        };
        return go(fact, 0);
    }

    // x's entries, linked to those of y = x (both records of the same component): x's values become y's.
    void relate(Tac& t, Eval& ev, const std::string& x, H eq_x_y, const std::string& y) {
        const Entries& ex = ev.recs.at(x);
        for (size_t i = 0; i < ex.xs.size(); ++i) {
            H at = ev.at_of(x, i);
            H at2 = t.mp(t.inst(t.p.use(lm_.pmem_cong3()), {ev.z[i], ex.xs[i], x, y}), {eq_x_y, at});
            H e = ev.entry_eq(y, i, ex.xs[i], at2);
            ev.same_as(ev.recs.at(y).xs[i], ex.xs[i], t.p.eq_sym(e));
        }
    }

    // ---- Well-formedness ----

    H wellformed(Tac& t, const FmP& claim, const std::vector<Comp>& cs, const std::string& in) {
        return with_components(t, claim, cs.size(), [&](const std::vector<std::string>& C, const std::vector<H>& ch, FmP body) {
            return numerals(t, N, [&](const std::vector<std::string>& z, const std::vector<H>& gz) {
                Eval ev(t, lm_, z, gz);
                size_t rules = 0;
                for (size_t i = 0; i < cs.size(); ++i)
                    if (cs[i].kind == ComponentDef::Rules) rules = i;
                const Comp& rc = cs[rules];
                size_t S = rc.roles[0], A = rc.roles[1], B = rc.roles[2], I = 0;
                for (size_t i = 0; i < cs.size(); ++i)
                    if (cs[i].kind == ComponentDef::Condition) I = i;
                if (body->k != Fm::Atom || body->name != "Sys.wellformed") throw std::runtime_error("an unknown well-formedness");
                H def = t.inst(t.p.use("Sys.wellformed_def"), body->args);
                FmP parts = t.p.fm(def)->b;
                std::vector<FmP> goals = conjuncts(parts, 3);
                H w1 = t.all("u", [&](const std::string& u) {
                    return t.assume(atom("elem", {u, C[I]}), [&](H h) { return t.p.and_l(t.p.iff_l(member_iff(t, ch[I], u), h)); });
                });
                H w2 = t.all("q", [&](const std::string& q) {
                    return t.assume(atom("elem", {q, C[rules]}), [&](H h) {
                        H sm = t.p.iff_l(member_iff(t, ch[rules], q), h);
                        FmP goal = subst(as_all(goals[1])->body, {{as_all(goals[1])->v, q}})->b;
                        return typed_once(t, in, {}, {C[S], C[A], C[B]}, ch[S], ch[B], q, sm, &ev,
                                          [&](const std::string& s, H sS, const std::string& a, H aA, const std::string& b,
                                              H bB, const std::string& tt, H tS, H rec4) {
                            H t4 = t.p.iff_r(tuple4_iff(t, {q, s, a, b, tt}), rec4);
                            return exists_chain(t, goal, {s, a, b, tt}, {sS, aA, bB, tS}, t4);
                        });
                    });
                });
                H w3 = enabled(t, ev, C, ch, S, A, rules, goals[2]);
                return t.p.iff_r(def, t.join({w1, w2, w3}));
            });
        });
    }

    // (exists x1. (set(x1) & (m1 & (exists x2. ...)))): each witness with its membership, then last.
    H exists_chain(Tac& t, const FmP& goal, const std::vector<std::string>& ws, const std::vector<H>& mems, H last) {
        std::function<H(const FmP&, size_t)> go = [&](const FmP& g, size_t i) -> H {
            if (i == ws.size()) return last;
            auto s = as_some(g);
            FmP body = subst(s->body, {{s->v, ws[i]}});
            H inner = go(body->b, i + 1);
            return t.witness(g, ws[i], t.p.and_intro(mems[i], inner));
        };
        return go(goal, 0);
    }

    // Each step's parts typed: from q's membership in the step relation, its state, input, output and next state, each
    // in its set, then k, once: every case of a rule and of the state's values ends in the same two memberships.
    H typed(Tac& t, Eval& ev, const std::vector<H>& ch, size_t S, size_t B, H sm,
            const std::function<H(const std::string&, H, const std::string&, H, const std::string&, H, const std::string&, H, H)>& k) {
        return t.obtain(sm, "s", [&](const std::string& s, H b1) {
            std::vector<H> s1 = t.split(b1, 2);
            return t.obtain(s1[1], "a", [&](const std::string& a, H b2) {
                std::vector<H> a1 = t.split(b2, 2);
                return t.obtain(a1[1], "b", [&](const std::string& b, H b3) {
                    return t.obtain(b3, "t", [&](const std::string& tt, H b4) {
                        std::vector<H> rr = t.split(b4, 2);
                        size_t ks = arity(member_at(t, ch[S], s));
                        size_t kb = arity(member_at(t, ch[B], b));
                        H sS = s1[0];
                        H sm2 = t.p.iff_l(member_iff(t, ch[S], s), sS);
                        size_t nrules = disjuncts(t.p.fm(rr[1])).size();
                        auto val = ev.val;
                        auto num = ev.num, eqz = ev.eqz, rng = ev.rng;
                        auto recs = ev.recs;
                        H both = entries(t, ev, s, sm2, ks, true, [&] {
                            return t.cases(rr[1], nrules, [&](size_t, H rule) {
                                std::vector<H> parts = t.split(rule, 3);
                                return learn_record(t, ev, tt, parts[1], ks, [&] {
                                    return learn_record(t, ev, b, parts[2], kb, [&] {
                                        H tS = t.p.iff_r(member_iff(t, ch[S], tt), ev.prove(member_at(t, ch[S], tt)));
                                        H bB = t.p.iff_r(member_iff(t, ch[B], b), ev.prove(member_at(t, ch[B], b)));
                                        return t.p.and_intro(tS, bB);
                                    });
                                });
                            });
                        });
                        ev.val = val;
                        ev.num = num;
                        ev.eqz = eqz;
                        ev.rng = rng;
                        ev.recs = recs;
                        return k(s, sS, a, a1[0], b, t.p.and_r(both), tt, t.p.and_l(both), rr[0]);
                    });
                });
            });
        });
    }

    // Every state and input has a step: for each of their values, the first rule that applies.
    H enabled(Tac& t, Eval& ev, const std::vector<std::string>& C, const std::vector<H>& ch, size_t S, size_t A, size_t R,
              const FmP& goal3) {
        return t.all("s", [&](const std::string& s) {
            return t.assume(atom("elem", {s, C[S]}), [&](H sS) {
                return t.all("a", [&](const std::string& a) {
                    return t.assume(atom("elem", {a, C[A]}), [&](H aA) {
                        FmP g = subst(as_all(goal3)->body, {{as_all(goal3)->v, s}})->b;
                        g = subst(as_all(g)->body, {{as_all(g)->v, a}})->b;
                        size_t ks = arity(member_at(t, ch[S], s)), ka = arity(member_at(t, ch[A], a));
                        H sm = t.p.iff_l(member_iff(t, ch[S], s), sS);
                        H am = t.p.iff_l(member_iff(t, ch[A], a), aA);
                        return entries(t, ev, s, sm, ks, true, [&] {
                            return entries(t, ev, a, am, ka, true, [&] { return step_for(t, ev, C, ch, R, s, sS, a, aA, g); });
                        });
                    });
                });
            });
        });
    }

    H step_for(Tac& t, Eval& ev, const std::vector<std::string>& C, const std::vector<H>& ch, size_t R, const std::string& s, H sS, const std::string& a, H aA, const FmP& goal) {
        std::string q0 = fresh("_q");
        StepShape sh = step_shape(member_at(t, ch[R], q0));
        for (size_t j = 0; j < sh.rules.size(); ++j) {
            std::vector<FmP> parts = conjuncts(sh.rules[j], 3);
            FmP when = subst(parts[0], {{sh.s, s}, {sh.a, a}});
            if (!ev.truth(when)) continue;
            // The rule's next state and output, built from its values.
            return build(t, ev, subst(parts[1], {{sh.s, s}, {sh.a, a}}), [&](const std::string& tt) {
                return build(t, ev, subst(parts[2], {{sh.s, s}, {sh.a, a}, {sh.t, tt}}), [&](const std::string& b) {
                    H ex = t.inst(use_chain(t, t.p.use(lm_.rec_ex(4)), ev.zs(4), ev.gs(4)), {s, a, b, tt});
                    return t.obtain(ex, "q", [&](const std::string& q, H rec4) {
                        ev.recs.erase(q);
                        FmP sm = member_at(t, ch[R], q);
                        auto s1 = as_some(sm);
                        FmP b1 = subst(s1->body, {{s1->v, s}});
                        auto a1 = as_some(b1->b);
                        FmP b2 = subst(a1->body, {{a1->v, a}});
                        auto bb = as_some(b2->b);
                        FmP b3 = subst(bb->body, {{bb->v, b}});
                        auto t1 = as_some(b3);
                        FmP b4 = subst(t1->body, {{t1->v, tt}});
                        std::vector<FmP> rules = disjuncts(b4->b);
                        H rule = inject(t, ev.prove(rules[j]), rules, j);
                        H inner = t.witness(b3, tt, t.p.and_intro(rec4, rule));
                        H hb = t.witness(b2->b, b, inner);
                        H ha = t.witness(b1->b, a, t.p.and_intro(aA, hb));
                        H hs = t.witness(sm, s, t.p.and_intro(sS, ha));
                        H qT = t.p.iff_r(member_iff(t, ch[R], q), hs);
                        H t4 = t.p.iff_r(tuple4_iff(t, {q, s, a, b, tt}), rec4);
                        H trans = transition(t, C[R], s, a, b, tt, q, qT, t4);
                        auto gb = as_some(goal);
                        FmP gt = subst(gb->body, {{gb->v, b}});
                        H ht = t.witness(gt, tt, trans);
                        return t.witness(goal, b, ht);
                    });
                });
            });
        }
        throw std::runtime_error("no rule applies to a state and input: the system is not input-enabled");
    }

    H transition(Tac& t, const std::string& T, const std::string& s, const std::string& a, const std::string& b,
                 const std::string& tt, const std::string& q, H qT, H t4) {
        H def = t.inst(t.p.use("Sys.transition_def"), {T, s, a, b, tt});
        FmP target = t.p.fm(def)->b;
        return t.p.iff_r(def, t.witness(target, q, t.p.and_intro(qT, t4)));
    }

    // A record built from a record-of pattern's values, then k with its name.
    H build(Tac& t, Eval& ev, const FmP& recof, const std::function<H(const std::string&)>& k) {
        if (auto n = as_num(recof, ev.nums); n && n->first == 0) return k(ev.z[0]);
        auto r = as_record(recof, ev.nums);
        if (!r) throw std::runtime_error("a next state of an unknown shape");
        std::vector<FmP> vals = conjuncts(r->rest, r->xs.size());
        std::vector<std::string> es;
        for (size_t j = 0; j < vals.size(); ++j) {
            if (auto n = as_num(vals[j], ev.nums); n && n->second == r->xs[j]) {
                es.push_back(ev.z[n->first]);
                continue;
            }
            auto s = as_some(vals[j]);
            auto a = s ? as_at(s->body->a, ev.nums) : std::nullopt;
            if (!a || !ev.recs.count(a->r)) throw std::runtime_error("a next value of an unknown shape");
            es.push_back(ev.recs.at(a->r).xs.at(a->i));
        }
        H ex = t.inst(use_chain(t, t.p.use(lm_.rec_ex(es.size())), ev.zs(es.size()), ev.gs(es.size())), es);
        return t.obtain(ex, "r", [&](const std::string& x, H rec) {
            ev.recs[x] = {es, rec};
            return k(x);
        });
    }

    // ---- Well-formedness over parameters ----

    // A value of a rule, by the formula that defines it from earlier ones.
    struct Val {
        enum Kind { Opaque, Field, Append, Rest, Num, Record } kind = Opaque;
        H def;
        std::string from, elt;        // Field: the record or sequence read; Append: the sequence and element; Rest: the sequence
        size_t i = 0;                 // Field: the entry
        uint64_t n = 0;               // Num
        std::vector<std::string> ys;  // Record: its entries
    };
    struct Sym {
        std::map<std::string, Val> vals;
        std::map<std::string, H> types;
        std::map<std::string, std::pair<std::vector<std::string>, H>> recs;
    };

    static Val classify(const FmP& f, const std::string& v, H def, const Nums& nums) {
        Val x;
        x.def = def;
        if (auto a = as_at(f, nums); a && a->v == v) {
            x.kind = Val::Field;
            x.from = a->r;
            x.i = a->i;
        } else if (auto n = as_num(f, nums); n && n->second == v) {
            x.kind = Val::Num;
            x.n = n->first;
        } else if (auto r = as_rest(f); r && r->r == v) {
            x.kind = Val::Rest;
            x.from = r->v;
        } else if (auto ap = as_append(f); ap && ap->r == v) {
            x.kind = Val::Append;
            x.from = ap->v;
            x.elt = ap->y;
        } else if (auto rc = as_rec(f, nums); rc && rc->t == v) {
            x.kind = Val::Record;
            x.ys = rc->xs;
        }
        return x;
    }

    H wellformed_params(Tac& t, const FmP& claim, const std::vector<Comp>& cs, NameId inst, const std::string& in) {
        return with_params(t, claim, p_.name(inst).params, [&](const std::vector<std::string>& P, const std::vector<H>& hyps, FmP g) {
            return with_components(t, g, cs.size(), [&](const std::vector<std::string>& C, const std::vector<H>& ch, FmP body) {
                size_t R = 0, I = 0;
                for (size_t i = 0; i < cs.size(); ++i) {
                    if (cs[i].kind == ComponentDef::Rules) R = i;
                    if (cs[i].kind == ComponentDef::Condition) I = i;
                }
                size_t S = cs[R].roles[0], A = cs[R].roles[1], B = cs[R].roles[2];
                if (body->k != Fm::Atom || body->name != "Sys.wellformed") throw std::runtime_error("an unknown well-formedness");
                H def = t.inst(t.p.use("Sys.wellformed_def"), body->args);
                std::vector<FmP> goals = conjuncts(t.p.fm(def)->b, 3);
                H w1 = t.all("u", [&](const std::string& u) {
                    return t.assume(atom("elem", {u, C[I]}), [&](H h) { return t.p.and_l(t.p.iff_l(member_iff(t, ch[I], u), h)); });
                });
                H w2 = t.all("q", [&](const std::string& q) {
                    return t.assume(atom("elem", {q, C[R]}), [&](H h) {
                        H sm = t.p.iff_l(member_iff(t, ch[R], q), h);
                        FmP goal = subst(as_all(goals[1])->body, {{as_all(goals[1])->v, q}})->b;
                        return typed_once(t, in, P, {C[S], C[A], C[B]}, ch[S], ch[B], q, sm, nullptr,
                                          [&](const std::string& s, H sS, const std::string& a, H aA, const std::string& b,
                                              H bB, const std::string& tt, H tS, H rec4) {
                            H t4 = t.p.iff_r(tuple4_iff(t, {q, s, a, b, tt}), rec4);
                            return exists_chain(t, goal, {s, a, b, tt}, {sS, aA, bB, tS}, t4);
                        });
                    });
                });
                H w3 = enabled_params(t, C, ch, S, A, R, hyps, goals[2]);
                return t.p.iff_r(def, t.join({w1, w2, w3}));
            });
        });
    }

    // target = (exists x1. ... (exists xk. body)), from body at ws.
    H witness_all(Tac& t, const FmP& target, const std::vector<std::string>& ws, H inner) {
        std::vector<FmP> levels{target};
        for (size_t i = 0; i + 1 < ws.size(); ++i) {
            auto s = as_some(levels.back());
            levels.push_back(subst(s->body, {{s->v, ws[i]}}));
        }
        H h = inner;
        for (size_t i = ws.size(); i-- > 0;) h = t.witness(levels[i], ws[i], h);
        return h;
    }

    // ---- W2: each step's parts in their sets, each value typed by how its rule builds it ----

    H typed_params(Tac& t, const std::vector<H>& ch, size_t S, size_t B, H sm,
                   const std::function<H(const std::string&, H, const std::string&, H, const std::string&, H, const std::string&, H, H)>& k) {
        return t.obtain(sm, "s", [&](const std::string& s, H b1) {
            std::vector<H> s1 = t.split(b1, 2);
            return t.obtain(s1[1], "a", [&](const std::string& a, H b2) {
                std::vector<H> a1 = t.split(b2, 2);
                return t.obtain(a1[1], "b", [&](const std::string& b, H b3) {
                    return t.obtain(b3, "t", [&](const std::string& tt, H b4) {
                        std::vector<H> rr = t.split(b4, 2);
                        Sym sym;
                        return open_member(t, sym, s, t.p.iff_l(member_iff(t, ch[S], s), s1[0]), [&] {
                            size_t nr = disjuncts(t.p.fm(rr[1])).size();
                            H both = t.cases(rr[1], nr, [&](size_t, H rule) {
                                return rule_typed(t, sym, ch, S, B, tt, b, rule,
                                                  [&](H tS, H bB) { return t.p.and_intro(tS, bB); });
                            });
                            return k(s, s1[0], a, a1[0], b, t.p.and_r(both), tt, t.p.and_l(both), rr[0]);
                        });
                    });
                });
            });
        });
    }

    // x's entries and their types, from its membership (exists y. (Rec_k(x; y) & types)).
    H open_member(Tac& t, Sym& sym, const std::string& x, H m, const std::function<H()>& k) {
        auto rp = as_record(t.p.fm(m), zv());
        if (!rp) return k();
        size_t kf = rp->xs.size();
        std::vector<std::string> ys;
        std::function<H(H, size_t)> go = [&](H h, size_t i) -> H {
            if (i < kf)
                return t.obtain(h, "f", [&](const std::string& y, H b) {
                    ys.push_back(y);
                    H r = go(b, i + 1);
                    ys.pop_back();
                    return r;
                });
            std::vector<H> rv = t.split(h, 2);
            std::vector<H> tys = t.split(rv[1], kf);
            sym.recs[x] = {ys, rv[0]};
            for (size_t j = 0; j < kf; ++j) sym.types[ys[j]] = tys[j];
            return k();
        };
        return go(m, 0);
    }

    H rule_typed(Tac& t, Sym& sym, const std::vector<H>& ch, size_t S, size_t B, const std::string& tt, const std::string& b,
                 H rule, const std::function<H(H, H)>& k) {
        if (t.p.fm(rule)->k == Fm::Exists)
            return t.obtain(rule, "j", [&](const std::string& x, H body) {
                std::vector<H> p = t.split(body, 2);
                sym.types[x] = p[0];
                return rule_typed(t, sym, ch, S, B, tt, b, p[1], k);
            });
        std::vector<H> parts = t.split(rule, 3);
        return member_of(t, sym, ch[S], tt, parts[1], [&](H tS) {
            return member_of(t, sym, ch[B], b, parts[2], [&](H bB) { return k(tS, bB); });
        });
    }

    // From a fact (exists v. (D(v) & rest)): v and what D says of it, then rest the same way; k with the last fact.
    H walk(Tac& t, Sym& sym, H h, const std::function<H(H)>& k) {
        auto s = as_some(t.p.fm(h));
        if (!s || s->body->k != Fm::And) return k(h);
        return t.obtain(h, s->v, [&](const std::string& v, H b) {
            std::vector<H> dr = t.split(b, 2);
            sym.vals[v] = classify(t.p.fm(dr[0]), v, dr[0], zv());
            return walk(t, sym, dr[1], k);
        });
    }

    // elem(x, C) from the rule's record-of fact for x (exists y. (Rec_k(x; y) & values)), each value typed.
    H member_of(Tac& t, Sym& sym, H chr, const std::string& x, H recof, const std::function<H(H)>& k) {
        FmP M = member_at(t, chr, x);
        auto rp = as_record(t.p.fm(recof), zv());
        auto mp = as_record(M, zv());
        if (!rp || !mp || rp->xs.size() != mp->xs.size()) throw std::runtime_error("a next state or output of an unknown shape");
        size_t kf = rp->xs.size();
        std::vector<std::string> ys;
        std::vector<H> typed(kf);
        std::function<H(H, size_t)> go = [&](H h, size_t i) -> H {
            if (i < kf)
                return t.obtain(h, "y", [&](const std::string& y, H b) {
                    ys.push_back(y);
                    H r = go(b, i + 1);
                    ys.pop_back();
                    return r;
                });
            std::vector<H> rv = t.split(h, 2);
            std::vector<H> vals = t.split(rv[1], kf);
            std::map<std::string, std::string> m;
            for (size_t j = 0; j < kf; ++j) m[mp->xs[j]] = ys[j];
            std::vector<FmP> tys = conjuncts(subst(mp->rest, m), kf);
            std::function<H(size_t)> each = [&](size_t j) -> H {
                if (j == kf) {
                    H inner = t.p.and_intro(rv[0], t.join(typed));
                    return k(t.p.iff_r(member_iff(t, chr, x), witness_all(t, M, ys, inner)));
                }
                return walk(t, sym, vals[j], [&](H leaf) {
                    const FmP& lf = t.p.fm(leaf);
                    if (lf->k != Fm::Atom || lf->name != "eq" || lf->args[0] != ys[j])
                        throw std::runtime_error("a value of an unknown shape: " + print(lf).substr(0, 200));
                    const std::string r = lf->args[1];
                    H tr = type_of(t, sym, r, subst(tys[j], {{ys[j], r}}));
                    typed[j] = transport(t, lm_, r, ys[j], t.p.eq_sym(leaf), tr);
                    return each(j + 1);
                });
            };
            return each(0);
        };
        return go(recof, 0);
    }

    // The element type T(y) of a sequence type (exists n. (natural(n) & (tuple(v, n) & (forall i z. (pmem(i, z, v) -> T(z)))))).
    static FmP elem_type(const FmP& seq, const std::string& y) {
        auto n = as_some(seq);
        auto i = as_all(n->body->b->b);
        auto z = as_all(i->body);
        return subst(z->body->b, {{z->v, y}});
    }

    // The number z_c of the type `want`: its own number, the empty record, a natural, or one of a range's cases.
    H number_typed(Tac& t, const std::string& r, uint64_t c, const FmP& want) {
        if (!want) throw std::runtime_error("the number " + r + " with no type to meet");
        const Numbers& n = nums_.back();
        if (is_atom(want, "eq", {r, r})) return refl(t, r);
        if (is_atom(want, "zero", {r}) && c == 0) return n.gz[0];
        if (is_atom(want, "Sys.natural", {r}))
            return naturals(t, {n.z.begin(), n.z.begin() + c + 1}, {n.gz.begin(), n.gz.begin() + c + 1}).back();
        std::vector<FmP> ds = disjuncts(want);
        for (size_t j = 0; ds.size() > 1 && j < ds.size(); ++j)
            if (is_atom(ds[j], "eq", {r, r})) return inject(t, refl(t, r), ds, j);
        throw std::runtime_error("the number " + r + " does not meet its type " + print(want).substr(0, 200));
    }

    // A proof that r has the type `want`, or, want null, the type its definition gives it.
    H type_of(Tac& t, Sym& sym, const std::string& r, const FmP& want) {
        if (auto c = number(zv(), r)) return number_typed(t, r, *c, want);
        H out;
        if (auto it = sym.types.find(r); it != sym.types.end()) {
            out = it->second;
        } else {
            auto vi = sym.vals.find(r);
            if (vi == sym.vals.end()) throw std::runtime_error("no definition of the value " + r);
            const Val& v = vi->second;
            switch (v.kind) {
                case Val::Field: {
                    auto rc = sym.recs.find(v.from);
                    if (rc != sym.recs.end()) {
                        const auto& [ys, rec] = rc->second;
                        H e = entry_unique(t, v.from, rec, ys.size(), v.i, r, v.def);
                        out = transport(t, lm_, ys[v.i], r, t.p.eq_sym(e), type_of(t, sym, ys[v.i], nullptr));
                    } else {
                        if (v.i != 0) throw std::runtime_error("an entry of a sequence past its first");
                        out = seq_entry(t, type_of(t, sym, v.from, nullptr), r, v.def);
                    }
                    break;
                }
                case Val::Append: out = seq_append(t, sym, r, v); break;
                case Val::Rest: out = seq_rest(t, sym, r, v); break;
                case Val::Num: out = v.def; break;
                case Val::Record: out = record_typed(t, sym, r, v, want); break;
                default: throw std::runtime_error("no typing for the value " + r + ": " + print(t.p.fm(v.def)).substr(0, 200));
            }
        }
        if (want && !alpha_eq(t.p.fm(out), want))
            throw std::runtime_error("the value " + r + " has the type " + print(t.p.fm(out)).substr(0, 200) + ", not " +
                                     print(want).substr(0, 200));
        return out;
    }

    // T(r) from the sequence type of v and r its entry 0, pmem(z_0, r, v).
    H seq_entry(Tac& t, H sq, const std::string& r, H at) {
        return t.obtain(sq, "n", [&](const std::string&, H b) {
            std::vector<H> ps = t.split(b, 3);
            return t.mp(t.inst(ps[2], {t.p.fm(at)->args[0], r}), {at});
        });
    }

    H seq_append(Tac& t, Sym& sym, const std::string& r, const Val& v) {
        H sq = type_of(t, sym, v.from, nullptr);
        FmP target = subst(t.p.fm(sq), {{v.from, r}});
        H ty = type_of(t, sym, v.elt, elem_type(t.p.fm(sq), v.elt));
        return t.obtain(v.def, "n", [&](const std::string& n, H b) {
            std::vector<H> ts = t.split(b, 2);
            return t.obtain(sq, "k", [&](const std::string& k0, H bk) {
                std::vector<H> ps = t.split(bk, 3);
                H e = t.mp(t.inst(t.p.use(lm_.len_uniq()), {v.from, k0, n}), {ps[1], ts[0]});
                H natn = t.mp(t.inst(t.p.use(lm_.nat_cong()), {k0, n}), {e, ps[0]});
                return t.obtain(t.inst(t.p.use("nsucc_EX"), {n}), "m", [&](const std::string& m, H nsm) {
                    H facts = t.mp(t.inst(t.p.use("snoc_facts"), {n, m}), {nsm});
                    facts = t.mp(t.inst(facts, {v.from, v.elt, r}), {ts[0], ts[1]});
                    H natm = t.mp(t.inst(t.p.use(lm_.natural_succ()), {n, m}), {natn, nsm});
                    H ent = t.all("i", [&](const std::string& i) {
                        return t.all("z", [&](const std::string& z) {
                            return t.assume(atom("pmem", {i, z, r}), [&](H pz) {
                                H sp = t.inst(t.mp(t.inst(t.p.use("snoc_pmem"), {v.from, n, v.elt, r}), {ts[1]}), {i, z});
                                return t.cases(t.p.iff_l(sp, pz), [&](H old) { return t.mp(t.inst(ps[2], {i, z}), {old}); },
                                               [&](H nw) { return transport(t, lm_, v.elt, z, t.p.eq_sym(t.p.and_r(nw)), ty); });
                            });
                        });
                    });
                    return t.witness(target, m, t.join({natm, t.split(facts, 3)[0], ent}));
                });
            });
        });
    }

    H seq_rest(Tac& t, Sym& sym, const std::string& r, const Val& v) {
        H sq = type_of(t, sym, v.from, nullptr);
        FmP target = subst(t.p.fm(sq), {{v.from, r}});
        return t.obtain(v.def, "n", [&](const std::string& n, H b1) {
            return t.obtain(b1, "m", [&](const std::string& m, H b2) {
                std::vector<H> rs = t.split(b2, 4);
                return t.obtain(sq, "k", [&](const std::string& k0, H bk) {
                    std::vector<H> ps = t.split(bk, 3);
                    H e = t.mp(t.inst(t.p.use(lm_.len_uniq()), {v.from, k0, n}), {ps[1], rs[1]});
                    H natn = t.mp(t.inst(t.p.use(lm_.nat_cong()), {k0, n}), {e, ps[0]});
                    H natm = t.mp(t.inst(t.p.use(lm_.natural_pred()), {m, n}), {natn, rs[0]});
                    H ent = t.all("i", [&](const std::string& i) {
                        return t.all("z", [&](const std::string& z) {
                            return t.assume(atom("pmem", {i, z, r}), [&](H pz) {
                                return t.obtain(t.inst(t.p.use("nsucc_EX"), {i}), "j", [&](const std::string& j, H nij) {
                                    H sh = t.inst(t.mp(t.inst(rs[3], {i, j}), {nij}), {z});
                                    return t.mp(t.inst(ps[2], {j, z}), {t.p.iff_r(sh, pz)});
                                });
                            });
                        });
                    });
                    return t.witness(target, m, t.join({natm, rs[2], ent}));
                });
            });
        });
    }

    // A record value against a record type (exists y. (Rec_k(r; y) & body)); body a disjunction of cases for an enum.
    H record_typed(Tac& t, Sym& sym, const std::string& r, const Val& v, const FmP& want) {
        if (!want) throw std::runtime_error("a record value " + r + " with no type to meet");
        auto rp = as_record(want, zv());
        if (!rp || rp->t != r || rp->xs.size() != v.ys.size()) throw std::runtime_error("a record value of another shape: " + r);
        std::map<std::string, std::string> m;
        for (size_t i = 0; i < v.ys.size(); ++i) m[rp->xs[i]] = v.ys[i];
        FmP body = subst(rp->rest, m);
        std::vector<FmP> ds = body->k == Fm::Or ? disjuncts(body) : std::vector<FmP>{body};
        for (size_t j = 0; j < ds.size(); ++j) {
            std::vector<FmP> cs = conjuncts(ds[j], v.ys.size());
            bool fits = true;
            for (size_t i = 0; i < cs.size() && fits; ++i)
                if (auto n = as_num(cs[i], zv()); n && n->second == v.ys[i]) {
                    if (auto c = number(zv(), v.ys[i])) {
                        fits = *c == n->first;
                        continue;
                    }
                    auto vi = sym.vals.find(v.ys[i]);
                    fits = vi != sym.vals.end() && vi->second.kind == Val::Num && vi->second.n == n->first;
                }
            if (!fits) continue;
            std::vector<H> hs;
            for (size_t i = 0; i < cs.size(); ++i) hs.push_back(type_of(t, sym, v.ys[i], cs[i]));
            H hb = t.join(hs);
            if (ds.size() > 1) hb = inject(t, hb, ds, j);
            return witness_all(t, want, v.ys, t.p.and_intro(v.def, hb));
        }
        throw std::runtime_error("no case of its type fits the value " + r);
    }

    // ---- W3: every state and input has a step, by cases on the rules' guards ----

    // A fact's parts as facts: conjunctions split, existentials opened; each compound kept whole too. A value found to be
    // a number, eq(x, z_c), is carried into the facts about x, so that they read as the claims write numbers.
    H open_fact(Tac& t, Facts& fs, H h, const std::function<H()>& k) {
        const FmP& f = t.p.fm(h);
        if (f->k == Fm::Atom && f->name == "zero" && f->args.size() == 1 && !nums_.back().z.empty() &&
            !number(zv(), f->args[0])) {
            const Numbers& ns = nums_.back();
            fs.add(h);
            return open_fact(t, fs, t.mp(t.inst(t.p.use("zero_UNIQ"), {f->args[0], ns.z[0]}), {h, ns.gz[0]}), k);
        }
        if (f->k == Fm::Atom && f->name == "eq" && f->args.size() == 2) {
            Nums nv = zv();
            const std::string &x = f->args[0], &z = f->args[1];
            if (number(nv, z) && !number(nv, x)) {
                std::vector<H> about;
                for (H g : fs.all())
                    if (const FmP& gf = t.p.fm(g); gf->k == Fm::Atom && gf->name != "eq")
                        for (const std::string& a : gf->args)
                            if (a == x) {
                                about.push_back(g);
                                break;
                            }
                for (H g : about) fs.add(transport(t, lm_, x, z, h, g));
            }
        }
        fs.add(h);
        if (f->k == Fm::And) {
            H l = t.p.and_l(h), r = t.p.and_r(h);
            return open_fact(t, fs, l, [&] { return open_fact(t, fs, r, k); });
        }
        if (as_some(f)) return t.obtain(h, f->name, [&](const std::string&, H b) { return open_fact(t, fs, b, k); });
        return k();
    }

    // The same, each disjunction a case of its own: k in each.
    H open_cases(Tac& t, Facts& fs, H h, const std::function<H()>& k) {
        const FmP& f = t.p.fm(h);
        if (f->k == Fm::Or) {
            return t.cases(h, [&](H l) {
                size_t m = fs.mark();
                H r = open_cases(t, fs, l, k);
                fs.reset(m);
                return r;
            }, [&](H r) {
                size_t m = fs.mark();
                H out = open_cases(t, fs, r, k);
                fs.reset(m);
                return out;
            });
        }
        if (f->k == Fm::And) {
            fs.add(h);
            H l = t.p.and_l(h), r = t.p.and_r(h);
            return open_cases(t, fs, l, [&] { return open_cases(t, fs, r, k); });
        }
        if (as_some(f)) {
            fs.add(h);
            return t.obtain(h, f->name, [&](const std::string&, H b) { return open_cases(t, fs, b, k); });
        }
        return open_fact(t, fs, h, k);
    }

    // A rule's guard over its pattern variables: (exists x. (elem(x, T) & ... when)).
    static FmP guard_of(const FmP& rule) {
        if (auto b = as_some(rule)) return some(b->v, conj(b->body->a, guard_of(b->body->b)));
        return conjuncts(rule, 3)[0];
    }

    H enabled_params(Tac& t, const std::vector<std::string>& C, const std::vector<H>& ch, size_t S, size_t A, size_t R,
                     const std::vector<H>& hyps, const FmP& goal3) {
        return t.all("s", [&](const std::string& s) {
            return t.assume(atom("elem", {s, C[S]}), [&](H sS) {
                return t.all("a", [&](const std::string& a) {
                    return t.assume(atom("elem", {a, C[A]}), [&](H aA) {
                        FmP g = subst(as_all(goal3)->body, {{as_all(goal3)->v, s}})->b;
                        g = subst(as_all(g)->body, {{as_all(g)->v, a}})->b;
                        Facts fs(t);
                        for (H h : hyps) fs.add(h);
                        fs.add(sS);
                        fs.add(aA);
                        StepShape sh = step_shape(member_at(t, ch[R], fresh("_q")));
                        std::vector<FmP> rules, guards;
                        for (const FmP& r : sh.rules) {
                            rules.push_back(subst(r, {{sh.s, s}, {sh.a, a}}));
                            guards.push_back(guard_of(rules.back()));
                        }
                        std::vector<H> nots;
                        std::function<H(size_t)> choose = [&](size_t j) -> H {
                            if (j == guards.size()) {
                                H am = t.p.iff_l(member_iff(t, ch[A], a), aA);
                                H bot = open_cases(t, fs, am, [&] { return exhaust(t, fs, guards, nots); });
                                return t.p.bottom_elim(bot, g);
                            }
                            return t.cases(t.p.excluded_middle(guards[j]), [&](H yes) {
                                size_t m = fs.mark();
                                H r = fire(t, fs, C, ch, R, sh, s, a, rules[j], yes, g);
                                fs.reset(m);
                                return r;
                            }, [&](H no) {
                                size_t m = fs.mark();
                                fs.add(no);
                                nots.push_back(no);
                                H r = choose(j + 1);
                                nots.pop_back();
                                fs.reset(m);
                                return r;
                            });
                        };
                        return open_fact(t, fs, t.p.iff_l(member_iff(t, ch[S], s), sS), [&] { return choose(0); });
                    });
                });
            });
        });
    }

    // False from the guards' negations: by cases on the naturals' order and on the guards' negated parts, some guard holds.
    H exhaust(Tac& t, Facts& fs, const std::vector<FmP>& guards, const std::vector<H>& nots) {
        std::vector<std::string> nats;
        for (H h : fs.all())
            if (const FmP& f = t.p.fm(h); f->k == Fm::Atom && f->name == "Sys.natural") {
                bool dup = false;
                for (const auto& x : nats) dup = dup || x == f->args[0];
                if (!dup) nats.push_back(f->args[0]);
            }
        struct Decision {
            std::string x, y;
            FmP em;
        };
        std::vector<Decision> ds;
        for (size_t i = 0; i < nats.size(); ++i)
            for (size_t j = i + 1; j < nats.size(); ++j) ds.push_back({nats[i], nats[j], nullptr});
        for (const FmP& g : guards) {
            std::set<std::string> fv = free_vars(g);
            std::function<void(const FmP&)> scan = [&](const FmP& f) {
                if (f->k == Fm::Not) {
                    bool closed = true;
                    for (const auto& v : free_vars(f->a)) closed = closed && fv.count(v);
                    bool dup = false;
                    for (const auto& d : ds) dup = dup || (d.em && alpha_eq(d.em, f->a));
                    if (closed && !dup) ds.push_back({"", "", f->a});
                }
                if (f->a) scan(f->a);
                if (f->b) scan(f->b);
            };
            scan(g);
        }
        std::function<H(size_t)> decide = [&](size_t d) -> H {
            for (size_t j = 0; j < guards.size(); ++j)
                if (fs.provable(guards[j])) return t.p.not_elim(nots[j], fs.prove(guards[j]));
            if (d == ds.size()) throw std::runtime_error("a state and input that no rule's guard covers");
            auto branch = [&](H h) {
                size_t m = fs.mark();
                fs.add(h);
                H r = decide(d + 1);
                fs.reset(m);
                return r;
            };
            if (ds[d].em) return t.cases(t.p.excluded_middle(ds[d].em), branch, branch);
            H nx = fs.prove(atom("Sys.natural", {ds[d].x})), ny = fs.prove(atom("Sys.natural", {ds[d].y}));
            H three = t.mp(t.inst(t.p.use(lm_.trichotomy()), {ds[d].x, ds[d].y}), {nx, ny});
            return t.cases(three, 3, [&](size_t, H h) { return branch(h); });
        };
        return decide(0);
    }

    // Rule j fires on its guard: its values built, then its step, in the step relation, and the transition.
    H fire(Tac& t, Facts& fs, const std::vector<std::string>& C, const std::vector<H>& ch, size_t R, const StepShape& sh,
           const std::string& s, const std::string& a, const FmP& rule, H yes, const FmP& g) {
        if (auto b = as_some(rule))
            return t.obtain(yes, b->v, [&](const std::string& x, H body) {
                std::vector<H> p = t.split(body, 2);
                fs.add(p[0]);
                return fire(t, fs, C, ch, R, sh, s, a, subst(b->body, {{b->v, x}})->b, p[1], g);
            });
        return open_fact(t, fs, yes, [&] {
            std::vector<FmP> parts = conjuncts(rule, 3);
            auto np = as_record(parts[1], zv()), op = as_record(parts[2], zv());
            if (!np || !op) throw std::runtime_error("a next state or output of an unknown shape");
            std::vector<FmP> nvals = conjuncts(np->rest, np->xs.size()), ovals = conjuncts(op->rest, op->xs.size());
            std::vector<std::string> nv(nvals.size()), ov(ovals.size());
            std::function<H(size_t)> each = [&](size_t i) -> H {
                if (i < nvals.size())
                    return construct(t, fs, nvals[i], [&](const std::string& r) {
                        nv[i] = r;
                        return each(i + 1);
                    });
                if (i < nvals.size() + ovals.size())
                    return construct(t, fs, ovals[i - nvals.size()], [&](const std::string& r) {
                        ov[i - nvals.size()] = r;
                        return each(i + 1);
                    });
                return make_record(t, fs, nv, [&](const std::string& tt) {
                    return make_record(t, fs, ov, [&](const std::string& b) {
                        return make_record(t, fs, {s, a, b, tt}, [&](const std::string& q) {
                            H qT = t.p.iff_r(member_iff(t, ch[R], q), fs.prove(member_at(t, ch[R], q)));
                            H rec4 = fs.prove(enc::rec(q, {s, a, b, tt}, nums_.back().z));
                            H t4 = t.p.iff_r(tuple4_iff(t, {q, s, a, b, tt}), rec4);
                            H tr = transition(t, C[R], s, a, b, tt, q, qT, t4);
                            auto gb = as_some(g);
                            return t.witness(g, b, t.witness(subst(gb->body, {{gb->v, b}}), tt, tr));
                        });
                    });
                });
            };
            return each(0);
        });
    }

    H make_record(Tac& t, Facts& fs, const std::vector<std::string>& ys, const std::function<H(const std::string&)>& k) {
        return numerals(t, ys.size(), [&](const std::vector<std::string>&, const std::vector<H>&) {
            H ex = t.inst(at_numbers(t, t.p.use(lm_.rec_ex(ys.size())), ys.size() + 1), ys);
            return t.obtain(ex, "r", [&](const std::string& r, H rec) { return open_fact(t, fs, rec, [&] { return k(r); }); });
        });
    }

    // A value chain (exists v. (D(v) & rest)) ending in eq(y, r): each v the steps give, or built; k with r.
    H construct(Tac& t, Facts& fs, const FmP& f, const std::function<H(const std::string&)>& k) {
        auto s = as_some(f);
        if (!s || s->body->k != Fm::And) {
            if (f->k != Fm::Atom || f->name != "eq") throw std::runtime_error("a value of an unknown shape: " + print(f).substr(0, 200));
            return k(f->args[1]);
        }
        const FmP &D = s->body->a, &rest = s->body->b;
        if (auto w = fs.witness_of(some(s->v, D))) return construct(t, fs, subst(rest, {{s->v, *w}}), k);
        return make_value(t, fs, s->v, D, [&](const std::string& w) { return construct(t, fs, subst(rest, {{s->v, w}}), k); });
    }

    // not zero(n), n the length of v: from zero(n), v would be empty, against a guard's negation at hand.
    H nonzero(Tac& t, Facts& fs, const std::string& v, const std::string& n) {
        return t.refute(atom("zero", {n}), [&](H zn) {
            size_t m = fs.mark();
            fs.add(zn);
            H zv = t.mp(t.inst(t.p.use(lm_.empty_tuple()), {v, n}), {fs.prove(atom("tuple", {v, n})), zn});
            fs.add(zv);
            if (const Numbers& ns = nums_.back(); !ns.z.empty())
                fs.add(t.mp(t.inst(t.p.use("zero_UNIQ"), {v, ns.z[0]}), {zv, ns.gz[0]}));
            auto c = fs.contradiction();
            fs.reset(m);
            if (!c) throw std::runtime_error("rest or first of a sequence not known to be nonempty");
            return *c;
        });
    }

    H make_value(Tac& t, Facts& fs, const std::string& v, const FmP& D, const std::function<H(const std::string&)>& k) {
        auto length = [&](const std::string& w) {
            std::string n0 = fresh("_n");
            auto n = fs.witness_of(some(n0, atom("tuple", {w, n0})));
            if (!n) throw std::runtime_error("no length known for " + w);
            return *n;
        };
        if (auto ap = as_append(D); ap && ap->r == v) {
            std::string n = length(ap->v);
            return t.obtain(t.inst(t.p.use("snoc_EX"), {ap->v, n, ap->y}), "r", [&](const std::string& r, H sn) {
                fs.add(sn);
                return k(r);
            });
        }
        if (auto rp = as_rest(D); rp && rp->r == v) {
            std::string n = length(rp->v);
            H natn = fs.prove(atom("Sys.natural", {n})), tv = fs.prove(atom("tuple", {rp->v, n}));
            H nz = nonzero(t, fs, rp->v, n);
            std::string m0 = fresh("_m");
            FmP ex = some(m0, atom("nsucc", {m0, n}));
            H cases = t.mp(t.inst(t.p.use(lm_.zero_or_succ()), {n}), {natn});
            H succ = t.cases(cases, [&](H z) { return t.p.bottom_elim(t.p.not_elim(nz, z), ex); }, [&](H e) { return e; });
            return t.obtain(succ, "m", [&](const std::string& m, H nsm) {
                fs.add(nsm);
                H re = t.mp(t.inst(t.p.use(lm_.rest_ex()), {rp->v, n, m}), {tv, nsm, natn});
                return t.obtain(re, "r", [&](const std::string& r, H b) {
                    return open_fact(t, fs, b, [&] { return k(r); });
                });
            });
        }
        if (auto at = as_at(D, zv()); at && at->v == v && at->i == 0) {
            std::string n = length(at->r);
            H natn = fs.prove(atom("Sys.natural", {n})), tv = fs.prove(atom("tuple", {at->r, n}));
            H fe = t.mp(t.inst(t.p.use(lm_.first_ex()), {at->r, n}), {tv, natn, nonzero(t, fs, at->r, n)});
            return t.obtain(fe, "y", [&](const std::string& y, H hy) {
                const Numbers& ns = nums_.back();
                fs.add(t.mp(t.inst(hy, {ns.z.at(0)}), {ns.gz.at(0)}));
                return k(y);
            });
        }
        if (auto num = as_num(D, zv()); num && num->second == v) {
            uint64_t c = num->first;
            return numerals(t, c, [&](const std::vector<std::string>& z, const std::vector<H>&) {
                fs.add(refl(t, z[c]));
                return k(z[c]);
            });
        }
        if (auto rc = as_rec(D, zv()); rc && rc->t == v) return make_record(t, fs, rc->xs, k);
        throw std::runtime_error("sysprove cannot build a value " + print(D).substr(0, 200));
    }

    // ---- Existence ----

    H exists(Tac& t, const FmP& claim, const std::vector<Comp>& cs, size_t f, const std::string& inst) {
        const Comp& c = cs[f];
        std::vector<size_t> deps;
        if (c.kind == ComponentDef::Condition) deps = {c.of};
        if (c.kind == ComponentDef::Rules) deps = {c.roles[0], c.roles[1], c.roles[2]};
        return with_components(t, claim, deps.size(), [&](const std::vector<std::string>& C, const std::vector<H>& ch, FmP body) {
            std::map<std::string, std::string> args;
            for (size_t i = 0; i < deps.size(); ++i) args["par" + std::to_string(deps[i])] = C[i];
            auto [rq, rv] = request_formula(body, c.kind == ComponentDef::Condition);
            if (c.kind == ComponentDef::Condition) return condition_set(t, body, set_at(t, inst + "." + c.label, args, rq, rv, C[0]));
            return numerals(t, N, [&](const std::vector<std::string>& z, const std::vector<H>& gz) -> H {
                Eval ev(t, lm_, z, gz);
                if (c.kind == ComponentDef::Parts && arity(member_at_formula(body)) == 0) return singleton(t, ev, body);
                if (c.kind == ComponentDef::Parts) return parts_set(t, ev, body, inst + "." + c.label);
                return step_set(t, ev, body, C, ch, [&](const std::string& B) { return set_at(t, inst + "." + c.label, args, rq, rv, B); },
                                [&](const std::string& q, H m, const Typed& k) {
                                    return typed_once(t, inst, {}, C, ch[0], ch[2], q, m, &ev, k);
                                });
            });
        });
    }

    using Typed = std::function<H(const std::string&, H, const std::string&, H, const std::string&, H, const std::string&, H, H)>;

    // M(q) with its rules' disjunction replaced by the next state's membership in S and the output's in B.
    static FmP typed_goal(const FmP& M, const std::string& S, const std::string& B) {
        auto s = as_some(M);
        auto a = as_some(s->body->b);
        auto b = as_some(a->body->b);
        auto tt = as_some(b->body);
        FmP inner = conj(tt->body->a, conj(atom("elem", {tt->v, S}), atom("elem", {b->v, B})));
        return some(s->v, conj(s->body->a, some(a->v, conj(a->body->a, some(b->v, some(tt->v, inner))))));
    }

    // For all parameters P and sets S, A, B: S's and B's characterizations give every q of M(q) its typed parts.
    static FmP typing_statement(const std::vector<std::string>& P, const std::vector<std::string>& C3, const FmP& chS,
                                const FmP& chB, const std::string& q, const FmP& M) {
        FmP f = imp(chS, imp(chB, all(q, imp(M, typed_goal(M, C3[0], C3[2])))));
        for (size_t i = C3.size(); i-- > 0;) f = all(C3[i], f);
        for (size_t i = P.size(); i-- > 0;) f = all(P[i], f);
        return f;
    }

    H prove_typing(Tac& t, const FmP& stmt, size_t nvars, bool params) {
        std::vector<H> hyps;
        std::function<H(FmP, size_t)> go = [&](FmP g, size_t i) -> H {
            if (i < nvars) {
                auto b = as_all(g);
                FmP rest = b->body;
                std::string bv = b->v;
                return t.all(bv, [&](const std::string& x) { return go(subst(rest, {{bv, x}}), i + 1); });
            }
            if (hyps.size() < 2)
                return t.assume(g->a, [&](H c) {
                    hyps.push_back(c);
                    H h = go(g->b, i);
                    hyps.pop_back();
                    return h;
                });
            auto b = as_all(g);
            FmP rest = b->body;
            std::string bv = b->v;
            return t.all("q", [&](const std::string& q) {
                FmP r = subst(rest, {{bv, q}});
                return t.assume(r->a, [&](H m) {
                    std::vector<H> ch = {hyps[0], hyps[0], hyps[1]};
                    Typed k = [&](const std::string& s, H sS, const std::string& a, H aA, const std::string& bb, H bB,
                                  const std::string& tt, H tS, H rec4) {
                        auto l0 = as_some(r->b);
                        FmP l1 = subst(l0->body, {{l0->v, s}})->b;
                        auto a1 = as_some(l1);
                        FmP l2 = subst(a1->body, {{a1->v, a}})->b;
                        auto b2 = as_some(l2);
                        FmP l3 = subst(b2->body, {{b2->v, bb}});
                        H h3 = t.witness(l3, tt, t.p.and_intro(rec4, t.p.and_intro(tS, bB)));
                        H h1 = t.witness(l1, a, t.p.and_intro(aA, t.witness(l2, bb, h3)));
                        return t.witness(r->b, s, t.p.and_intro(sS, h1));
                    };
                    if (params) return typed_params(t, ch, 0, 2, m, k);
                    return numerals(t, N, [&](const std::vector<std::string>& z, const std::vector<H>& gz) {
                        Eval ev(t, lm_, z, gz);
                        return typed(t, ev, ch, 0, 2, m, k);
                    });
                });
            });
        };
        return go(stmt, 0);
    }

    // q's parts typed by the instance's lemma at P and C3 = (S, A, B), then k; in place if its hypotheses are not these.
    H typed_once(Tac& t, const std::string& inst, const std::vector<std::string>& P, const std::vector<std::string>& C3,
                 H chS, H chB, const std::string& q, H m, Eval* ev, const Typed& k) {
        const FmP M = t.p.fm(m);
        size_t kz = 0;
        const FmP stmt = close_numbers(typing_statement(P, C3, t.p.fm(chS), t.p.fm(chB), q, M), kz);
        const std::string name = lm_.own(inst + "_step_typed", [&] { return stmt; }, [&](Tac& t2) {
            return with_numbers(t2, stmt, [&](FmP rest) { return prove_typing(t2, rest, P.size() + 3, ev == nullptr); });
        });
        FmP f = known_.at(name);
        size_t kf = number_binders(f);
        const Numbers& nn = nums_.back();
        bool fits = nn.z.size() >= kf;
        for (size_t c = 0; fits && c < kf; ++c) {
            auto b = as_all(f);
            f = subst(b->body, {{b->v, nn.z[c]}})->b;
        }
        std::vector<std::string> at = P;
        at.insert(at.end(), C3.begin(), C3.end());
        for (const std::string& x : at) {
            if (!fits) break;
            auto b = as_all(f);
            if (!b) {
                fits = false;
                break;
            }
            f = subst(b->body, {{b->v, x}});
        }
        auto qb = fits && f->k == Fm::Imp && f->b->k == Fm::Imp ? as_all(f->b->b) : std::nullopt;
        fits = qb && alpha_eq(f->a, t.p.fm(chS)) && alpha_eq(f->b->a, t.p.fm(chB)) &&
               alpha_eq(subst(qb->body, {{qb->v, q}})->a, M);
        if (!fits) {
            std::vector<H> ch = {chS, chS, chB};
            return ev ? typed(t, *ev, ch, 0, 2, m, k) : typed_params(t, ch, 0, 2, m, k);
        }
        H T = t.mp(t.inst(t.mp(t.inst(at_numbers(t, t.p.use(name), kf), at), {chS, chB}), {q}), {m});
        return t.obtain(T, "s", [&](const std::string& s, H b1) {
            std::vector<H> s1 = t.split(b1, 2);
            return t.obtain(s1[1], "a", [&](const std::string& a, H b2) {
                std::vector<H> a1 = t.split(b2, 2);
                return t.obtain(a1[1], "b", [&](const std::string& b, H b3) {
                    return t.obtain(b3, "t", [&](const std::string& tt, H b4) {
                        std::vector<H> rr = t.split(b4, 2);
                        std::vector<H> mb = t.split(rr[1], 2);
                        return k(s, s1[0], a, a1[0], b, mb[1], tt, mb[0], rr[0]);
                    });
                });
            });
        });
    }

    // ---- Existence over parameters: each set cut from a tower over the naturals and the type parameters ----

    // U_0 the naturals with each type parameter's members, U_(i+1) = U_i with Pow(Pow(Pow(U_i))).
    struct Tower {
        H nat_in;                         // forall x. natural(x) -> x in U_0
        std::map<std::string, H> type_in;  // J: forall x. x in J -> x in U_0
        std::vector<std::string> U;
        std::vector<H> up, pow_in;        // i: U_i, and Pow(Pow(Pow(U_i))), inside U_(i+1)
        std::vector<std::array<std::string, 3>> P;
        std::vector<std::array<H, 3>> Ph;
    };

    // forall x. x in side -> x in U, from U's definition as a union.
    H sub_of(Tac& t, H def, const std::string& side, bool left) {
        return t.all("x", [&](const std::string& x) {
            return t.assume(atom("elem", {x, side}), [&](H h) {
                H u = t.inst(def, {x});
                FmP d = t.p.fm(u)->b;
                return t.p.iff_r(u, left ? t.p.or_intro_l(h, d->b) : t.p.or_intro_r(d->a, h));
            });
        });
    }

    // forall x. A(x) -> C(x) from forall x. A(x) -> B(x) and forall x. B(x) -> C(x).
    H compose(Tac& t, H f, H g) {
        auto fb = as_all(t.p.fm(f));
        return t.all("x", [&](const std::string& x) {
            return t.assume(subst(fb->body, {{fb->v, x}})->a, [&](H h) { return t.mp(t.inst(g, {x}), {t.mp(t.inst(f, {x}), {h})}); });
        });
    }

    H tower(Tac& t, const std::vector<std::string>& types, size_t d, const std::function<H(Tower&)>& k) {
        Tower tw;
        return t.obtain(t.p.use("Nat.nat_EX"), "N", [&](const std::string& N, H nn) {
            H nat_n = t.all("x", [&](const std::string& x) {
                return t.assume(atom("Sys.natural", {x}), [&](H h) {
                    return t.mp(t.inst(t.p.iff_l(t.inst(t.p.use("Sys.natural_nat"), {x}), h), {N}), {nn});
                });
            });
            std::function<H(size_t, const std::string&, H)> base = [&](size_t i, const std::string& V, H nat_v) -> H {
                if (i == types.size()) {
                    tw.nat_in = nat_v;
                    tw.U.push_back(V);
                    return levels(t, tw, d, k);
                }
                return t.obtain(t.inst(t.p.use("union2_ex"), {V, types[i]}), "U", [&](const std::string& W, H def) {
                    H l = sub_of(t, def, V, true);
                    for (auto& [J, h] : tw.type_in) h = compose(t, h, l);
                    tw.type_in[types[i]] = sub_of(t, def, types[i], false);
                    return base(i + 1, W, compose(t, nat_v, l));
                });
            };
            return base(0, N, nat_n);
        });
    }

    H levels(Tac& t, Tower& tw, size_t d, const std::function<H(Tower&)>& k) {
        if (tw.U.size() == d + 1) return k(tw);
        const std::string U = tw.U.back();
        return powers(t, U, [&](const std::string& p1, H h1, const std::string& p2, H h2, const std::string& p3, H h3) {
            return t.obtain(t.inst(t.p.use("union2_ex"), {U, p3}), "U", [&](const std::string& W, H def) {
                tw.up.push_back(sub_of(t, def, U, true));
                tw.pow_in.push_back(sub_of(t, def, p3, false));
                tw.P.push_back({p1, p2, p3});
                tw.Ph.push_back({h1, h2, h3});
                tw.U.push_back(W);
                return levels(t, tw, d, k);
            });
        });
    }

    H lift(Tac& t, Tower& tw, const std::string& x, H h, size_t from, size_t to) {
        for (size_t l = from; l < to; ++l) h = t.mp(t.inst(tw.up[l], {x}), {h});
        return h;
    }

    // (exists n. (natural(n) & (tuple(x, n) & (forall i y. (pmem(i, y, x) -> T(y)))))): T at its bound y.
    static std::optional<std::pair<std::string, FmP>> as_seq(const FmP& ty, const std::string& x) {
        auto n = as_some(ty);
        if (!n || n->body->k != Fm::And || !is_atom(n->body->a, "Sys.natural", {n->v})) return {};
        const FmP& r = n->body->b;
        if (r->k != Fm::And || !is_atom(r->a, "tuple", {x, n->v})) return {};
        auto i = as_all(r->b);
        auto y = i ? as_all(i->body) : std::nullopt;
        if (!y || y->body->k != Fm::Imp || !is_atom(y->body->a, "pmem", {i->v, y->v, x})) return {};
        return std::make_pair(y->v, y->body->b);
    }

    // The level of the tower that holds every value of the type ty(x).
    size_t depth_of(const FmP& ty, const std::string& x) {
        if (ty->k == Fm::Atom && ty->name == "elem" && ty->args[0] == x) return 0;
        if (ty->k == Fm::Atom && (ty->name == "Sys.natural" || ty->name == "zero")) return 0;
        if (auto n = as_num(ty, zv()); n && n->second == x) return 0;
        if (auto sq = as_seq(ty, x)) return 1 + depth_of(sq->second, sq->first);
        if (auto rp = as_record(ty, zv()); rp && rp->t == x) {
            size_t d = 0;
            for (const FmP& c : rp->rest->k == Fm::Or ? disjuncts(rp->rest) : std::vector<FmP>{rp->rest}) {
                std::vector<FmP> cs = conjuncts(c, rp->xs.size());
                for (size_t i = 0; i < cs.size(); ++i) d = std::max(d, depth_of(cs[i], rp->xs[i]));
            }
            return 1 + d;
        }
        throw std::runtime_error("no superset for the type " + print(ty).substr(0, 200));
    }

    // natural(z_i) for a chain of numerals.
    std::vector<H> naturals(Tac& t, const std::vector<std::string>& z, const std::vector<H>& gz) {
        std::vector<H> nz{t.mp(t.inst(t.p.use(lm_.natural_zero()), {z[0]}), {gz[0]})};
        for (size_t i = 1; i < z.size(); ++i) nz.push_back(t.mp(t.inst(t.p.use(lm_.natural_succ()), {z[i - 1], z[i]}), {nz[i - 1], gz[i]}));
        return nz;
    }

    // x in U_d from ty(x), d its depth.
    H in_tower(Tac& t, Tower& tw, const std::string& x, H hty) {
        const FmP ty = t.p.fm(hty);
        size_t d = depth_of(ty, x);
        if (ty->k == Fm::Atom && ty->name == "elem") {
            auto it = tw.type_in.find(ty->args[1]);
            if (it == tw.type_in.end()) throw std::runtime_error("no superset for members of " + ty->args[1]);
            return t.mp(t.inst(it->second, {x}), {hty});
        }
        if (ty->k == Fm::Atom && ty->name == "Sys.natural") return t.mp(t.inst(tw.nat_in, {x}), {hty});
        if (ty->k == Fm::Atom && ty->name == "zero")
            return t.mp(t.inst(tw.nat_in, {x}), {t.mp(t.inst(t.p.use(lm_.natural_zero()), {x}), {hty})});
        if (auto n = as_num(ty, zv()); n && n->second == x)
            return numerals(t, n->first, [&](const std::vector<std::string>& z, const std::vector<H>& gz) {
                H nz = naturals(t, {z.begin(), z.begin() + n->first + 1}, {gz.begin(), gz.begin() + n->first + 1}).back();
                H nx = t.mp(t.inst(t.p.use(lm_.nat_cong()), {z[n->first], x}), {t.p.eq_sym(hty), nz});
                return t.mp(t.inst(tw.nat_in, {x}), {nx});
            });
        size_t e = d - 1;
        auto index_in = [&](const std::string& n, H natn) {
            return t.all("i", [&](const std::string& i) {
                return t.assume(atom("elem", {i, n}), [&](H h) {
                    H ni = t.mp(t.inst(t.p.use(lm_.natural_elem()), {n, i}), {natn, h});
                    return lift(t, tw, i, t.mp(t.inst(tw.nat_in, {i}), {ni}), 0, e);
                });
            });
        };
        auto into_pow = [&](const std::string& n, H tup, H idx, H ent) {
            H tp = t.inst(t.p.use(lm_.tuple_pow()), {x, n, tw.U[e], tw.P[e][0], tw.P[e][1], tw.P[e][2]});
            H in3 = t.mp(tp, {tup, idx, ent, tw.Ph[e][0], tw.Ph[e][1], tw.Ph[e][2]});
            return t.mp(t.inst(tw.pow_in[e], {x}), {in3});
        };
        if (as_seq(ty, x))
            return t.obtain(hty, "n", [&](const std::string& n, H b) {
                std::vector<H> ps = t.split(b, 3);
                H ent = t.all("i", [&](const std::string& i) {
                    return t.all("y", [&](const std::string& y) {
                        return t.assume(atom("pmem", {i, y, x}), [&](H h) {
                            H ty_y = t.mp(t.inst(ps[2], {i, y}), {h});
                            return lift(t, tw, y, in_tower(t, tw, y, ty_y), depth_of(t.p.fm(ty_y), y), e);
                        });
                    });
                });
                return into_pow(n, ps[1], index_in(n, ps[0]), ent);
            });
        auto rp = as_record(ty, zv());
        size_t k = rp->xs.size();
        std::vector<std::string> xs;
        std::function<H(H, size_t)> go = [&](H h, size_t i) -> H {
            if (i < k)
                return t.obtain(h, "x", [&](const std::string& xi, H b) {
                    xs.push_back(xi);
                    H r = go(b, i + 1);
                    xs.pop_back();
                    return r;
                });
            std::vector<H> rb = t.split(h, 2);
            size_t nc = disjuncts(t.p.fm(rb[1])).size();
            auto each = [&](size_t, H hc) {
                std::vector<H> tys = t.split(hc, k);
                std::vector<H> xin;
                for (size_t j = 0; j < k; ++j)
                    xin.push_back(lift(t, tw, xs[j], in_tower(t, tw, xs[j], tys[j]), depth_of(t.p.fm(tys[j]), xs[j]), e));
                return numerals(t, k, [&](const std::vector<std::string>& z, const std::vector<H>& gz) {
                    std::vector<H> parts = t.split(rb[0], k + 1);
                    H td = t.p.iff_l(t.inst(t.p.use("tuple_def"), {x, z[k]}), parts[0]);
                    H fun = t.split(td, 4)[3];
                    H ent = t.all("i", [&](const std::string& i) {
                        return t.all("y", [&](const std::string& y) {
                            return t.assume(atom("pmem", {i, y, x}), [&](H py) {
                                H dom = t.mp(t.inst(t.mp(t.inst(t.p.use("tuple_dom"), {x, z[k]}), {parts[0]}), {i, y}), {py});
                                H cs = t.mp(t.inst(at_numbers(t, t.p.use(lm_.index_cases(k)), k + 1), {i}), {dom});
                                return t.cases(cs, k, [&](size_t j, H eij) {
                                    H pj = t.mp(t.inst(t.p.use(lm_.pmem_cong1()), {i, z[j], y, x}), {eij, py});
                                    H yx = t.mp(t.inst(fun, {z[j], y, xs[j]}), {pj, parts[j + 1]});
                                    return t.mp(t.inst(t.p.use("elem_first_subst"), {xs[j], y, tw.U[e]}), {t.p.eq_sym(yx), xin[j]});
                                });
                            });
                        });
                    });
                    return into_pow(z[k], parts[0], index_in(z[k], naturals(t, {z.begin(), z.begin() + k + 1}, {gz.begin(), gz.begin() + k + 1})[k]), ent);
                });
            };
            if (nc == 1) return each(0, rb[1]);
            return t.cases(rb[1], nc, each);
        };
        return go(hty, 0);
    }

    H exists_params(Tac& t, const FmP& claim, const std::vector<Comp>& cs, size_t f, NameId inst) {
        const Comp& c = cs[f];
        const std::string purpose = p_.name(inst).text + "." + c.label;
        std::vector<size_t> deps;
        if (c.kind == ComponentDef::Condition) deps = {c.of};
        if (c.kind == ComponentDef::Rules) deps = {c.roles[0], c.roles[1], c.roles[2]};
        const std::vector<VarId>& ps = p_.name(inst).params;
        return with_params(t, claim, ps, [&](const std::vector<std::string>& P, const std::vector<H>&, FmP g) {
            return with_components(t, g, deps.size(), [&](const std::vector<std::string>& C, const std::vector<H>& ch, FmP body) {
                std::map<std::string, std::string> args;
                std::vector<std::string> types;
                for (size_t i = 0; i < ps.size(); ++i) {
                    args["par_" + p_.vars[ps[i].v].hint] = P[i];
                    if (!p_.vars[ps[i].v].bound) types.push_back(P[i]);
                }
                for (size_t i = 0; i < deps.size(); ++i) args["par" + std::to_string(deps[i])] = C[i];
                auto [rq, rv] = request_formula(body, c.kind == ComponentDef::Condition);
                if (c.kind == ComponentDef::Condition) return condition_set(t, body, set_at(t, purpose, args, rq, rv, C[0]));
                if (c.kind == ComponentDef::Rules)
                    return numerals(t, N, [&](const std::vector<std::string>& z, const std::vector<H>& gz) {
                        Eval ev(t, lm_, z, gz);
                        return step_set(t, ev, body, C, ch, [&](const std::string& B) { return set_at(t, purpose, args, rq, rv, B); },
                                        [&](const std::string& q, H m, const Typed& k) {
                                            return typed_once(t, p_.name(inst).text, P, C, ch[0], ch[2], q, m, nullptr, k);
                                        });
                    });
                std::string q0 = fresh("_q");
                FmP M = subst(member_at_formula(body), {{as_all(as_some(body)->body)->v, q0}});
                return tower(t, types, depth_of(M, q0), [&](Tower& tw) {
                    return separated(t, body, set_at(t, purpose, args, rq, rv, tw.U.back()),
                                     [&](const std::string& q, H m) { return in_tower(t, tw, q, m); });
                });
            });
        });
    }

    // M of (exists C. (set(C) & (forall q. (set(q) -> (elem(q, C) <-> M(q)))))), q free.
    static FmP member_at_formula(const FmP& body) {
        auto b = as_some(body);
        auto q = as_all(b->body);
        return q->body->b;
    }

    // {0}: the record with no parts.
    H singleton(Tac& t, Eval& ev, const FmP& body) {
        const std::string& z0 = ev.z[0];
        H ex = t.inst(t.p.use("upair_ex"), {z0, z0});
        return t.obtain(ex, "C", [&](const std::string& Cs, H up) {
            H all_q = t.all("q", [&](const std::string& q) {
                H d = t.inst(t.split(t.p.iff_l(t.inst(t.p.use("upair_def"), {z0, z0, Cs}), up), 3)[2], {q});
                H l = t.assume(atom("elem", {q, Cs}), [&](H h) {
                    H o = t.p.iff_l(d, h);
                    auto zero_q = [&](H e) {
                        return t.mp(t.inst(t.p.use(lm_.zero_cong()), {z0, q}), {t.p.eq_sym(e), ev.gz[0]});
                    };
                    return t.cases(o, zero_q, zero_q);
                });
                H r = t.assume(atom("zero", {q}), [&](H h) {
                    H e = t.mp(t.inst(t.p.use("zero_UNIQ"), {q, z0}), {h, ev.gz[0]});
                    return t.p.iff_r(d, t.p.or_intro_l(e, atom("eq", {q, z0})));
                });
                return t.p.iff_intro(l, r);
            });
            return t.witness(body, Cs, all_q);
        });
    }

    // Pow(Pow(Pow(W))) and its powers, then k.
    H powers(Tac& t, const std::string& W, const std::function<H(const std::string&, H, const std::string&, H, const std::string&, H)>& k) {
        return t.obtain(t.inst(t.p.use("Pow_EX"), {W}), "P", [&](const std::string& p1, H h1) {
            return t.obtain(t.inst(t.p.use("Pow_EX"), {p1}), "P", [&](const std::string& p2, H h2) {
                return t.obtain(t.inst(t.p.use("Pow_EX"), {p2}), "P", [&](const std::string& p3, H h3) { return k(p1, h1, p2, h2, p3, h3); });
            });
        });
    }

    // From the SET claim at B: the set, its members those of B that meet M, here every record that meets M.
    H separated(Tac& t, const FmP& body, H set_at_b, const std::function<H(const std::string& q, H m)>& bound) {
        auto cb = as_some(body);
        return t.obtain(set_at_b, "C", [&](const std::string& Cs, H all_w) {
            auto qb = as_all(subst(cb->body, {{cb->v, Cs}}));
            H all_q = t.all("q", [&](const std::string& q) {
                H iffw = t.inst(all_w, {q});
                FmP mq = t.p.fm(iffw)->b->b;
                FmP Mq = subst(qb->body, {{qb->v, q}})->b;
                H l = t.assume(atom("elem", {q, Cs}), [&](H h) { return from_request(t, t.p.and_r(t.p.iff_l(iffw, h))); });
                H r = t.assume(Mq, [&](H h) { return t.p.iff_r(iffw, t.p.and_intro(bound(q, h), to_request(t, h, mq))); });
                return t.p.iff_intro(l, r);
            });
            return t.witness(body, Cs, all_q);
        });
    }

    // A condition's set from the SET claim at its bound: the claim's own when the request wrote its formula as the claim
    // does, else each member's condition carried to and from the request's form of it.
    H condition_set(Tac& t, const FmP& body, H set_at_b) {
        if (alpha_eq(t.p.fm(set_at_b), body)) return set_at_b;
        auto cb = as_some(body);
        return t.obtain(set_at_b, "C", [&](const std::string& Cs, H all_w) {
            auto qb = as_all(subst(cb->body, {{cb->v, Cs}}));
            H all_q = t.all("q", [&](const std::string& q) {
                H iffw = t.inst(all_w, {q});
                FmP Mq = subst(qb->body, {{qb->v, q}})->b;
                H l = t.assume(atom("elem", {q, Cs}), [&](H h) {
                    H in = t.p.iff_l(iffw, h);
                    return t.p.and_intro(t.p.and_l(in), from_request(t, t.p.and_r(in)));
                });
                H r = t.assume(Mq, [&](H h) {
                    return t.p.iff_r(iffw, t.p.and_intro(t.p.and_l(h), to_request(t, t.p.and_r(h), t.p.fm(iffw)->b->b)));
                });
                return t.p.iff_intro(l, r);
            });
            return t.witness(body, Cs, all_q);
        });
    }

    // M from the request's form of it, (exists c. (same_members(c, p) & M[c/p])): each c is its p, by extensionality.
    H from_request(Tac& t, H h) {
        auto s = as_some(t.p.fm(h));
        if (!s || s->body->k != Fm::And || members_of(s->body->a, s->v).empty()) return h;
        return t.obtain(h, s->v, [&](const std::string& c, H b) {
            std::vector<H> parts = t.split(b, 2);
            std::string p = members_of(t.p.fm(parts[0]), c);
            H e = t.p.iff_r(t.inst(t.p.use("extensionality"), {c, p}), parts[0]);
            return transport(t, lm_, c, p, e, from_request(t, parts[1]));
        });
    }

    H to_request(Tac& t, H h, const FmP& target) {
        auto s = as_some(target);
        std::string p = s && s->body->k == Fm::And ? members_of(s->body->a, s->v) : "";
        if (p.empty()) return h;
        FmP body = subst(s->body, {{s->v, p}});
        H same = t.p.iff_l(t.inst(t.p.use("extensionality"), {p, p}), refl(t, p));
        return t.witness(target, p, t.p.and_intro(same, to_request(t, h, body->b)));
    }

    // The SET claim for purpose at its parameters and at B. Its request named each free variable of the claim's formula M
    // par<j> for the instance's component j or par_<p> for its parameter p (args), and listed them in their names' order.
    H set_at(Tac& t, const std::string& purpose, const std::map<std::string, std::string>& args, const FmP& M,
             const std::string& q, const std::string& B) {
        std::map<std::string, std::string> name_of, used;
        for (const auto& [n, v] : args) name_of[v] = n;
        Nums nv = zv();
        for (const auto& [v, c] : nv) name_of[v] = "num" + std::to_string(c);
        for (const std::string& v : free_vars(M)) {
            if (v == q) continue;
            auto it = name_of.find(v);
            if (it == name_of.end()) throw std::runtime_error("the set for " + purpose + " has a variable " + v + " of no name");
            used[it->second] = v;
        }
        const std::string name = sets_name(sets_, purpose);
        size_t binders = 0;
        for (FmP f = known_.at(name); auto b = as_all(f); f = b->body) ++binders;
        if (binders != used.size() + 1) throw std::runtime_error("the set for " + purpose + " has other parameters");
        H h = t.p.use(name);
        for (const auto& [n, v] : used) h = t.inst(h, {v});
        return t.inst(h, {B});
    }

    // The formula a component's request was made from, at the claim's q: its members' formula, a condition's own part.
    static std::pair<FmP, std::string> request_formula(const FmP& body, bool condition) {
        auto q = as_all(as_some(body)->body);
        FmP m = q->body->b;
        return {condition ? m->b : m, q->v};
    }

    // y in W from eq(y, x), x a numeral of known value below W's.
    H into(Tac& t, Eval& ev, const std::string& y, const std::string& x, H eq_y_x, const std::string& W, uint64_t M) {
        uint64_t c = ev.known(x);
        H zin = use_chain(t, t.p.use(lm_.below(c, M)), ev.zs(M), ev.gs(M));
        H xin = t.mp(t.inst(t.p.use("elem_first_subst"), {ev.z[c], x, W}), {t.p.eq_sym(ev.eqz.at(x)), zin});
        return t.mp(t.inst(t.p.use("elem_first_subst"), {x, y, W}), {t.p.eq_sym(eq_y_x), xin});
    }

    // A tuple's entries all in W: each index one of the record's, its entry that one's.
    H entries_in(Tac& t, Eval& ev, const std::string& q, size_t k, const std::function<H(size_t, const std::string&, H)>& in_w) {
        const Entries& e = ev.recs.at(q);
        H tup = t.split(e.rec, k + 1)[0];
        return t.all("i", [&](const std::string& i) {
            return t.all("y", [&](const std::string& y) {
                return t.assume(atom("pmem", {i, y, q}), [&](H py) -> H {
                    H dom = t.mp(t.inst(t.mp(t.inst(t.p.use("tuple_dom"), {q, ev.z[k]}), {tup}), {i, y}), {py});
                    H cases = t.mp(t.inst(use_chain(t, t.p.use(lm_.index_cases(k)), ev.zs(k), ev.gs(k)), {i}), {dom});
                    std::vector<H> parts = t.split(e.rec, k + 1);
                    return t.cases(cases, k, [&](size_t j, H eij) {
                        H pj = t.mp(t.inst(t.p.use(lm_.pmem_cong1()), {i, ev.z[j], y, q}), {eij, py});
                        H td = t.p.iff_l(t.inst(t.p.use("tuple_def"), {q, ev.z[k]}), tup);
                        H fun = t.split(td, 4)[3];
                        H yx = t.mp(t.inst(fun, {ev.z[j], y, e.xs[j]}), {pj, parts[j + 1]});
                        return in_w(j, y, yx);
                    });
                });
            });
        });
    }

    // Indices below z_k are in z_M, k <= M.
    H indices_in(Tac& t, Eval& ev, size_t k, size_t M, const std::function<H(const std::string&, H)>& from_m) {
        return t.all("i", [&](const std::string& i) {
            return t.assume(atom("elem", {i, ev.z[k]}), [&](H h) {
                for (size_t j = k; j < M; ++j)
                    h = t.p.iff_r(t.inst(succ_unfold(t, ev.z[j], ev.z[j + 1], ev.gz[j + 1]), {i}), t.p.or_intro_l(h, atom("eq", {i, ev.z[j]})));
                return from_m(i, h);
            });
        });
    }

    H parts_set(Tac& t, Eval& ev, const FmP& body, const std::string& purpose) {
        FmP mform = member_at_formula(body);
        size_t k = arity(mform);
        size_t M = k;
        // The largest range among the parts.
        FmP g = mform;
        for (size_t i = 0; i < k; ++i) g = as_some(g)->body;
        std::vector<FmP> rngs = conjuncts(g->b, k);
        for (const FmP& r : rngs) M = std::max(M, disjuncts(r).size());
        const std::string& W = ev.z[M];
        auto [rq, rv] = request_formula(body, false);
        return powers(t, W, [&](const std::string& p1, H h1, const std::string& p2, H h2, const std::string& p3, H h3) {
            H setb = set_at(t, purpose, {}, rq, rv, p3);
            return separated(t, body, setb, [&](const std::string& q, H m) {
                return entries(t, ev, q, m, k, false, [&]() -> H {
                    const Entries& e = ev.recs.at(q);
                    H tup = t.split(e.rec, k + 1)[0];
                    H idx = indices_in(t, ev, k, M, [&](const std::string&, H h) { return h; });
                    H ent = entries_in(t, ev, q, k, [&](size_t j, const std::string& y, H yx) {
                        return range_in(t, ev, q, j, y, yx, W, M);
                    });
                    H tp = t.inst(t.p.use(lm_.tuple_pow()), {q, ev.z[k], W, p1, p2, p3});
                    return t.mp(tp, {tup, idx, ent, h1, h2, h3});
                });
            });
        });
    }

    // y = entry j of q, in W, the entry's range read from q's membership m.
    H range_in(Tac& t, Eval& ev, const std::string& q, size_t j, const std::string& y, H yx, const std::string& W, size_t M) {
        const std::string& x = ev.recs.at(q).xs[j];
        H rng = ev.rng.at(x);
        size_t n = disjuncts(t.p.fm(rng)).size();
        auto each = [&](size_t c, H h) {
            ev.value(x, c, h);
            return into(t, ev, y, x, yx, W, M);
        };
        if (n == 1) return each(0, rng);
        return t.cases(rng, n, each);
    }

    // x in the union, from membership in one of its sides.
    H in_union(Tac& t, H def, const std::string& x, H side, bool left) {
        H u = t.inst(def, {x});
        FmP d = t.p.fm(u)->b;
        return t.p.iff_r(u, left ? t.p.or_intro_l(side, d->b) : t.p.or_intro_r(d->a, side));
    }

    // The step relation inside Pow(Pow(Pow(W))), W the indices, states, inputs and outputs together.
    H step_set(Tac& t, Eval& ev, const FmP& body, const std::vector<std::string>& C, const std::vector<H>& ch,
               const std::function<H(const std::string&)>& set_at_b,
               const std::function<H(const std::string&, H, const Typed&)>& typer) {
        auto unite = [&](const std::string& a, const std::string& b, const std::function<H(const std::string&, H)>& k) {
            return t.obtain(t.inst(t.p.use("union2_ex"), {a, b}), "U", k);
        };
        return unite(ev.z[4], C[0], [&](const std::string& u1, H d1) {
            return unite(u1, C[1], [&](const std::string& u2, H d2) {
                return unite(u2, C[2], [&](const std::string& W, H d3) {
                    auto up = [&](const std::string& x, H in, int from) {
                        if (from <= 1) in = in_union(t, d2, x, in, true);
                        if (from <= 2) in = in_union(t, d3, x, in, true);
                        return in;
                    };
                    return powers(t, W, [&](const std::string& p1, H h1, const std::string& p2, H h2, const std::string& p3, H h3) {
                        return separated(t, body, set_at_b(p3), [&](const std::string& q, H m) {
                            return typer(q, m, [&](const std::string& s, H sS, const std::string& a, H aA,
                                                const std::string& b, H bB, const std::string& tt, H tS, H rec4) {
                                ev.recs[q] = {{s, a, b, tt}, rec4};
                                H tup = t.split(rec4, 5)[0];
                                H idx = indices_in(t, ev, 4, 4, [&](const std::string& i, H h) { return up(i, in_union(t, d1, i, h, true), 1); });
                                std::vector<H> in_w{up(s, in_union(t, d1, s, sS, false), 1), up(a, in_union(t, d2, a, aA, false), 2),
                                                    in_union(t, d3, b, bB, false), up(tt, in_union(t, d1, tt, tS, false), 1)};
                                std::vector<std::string> es{s, a, b, tt};
                                H ent = entries_in(t, ev, q, 4, [&](size_t j, const std::string& y, H yx) {
                                    return t.mp(t.inst(t.p.use("elem_first_subst"), {es[j], y, W}), {t.p.eq_sym(yx), in_w[j]});
                                });
                                H tp = t.inst(t.p.use(lm_.tuple_pow()), {q, ev.z[4], W, p1, p2, p3});
                                return t.mp(tp, {tup, idx, ent, h1, h2, h3});
                            });
                        });
                    });
                });
            });
        });
    }

    // ---- Theorems over parameters ----

    H trans(Tac& t, const std::string& a, const std::string& b, const std::string& c, H ab, H bc) {
        return t.mp(t.inst(t.p.use("eq_trans"), {a, b, c}), {ab, bc});
    }
    // pmem(z_0, v, r) and r = ⟨x⟩: eq(v, x).
    H only(Tac& t, const std::string& r, const std::string&, H rec, const std::string& v, H at) {
        return entry_unique(t, r, rec, 1, 0, v, at);
    }
    H tuple_move(Tac& t, const std::string& v, const std::string& w, const std::string& n, H eq_vw, H tv) {
        return t.mp(t.inst(t.p.use(lm_.tuple_cong1()), {v, w, n}), {eq_vw, tv});
    }
    // a <= c and a = b: b <= c.
    H le_move(Tac& t, const std::string& a, const std::string& b, const std::string& c, H eab, H le) {
        return t.cases(le, [&](H ac) {
            return t.p.or_intro_l(t.mp(t.inst(t.p.use("elem_first_subst"), {a, b, c}), {eab, ac}), atom("eq", {b, c}));
        }, [&](H eac) {
            return t.p.or_intro_r(atom("elem", {b, c}), trans(t, b, a, c, t.p.eq_sym(eab), eac));
        });
    }

    // reachable(m(p)) ⊆ { s in m(p).State | length(s.f) ≤ c }, by the invariance rule at that set: each rule keeps f,
    // appends to it under length(f) < c, or takes its rest.
    // A claim's parameters, a typed one with its type's hypothesis; body proves the rest.
    H with_params(Tac& t, const FmP& claim, const std::vector<VarId>& ps,
                  const std::function<H(const std::vector<std::string>&, const std::vector<H>&, FmP)>& body) {
        std::vector<std::string> P;
        std::vector<H> hyps;
        std::function<H(FmP, size_t)> go = [&](FmP g, size_t i) -> H {
            if (i == ps.size()) return body(P, hyps, g);
            auto b = as_all(g);
            if (!b) throw std::runtime_error("a claim without its parameter " + p_.vars[ps[i].v].hint);
            FmP rest = b->body;
            std::string bv = b->v;
            return t.all(p_.vars[ps[i].v].hint, [&](const std::string& x) {
                P.push_back(x);
                FmP r = subst(rest, {{bv, x}});
                H h = p_.vars[ps[i].v].bound ? t.assume(r->a, [&](H hh) {
                    hyps.push_back(hh);
                    H res = go(r->b, i + 1);
                    hyps.pop_back();
                    return res;
                }) : go(r, i + 1);
                P.pop_back();
                return h;
            });
        };
        return go(claim, 0);
    }

    H length_theorem(Tac& t, const FmP& claim, const Theorem& th) {
        if (p_.instances.size() != 1) throw std::runtime_error("a theorem over several systems has no proof route yet");
        NameId inst = p_.instances[0];
        std::vector<Comp> cs = comps_of(p_, inst);
        size_t R = 0, I = 0;
        for (size_t i = 0; i < cs.size(); ++i) {
            if (cs[i].kind == ComponentDef::Rules) R = i;
            if (cs[i].kind == ComponentDef::Condition) I = i;
        }
        size_t S = cs[R].roles[0], A = cs[R].roles[1], B = cs[R].roles[2];
        return with_params(t, claim, th.params, [&](const std::vector<std::string>& P, const std::vector<H>& hyps, FmP g) {
            return with_components(t, g, cs.size(), [&](const std::vector<std::string>& C, const std::vector<H>& ch, FmP body) {
                return length_body(t, th, inst, C, ch, S, A, B, R, I, P, hyps, body);
            });
        });
    }

    H length_body(Tac& t, const Theorem& th, NameId inst, const std::vector<std::string>& C, const std::vector<H>& ch,
                  size_t S, size_t A, size_t B, size_t R, size_t I, const std::vector<std::string>& P,
                  const std::vector<H>& hyps, FmP body) {
        auto bx = as_all(body);
        if (!bx || bx->body->k != Fm::Imp || bx->body->b->k != Fm::And)
            throw std::runtime_error("only reachable(m) ⊆ { s in m.State | φ } has a proof route yet");
        auto phi = [&](const std::string& x) { return subst(bx->body->b->b, {{bx->v, x}}); };
        // φ(x) = (exists v. (At_0(v, x) & (exists n. (tuple(v, n) & (n in c | n = c))))).
        FmP probe = phi(fresh("_x"));
        auto v1 = as_some(probe);
        auto n1 = v1 ? as_some(v1->body->b) : std::nullopt;
        if (!n1 || n1->body->k != Fm::And || n1->body->b->k != Fm::Or)
            throw std::runtime_error("only length(s.f) ≤ c has a proof route over parameters yet");
        std::string c = n1->body->b->a->args[1];
        H hcap;
        bool found = false;
        for (H h : hyps)
            if (is_atom(t.p.fm(h), "Sys.natural", {c})) {
                hcap = h;
                found = true;
            }
        if (!found) throw std::runtime_error("the bound " + c + " is not a natural-number parameter");
        auto le = [&](const std::string& n) { return disj(atom("elem", {n, c}), atom("eq", {n, c})); };
        // The invariant is cut by the successor sc of c: n <= c is n in sc.
        return t.obtain(t.inst(t.p.use("nsucc_EX"), {c}), "S", [&](const std::string& sc, H nsc) {
        H below = succ_unfold(t, c, sc, nsc);
        // φ(u) and φ'(u), its form with n in sc, each from the other.
        auto conv = [&](const std::string& u, H from, bool to_succ) {
            FmP target = to_succ ? below_succ(phi(u), c, sc) : phi(u);
            return t.obtain(from, "v", [&](const std::string& v, H bv) {
                std::vector<H> av = t.split(bv, 2);
                return t.obtain(av[1], "n", [&](const std::string& n, H bn) {
                    std::vector<H> tn = t.split(bn, 2);
                    H iffn = t.inst(below, {n});
                    H len = to_succ ? t.p.iff_r(iffn, tn[1]) : t.p.iff_l(iffn, tn[1]);
                    auto s1 = as_some(target);
                    FmP inner = subst(s1->body, {{s1->v, v}})->b;
                    return t.witness(target, v, t.p.and_intro(av[0], t.witness(inner, n, t.p.and_intro(tn[0], len))));
                });
            });
        };
        std::string hint;
        for (VarId v : th.params)
            if (p_.vars[v.v].bound) hint = p_.vars[v.v].hint;
        std::string q0 = fresh("_q");
        H setb = set_at(t, th.name, {{"par_succ_" + hint, sc}}, below_succ(phi(q0), c, sc), q0, C[S]);
        return t.obtain(setb, "P", [&](const std::string& Pset, H pc) {
            H wf = t.mp(t.inst(cite(t, ns_ + "." + p_.name(inst).text + "_wellformed"), P), hyps);
            wf = t.mp(t.inst(wf, C), ch);
            // φ(u), witnessed by u's queue g and its length n.
            auto phi_at = [&](const std::string& u, const std::string& g, H at_g, const std::string& n, H tgn, H len) {
                FmP target = phi(u);
                auto s1 = as_some(target);
                FmP inner = subst(s1->body, {{s1->v, g}})->b;
                return t.witness(target, g, t.p.and_intro(at_g, t.witness(inner, n, t.p.and_intro(tgn, len))));
            };
            auto in_p = [&](const std::string& u, H uS, H pu) {
                H iffu = t.inst(pc, {u});
                return t.p.iff_r(iffu, t.p.and_intro(uS, to_request(t, conv(u, pu, true), t.p.fm(iffu)->b->b)));
            };
            H i1 = t.all("u", [&](const std::string& u) {
                return t.assume(atom("elem", {u, Pset}), [&](H h) { return t.p.and_l(t.p.iff_l(t.inst(pc, {u}), h)); });
            });
            H i2 = t.all("u", [&](const std::string& u) {
                return t.assume(atom("elem", {u, C[I]}), [&](H h) {
                    std::vector<H> im = t.split(t.p.iff_l(member_iff(t, ch[I], u), h), 2);
                    return t.obtain(im[1], "v", [&](const std::string& v, H b) {
                        std::vector<H> av = t.split(b, 2);
                        const std::string w = t.p.fm(av[1])->args[1];
                        H zv = t.mp(t.inst(t.p.use(lm_.zero_cong()), {w, v}), {t.p.eq_sym(av[1]), nums_.back().gz.at(0)});
                        H none = t.p.iff_l(t.p.forall_elim(t.p.use("zero_def"), v), zv);
                        H tvv = t.mp(t.p.forall_elim(t.p.use("tuple_zero"), v), {none});
                        H lev = t.mp(t.inst(t.p.use(lm_.zero_le()), {v, c}), {zv, hcap});
                        return in_p(u, im[0], phi_at(u, v, av[0], v, tvv, lev));
                    });
                });
            });
            H i3 = t.all("x", [&](const std::string& x) {
                return t.assume(atom("elem", {x, Pset}), [&](H xP) {
                    std::vector<H> xs = t.split(t.p.iff_l(t.inst(pc, {x}), xP), 2);
                    xs[1] = conv(x, from_request(t, xs[1]), false);
                    return t.all("a", [&](const std::string& a) {
                        return t.all("b", [&](const std::string& b) {
                            return t.all("u", [&](const std::string& u) {
                                H tdef = t.inst(t.p.use("Sys.transition_def"), {C[R], x, a, b, u});
                                return t.assume(t.p.fm(tdef)->a, [&](H tr) {
                                    H uS = t.mp(t.inst(t.mp(t.inst(t.p.use("Sys.wellformed_target"), {C[S], C[A], C[B], C[R], C[I]}),
                                                                {wf}), {x}), {xs[0]});
                                    uS = t.mp(t.inst(uS, {a, b, u}), {tr});
                                    return step_closed(t, C, ch, S, R, c, hcap, x, xs, a, b, u, uS, tr, tdef, phi_at, in_p, le);
                                });
                            });
                        });
                    });
                });
            });
            H i4 = t.all("u", [&](const std::string& u) { return t.assume(atom("elem", {u, Pset}), [](H h) { return h; }); });
            H inv = t.mp(t.inst(t.p.use("Sys.invariance"), {C[S], C[R], C[I], Pset, Pset}), {i1, i2, i3, i4});
            return t.all("x", [&](const std::string& x) {
                return t.assume(subst(bx->body->a, {{bx->v, x}}), [&](H h) {
                    std::vector<H> xs = t.split(t.p.iff_l(t.inst(pc, {x}), t.mp(t.inst(inv, {x}), {t.p.and_r(h)})), 2);
                    return t.p.and_intro(xs[0], conv(x, from_request(t, xs[1]), false));
                });
            });
        });
        });
    }

    using PhiAt = std::function<H(const std::string&, const std::string&, H, const std::string&, H, H)>;
    using InP = std::function<H(const std::string&, H, H)>;

    H step_closed(Tac& t, const std::vector<std::string>& C, const std::vector<H>& ch, size_t S, size_t R, const std::string& c,
                  H hcap, const std::string& x, const std::vector<H>& xs, const std::string& a, const std::string& b,
                  const std::string& u, H uS, H tr, H tdef, const PhiAt& phi_at, const InP& in_p,
                  const std::function<FmP(const std::string&)>& le) {
        H ex = t.p.iff_l(tdef, tr);
        return t.obtain(ex, "q", [&](const std::string& q, H qb) {
            std::vector<H> qt = t.split(qb, 2);
            H rq = t.p.iff_l(tuple4_iff(t, {q, x, a, b, u}), qt[1]);
            std::vector<H> rqs = t.split(rq, 5);
            H atx = rqs[1], atu = rqs[4];
            const std::string z0 = t.p.fm(atx)->args[0];
            H sm = t.p.iff_l(member_iff(t, ch[R], q), qt[0]);
            return t.obtain(sm, "s", [&](const std::string& s, H b1) {
                std::vector<H> s1 = t.split(b1, 2);
                return t.obtain(s1[1], "a", [&](const std::string& a2, H b2) {
                    return t.obtain(t.split(b2, 2)[1], "b", [&](const std::string& b3, H b3h) {
                        return t.obtain(b3h, "t", [&](const std::string& tt, H b4) {
                            std::vector<H> rr = t.split(b4, 2);
                            H e_xs = entry_unique(t, q, rr[0], 4, 0, x, atx);
                            H e_ut = entry_unique(t, q, rr[0], 4, 3, u, atu);
                            // x's queue and its length, from x in the invariant.
                            return t.obtain(xs[1], "v", [&](const std::string& vx, H bx2) {
                                std::vector<H> avx = t.split(bx2, 2);
                                return t.obtain(avx[1], "n", [&](const std::string& nx, H bn) {
                                    std::vector<H> tn = t.split(bn, 2);
                                    // s's queue f, of natural length n0.
                                    H ms = t.p.iff_l(member_iff(t, ch[S], s), s1[0]);
                                    return t.obtain(ms, "f", [&](const std::string& f, H bf) {
                                        std::vector<H> rf = t.split(bf, 2);
                                        return t.obtain(rf[1], "n", [&](const std::string& n0, H bn0) {
                                            std::vector<H> nf = t.split(bn0, 3);
                                            H atvx_s = t.mp(t.inst(t.p.use(lm_.pmem_cong3()), {z0, vx, x, s}), {e_xs, avx[0]});
                                            H e_vxf = only(t, s, f, rf[0], vx, atvx_s);
                                            // u's queue g.
                                            H mu = t.p.iff_l(member_iff(t, ch[S], u), uS);
                                            return t.obtain(mu, "g", [&](const std::string& g, H bg) {
                                                std::vector<H> rg = t.split(bg, 2);
                                                H at_gu = t.split(rg[0], 2)[1];
                                                H at_gt = t.mp(t.inst(t.p.use(lm_.pmem_cong3()), {z0, g, u, tt}), {e_ut, at_gu});
                                                size_t nr = disjuncts(t.p.fm(rr[1])).size();
                                                return t.cases(rr[1], nr, [&](size_t, H rule) {
                                                    return closed_rule(t, s, f, rf[0], n0, nf, tt, g, at_gu, at_gt, u, uS, vx, nx, tn,
                                                                       e_vxf, c, hcap, rule, phi_at, in_p, le);
                                                });
                                            });
                                        });
                                    });
                                });
                            });
                        });
                    });
                });
            });
        });
    }

    H closed_rule(Tac& t, const std::string& s, const std::string& f, H rec_s, const std::string& n0, const std::vector<H>& nf,
                  const std::string& tt, const std::string& g, H at_gu, H at_gt, const std::string& u, H uS,
                  const std::string& vx, const std::string& nx, const std::vector<H>& tn, H e_vxf, const std::string& c,
                  H hcap, H rule, const PhiAt& phi_at, const InP& in_p, const std::function<FmP(const std::string&)>& le) {
        // The rule's pattern variables.
        if (t.p.fm(rule)->k == Fm::Exists)
            return t.obtain(rule, "j", [&](const std::string&, H b) {
                return closed_rule(t, s, f, rec_s, n0, nf, tt, g, at_gu, at_gt, u, uS, vx, nx, tn, e_vxf, c, hcap,
                                   t.split(b, 2)[1], phi_at, in_p, le);
            });
        std::vector<H> parts = t.split(rule, 3);
        return t.obtain(parts[1], "y", [&](const std::string& y, H by) {
            std::vector<H> ry = t.split(by, 2);
            H e_gy = only(t, tt, y, ry[0], g, at_gt);
            return t.obtain(ry[1], "v", [&](const std::string& v, H bv) {
                std::vector<H> av = t.split(bv, 2);
                H e_vf = only(t, s, f, rec_s, v, av[0]);
                H e_vxv = trans(t, vx, f, v, e_vxf, t.p.eq_sym(e_vf));
                FmP shape = t.p.fm(av[1]);
                if (shape->k == Fm::Atom) {
                    // Kept: g = y = v = vx, of length nx.
                    H e_gv = trans(t, g, y, v, e_gy, av[1]);
                    H e_vxg = trans(t, vx, v, g, e_vxv, t.p.eq_sym(e_gv));
                    return in_p(u, uS, phi_at(u, g, at_gu, nx, tuple_move(t, vx, g, nx, e_vxg, tn[0]), tn[1]));
                }
                return t.obtain(av[1], "r", [&](const std::string& r, H br) {
                    std::vector<H> lr = t.split(br, 2);
                    H e_rg = t.p.eq_sym(trans(t, g, y, r, e_gy, lr[1]));
                    auto a1 = as_some(t.p.fm(lr[0]));
                    if (a1 && a1->body->k == Fm::And && a1->body->a->k == Fm::Atom && a1->body->a->name == "tuple") {
                        // Appended: under length(f) < c, the new length, its successor, is at most c.
                        return t.obtain(lr[0], "n", [&](const std::string& n3, H bn3) {
                            std::vector<H> ts = t.split(bn3, 2);
                            return t.obtain(t.inst(t.p.use("nsucc_EX"), {n3}), "m", [&](const std::string& m, H nsm) {
                                H facts = t.mp(t.inst(t.p.use("snoc_facts"), {n3, m}), {nsm});
                                const FmP& sn = t.p.fm(ts[1]);
                                facts = t.mp(t.inst(facts, {v, sn->args[2], r}), {ts[0], ts[1]});
                                H trm = t.split(facts, 3)[0];
                                H tgm = tuple_move(t, r, g, m, e_rg, trm);
                                FmP when = t.p.fm(parts[0]);
                                H guard = when->k == Fm::And ? t.p.and_r(parts[0]) : parts[0];
                                return t.obtain(guard, "v", [&](const std::string& v2, H bv2) {
                                    std::vector<H> av2 = t.split(bv2, 2);
                                    return t.obtain(av2[1], "n", [&](const std::string& n2, H bn2) {
                                        std::vector<H> tn2 = t.split(bn2, 2);
                                        H e_v2v = trans(t, v2, f, v, only(t, s, f, rec_s, v2, av2[0]), t.p.eq_sym(e_vf));
                                        H tvn2 = tuple_move(t, v2, v, n2, e_v2v, tn2[0]);
                                        H e_n2n3 = t.mp(t.inst(t.p.use(lm_.len_uniq()), {v, n2, n3}), {tvn2, ts[0]});
                                        H n3c = t.mp(t.inst(t.p.use("elem_first_subst"), {n2, n3, c}), {e_n2n3, tn2[1]});
                                        H tvn0 = tuple_move(t, f, v, n0, t.p.eq_sym(e_vf), nf[1]);
                                        H e_n0n3 = t.mp(t.inst(t.p.use(lm_.len_uniq()), {v, n0, n3}), {tvn0, ts[0]});
                                        H nat3 = t.mp(t.inst(t.p.use(lm_.nat_cong()), {n0, n3}), {e_n0n3, nf[0]});
                                        H lem = t.mp(t.inst(t.p.use(lm_.succ_le()), {n3, c, m}), {nat3, hcap, n3c, nsm});
                                        return in_p(u, uS, phi_at(u, g, at_gu, m, tgm, lem));
                                    });
                                });
                            });
                        });
                    }
                    // Its rest: one shorter than a queue of length at most c.
                    return t.obtain(lr[0], "n", [&](const std::string& n, H bn) {
                        return t.obtain(bn, "m", [&](const std::string& m, H bm) {
                            std::vector<H> rs = t.split(bm, 4);
                            H tgm = tuple_move(t, r, g, m, e_rg, rs[2]);
                            H tvnx = tuple_move(t, vx, v, nx, e_vxv, tn[0]);
                            H e_nxn = t.mp(t.inst(t.p.use(lm_.len_uniq()), {v, nx, n}), {tvnx, rs[1]});
                            H len = le_move(t, nx, n, c, e_nxn, tn[1]);
                            H lem = t.mp(t.inst(t.p.use(lm_.pred_le()), {m, n, c}), {hcap, rs[0], len});
                            return in_p(u, uS, phi_at(u, g, at_gu, m, tgm, lem));
                        });
                    });
                });
            });
        });
    }

    // ---- Theorems ----

    // reachable(m) ⊆ { s in m.State | φ }, by the invariance rule at { s in m.State | φ }.
    H theorem(Tac& t, const FmP& claim, const std::string& name) {
        if (p_.instances.size() != 1) throw std::runtime_error("a theorem over several systems has no proof route yet");
        NameId inst = p_.instances[0];
        std::vector<Comp> cs = comps_of(p_, inst);
        size_t R = 0, I = 0;
        for (size_t i = 0; i < cs.size(); ++i) {
            if (cs[i].kind == ComponentDef::Rules) R = i;
            if (cs[i].kind == ComponentDef::Condition) I = i;
        }
        size_t S = cs[R].roles[0], A = cs[R].roles[1], B = cs[R].roles[2];
        return with_components(t, claim, cs.size(), [&](const std::vector<std::string>& C, const std::vector<H>& ch, FmP body) {
            auto bx = as_all(body);
            if (!bx || bx->body->k != Fm::Imp || bx->body->b->k != Fm::And || bx->body->a->k != Fm::And ||
                !is_atom(bx->body->b->a, "elem", {bx->v, C[S]}) || bx->body->a->b->name != "Sys.reachable")
                throw std::runtime_error("only reachable(m) ⊆ { s in m.State | φ } has a proof route yet");
            auto phi = [&](const std::string& x) { return subst(bx->body->b->b, {{bx->v, x}}); };
            return numerals(t, N, [&](const std::vector<std::string>& z, const std::vector<H>& gz) {
                Eval ev(t, lm_, z, gz);
                std::string q0 = fresh("_q");
                H setb = set_at(t, name, {}, phi(q0), q0, C[S]);
                return t.obtain(setb, "P", [&](const std::string& P, H pc) {
                    H wf = t.mp(t.inst(cite(t, ns_ + "." + p_.name(inst).text + "_wellformed"), C), ch);
                    size_t ks = arity(member_at(t, ch[S], fresh("_s")));
                    size_t ka = arity(member_at(t, ch[A], fresh("_a")));
                    auto in_p = [&](const std::string& u, H uS) {
                        H pu = ev.prove(phi(u));
                        H iffu = t.inst(pc, {u});
                        return t.p.iff_r(iffu, t.p.and_intro(uS, to_request(t, pu, t.p.fm(iffu)->b->b)));
                    };
                    H i1 = t.all("u", [&](const std::string& u) {
                        return t.assume(atom("elem", {u, P}), [&](H h) { return t.p.and_l(t.p.iff_l(t.inst(pc, {u}), h)); });
                    });
                    H i2 = t.all("u", [&](const std::string& u) {
                        return t.assume(atom("elem", {u, C[I]}), [&](H h) {
                            std::vector<H> im = t.split(t.p.iff_l(member_iff(t, ch[I], u), h), 2);
                            FmP goal = atom("elem", {u, P});
                            return entries(t, ev, u, t.p.iff_l(member_iff(t, ch[S], u), im[0]), ks, true, [&] {
                                if (!ev.truth(t.p.fm(im[1])))
                                    return t.p.bottom_elim(t.p.not_elim(ev.disprove(t.p.fm(im[1])), im[1]), goal);
                                if (!ev.truth(phi(u))) throw std::runtime_error("an initial state does not meet the property");
                                return in_p(u, im[0]);
                            });
                        });
                    });
                    H i3 = t.all("x", [&](const std::string& x) {
                        return t.assume(atom("elem", {x, P}), [&](H xP) {
                            std::vector<H> xs = t.split(t.p.iff_l(t.inst(pc, {x}), xP), 2);
                            xs[1] = from_request(t, xs[1]);
                            return t.all("a", [&](const std::string& a) {
                                return t.all("b", [&](const std::string& b) {
                                    return t.all("u", [&](const std::string& u) {
                                        H tdef = t.inst(t.p.use("Sys.transition_def"), {C[R], x, a, b, u});
                                        return t.assume(t.p.fm(tdef)->a, [&](H tr) {
                                            return closed(t, ev, C, ch, {S, A, B, R, I}, wf, pc, P, phi, ks, ka, x, xs, a, b, u, tr, tdef);
                                        });
                                    });
                                });
                            });
                        });
                    });
                    H i4 = t.all("u", [&](const std::string& u) { return t.assume(atom("elem", {u, P}), [](H h) { return h; }); });
                    H inv = t.mp(t.inst(t.p.use("Sys.invariance"), {C[S], C[R], C[I], P, P}), {i1, i2, i3, i4});
                    return t.all("x", [&](const std::string& x) {
                        return t.assume(subst(bx->body->a, {{bx->v, x}}), [&](H h) {
                            H xp = t.mp(t.inst(inv, {x}), {t.p.and_r(h)});
                            H in = t.p.iff_l(t.inst(pc, {x}), xp);
                            return t.p.and_intro(t.p.and_l(in), from_request(t, t.p.and_r(in)));
                        });
                    });
                });
            });
        });
    }

    // The invariant is closed: a step from x, in it, ends in u, in it; by cases over x's values and the rules.
    // roles: the state, input, output, step and initial components' positions.
    H closed(Tac& t, Eval& ev, const std::vector<std::string>& C, const std::vector<H>& ch, std::array<size_t, 5> roles, H wf,
             H pc, const std::string& P, const std::function<FmP(const std::string&)>& phi, size_t ks, size_t ka,
             const std::string& x, const std::vector<H>& xs, const std::string& a, const std::string& b, const std::string& u,
             H tr, H tdef) {
        auto [S, A, B, R, I] = roles;
        FmP goal = atom("elem", {u, P});
        H uS = t.mp(t.inst(t.mp(t.inst(t.p.use("Sys.wellformed_target"), {C[S], C[A], C[B], C[R], C[I]}), {wf}), {x}), {xs[0]});
        uS = t.mp(t.inst(uS, {a, b, u}), {tr});
        H ex = t.p.iff_l(tdef, tr);
        return t.obtain(ex, "q", [&](const std::string& q, H body) {
            std::vector<H> qt = t.split(body, 2);
            H rq = t.p.iff_l(tuple4_iff(t, {q, x, a, b, u}), qt[1]);
            std::vector<H> rqs = t.split(rq, 5);
            H atx = rqs[1], atu = rqs[4];
            H sm = t.p.iff_l(member_iff(t, ch[R], q), qt[0]);
            return t.obtain(sm, "s", [&](const std::string& s, H b1) {
                std::vector<H> s1 = t.split(b1, 2);
                return t.obtain(s1[1], "a", [&](const std::string& a2, H b2) {
                    std::vector<H> a1 = t.split(b2, 2);
                    return t.obtain(a1[1], "b", [&](const std::string& b3, H b3h) {
                        return t.obtain(b3h, "t", [&](const std::string& tt, H b4) {
                            std::vector<H> rr = t.split(b4, 2);
                            ev.recs[q] = {{s, a2, b3, tt}, rr[0]};
                            H xs_eq = ev.entry_eq(q, 0, x, atx);
                            H ut_eq = ev.entry_eq(q, 3, u, atu);
                            return entries(t, ev, x, t.p.iff_l(member_iff(t, ch[S], x), xs[0]), ks, true, [&] {
                                if (!ev.truth(t.p.fm(xs[1])))
                                    return t.p.bottom_elim(t.p.not_elim(ev.disprove(t.p.fm(xs[1])), xs[1]), goal);
                                return entries(t, ev, s, t.p.iff_l(member_iff(t, ch[S], s), s1[0]), ks, false, [&] {
                                    relate(t, ev, x, xs_eq, s);
                                    return entries(t, ev, a2, t.p.iff_l(member_iff(t, ch[A], a2), a1[0]), ka, true, [&] {
                                        size_t n = disjuncts(t.p.fm(rr[1])).size();
                                        return t.cases(rr[1], n, [&](size_t, H rule) {
                                            std::vector<H> parts = t.split(rule, 3);
                                            if (!ev.truth(t.p.fm(parts[0])))
                                                return t.p.bottom_elim(t.p.not_elim(ev.disprove(t.p.fm(parts[0])), parts[0]), goal);
                                            return learn_record(t, ev, tt, parts[1], ks, [&] {
                                                return entries(t, ev, u, t.p.iff_l(member_iff(t, ch[S], u), uS), ks, false, [&] {
                                                    relate(t, ev, tt, t.p.eq_sym(ut_eq), u);
                                                    if (!ev.truth(phi(u)))
                                                        throw std::runtime_error("a step leaves the property: it is no invariant");
                                                    H pu = ev.prove(phi(u));
                                                    H iffu = t.inst(pc, {u});
                                                    return t.p.iff_r(iffu, t.p.and_intro(uS, to_request(t, pu, t.p.fm(iffu)->b->b)));
                                                });
                                            });
                                        });
                                    });
                                });
                            });
                        });
                    });
                });
            });
        });
    }
};

}  // namespace

std::map<std::string, std::string> requests(const Program& p, const Claims& claims, const std::string& ns) {
    std::map<std::string, std::string> out;
    auto find = [&](const std::string& n) -> FmP {
        for (const auto& [name, f] : claims)
            if (name == n) return f;
        throw std::runtime_error("no claim " + n);
    };
    // A claim's numbers at its top, each named num<its value>.
    auto skip_numbers = [&](FmP f) {
        for (size_t c = 0;; ++c) {
            auto b = as_all(f);
            if (!b || b->body->k != Fm::Imp ||
                !(c == 0 ? is_atom(b->body->a, "zero", {b->v}) : is_atom(b->body->a, "nsucc", {"num" + std::to_string(c - 1), b->v})))
                return f;
            f = subst(b->body, {{b->v, "num" + std::to_string(c)}})->b;
        }
    };
    // A claim's leading parameters, each named par_<its name>, a typed one's hypothesis passed over.
    auto skip_params = [&](FmP f, const std::vector<VarId>& ps) {
        for (VarId v : ps) {
            auto b = as_all(f);
            if (!b) throw std::runtime_error("a claim without its parameter " + p.vars[v.v].hint);
            f = subst(b->body, {{b->v, "par_" + p.vars[v.v].hint}});
            if (p.vars[v.v].bound) {
                if (f->k != Fm::Imp) throw std::runtime_error("a claim without the type of " + p.vars[v.v].hint);
                f = f->b;
            }
        }
        return f;
    };
    auto request = [&](FmP phi, const std::string& var, const std::vector<std::string>& params) {
        // The class machine takes a parameter only on a membership's right side: elsewhere it is a variable c with its members.
        for (const std::string& v : params)
            if (misplaced(phi, v)) {
                std::string c = "c_" + v;
                phi = some(c, conj(same_members(c, v), subst(phi, {{v, c}})));
            }
        std::string s = "shape: SET\nvar: " + var + "\nparams: ";
        for (size_t i = 0; i < params.size(); ++i) s += (i ? ", " : "") + params[i] + " set";
        return s + "\nformula: " + print(phi) + "\n";
    };
    for (NameId i : p.instances) {
        const std::string& in = p.name(i).text;
        std::vector<Comp> cs = comps_of(p, i);
        FmP f = skip_params(skip_numbers(find(ns + "." + in + "_wellformed")), p.name(i).params);
        std::vector<std::string> names;
        for (size_t j = 0; j < cs.size(); ++j) {
            auto b = as_all(f);
            std::string x = "par" + std::to_string(j);
            names.push_back(x);
            f = subst(b->body, {{b->v, x}});
        }
        for (size_t j = 0; j < cs.size(); ++j) {
            FmP chr = f->a;
            f = f->b;
            auto q = as_all(chr);
            FmP m = subst(q->body, {{q->v, "u"}})->b;
            if (cs[j].kind == ComponentDef::Condition) m = m->b;
            if (cs[j].kind == ComponentDef::Parts && m->k == Fm::Atom) continue;
            std::vector<std::string> params;
            for (const std::string& v : free_vars(m))
                if (v != "u") params.push_back(v);
            out[in + "." + cs[j].label] = request(m, "u", params);
        }
    }
    for (const Theorem& th : p.theorems) {
        FmP f = skip_params(skip_numbers(find(ns + "." + th.name)), th.params);
        while (auto b = as_all(f)) f = subst(b->body, {{b->v, "par" + b->v}});
        while (f->k == Fm::Imp && as_all(f->a)) f = f->b;
        auto x = as_all(f);
        if (!x || x->body->k != Fm::Imp || x->body->b->k != Fm::And) continue;
        FmP phi = subst(x->body->b->b, {{x->v, "u"}});
        for (VarId v : th.params)
            if (p.vars[v.v].bound) phi = below_succ(phi, "par_" + p.vars[v.v].hint, "par_succ_" + p.vars[v.v].hint);
        std::vector<std::string> params;
        for (const std::string& v : free_vars(phi))
            if (v != "u") params.push_back(v);
        out[th.name] = request(phi, "u", params);
    }
    return out;
}

std::string prove_claims(const Program& p, const Claims& claims, std::map<std::string, FmP>& known, Lemmas& lm,
                         const std::map<std::string, std::string>& sets, const std::string& ns) {
    ClaimProofs cp(p, known, lm, sets, ns);
    std::string out, missing;
    std::vector<std::string> names;
    for (const auto& [name, f] : claims) {
        try {
            out += cp.prove(name, f) + "\n";
        } catch (const std::exception& e) {
            missing += std::string(missing.empty() ? "" : "\n") + "no proof of " + name + ": " + e.what();
            names.push_back(name);
            // In its place, so a later proof may cite it: the checker then counts that proof conditional.
            out += "proof " + name + ": UNPROVED\n\n";
        }
        known[name] = f;
    }
    if (!missing.empty()) throw Unproved(missing, out, names);
    return out;
}

}  // namespace sys2fol::prove
