#include "src/prove/lemmas.h"

#include <sstream>
#include <stdexcept>
#include <tuple>

namespace sys2fol::prove {

namespace {

std::vector<std::string> names(const std::string& hint, size_t n) {
    std::vector<std::string> xs;
    for (size_t i = 0; i < n; ++i) xs.push_back(fresh(hint));
    return xs;
}

// (forall x0. (set(x0) -> ... body)) over the given names.
FmP all_of(const std::vector<std::string>& xs, FmP body) {
    for (size_t i = xs.size(); i-- > 0;) body = all(xs[i], body);
    return body;
}

// Proves all_of(xs, ...) with fresh variables, body(xs).
H intro_all(Tac& t, size_t n, const std::string& hint,
            const std::function<H(const std::vector<std::string>&)>& body) {
    std::vector<std::string> xs;
    std::function<H(size_t)> go = [&](size_t i) -> H {
        if (i == n) return body(xs);
        return t.all(hint, [&](const std::string& x) {
            xs.push_back(x);
            H h = go(i + 1);
            xs.pop_back();
            return h;
        });
    };
    return go(0);
}

H zero_unfold(Tac& t, const std::string& z, H g) {
    return t.p.iff_l(t.p.forall_elim(t.p.use("zero_def"), z), g);
}

}  // namespace

H refl(Tac& t, const std::string& x) { return t.p.forall_elim(t.p.use("eq_refl"), x); }

H intro_chain(Tac& t, size_t k, const std::function<H(const std::vector<std::string>&, const std::vector<H>&)>& body) {
    std::vector<std::string> zs;
    std::vector<H> gs;
    std::function<H(size_t)> go = [&](size_t i) -> H {
        if (i == k + 1) return body(zs, gs);
        return t.all("z", [&](const std::string& z) {
            FmP guard = i == 0 ? atom("zero", {z}) : atom("nsucc", {zs.back(), z});
            zs.push_back(z);
            H h = t.assume(guard, [&](H g) {
                gs.push_back(g);
                H r = go(i + 1);
                gs.pop_back();
                return r;
            });
            zs.pop_back();
            return h;
        });
    };
    return go(0);
}

H use_chain(Tac& t, H h, const std::vector<std::string>& zs, const std::vector<H>& guards) {
    for (size_t i = 0; i < zs.size(); ++i) h = t.mp(t.inst(h, {zs[i]}), {guards[i]});
    return h;
}

H canonical(Tac& t, size_t k, const std::function<H(const std::vector<std::string>&, const std::vector<H>&)>& body) {
    std::vector<std::string> zs;
    std::vector<H> gs;
    std::function<H(size_t)> go = [&](size_t i) -> H {
        if (i == k + 1) return body(zs, gs);
        H ex = i == 0 ? t.p.use("zero_EX") : t.inst(t.p.use("nsucc_EX"), {zs.back()});
        return t.obtain(ex, "c", [&](const std::string& z, H g) {
            zs.push_back(z);
            gs.push_back(g);
            H h = go(i + 1);
            zs.pop_back();
            gs.pop_back();
            return h;
        });
    };
    return go(0);
}

std::vector<H> chains_equal(Tac& t, const std::vector<std::string>& a, const std::vector<H>& ga,
                            const std::vector<std::string>& b, const std::vector<H>& gb) {
    std::vector<H> eqs;
    for (size_t i = 0; i < a.size() && i < b.size(); ++i) {
        if (i == 0) {
            eqs.push_back(t.mp(t.inst(t.p.use("zero_UNIQ"), {a[0], b[0]}), {ga[0], gb[0]}));
        } else {
            H e = t.inst(t.p.use("nsucc_eq"), {a[i - 1], b[i - 1], a[i], b[i]});
            eqs.push_back(t.mp(e, {eqs.back(), ga[i], gb[i]}));
        }
    }
    return eqs;
}

H succ_unfold(Tac& t, const std::string& n, const std::string& m, H g) {
    return t.p.iff_l(t.inst(t.p.use("nsucc_def"), {n, m}), g);
}

H inject(Tac& t, H h, const std::vector<FmP>& ds, size_t j) {
    if (j + 1 < ds.size()) h = t.p.or_intro_l(h, disj(std::vector<FmP>(ds.begin() + j + 1, ds.end())));
    for (size_t i = j; i-- > 0;) h = t.p.or_intro_r(ds[i], h);
    return h;
}

namespace {

struct FamilyInfo {
    Family family;
    const char* name;
    size_t sizes;
};
constexpr FamilyInfo kFamilies[] = {
    {Family::below, "below", 2},
    {Family::distinct, "distinct", 2},
    {Family::rec_ex, "rec_ex", 1},
    {Family::index_cases, "index_cases", 1},
};

const FamilyInfo& info(Family f) {
    for (const FamilyInfo& i : kFamilies)
        if (i.family == f) return i;
    throw std::logic_error("a family with no name");
}

}  // namespace

bool Instance::operator<(const Instance& o) const {
    return std::tie(family, sizes) < std::tie(o.family, o.sizes);
}

std::string base_name(const Instance& in) {
    std::string s = info(in.family).name;
    for (uint64_t n : in.sizes) s += "_" + std::to_string(n);
    return s;
}

std::string to_line(const Instance& in) {
    std::string s = info(in.family).name;
    for (uint64_t n : in.sizes) s += " " + std::to_string(n);
    return s;
}

Instance from_line(const std::string& line) {
    std::istringstream in(line);
    std::string name;
    in >> name;
    for (const FamilyInfo& i : kFamilies) {
        if (name != i.name) continue;
        Instance r{i.family, {}};
        for (uint64_t n; in >> n;) r.sizes.push_back(n);
        if (!in.eof() || r.sizes.size() != i.sizes) break;
        return r;
    }
    throw std::runtime_error("not an instance: " + line);
}

std::string Lemmas::instance(const Instance& in, const std::function<FmP()>& statement,
                             const std::function<H(Tac&)>& proof) {
    if (project_.empty()) return make(ns_ + ".lemma." + base_name(in), statement, proof);
    std::string name = project_ + ".instance." + base_name(in);
    if (prove_instances_) return make(name, statement, proof);
    if (needs_.insert(in).second) known_[name] = statement();
    return name;
}

std::string Lemmas::prove_instance(const Instance& in) {
    const std::vector<uint64_t>& n = in.sizes;
    switch (in.family) {
        case Family::below: return below(n[0], n[1]);
        case Family::distinct: return distinct(n[0], n[1]);
        case Family::rec_ex: return rec_ex(n[0]);
        case Family::index_cases: return index_cases(n[0]);
    }
    throw std::logic_error("a family with no case");
}

std::string Lemmas::make(const std::string& name, const std::function<FmP()>& statement,
                         const std::function<H(Tac&)>& proof) {
    if (made_.count(name)) return name;
    made_[name] = true;
    FmP s = statement();
    Proof p(name, known_);
    Tac t(p);
    H h = proof(t);
    if (!alpha_eq(p.fm(h), s))
        throw std::runtime_error("the proof of " + name + " ends with " + print(p.fm(h)).substr(0, 400) + ", not " +
                                 print(s).substr(0, 400));
    p.qed(h);
    proofs_ += p.text() + "\n";
    claims_.push_back({name, s});
    known_[name] = s;
    return name;
}

std::string Lemmas::header() const {
    std::string s = "# Written by sysprove: facts about numbers and records that proofs cite.\n";
    for (const auto& [name, f] : claims_) s += "\nclaim " + name + ": " + print(f) + "\n";
    return s;
}

std::string Lemmas::below(uint64_t c, uint64_t d) {
    auto statement = [&] {
        return enc::chain(d, [&](const std::vector<std::string>& z) { return atom("elem", {z[c], z[d]}); });
    };
    return instance({Family::below, {c, d}}, statement, [&](Tac& t) {
        return intro_chain(t, d, [&](const std::vector<std::string>& z, const std::vector<H>& g) {
            H u = t.inst(succ_unfold(t, z[c], z[c + 1], g[c + 1]), {z[c]});
            H e = t.p.iff_r(u, t.p.or_intro_r(atom("elem", {z[c], z[c]}), refl(t, z[c])));
            for (uint64_t k = c + 1; k < d; ++k) {
                H uk = t.inst(succ_unfold(t, z[k], z[k + 1], g[k + 1]), {z[c]});
                e = t.p.iff_r(uk, t.p.or_intro_l(e, atom("eq", {z[c], z[k]})));
            }
            return e;
        });
    });
}

std::string Lemmas::distinct(uint64_t c, uint64_t d) {
    std::string b = below(c, d);
    auto statement = [&] {
        return enc::chain(d, [&](const std::vector<std::string>& z) { return neg(atom("eq", {z[c], z[d]})); });
    };
    return instance({Family::distinct, {c, d}}, statement, [&](Tac& t) {
        return intro_chain(t, d, [&](const std::vector<std::string>& z, const std::vector<H>& g) {
            return t.refute(atom("eq", {z[c], z[d]}), [&](H h) {
                H m = use_chain(t, t.p.use(b), z, g);
                H e = t.mp(t.inst(t.p.use("elem_second"), {z[d], z[c], z[c]}), {t.p.eq_sym(h), m});
                return t.p.not_elim(t.inst(t.p.use("no_self_member"), {z[c]}), e);
            });
        });
    });
}

std::string Lemmas::rec_ex(size_t k) {
    std::string tc = tuple_cong2(), pc = pmem_cong1();
    auto statement = [&] {
        return enc::chain(k, [&](const std::vector<std::string>& z) {
            std::vector<std::string> xs = names("_x", k);
            std::string r = fresh("_r");
            return all_of(xs, some(r, enc::rec(r, xs, z)));
        });
    };
    return instance({Family::rec_ex, {k}}, statement, [&](Tac& t) {
        return intro_chain(t, k, [&](const std::vector<std::string>& z, const std::vector<H>& g) {
            return intro_all(t, k, "x", [&](const std::vector<std::string>& xs) {
                H tz = t.mp(t.p.forall_elim(t.p.use("tuple_zero"), z[0]), {zero_unfold(t, z[0], g[0])});
                std::vector<H> pm;
                std::function<H(size_t, const std::string&, H)> build = [&](size_t j, const std::string& r, H tup) -> H {
                    if (j == k) {
                        std::vector<H> parts{tup};
                        parts.insert(parts.end(), pm.begin(), pm.end());
                        std::string rv = fresh("_r");
                        return t.witness(some(rv, enc::rec(rv, xs, z)), r, t.join(parts));
                    }
                    H sx = t.inst(t.p.use("snoc_EX"), {r, z[j], xs[j]});
                    return t.obtain(sx, "s", [&](const std::string& s, H snoc) {
                        H f = t.mp(t.inst(t.p.use("snoc_facts"), {z[j], z[j + 1]}), {g[j + 1]});
                        f = t.mp(t.inst(f, {r, xs[j], s}), {tup, snoc});
                        std::vector<H> facts = t.split(f, 3);
                        std::vector<H> saved = pm;
                        for (size_t l = 0; l < pm.size(); ++l) pm[l] = t.mp(t.inst(facts[2], {z[l], xs[l]}), {pm[l]});
                        pm.push_back(facts[1]);
                        H h = build(j + 1, s, facts[0]);
                        pm = saved;
                        return h;
                    });
                };
                return build(0, z[0], tz);
            });
        });
    });
}

std::string Lemmas::index_cases(size_t k) {
    auto statement = [&] {
        return enc::chain(k, [&](const std::vector<std::string>& z) {
            std::string i = fresh("_i");
            std::vector<FmP> ds;
            for (size_t j = 0; j < k; ++j) ds.push_back(atom("eq", {i, z[j]}));
            return all(i, imp(atom("elem", {i, z[k]}), disj(ds)));
        });
    };
    return instance({Family::index_cases, {k}}, statement, [&](Tac& t) {
        return intro_chain(t, k, [&](const std::vector<std::string>& z, const std::vector<H>& g) {
            return t.all("i", [&](const std::string& i) {
                std::vector<FmP> ds;
                for (size_t j = 0; j < k; ++j) ds.push_back(atom("eq", {i, z[j]}));
                FmP goal = disj(ds);
                return t.assume(atom("elem", {i, z[k]}), [&](H mem) {
                    std::function<H(size_t, H)> go = [&](size_t j, H m) -> H {
                        if (j == 0) return t.p.bottom_elim(t.p.not_elim(t.inst(zero_unfold(t, z[0], g[0]), {i}), m), goal);
                        H s = t.p.iff_l(t.inst(succ_unfold(t, z[j - 1], z[j], g[j]), {i}), m);
                        return t.cases(s, [&](H l) { return go(j - 1, l); }, [&](H r) { return inject(t, r, ds, j - 1); });
                    };
                    return go(k, mem);
                });
            });
        });
    });
}

namespace {

// P(..., y, ...) from P(..., x, ...), x at position k, by P's congruence there.
H cong_atom(Tac& t, Lemmas& lm, H h, size_t k, const std::string& y, H exy) {
    FmP a = t.p.fm(h);
    const std::vector<std::string>& A = a->args;
    const std::string x = A[k];
    const std::string& p = a->name;
    auto use = [&](const std::string& n, const std::vector<std::string>& args, const std::vector<H>& ants) {
        return t.mp(t.inst(t.p.use(n), args), ants);
    };
    if (p == "elem") return k == 0 ? use("elem_first_subst", {x, y, A[1]}, {exy, h}) : use("elem_second", {x, y, A[0]}, {exy, h});
    if (p == "eq") return k == 0 ? use("eq_trans", {y, x, A[1]}, {t.p.eq_sym(exy), h}) : use("eq_trans", {A[0], x, y}, {h, exy});
    if (p == "zero") return use(lm.zero_cong(), {x, y}, {exy, h});
    if (p == "Sys.natural") return use(lm.nat_cong(), {x, y}, {exy, h});
    if (p == "tuple") return k == 0 ? use(lm.tuple_cong1(), {x, y, A[1]}, {exy, h}) : use(lm.tuple_cong2(), {A[0], x, y}, {exy, h});
    if (p == "pmem") {
        if (k == 0) return use(lm.pmem_cong1(), {x, y, A[1], A[2]}, {exy, h});
        if (k == 1) return use(lm.pmem_cong2(), {A[0], x, y, A[2]}, {exy, h});
        return use(lm.pmem_cong3(), {A[0], A[1], x, y}, {exy, h});
    }
    if (p == "nsucc") return k == 0 ? use("nsucc_CONG", {x, y, A[1]}, {exy, h}) : use(lm.nsucc_cong2(), {A[0], x, y}, {exy, h});
    if (p == "kpair") {
        if (k == 2) return use("kpair_res_cong", {A[0], A[1], x, y}, {h, exy});
        return use("kpair_arg_cong", {A[0], A[1], k == 0 ? y : A[0], k == 1 ? y : A[1], A[2]},
                   {h, k == 0 ? exy : refl(t, A[0]), k == 1 ? exy : refl(t, A[1])});
    }
    if (p == "snoc") {
        if (k == 3) return use("snoc_res_cong", {A[0], A[1], A[2], x, y}, {h, exy});
        std::vector<std::string> args;
        std::vector<H> ants;
        for (size_t j = 0; j < 3; ++j) {
            args.insert(args.end(), {A[j], j == k ? y : A[j]});
            ants.push_back(j == k ? exy : refl(t, A[j]));
        }
        args.push_back(A[3]);
        ants.push_back(h);
        return use("snoc_CONG", args, ants);
    }
    throw std::runtime_error("no congruence for " + p);
}

}  // namespace

H transport(Tac& t, Lemmas& lm, const std::string& x, const std::string& y, H exy, H h) {
    FmP f = t.p.fm(h);
    if (!free_vars(f).count(x)) return h;
    auto moved = [&](const FmP& g) { return subst(g, {{x, y}}); };
    auto back = [&](H g) { return transport(t, lm, y, x, t.p.eq_sym(exy), g); };
    auto on = [&](H g) { return transport(t, lm, x, y, exy, g); };
    switch (f->k) {
        case Fm::Atom:
            for (size_t k = 0; k < f->args.size(); ++k)
                if (t.p.fm(h)->args[k] == x) h = cong_atom(t, lm, h, k, y, exy);
            return h;
        case Fm::Not: return t.refute(moved(f->a), [&](H a) { return t.p.not_elim(h, back(a)); });
        case Fm::And: return t.p.and_intro(on(t.p.and_l(h)), on(t.p.and_r(h)));
        case Fm::Or:
            return t.cases(h, [&](H l) { return t.p.or_intro_l(on(l), moved(f->b)); },
                           [&](H r) { return t.p.or_intro_r(moved(f->a), on(r)); });
        case Fm::Imp: return t.assume(moved(f->a), [&](H a) { return on(t.p.implies_elim(h, back(a))); });
        case Fm::Iff: {
            H l = t.assume(moved(f->a), [&](H a) { return on(t.p.iff_l(h, back(a))); });
            H r = t.assume(moved(f->b), [&](H b) { return on(t.p.iff_r(h, back(b))); });
            return t.p.iff_intro(l, r);
        }
        case Fm::Forall:
            if (f->a->k != Fm::Imp || !(f->a->a->k == Fm::Atom && f->a->a->name == "set")) break;
            return t.all(f->name, [&](const std::string& w) { return on(t.inst(h, {w})); });
        case Fm::Exists:
            return t.obtain(h, f->name, [&](const std::string& w, H b) { return t.witness(moved(f), w, on(b)); });
        case Fm::False: return h;
    }
    throw std::runtime_error("transport through an unguarded quantifier: " + print(f).substr(0, 200));
}

}  // namespace sys2fol::prove
