#include "src/lang/fol.h"

#include <functional>
#include <set>

namespace sys2fol {

namespace {

using Cont = std::function<std::string(const std::string&)>;

std::string all(const std::string& v, const std::string& body) { return "(forall " + v + ". (set(" + v + ") -> " + body + "))"; }
std::string ex(const std::string& v, const std::string& body) { return "(exists " + v + ". (set(" + v + ") & " + body + "))"; }
std::string bin(const std::string& a, const char* op, const std::string& b) { return "(" + a + " " + op + " " + b + ")"; }

std::string fold(const std::vector<std::string>& xs, const char* op, const std::string& empty) {
    if (xs.empty()) return empty;
    std::string s = xs.back();
    for (size_t i = xs.size() - 1; i-- > 0;) s = bin(xs[i], op, s);
    return s;
}

class Writer {
public:
    explicit Writer(const Program& p) : p_(p) {}

    std::string comp(NameId inst, FieldId f) const { return p_.name(inst).text + "_" + p_.field(f).label; }

    std::string formula(const NodeP& n) {
        switch (n->k) {
            case K::True: return "(false -> false)";
            case K::Not: return "(~ " + formula(n->kids[0]) + ")";
            case K::And: return bin(formula(n->kids[0]), "&", formula(n->kids[1]));
            case K::Or: return bin(formula(n->kids[0]), "|", formula(n->kids[1]));
            case K::Implies: return bin(formula(n->kids[0]), "->", formula(n->kids[1]));
            case K::Eq: {
                const NodeP &l = n->kids[0], &r = n->kids[1];
                if (r->k == K::Num) return term(l, [&](const std::string& x) { return numeral(r->num, x); });
                if (l->k == K::Num) return term(r, [&](const std::string& x) { return numeral(l->num, x); });
                return term(l, [&](const std::string& x) {
                    return term(r, [&](const std::string& y) { return "eq(" + x + ", " + y + ")"; });
                });
            }
            case K::In: return term(n->kids[0], [&](const std::string& x) { return member(n->kids[1], x); });
            case K::Subset: {
                std::string x = fresh("x");
                return all(x, bin(member(n->kids[0], x), "->", member(n->kids[1], x)));
            }
            case K::Pred: return args(n, 0, {});
            case K::Lt:
            case K::Le:
                return term(n->kids[0], [&](const std::string& a) {
                    return term(n->kids[1], [&](const std::string& b) {
                        const std::string &x = n->num ? b : a, &y = n->num ? a : b;
                        std::string lt = "elem(" + x + ", " + y + ")";
                        return n->k == K::Lt ? lt : bin(lt, "|", "eq(" + x + ", " + y + ")");
                    });
                });
            case K::All:
            case K::Some: {
                std::string v = bind(n->var);
                std::string body = bin(member(n->kids[0], v), n->k == K::All ? "->" : "&", formula(n->kids[1]));
                bound_.erase(n->var);
                return n->k == K::All ? all(v, body) : ex(v, body);
            }
            default: throw Error(n->pos, "'" + p_.show(n) + "' is not a formula");
        }
    }

    std::string member(const NodeP& s, const std::string& x) {
        switch (s->k) {
            case K::Comp: return "elem(" + x + ", " + comp(s->name, s->field) + ")";
            case K::Var: return "elem(" + x + ", " + var(s->var) + ")";
            case K::Range: {
                if (s->kids[0]->k != K::Num || s->kids[0]->num != 0 || s->kids[1]->k != K::Num)
                    throw Error(s->pos, "only a range 0 ..< n with n written as a number is supported yet");
                std::vector<std::string> cases;
                for (uint64_t i = 0; i < s->kids[1]->num; ++i) cases.push_back(numeral(i, x));
                return fold(cases, "|", "false");
            }
            case K::RecordType: {
                std::vector<std::string> xs, members;
                for (size_t i = 0; i < s->parts.size(); ++i) xs.push_back(fresh("x"));
                for (size_t i = 0; i < s->parts.size(); ++i) members.push_back(member(s->kids[i], xs[i]));
                std::vector<std::string> body{record(x, xs)};
                body.insert(body.end(), members.begin(), members.end());
                std::string f = fold(body, "&", "");
                for (size_t i = xs.size(); i-- > 0;) f = ex(xs[i], f);
                return f;
            }
            case K::SetOf: {
                bound_[s->var] = x;
                std::string f = bin(member(s->kids[0], x), "&", formula(s->kids[1]));
                bound_.erase(s->var);
                return f;
            }
            case K::SetType: {
                std::string y = fresh("y");
                return all(y, bin("elem(" + y + ", " + x + ")", "->", member(s->kids[0], y)));
            }
            case K::PredType: return p_.name(s->name).fol + "(" + x + ")";
            case K::SeqType: {
                std::string n = fresh("n"), i = fresh("i"), y = fresh("y");
                std::string entries = all(i, all(y, bin("pmem(" + i + ", " + y + ", " + x + ")", "->", member(s->kids[0], y))));
                return ex(n, bin("Sys.natural(" + n + ")", "&", bin("tuple(" + x + ", " + n + ")", "&", entries)));
            }
            case K::EnumType: {
                std::string c = fresh("c"), q = fresh("p");
                std::vector<std::string> cases;
                for (size_t k = 0; k < s->kids.size(); ++k) cases.push_back(bin(numeral(k, c), "&", member(s->kids[k], q)));
                return ex(c, ex(q, bin(record(x, {c, q}), "&", fold(cases, "|", "false"))));
            }
            default: throw Error(s->pos, "'" + p_.show(s) + "' is not a set the compiler can read yet");
        }
    }

    std::string term(const NodeP& t, const Cont& k) {
        switch (t->k) {
            case K::Var: return k(var(t->var));
            case K::Comp: return k(comp(t->name, t->field));
            case K::Num: {
                std::string x = fresh("v");
                return ex(x, bin(numeral(t->num, x), "&", k(x)));
            }
            case K::Field:
                return term(t->kids[0], [&](const std::string& r) {
                    std::string x = fresh("v");
                    return ex(x, bin(at(p_.field(t->field).index, x, r), "&", k(x)));
                });
            case K::Length:
                return term(t->kids[0], [&](const std::string& q) {
                    std::string n = fresh("n");
                    return ex(n, bin("tuple(" + q + ", " + n + ")", "&", k(n)));
                });
            case K::First:
                return term(t->kids[0], [&](const std::string& q) {
                    std::string v = fresh("v");
                    return ex(v, bin(at(0, v, q), "&", k(v)));
                });
            case K::Rest:
                return term(t->kids[0], [&](const std::string& q) {
                    std::string r = fresh("r");
                    return ex(r, bin(rest(q, r), "&", k(r)));
                });
            case K::Append:
                return term(t->kids[0], [&](const std::string& q) {
                    return term(t->kids[1], [&](const std::string& y) {
                        std::string r = fresh("r"), n = fresh("n");
                        std::string app = ex(n, bin("tuple(" + q + ", " + n + ")", "&", "snoc(" + q + ", " + n + ", " + y + ", " + r + ")"));
                        return ex(r, bin(app, "&", k(r)));
                    });
                });
            case K::SeqLit:
                return terms(t->kids, 0, {}, [&](const std::vector<std::string>& ys) {
                    std::string v = fresh("v");
                    return ex(v, bin(record(v, ys), "&", k(v)));
                });
            case K::Case:
                return terms(t->kids, 0, {}, [&](const std::vector<std::string>& ys) {
                    std::string c = fresh("c"), q = fresh("p"), v = fresh("v");
                    std::string tagged = ex(v, bin(record(v, {c, q}), "&", k(v)));
                    return ex(c, bin(numeral(p_.name(t->name).index, c), "&", ex(q, bin(record(q, ys), "&", tagged))));
                });
            default: throw Error(t->pos, "'" + p_.show(t) + "' cannot be a value yet");
        }
    }

    std::string characterization(NameId inst, FieldId f, const std::string& c) {
        const ComponentDef& def = p_.name(inst).components.at(f);
        std::string q = fresh("q");
        if (def.kind != ComponentDef::Rules) return all(q, bin("elem(" + q + ", " + c + ")", "<->", member(def.set, q)));
        std::string s = bind(def.s), a = bind(def.a), b = bind(def.b), t = bind(def.t);
        std::vector<std::string> cases;
        for (const RuleDef& r : def.rules) {
            std::vector<std::string> vs;
            for (VarId v : r.binders) vs.push_back(bind(v));
            std::string c = fold({formula(r.when), record_of(t, r.next), record_of(b, r.out)}, "&", "");
            for (size_t i = vs.size(); i-- > 0;) {
                c = ex(vs[i], bin(member(p_.vars[r.binders[i].v].bound, vs[i]), "&", c));
                bound_.erase(r.binders[i]);
            }
            cases.push_back(c);
        }
        std::string step = bin(record(q, {s, a, b, t}), "&", fold(cases, "|", "false"));
        std::string body = ex(s, bin("elem(" + s + ", " + comp(inst, def.state) + ")", "&",
                                     ex(a, bin("elem(" + a + ", " + comp(inst, def.input) + ")", "&", ex(b, ex(t, step))))));
        for (VarId v : {def.s, def.a, def.b, def.t}) bound_.erase(v);
        return all(q, bin("elem(" + q + ", " + c + ")", "<->", body));
    }

    // Every component in `comps`, each with its characterization, around `body`.
    std::string with(const std::vector<std::pair<NameId, FieldId>>& comps, const std::string& body) {
        std::string f = body;
        for (size_t i = comps.size(); i-- > 0;) {
            std::string c = comp(comps[i].first, comps[i].second);
            f = bin(characterization(comps[i].first, comps[i].second, c), "->", f);
        }
        for (size_t i = comps.size(); i-- > 0;) f = all(comp(comps[i].first, comps[i].second), f);
        return f;
    }

    // The parameters named before a claim is written, then each quantified with its type.
    std::vector<std::string> open(const std::vector<VarId>& ps) {
        std::vector<std::string> out;
        for (VarId v : ps) out.push_back(bind(v));
        return out;
    }
    std::string close(const std::vector<VarId>& ps, const std::vector<std::string>& ns, std::string f) {
        for (size_t i = ps.size(); i-- > 0;) {
            const NodeP& type = p_.vars[ps[i].v].bound;
            f = all(ns[i], type ? bin(member(type, ns[i]), "->", f) : f);
            bound_.erase(ps[i]);
        }
        return f;
    }
    // An instance's parameters stand for the arguments it is applied to.
    void alias(VarId param, VarId arg) { bound_[param] = var(arg); }

    std::string fresh(const std::string& hint) { return hint + std::to_string(++counter_); }

private:
    const Program& p_;
    std::map<VarId, std::string> bound_;
    int counter_ = 0;

    std::string bind(VarId v) { return bound_[v] = fresh(p_.vars[v.v].hint); }
    std::string var(VarId v) {
        auto it = bound_.find(v);
        if (it == bound_.end()) throw Error({}, "the variable " + p_.vars[v.v].hint + " is not bound");
        return it->second;
    }

    std::string terms(const std::vector<NodeP>& ts, size_t i, std::vector<std::string> names,
                      const std::function<std::string(const std::vector<std::string>&)>& k) {
        if (i == ts.size()) return k(names);
        return term(ts[i], [&](const std::string& x) {
            std::vector<std::string> more = names;
            more.push_back(x);
            return terms(ts, i + 1, more, k);
        });
    }

    // r is q without its first entry, every other entry one index down.
    std::string rest(const std::string& q, const std::string& r) {
        std::string n = fresh("n"), m = fresh("m"), i = fresh("i"), j = fresh("j"), y = fresh("y");
        std::string shift = all(i, all(j, bin("nsucc(" + i + ", " + j + ")", "->",
                                              all(y, bin("pmem(" + j + ", " + y + ", " + q + ")", "<->", "pmem(" + i + ", " + y + ", " + r + ")")))));
        std::string body = bin("nsucc(" + m + ", " + n + ")", "&",
                               bin("tuple(" + q + ", " + n + ")", "&", bin("tuple(" + r + ", " + m + ")", "&", shift)));
        return ex(n, ex(m, body));
    }

    std::string args(const NodeP& n, size_t i, std::vector<std::string> names) {
        if (i == n->kids.size()) {
            std::string s = p_.name(n->name).fol + "(";
            for (size_t k = 0; k < names.size(); ++k) s += (k ? ", " : "") + names[k];
            return s + ")";
        }
        return term(n->kids[i], [&](const std::string& x) {
            std::vector<std::string> more = names;
            more.push_back(x);
            return args(n, i + 1, more);
        });
    }

    // Numerals z0, …, zn, z0 being 0 and each the successor of the one before, around `inner`.
    std::string chain(size_t n, const std::function<std::string(const std::vector<std::string>&)>& inner) {
        std::vector<std::string> zs;
        for (size_t i = 0; i <= n; ++i) zs.push_back(fresh("n"));
        std::string body = inner(zs);
        for (size_t i = n + 1; i-- > 0;) {
            std::string guard = i == 0 ? "zero(" + zs[0] + ")" : "nsucc(" + zs[i - 1] + ", " + zs[i] + ")";
            body = all(zs[i], bin(guard, "->", body));
        }
        return body;
    }

    std::string numeral(uint64_t n, const std::string& x) {
        if (n == 0) return "zero(" + x + ")";
        return chain(n - 1, [&](const std::vector<std::string>& z) { return "nsucc(" + z[n - 1] + ", " + x + ")"; });
    }

    std::string at(uint32_t i, const std::string& x, const std::string& r) {
        return chain(i, [&](const std::vector<std::string>& z) { return "pmem(" + z[i] + ", " + x + ", " + r + ")"; });
    }

    // r is the tuple ⟨xs⟩, written as the library writes Sys.tuple2 and Sys.tuple4.
    std::string record(const std::string& r, const std::vector<std::string>& xs) {
        if (xs.empty()) return "zero(" + r + ")";
        return chain(xs.size(), [&](const std::vector<std::string>& z) {
            std::vector<std::string> parts{"tuple(" + r + ", " + z[xs.size()] + ")"};
            for (size_t i = 0; i < xs.size(); ++i) parts.push_back("pmem(" + z[i] + ", " + xs[i] + ", " + r + ")");
            return fold(parts, "&", "");
        });
    }

    // r is the record of `values`.
    std::string record_of(const std::string& r, const std::vector<NodeP>& values) {
        std::vector<std::string> xs;
        for (size_t i = 0; i < values.size(); ++i) xs.push_back(fresh("x"));
        std::vector<std::string> body{record(r, xs)};
        for (size_t i = 0; i < values.size(); ++i) {
            const NodeP& v = values[i];
            const std::string& x = xs[i];
            if (v->k == K::Num) body.push_back(numeral(v->num, x));
            else body.push_back(term(v, [&](const std::string& y) { return "eq(" + x + ", " + y + ")"; }));
        }
        std::string f = fold(body, "&", "");
        for (size_t i = xs.size(); i-- > 0;) f = ex(xs[i], f);
        return f;
    }
};

void instances_in(const Program& p, const NodeP& n, std::set<NameId>& out) {
    if (n->k == K::Comp || n->k == K::Inst) out.insert(n->name);
    for (const NodeP& k : n->kids) instances_in(p, k, out);
}

// Each parameterized instance a claim applies, with the theorem's parameters it is applied to.
void applications(const Program& p, const NodeP& n, std::map<NameId, std::vector<NodeP>>& out) {
    if (n->k == K::Inst && !n->kids.empty()) {
        auto [it, fresh] = out.insert({n->name, n->kids});
        if (!fresh && it->second.size() == n->kids.size())
            for (size_t i = 0; i < n->kids.size(); ++i)
                if (n->kids[i]->k != K::Var || it->second[i]->k != K::Var || !(n->kids[i]->var == it->second[i]->var))
                    throw Error(n->pos, p.name(n->name).text + " is applied to two argument lists: not supported yet");
    }
    for (const NodeP& k : n->kids) applications(p, k, out);
}

std::vector<std::pair<NameId, FieldId>> components_of(const Program& p, const std::set<NameId>& insts) {
    std::vector<std::pair<NameId, FieldId>> out;
    for (NameId i : p.instances)
        if (insts.count(i))
            for (FieldId f : p.name(p.name(i).structure).fields) out.push_back({i, f});
    return out;
}

}  // namespace

std::vector<Claim> claims(Program& p, const std::string& ns, std::vector<std::string>* steps) {
    std::vector<Claim> out;
    for (NameId inst : p.instances)
        for (auto& [f, def] : p.names[inst.v].components) {
            if (def.set) def.set = p.expand(def.set, steps);
            for (RuleDef& r : def.rules) {
                r.when = p.expand(r.when, steps);
                for (NodeP& v : r.next) v = p.expand(v, steps);
                for (NodeP& v : r.out) v = p.expand(v, steps);
            }
        }
    for (NameId inst : p.instances) {
        Writer w(p);
        const NameInfo& info = p.name(inst);
        auto comps = components_of(p, {inst});
        NodeP wf = p.expand(p.wellformedness(inst), steps);
        std::vector<std::string> pn = w.open(info.params);
        out.push_back({ns + "." + info.text + "_wellformed", info.text + " is well formed: " + p.show(wf),
                       w.close(info.params, pn, w.with(comps, w.formula(wf)))});
        for (FieldId f : p.name(info.structure).fields) {
            const ComponentDef& def = info.components.at(f);
            std::vector<std::pair<NameId, FieldId>> deps;
            if (def.kind == ComponentDef::Condition) deps.push_back({inst, def.set->kids[0]->field});
            if (def.kind == ComponentDef::Rules) deps = {{inst, def.state}, {inst, def.input}, {inst, def.output}};
            Writer e(p);
            std::vector<std::string> en = e.open(info.params);
            std::string c = e.fresh("C");
            out.push_back({ns + "." + info.text + "_" + p.field(f).label + "_exists",
                           "the set " + info.text + "." + p.field(f).label + " exists",
                           e.close(info.params, en, e.with(deps, ex(c, e.characterization(inst, f, c))))});
        }
    }
    for (const Theorem& t : p.theorems) {
        NodeP claim = p.expand(t.claim, steps);
        std::set<NameId> insts;
        instances_in(p, claim, insts);
        Writer w(p);
        std::vector<std::string> tn = w.open(t.params);
        std::map<NameId, std::vector<NodeP>> apps;
        applications(p, t.claim, apps);
        for (NameId i : insts) {
            const std::vector<VarId>& ps = p.name(i).params;
            if (ps.empty()) continue;
            auto it = apps.find(i);
            if (it == apps.end()) throw Error(t.pos, p.name(i).text + " needs its arguments");
            for (size_t k = 0; k < ps.size(); ++k) {
                if (it->second[k]->k != K::Var) throw Error(t.pos, "an instance's arguments are the theorem's parameters, yet");
                w.alias(ps[k], it->second[k]->var);
            }
        }
        out.push_back({ns + "." + t.name, p.show(claim), w.close(t.params, tn, w.with(components_of(p, insts), w.formula(claim)))});
    }
    return out;
}

std::string header(const std::vector<Claim>& claims, const std::string& source) {
    std::string s = "# Written by sysc from " + source + ". Each claim is printed above it, as the language reads it.\n";
    for (const Claim& c : claims) s += "\n# " + c.plain + "\nclaim " + c.name + ": " + c.formula + "\n";
    return s;
}

}  // namespace sys2fol
