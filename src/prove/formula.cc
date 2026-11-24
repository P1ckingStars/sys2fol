#include "src/prove/formula.h"

#include <functional>
#include <stdexcept>

#include "src/parser/parser.h"

namespace sys2fol::prove {

namespace {

std::shared_ptr<Fm> mk(Fm::K k) {
    auto f = std::make_shared<Fm>();
    f->k = k;
    return f;
}

FmP bin(Fm::K k, FmP a, FmP b) {
    auto f = mk(k);
    f->a = std::move(a);
    f->b = std::move(b);
    return f;
}

FmP quant(Fm::K k, const std::string& x, FmP body) {
    auto f = mk(k);
    f->name = x;
    f->a = std::move(body);
    return f;
}

FmP convert(const logic::Formula& f, std::vector<std::string>& names) {
    if (f.is_predicate()) {
        const logic::PredicateInstance& p = f.as_predicate();
        std::vector<std::string> args;
        for (const logic::Term& t : p.args()) {
            if (!t.is_generalized()) throw std::runtime_error("a statement whose terms are not its variables");
            args.push_back(names[names.size() - 1 - t.as_variable()]);
        }
        return atom(p.predicate().get().get_name(), std::move(args));
    }
    if (f.is_compound()) {
        const logic::Compound& c = f.as_compound();
        switch (c.op) {
            case logic::Op::Bottom: return falsum();
            case logic::Op::Not: return neg(convert(c.left.get(), names));
            case logic::Op::And: return conj(convert(c.left.get(), names), convert(c.right.get(), names));
            case logic::Op::Or: return disj(convert(c.left.get(), names), convert(c.right.get(), names));
            case logic::Op::Implies: return imp(convert(c.left.get(), names), convert(c.right.get(), names));
            case logic::Op::Iff: return iff(convert(c.left.get(), names), convert(c.right.get(), names));
            default: throw std::runtime_error("an unknown connective");
        }
    }
    if (f.is_quantified()) {
        const logic::Quantified& q = f.as_quantified();
        std::string x = fresh("_b");
        names.push_back(x);
        FmP body = convert(q.body.get(), names);
        names.pop_back();
        return quant(q.op == logic::Op::Forall ? Fm::Forall : Fm::Exists, x, body);
    }
    throw std::runtime_error("a statement that refers to a sentence or a schema variable");
}

}  // namespace

std::string fresh(const std::string& hint) {
    static int n = 0;
    return hint + std::to_string(++n);
}

FmP atom(const std::string& p, std::vector<std::string> args) {
    auto f = mk(Fm::Atom);
    f->name = p;
    f->args = std::move(args);
    return f;
}
FmP falsum() { return mk(Fm::False); }
FmP neg(FmP a) {
    auto f = mk(Fm::Not);
    f->a = std::move(a);
    return f;
}
FmP conj(FmP a, FmP b) { return bin(Fm::And, std::move(a), std::move(b)); }
FmP disj(FmP a, FmP b) { return bin(Fm::Or, std::move(a), std::move(b)); }
FmP imp(FmP a, FmP b) { return bin(Fm::Imp, std::move(a), std::move(b)); }
FmP iff(FmP a, FmP b) { return bin(Fm::Iff, std::move(a), std::move(b)); }
FmP forall(const std::string& x, FmP body) { return quant(Fm::Forall, x, std::move(body)); }
FmP exists(const std::string& x, FmP body) { return quant(Fm::Exists, x, std::move(body)); }
FmP is_set(const std::string& x) { return atom("set", {x}); }
FmP all(const std::string& x, FmP body) { return forall(x, imp(is_set(x), std::move(body))); }
FmP some(const std::string& x, FmP body) { return exists(x, conj(is_set(x), std::move(body))); }

FmP conj(const std::vector<FmP>& xs) {
    FmP f = xs.back();
    for (size_t i = xs.size() - 1; i-- > 0;) f = conj(xs[i], f);
    return f;
}

FmP disj(const std::vector<FmP>& xs) {
    if (xs.empty()) return falsum();
    FmP f = xs.back();
    for (size_t i = xs.size() - 1; i-- > 0;) f = disj(xs[i], f);
    return f;
}

std::string print(const FmP& f) {
    switch (f->k) {
        case Fm::Atom: {
            std::string s = f->name + "(";
            for (size_t i = 0; i < f->args.size(); ++i) s += (i ? ", " : "") + f->args[i];
            return s + ")";
        }
        case Fm::False: return "false";
        case Fm::Not: return "(~ " + print(f->a) + ")";
        case Fm::And: return "(" + print(f->a) + " & " + print(f->b) + ")";
        case Fm::Or: return "(" + print(f->a) + " | " + print(f->b) + ")";
        case Fm::Imp: return "(" + print(f->a) + " -> " + print(f->b) + ")";
        case Fm::Iff: return "(" + print(f->a) + " <-> " + print(f->b) + ")";
        case Fm::Forall: return "(forall " + f->name + ". " + print(f->a) + ")";
        case Fm::Exists: return "(exists " + f->name + ". " + print(f->a) + ")";
    }
    return "";
}

std::set<std::string> free_vars(const FmP& f) {
    std::set<std::string> out;
    std::function<void(const FmP&, std::set<std::string>&)> go = [&](const FmP& g, std::set<std::string>& bound) {
        switch (g->k) {
            case Fm::Atom:
                for (const std::string& a : g->args)
                    if (!bound.count(a)) out.insert(a);
                return;
            case Fm::False: return;
            case Fm::Forall:
            case Fm::Exists: {
                bool had = bound.count(g->name);
                bound.insert(g->name);
                go(g->a, bound);
                if (!had) bound.erase(g->name);
                return;
            }
            default:
                go(g->a, bound);
                if (g->b) go(g->b, bound);
        }
    };
    std::set<std::string> bound;
    go(f, bound);
    return out;
}

FmP subst(const FmP& f, const std::map<std::string, std::string>& m) {
    if (m.empty()) return f;
    switch (f->k) {
        case Fm::Atom: {
            std::vector<std::string> args = f->args;
            for (std::string& a : args)
                if (auto it = m.find(a); it != m.end()) a = it->second;
            return atom(f->name, std::move(args));
        }
        case Fm::False: return f;
        case Fm::Forall:
        case Fm::Exists: {
            std::map<std::string, std::string> inner = m;
            inner.erase(f->name);
            std::string x = f->name;
            for (const auto& [from, to] : inner)
                if (to == x) {
                    x = fresh("_b");
                    inner[f->name] = x;
                    break;
                }
            return quant(f->k, x, subst(f->a, inner));
        }
        default: return f->b ? bin(f->k, subst(f->a, m), subst(f->b, m)) : neg(subst(f->a, m));
    }
}

bool alpha_eq(const FmP& a, const FmP& b) {
    std::function<bool(const FmP&, const FmP&, std::map<std::string, std::string>&,
                       std::map<std::string, std::string>&)>
        go = [&](const FmP& x, const FmP& y, std::map<std::string, std::string>& l, std::map<std::string, std::string>& r) {
            if (x->k != y->k) return false;
            switch (x->k) {
                case Fm::Atom: {
                    if (x->name != y->name || x->args.size() != y->args.size()) return false;
                    for (size_t i = 0; i < x->args.size(); ++i) {
                        auto il = l.find(x->args[i]);
                        auto ir = r.find(y->args[i]);
                        if ((il == l.end()) != (ir == r.end())) return false;
                        if (il == l.end() ? x->args[i] != y->args[i] : il->second != ir->second) return false;
                    }
                    return true;
                }
                case Fm::False: return true;
                case Fm::Forall:
                case Fm::Exists: {
                    std::string mark = fresh("_a");
                    auto sl = l.find(x->name) == l.end() ? std::optional<std::string>() : l[x->name];
                    auto sr = r.find(y->name) == r.end() ? std::optional<std::string>() : r[y->name];
                    l[x->name] = mark;
                    r[y->name] = mark;
                    bool ok = go(x->a, y->a, l, r);
                    if (sl) l[x->name] = *sl; else l.erase(x->name);
                    if (sr) r[y->name] = *sr; else r.erase(y->name);
                    return ok;
                }
                default: return go(x->a, y->a, l, r) && (!x->b || go(x->b, y->b, l, r));
            }
        };
    std::map<std::string, std::string> l, r;
    return go(a, b, l, r);
}

FmP generalize(const FmP& body, const std::string& t) {
    std::string x = fresh("_b");
    return exists(x, subst(body, {{t, x}}));
}

std::vector<std::pair<std::string, FmP>> read_statements(const std::string& text, bool claims_only) {
    logic::GlobalContext ctx;
    std::vector<std::pair<std::string, FmP>> out;
    for (const logic::ParsedStatement& s : logic::parse_statements(text, ctx)) {
        if (claims_only && s.kind != logic::ParsedStatement::Kind::Claim) continue;
        std::vector<std::string> names;
        out.push_back({s.name, convert(s.formula.get().root().get(), names)});
    }
    return out;
}

}  // namespace sys2fol::prove
