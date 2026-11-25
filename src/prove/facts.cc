#include "src/prove/facts.h"

#include <stdexcept>

#include "src/prove/lemmas.h"

namespace sys2fol::prove {

namespace {

bool guarded_some(const FmP& f) {
    return f->k == Fm::Exists && f->a->k == Fm::And && f->a->a->k == Fm::Atom && f->a->a->name == "set" &&
           f->a->a->args == std::vector<std::string>{f->name};
}

FmP body_at(const FmP& ex, const std::string& x) { return subst(ex->a->b, {{ex->name, x}}); }

}  // namespace

void Facts::add(H h) { facts_.push_back(h); }

std::string Facts::resolve(const Sub& s, const std::string& x) const {
    std::string y = x;
    for (auto it = s.find(y); it != s.end(); it = s.find(y)) y = it->second;
    return y;
}

bool Facts::unify(const FmP& p, const FmP& g, Sub& s, std::map<std::string, std::string>& bound) const {
    if (p->k != g->k) return false;
    switch (p->k) {
        case Fm::False: return true;
        case Fm::Atom: {
            if (p->name != g->name || p->args.size() != g->args.size()) return false;
            for (size_t i = 0; i < p->args.size(); ++i) {
                const std::string &pa = p->args[i], &ga = g->args[i];
                if (auto b = bound.find(pa); b != bound.end()) {
                    if (b->second != ga) return false;
                    continue;
                }
                for (const auto& [pb, gb] : bound)
                    if (gb == ga) return false;
                std::string r = resolve(s, pa);
                if (open_.count(r)) s[r] = ga;
                else if (r != ga) return false;
            }
            return true;
        }
        case Fm::Not: return unify(p->a, g->a, s, bound);
        case Fm::And:
        case Fm::Or:
        case Fm::Imp:
        case Fm::Iff: return unify(p->a, g->a, s, bound) && unify(p->b, g->b, s, bound);
        case Fm::Forall:
        case Fm::Exists: {
            auto old = bound.find(p->name);
            std::optional<std::string> saved;
            if (old != bound.end()) saved = old->second;
            bound[p->name] = g->name;
            bool ok = unify(p->a, g->a, s, bound);
            if (saved) bound[p->name] = *saved;
            else bound.erase(p->name);
            return ok;
        }
    }
    return false;
}

bool Facts::plan(const FmP& f, const Sub& s, const std::function<bool(const Sub&)>& k, int depth) {
    if (depth > 200) return false;
    for (H h : facts_) {
        Sub s2 = s;
        std::map<std::string, std::string> bound;
        if (unify(f, t_.p.fm(h), s2, bound) && k(s2)) return true;
    }
    switch (f->k) {
        case Fm::Atom: {
            if (f->name != "eq" || f->args.size() != 2) return false;
            std::string a = resolve(s, f->args[0]), b = resolve(s, f->args[1]);
            bool oa = open_.count(a) > 0, ob = open_.count(b) > 0;
            if (!oa && !ob && a == b && k(s)) return true;
            if (oa != ob) {
                Sub s2 = s;
                if (oa) s2[a] = b;
                else s2[b] = a;
                if (k(s2)) return true;
            }
            FmP sym = atom("eq", {f->args[1], f->args[0]});
            for (H h : facts_) {
                Sub s2 = s;
                std::map<std::string, std::string> bound;
                if (unify(sym, t_.p.fm(h), s2, bound) && k(s2)) return true;
            }
            return false;
        }
        case Fm::And: return plan(f->a, s, [&](const Sub& s2) { return plan(f->b, s2, k, depth + 1); }, depth + 1);
        case Fm::Or: return plan(f->a, s, k, depth + 1) || plan(f->b, s, k, depth + 1);
        case Fm::Exists: {
            if (!guarded_some(f)) return false;
            std::string v = fresh("_w");
            open_.insert(v);
            bool ok = plan(body_at(f, v), s, [&](const Sub& s2) { return resolve(s2, v) != v && k(s2); }, depth + 1);
            open_.erase(v);
            return ok;
        }
        default: return false;
    }
}

std::optional<H> Facts::known(const FmP& f) const {
    for (H h : facts_)
        if (alpha_eq(f, t_.p.fm(h))) return h;
    return {};
}

bool Facts::provable(const FmP& f) {
    return plan(f, {}, [](const Sub&) { return true; }, 0);
}

std::optional<std::string> Facts::witness_of(const FmP& f) {
    if (!guarded_some(f)) return {};
    std::string v = fresh("_w"), w;
    open_.insert(v);
    bool ok = plan(body_at(f, v), {}, [&](const Sub& s) {
        w = resolve(s, v);
        return w != v;
    }, 0);
    open_.erase(v);
    if (!ok) return {};
    return w;
}

H Facts::prove(const FmP& f) {
    if (auto h = known(f)) return *h;
    switch (f->k) {
        case Fm::Atom:
            if (f->name == "eq" && f->args.size() == 2) {
                if (f->args[0] == f->args[1]) return refl(t_, f->args[0]);
                if (auto h = known(atom("eq", {f->args[1], f->args[0]}))) return t_.p.eq_sym(*h);
            }
            break;
        case Fm::And: return t_.p.and_intro(prove(f->a), prove(f->b));
        case Fm::Or:
            if (provable(f->a)) return t_.p.or_intro_l(prove(f->a), f->b);
            return t_.p.or_intro_r(f->a, prove(f->b));
        case Fm::Exists:
            if (auto w = witness_of(f)) return t_.witness(f, *w, prove(body_at(f, *w)));
            break;
        default: break;
    }
    std::string at_hand;
    if (getenv("SYSPROVE_FULL"))
        for (H h : facts_) at_hand += "\n  " + print(t_.p.fm(h)).substr(0, 300);
    throw std::runtime_error("no proof from the steps at hand of " + print(f).substr(0, getenv("SYSPROVE_FULL") ? std::string::npos : 300) + at_hand);
}

std::optional<H> Facts::contradiction() {
    for (size_t i = 0; i < facts_.size(); ++i) {
        H h = facts_[i];
        const FmP& f = t_.p.fm(h);
        if (f->k == Fm::Not && provable(f->a)) return t_.p.not_elim(h, prove(f->a));
    }
    return {};
}

}  // namespace sys2fol::prove
