#include "src/prove/tactics.h"

#include <stdexcept>

namespace sys2fol::prove {

namespace enc {

FmP chain(size_t k, const std::function<FmP(const std::vector<std::string>&)>& inner) {
    std::vector<std::string> zs;
    for (size_t i = 0; i <= k; ++i) zs.push_back(fresh("_n"));
    FmP body = inner(zs);
    for (size_t i = k + 1; i-- > 0;) {
        FmP guard = i == 0 ? atom("zero", {zs[0]}) : atom("nsucc", {zs[i - 1], zs[i]});
        body = all(zs[i], imp(guard, body));
    }
    return body;
}

FmP rec(const std::string& r, const std::vector<std::string>& xs, const std::vector<std::string>& z) {
    if (xs.empty()) return atom("zero", {r});
    std::vector<FmP> parts{atom("tuple", {r, z.at(xs.size())})};
    for (size_t i = 0; i < xs.size(); ++i) parts.push_back(atom("pmem", {z[i], xs[i], r}));
    return conj(parts);
}

}  // namespace enc

H Tac::inst(H h, const std::vector<std::string>& ts) {
    for (const std::string& t : ts) h = guards(p.forall_elim(h, t));
    return h;
}

H Tac::guards(H h) {
    while (true) {
        const FmP& f = p.fm(h);
        if (f->k != Fm::Imp || f->a->k != Fm::Atom || f->a->name != "set" || f->a->args.size() != 1) return h;
        auto it = set_of.find(f->a->args[0]);
        if (it == set_of.end()) return h;
        h = p.implies_elim(h, it->second);
    }
}

H Tac::mp(H h, const std::vector<H>& ants) {
    for (H a : ants) h = p.implies_elim(h, a);
    return h;
}

H Tac::all(const std::string& hint, const std::function<H(const std::string&)>& body) {
    std::string x = fresh(hint);
    p.fix(x);
    set_of[x] = p.assume(is_set(x));
    H b = body(x);
    H i = p.implies_intro(b);
    set_of.erase(x);
    return p.forall_intro(i);
}

H Tac::assume(FmP a, const std::function<H(H)>& body) {
    H h = p.assume(std::move(a));
    return p.implies_intro(body(h));
}

H Tac::refute(FmP a, const std::function<H(H)>& to_false) {
    H h = p.assume(std::move(a));
    return p.not_intro(to_false(h));
}

H Tac::obtain(H ex, const std::string& hint, const std::function<H(const std::string&, H)>& k) {
    auto [w, body] = p.exists_elim(ex, hint);
    const FmP& f = p.fm(body);
    if (f->k != Fm::And || f->a->k != Fm::Atom || f->a->name != "set") throw std::runtime_error("obtain of an unguarded exists");
    set_of[w] = p.and_l(body);
    H c = k(w, p.and_r(body));
    set_of.erase(w);
    return p.exists_close(c);
}

H Tac::cases(H o, const std::function<H(H)>& left, const std::function<H(H)>& right) {
    const FmP& f = p.fm(o);
    if (f->k != Fm::Or) throw std::runtime_error("cases of a step that is no disjunction");
    FmP a = f->a, b = f->b;
    H l = assume(a, left);
    H r = assume(b, right);
    return p.or_elim(o, l, r);
}

H Tac::cases(H o, size_t n, const std::function<H(size_t, H)>& each) {
    std::function<H(H, size_t)> go = [&](H d, size_t i) -> H {
        if (i + 1 == n) return each(i, d);
        return cases(d, [&](H l) { return each(i, l); }, [&](H r) { return go(r, i + 1); });
    };
    if (n == 0) throw std::runtime_error("cases of an empty disjunction");
    return go(o, 0);
}

H Tac::witness(H phi, const std::string& t) {
    auto it = set_of.find(t);
    if (it == set_of.end()) throw std::runtime_error("no step says " + t + " is a set");
    return p.exists_intro(p.and_intro(it->second, phi), t);
}

H Tac::witness(FmP target, const std::string& t, H phi) {
    auto it = set_of.find(t);
    if (it == set_of.end()) throw std::runtime_error("no step says " + t + " is a set");
    return p.ex_intro(std::move(target), t, p.and_intro(it->second, phi));
}

std::vector<H> Tac::split(H h, size_t n) {
    std::vector<H> out;
    for (size_t i = 0; i + 1 < n; ++i) {
        out.push_back(p.and_l(h));
        h = p.and_r(h);
    }
    out.push_back(h);
    return out;
}

H Tac::join(const std::vector<H>& hs) {
    H h = hs.back();
    for (size_t i = hs.size() - 1; i-- > 0;) h = p.and_intro(hs[i], h);
    return h;
}

}  // namespace sys2fol::prove
