#pragma once

#include <cstdint>
#include <functional>
#include <map>
#include <string>
#include <vector>

#include "src/prove/proof.h"

namespace sys2fol::prove {

// The writer's encodings, as formulas: numbers named at a statement's top, and records over them.
namespace enc {
// Numerals z0, ..., zk, z0 being 0 and each the successor of the one before, around `inner`.
FmP chain(size_t k, const std::function<FmP(const std::vector<std::string>&)>& inner);
// r is the tuple of xs: tuple(r, z_k) and pmem(z_i, x_i, r), at the numbers z.
FmP rec(const std::string& r, const std::vector<std::string>& xs, const std::vector<std::string>& z);
}  // namespace enc

// Common shapes of steps over a Proof. Every variable a tactic introduces is a set, and its set(x) step is kept.
class Tac {
public:
    explicit Tac(Proof& p) : p(p) {}
    Proof& p;
    std::map<std::string, H> set_of;

    // forall_elim at each term, discharging the set guards that follow.
    H inst(H h, const std::vector<std::string>& ts);
    H guards(H h);
    H mp(H h, const std::vector<H>& ants);
    // (forall x. (set(x) -> body(x))), x fresh.
    H all(const std::string& hint, const std::function<H(const std::string&)>& body);
    H assume(FmP a, const std::function<H(H)>& body);
    // (~ a), from a to false.
    H refute(FmP a, const std::function<H(H)>& to_false);
    // From (exists x. (set(x) & phi)): k(x, phi) gives the conclusion, which must not mention x.
    H obtain(H ex, const std::string& hint, const std::function<H(const std::string&, H)>& k);
    // The conclusion from a | b, each side proving it.
    H cases(H o, const std::function<H(H)>& left, const std::function<H(H)>& right);
    // The same over a right-nested disjunction of n.
    H cases(H o, size_t n, const std::function<H(size_t, H)>& each);
    // (exists x. (set(x) & phi)) from phi at t.
    H witness(H phi_at_t, const std::string& t);
    // `target`, (exists x. (set(x) & phi(x))), from phi(t): exactly phi's positions of x become t.
    H witness(FmP target, const std::string& t, H phi_at_t);
    std::vector<H> split(H h, size_t n);
    H join(const std::vector<H>& hs);
    H contradiction(H negation, H a) { return p.not_elim(negation, a); }
};

}  // namespace sys2fol::prove
