#pragma once

#include <map>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

#include "src/lang/core.h"
#include "src/prove/lemmas.h"

namespace sys2fol::prove {

using Claims = std::vector<std::pair<std::string, FmP>>;

// Claims with no proof, and the proofs of the others.
struct Unproved : std::runtime_error {
    std::string proofs;
    std::vector<std::string> names;
    Unproved(const std::string& what, std::string done, std::vector<std::string> missing)
        : std::runtime_error(what), proofs(std::move(done)), names(std::move(missing)) {}
};

// The class machine requests a spec's proofs need, by purpose: each set a proof separates from a set it has.
std::map<std::string, std::string> requests(const Program& p, const Claims& claims, const std::string& ns);

// Proofs of every claim, in order. `sets` names the class machine's claim for each purpose. A finite system's claims
// are proved by cases over the values of its records' entries; a theorem `reachable(m) ⊆ { s in m.State | φ }` by
// the invariance rule, with { s in m.State | φ } its own invariant.
std::string prove_claims(const Program& p, const Claims& claims, std::map<std::string, FmP>& known, Lemmas& lm,
                         const std::map<std::string, std::string>& sets, const std::string& ns);

}  // namespace sys2fol::prove
