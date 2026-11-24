#pragma once

#include <memory>
#include <string>
#include <vector>

namespace sys2fol::render {

// A fol-zfc formula as the checker parsed it. A variable is the depth of the quantifier that binds it.
struct F;
using FP = std::shared_ptr<const F>;

struct F {
    enum Kind { Atom, False, Not, And, Or, Implies, Iff, All, Ex };
    Kind kind;
    std::string pred;        // Atom
    std::vector<int> args;   // Atom
    std::vector<FP> kids;    // a connective's operands; a quantifier's body
    int var = -1;            // All, Ex
};

struct FolClaim {
    std::string name;
    FP formula;
};

// The claims of a fol-zfc header, in order, read by fol-zfc's own parser.
std::vector<FolClaim> read_claims(const std::string& text);

std::string show(const FP& f);

}  // namespace sys2fol::render
