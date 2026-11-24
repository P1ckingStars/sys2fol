#pragma once

#include <string>
#include <vector>

#include "src/lang/core.h"

namespace sys2fol {

struct Claim {
    std::string name;
    std::string plain;     // the expanded claim, in the language
    std::string formula;   // the claim in fol-zfc
};

// Each instance's well-formedness and the existence of its sets, then each theorem; `steps` gets every β step.
std::vector<Claim> claims(Program& p, const std::string& ns, std::vector<std::string>* steps);

std::string header(const std::vector<Claim>& claims, const std::string& source);

}  // namespace sys2fol
