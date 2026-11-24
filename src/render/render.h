#pragma once

#include <string>
#include <vector>

#include "src/lang/core.h"
#include "src/render/fol_read.h"

namespace sys2fol::render {

// The spec as its checked claims say it. A claim holds definitions only expanded, so types, aliases, externs and
// structures print from the source and serve as the vocabulary; every instance and theorem prints from the claims. The
// claims must be exactly the spec's: each instance well formed and each of its sets existing, then each theorem.
std::string render(Program& p, const Source& spec, const std::vector<Decl>& forms, const std::vector<FolClaim>& claims,
                   const std::string& claims_file);

// The first difference between two texts in the language, token by token; empty when they agree.
std::string difference(const std::string& source, const std::string& printed);

}  // namespace sys2fol::render
