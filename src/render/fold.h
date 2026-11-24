#pragma once

#include <map>
#include <utility>
#include <vector>

#include "src/lang/core.h"

namespace sys2fol::render {

// Writes a claim's reading back with the spec's aliases. Every fold is checked: an alias replaces a term only when the
// alias's plain body, its holes filled, is the term. Where several aliases fit, the source's choice is taken as a hint.
class Folder {
public:
    Folder(Program& p, Program& hints);

    // An instance's record parts: each part's set written as the source writes it when that is the same set.
    void parts(NameId inst);
    // An instance's conditions and rules.
    void instance(NameId inst);
    NodeP fold(const NodeP& n);
    // Bound variables named as the source names them, in order, when the two have the same binders.
    void name_binders(const NodeP& reading, const NodeP& source);
    // A comparison written reversed in the source (a >= b for b <= a) is printed so, being the same formula.
    NodeP respell(const NodeP& reading, const NodeP& source, std::map<VarId, VarId> bound);
    // The source's variables that stand for the reading's: an instance's parameters, read from its claims.
    std::map<VarId, VarId> source_vars;

private:
    Program& p_;
    Program& hints_;
    std::vector<std::pair<NameId, NodeP>> defined_;   // aliases with holes, and their plain bodies

    NodeP value(const NodeP& v, const NodeP& type);
    NodeP type_of(const NodeP& t) const;
    bool natural(const NodeP& t) const;
    bool alike(const NodeP& r, const NodeP& s, const std::map<VarId, VarId>& bound) const;
    NodeP fold_set(const NodeP& set, const NodeP& hint);
};

}  // namespace sys2fol::render
