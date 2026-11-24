#pragma once

#include <map>
#include <utility>
#include <vector>

#include "src/lang/core.h"
#include "src/render/fol_read.h"

namespace sys2fol::render {

using CompRef = std::pair<NameId, FieldId>;

// Reads the claims sysc writes back into the core, every alias expanded. It inverts the writer's encoding pattern by
// pattern and reads nothing else, so what it returns is what the claim says. An instance's components are read into
// `p`; `hints` is the source's own reading, consulted only for the labels of record parts.
class Decompiler {
public:
    Decompiler(Program& p, const Program& hints);

    // The leading components `comps` of a claim, each read through its characterization (or checked against the
    // reading of it an earlier claim gave); returns the rest of the claim.
    FP components(const FP& f, const std::vector<CompRef>& comps);
    // `forall q. (q in c <-> ...)`, the set `comp` bound at depth `c`.
    void characterization(const FP& f, CompRef comp, int c);
    // `exists c. (set(c) & forall q. (q in c <-> ...))`: some set is `comp`.
    void existence(const FP& f, CompRef comp);
    // The leading parameters of a claim, as `hints` names them: each a fresh variable over the type the claim gives it.
    FP params(const FP& f, const std::vector<VarId>& hints, std::vector<VarId>& out, const std::vector<VarId>* reuse);
    NodeP formula(const FP& f);

    std::map<int, NodeP> env;   // a fol variable, by depth, to the core term it stands for

private:
    Program& p_;
    const Program& hints_;
    std::map<std::string, NameId> externs_, types_;

    NodeP term(int v, const FP& where) const;
    NodeP predicate(const FP& f);
    NodeP member(const FP& f, int x, bool record);
    NodeP record_type(const FP& f, int x);
    NodeP sequence_type(const FP& f, int x);
    NodeP enum_type(const FP& f, int x);
    bool sequence(const NodeP& t) const;
    NodeP record_membership(const FP& f);
    NodeP bind(K k, int x, const NodeP& bound, const FP& body);
    FieldId part(const NodeP& t, uint32_t i, const FP& where) const;
    const std::vector<FieldId>* parts_of(const NodeP& set) const;
    ComponentDef rules(const FP& m, int q, NameId inst, FieldId f);
    std::vector<NodeP> values(const FP& f, int r, size_t n);
    NodeP labelled(const NodeP& rec, CompRef comp);
};

// Equal up to the names of bound variables; records compare by their parts' types.
bool same(const NodeP& a, const NodeP& b, std::map<VarId, VarId>& bound);
bool same(const NodeP& a, const NodeP& b);
bool same(const ComponentDef& a, const ComponentDef& b);

// Which notation writes `f` of `inst`, from its structure's type for the field.
ComponentDef::Kind kind_of(const Program& p, NameId inst, FieldId f, FieldId* of = nullptr, FieldId roles[3] = nullptr);

NodeP comp_node(NameId inst, FieldId f);

}  // namespace sys2fol::render
