#pragma once

#include <cstdint>
#include <map>
#include <memory>
#include <set>
#include <string>
#include <vector>

#include "src/lang/syntax.h"

namespace sys2fol {

struct VarId {
    uint32_t v = 0;
    auto operator<=>(const VarId&) const = default;
};
struct NameId {
    uint32_t v = 0;
    auto operator<=>(const NameId&) const = default;
};
struct FieldId {
    uint32_t v = 0;
    auto operator<=>(const FieldId&) const = default;
};

// The core: terms (sort term) and formulas (sort formula) after names are resolved.
enum class K : uint8_t {
    Var, Num, Inst, Comp, Field, RecordType, Tuple, Range, SetOf, SetType,
    True, Not, And, Or, Implies, Eq, In, Subset, Pred, All, Some,
    Use,  // an alias applied to its arguments, before expansion
    // Sequences, index tuples (decision 12): their set, a literal, and the operations on them.
    SeqType, SeqLit, Length, First, Rest, Append,
    Lt, Le,         // on natural numbers; num 1 when written reversed (>, >=)
    Case,           // a case of an enum whose cases carry fields, applied to its fields
    EnumType,       // such an enum's set: kids its cases' records of fields, cases their names
    PredType,       // a set given by a library predicate, as nat by Sys.natural
};

bool is_formula(K k);

struct Node;
using NodeP = std::shared_ptr<const Node>;

struct Node {
    K k;
    Pos pos;
    VarId var;                   // Var; the binder of SetOf, All, Some
    NameId name;                 // Inst, Comp: the instance; Pred: the extern; Use: the alias
    FieldId field;               // Comp, Field
    uint64_t num = 0;            // Num
    std::vector<NodeP> kids;     // operands; RecordType: the parts' types
    std::vector<FieldId> parts;  // RecordType
    std::vector<NameId> cases;   // EnumType
};

struct VarInfo {
    std::string hint;
    NodeP bound;                 // the set the variable ranges over, if known
    NameId structure;            // a parameter that is an instance of this structure
    bool of_structure = false;
};

struct FieldInfo {
    std::string label;
    uint32_t index = 0;          // position among its structure's fields, or its record's parts
    NodeP type;
};

struct RuleDef {
    Pos pos;
    std::vector<VarId> binders;  // the pattern's variables, each over its field's type
    NodeP when;                  // the pattern and the guard
    std::vector<NodeP> next;     // per state part
    std::vector<NodeP> out;      // per output part
    std::vector<std::pair<bool, size_t>> said;  // the description's equations as written: (an output?, its part)
};

struct ComponentDef {
    enum Kind { Parts, Condition, Rules };
    Kind kind = Parts;
    NodeP set;                   // Parts: a RecordType; Condition: a SetOf
    FieldId state, input, output;  // Rules: the fields the step's tuple names
    VarId s, a, b, t;
    std::vector<RuleDef> rules;
};

struct NameInfo {
    enum Kind { Extern, ExternType, Alias, Structure, Instance, Constructor };
    Kind kind;
    std::string text;
    Pos pos;
    std::vector<VarId> params;   // Alias, Extern, Instance
    NodeP body;                  // Alias; Constructor: the record of its fields
    std::string fol;             // Extern, ExternType
    uint32_t index = 0;          // Constructor: its case's number
    NameId enum_of;              // an enum case: the enum
    bool is_case = false;
    std::vector<FieldId> fields;                               // Structure
    std::vector<std::pair<std::string, NodeP>> conditions;     // Structure: over Comp(structure, field)
    NameId structure;                                          // Instance
    std::map<FieldId, ComponentDef> components;                // Instance
};

struct Theorem {
    std::string name;
    Pos pos;
    NodeP claim;
    std::vector<VarId> params;
};

class Program {
public:
    std::vector<NameInfo> names;
    std::vector<FieldInfo> fields;
    std::vector<VarInfo> vars;
    std::vector<Theorem> theorems;
    std::vector<NameId> instances;

    void load(const Source& source);

    // The β-normal form: every alias replaced by its body, its holes filled. Each replacement is appended to `steps`.
    NodeP expand(const NodeP& n, std::vector<std::string>* steps = nullptr);
    // An instance's well-formedness: its structure's conditions, at the instance's components.
    NodeP wellformedness(NameId instance);

    // `bare` holds variables whose fields print as their labels alone, as a rule or a condition writes them; the fields
    // of `own`, a structure, print bare too, as its declaration writes them.
    std::string show(const NodeP& n, const std::set<VarId>* bare = nullptr, const NameId* own = nullptr) const;
    const NameInfo& name(NameId id) const { return names[id.v]; }
    const FieldInfo& field(FieldId id) const { return fields[id.v]; }
    VarId new_var(const std::string& hint, NodeP bound);
    FieldId new_field(const std::string& label, uint32_t index, NodeP type);

private:
    std::map<std::string, NameId> globals_;
    std::string file_;

    struct Scope;
    NodeP resolve(const Expr& e, const Scope* scope);
    NodeP enum_type(const Expr& e, const Scope* scope);
    NodeP pattern(const Expr& e, Scope& scope, std::vector<VarId>& binders);
    std::vector<VarId> parameters(const std::vector<Param>& ps, Scope& scope);
    NodeP resolve_field(const NodeP& base, const std::string& label, Pos pos) const;
    const ComponentDef* component(const NodeP& set) const;
    NameId declare(NameInfo info);
    NodeP subst(const NodeP& n, std::map<VarId, NodeP>& map);
    void instance(const Decl& d);
    ComponentDef rules(NameId inst, const NameInfo& structure, const FieldContent& c, const NodeP& tuple, const Scope* outer);
};

}  // namespace sys2fol
