#include "src/lang/core.h"

#include <functional>
#include <set>

namespace sys2fol {

bool is_formula(K k) {
    switch (k) {
        case K::True: case K::Not: case K::And: case K::Or: case K::Implies: case K::Eq: case K::In:
        case K::Subset: case K::Pred: case K::All: case K::Some: case K::Lt: case K::Le: return true;
        default: return false;
    }
}

struct Program::Scope {
    const Scope* parent = nullptr;
    std::map<std::string, NodeP> names;
    const NodeP* lookup(const std::string& s) const {
        for (const Scope* p = this; p; p = p->parent) {
            auto it = p->names.find(s);
            if (it != p->names.end()) return &it->second;
        }
        return nullptr;
    }
};

namespace {

std::shared_ptr<Node> make(K k, Pos pos, std::vector<NodeP> kids = {}) {
    auto n = std::make_shared<Node>();
    n->k = k;
    n->pos = pos;
    n->kids = std::move(kids);
    return n;
}

NodeP var_node(VarId v, Pos pos) {
    auto n = make(K::Var, pos);
    n->var = v;
    return n;
}

NodeP with_kids(const NodeP& n, std::vector<NodeP> kids) {
    auto c = std::make_shared<Node>(*n);
    c->kids = std::move(kids);
    return c;
}

NodeP comp_node(NameId inst, FieldId f, Pos pos) {
    auto n = make(K::Comp, pos);
    n->name = inst;
    n->field = f;
    return n;
}

}  // namespace

VarId Program::new_var(const std::string& hint, NodeP bound) {
    vars.push_back(VarInfo{hint, std::move(bound), {}, false});
    return VarId{static_cast<uint32_t>(vars.size() - 1)};
}

FieldId Program::new_field(const std::string& label, uint32_t index, NodeP type) {
    fields.push_back(FieldInfo{label, index, std::move(type)});
    return FieldId{static_cast<uint32_t>(fields.size() - 1)};
}

NameId Program::declare(NameInfo info) {
    if (globals_.count(info.text)) throw Error(info.pos, "'" + info.text + "' is declared twice");
    NameId id{static_cast<uint32_t>(names.size())};
    globals_[info.text] = id;
    names.push_back(std::move(info));
    return id;
}

const ComponentDef* Program::component(const NodeP& set) const {
    if (!set || set->k != K::Comp) return nullptr;
    const auto& cs = names[set->name.v].components;
    auto it = cs.find(set->field);
    return it == cs.end() ? nullptr : &it->second;
}

NodeP Program::resolve_field(const NodeP& base, const std::string& label, Pos pos) const {
    auto field_of = [&](const std::vector<FieldId>& fs) -> const FieldId* {
        for (const FieldId& f : fs)
            if (fields[f.v].label == label) return &f;
        return nullptr;
    };
    if (base->k == K::Inst) {
        const NameInfo& s = names[names[base->name.v].structure.v];
        if (const FieldId* f = field_of(s.fields)) return comp_node(base->name, *f, pos);
        throw Error(pos, "a " + s.text + " has no field '" + label + "'");
    }
    if (base->k == K::Var) {
        const VarInfo& v = vars[base->var.v];
        const FieldId* f = nullptr;
        if (v.of_structure) {
            f = field_of(names[v.structure.v].fields);
        } else if (const ComponentDef* c = component(v.bound); c && c->kind == ComponentDef::Parts) {
            f = field_of(c->set->parts);
        }
        if (f) {
            auto n = make(K::Field, pos, {base});
            n->field = *f;
            return n;
        }
    }
    throw Error(pos, "'" + label + "' is not a field of " + show(base));
}

NodeP Program::resolve(const Expr& e, const Scope* sc) {
    auto global = [&](const std::string& s) -> NameId {
        auto it = globals_.find(s);
        if (it == globals_.end()) throw Error(e.pos, "'" + s + "' is not declared");
        return it->second;
    };
    switch (e.kind) {
        case Expr::Number: {
            auto n = make(K::Num, e.pos);
            n->num = std::stoull(e.text);
            return n;
        }
        case Expr::Paren: {
            if (e.args.size() == 1) return resolve(*e.args[0], sc);
            std::vector<NodeP> items;
            for (const ExprP& a : e.args) items.push_back(resolve(*a, sc));
            return make(K::Tuple, e.pos, std::move(items));
        }
        case Expr::Name: {
            if (const NodeP* local = sc ? sc->lookup(e.text) : nullptr) return *local;
            NameId id = global(e.text);
            const NameInfo& info = names[id.v];
            if (info.kind == NameInfo::Instance) {
                if (!info.params.empty()) throw Error(e.pos, "'" + e.text + "' needs its arguments");
                auto n = make(K::Inst, e.pos);
                n->name = id;
                return n;
            }
            if (info.kind == NameInfo::ExternType) {
                auto n = make(K::PredType, e.pos);
                n->name = id;
                return n;
            }
            if (info.kind == NameInfo::Constructor) {
                if (!info.body->kids.empty()) throw Error(e.pos, "'" + e.text + "' needs its fields");
                auto n = make(K::Case, e.pos);
                n->name = id;
                return n;
            }
            if (info.kind == NameInfo::Alias && info.params.empty()) {
                auto n = make(K::Use, e.pos);
                n->name = id;
                return n;
            }
            throw Error(e.pos, "'" + e.text + "' needs its arguments");
        }
        case Expr::Call: {
            const Expr& f = *e.args[0];
            if (f.kind != Expr::Name) throw Error(e.pos, "only a declared name can be applied");
            static const std::map<std::string, K> builtin = {{"length", K::Length}, {"first", K::First}, {"rest", K::Rest}};
            if (!globals_.count(f.text) && builtin.count(f.text)) {
                if (e.args.size() != 2) throw Error(e.pos, "'" + f.text + "' takes one sequence");
                return make(builtin.at(f.text), e.pos, {resolve(*e.args[1], sc)});
            }
            NameId id = global(f.text);
            if (names[id.v].kind == NameInfo::Instance || names[id.v].kind == NameInfo::Constructor) {
                const NameInfo& info = names[id.v];
                size_t want = info.kind == NameInfo::Instance ? info.params.size() : info.body->kids.size();
                if (e.args.size() - 1 != want) throw Error(e.pos, "'" + f.text + "' takes " + std::to_string(want) + " arguments");
                std::vector<NodeP> args;
                for (size_t k = 1; k < e.args.size(); ++k) args.push_back(resolve(*e.args[k], sc));
                auto n = make(info.kind == NameInfo::Instance ? K::Inst : K::Case, e.pos, std::move(args));
                n->name = id;
                return n;
            }
            const NameInfo& info = names[id.v];
            if (info.kind != NameInfo::Alias && info.kind != NameInfo::Extern)
                throw Error(e.pos, "'" + f.text + "' cannot be applied");
            if (e.args.size() - 1 != info.params.size())
                throw Error(e.pos, "'" + f.text + "' takes " + std::to_string(info.params.size()) + " arguments");
            std::vector<NodeP> args;
            for (size_t k = 1; k < e.args.size(); ++k) args.push_back(resolve(*e.args[k], sc));
            auto n = make(info.kind == NameInfo::Extern ? K::Pred : K::Use, e.pos, std::move(args));
            n->name = id;
            return n;
        }
        case Expr::Field: return resolve_field(resolve(*e.args[0], sc), e.text, e.pos);
        case Expr::Next: throw Error(e.pos, "'next' belongs in a rule's description");
        case Expr::Unary: {
            NodeP x = resolve(*e.args[0], sc);
            if (e.text == "not") return make(K::Not, e.pos, {x});
            if (e.text == "sequence of") return make(K::SeqType, e.pos, {x});
            return make(K::SetType, e.pos, {x});
        }
        case Expr::SeqLit: {
            std::vector<NodeP> items;
            for (const ExprP& a : e.args) items.push_back(resolve(*a, sc));
            return make(K::SeqLit, e.pos, std::move(items));
        }
        case Expr::Enum: return enum_type(e, sc);
        case Expr::Case: throw Error(e.pos, "a case belongs in an enum");
        case Expr::Binary: {
            NodeP l = resolve(*e.args[0], sc), r = resolve(*e.args[1], sc);
            const std::string& op = e.text;
            if (op == "and") return make(K::And, e.pos, {l, r});
            if (op == "or") return make(K::Or, e.pos, {l, r});
            if (op == "implies") return make(K::Implies, e.pos, {l, r});
            if (op == "=") return make(K::Eq, e.pos, {l, r});
            if (op == "!=") return make(K::Not, e.pos, {make(K::Eq, e.pos, {l, r})});
            if (op == "in") return make(K::In, e.pos, {l, r});
            if (op == "subset") return make(K::Subset, e.pos, {l, r});
            if (op == "<" || op == "<=" || op == ">" || op == ">=") {
                auto n = make(op[0] == '<' ? (op.size() == 1 ? K::Lt : K::Le) : (op.size() == 1 ? K::Lt : K::Le), e.pos, {l, r});
                n->num = op[0] == '>';
                return n;
            }
            if (op == "++") {
                if (r->k != K::SeqLit || r->kids.size() != 1) throw Error(e.pos, "only q ++ [x] is supported yet");
                return make(K::Append, e.pos, {l, r->kids[0]});
            }
            throw Error(e.pos, "'" + op + "' is not supported yet");
        }
        case Expr::Range: return make(K::Range, e.pos, {resolve(*e.args[0], sc), resolve(*e.args[1], sc)});
        case Expr::SetOf:
        case Expr::Quant: {
            NodeP bound = resolve(*e.args[0], sc);
            VarId v = new_var(e.var, bound);
            Scope inner{sc, {}};
            inner.names[e.var] = var_node(v, e.pos);
            NodeP body = resolve(*e.args[1], &inner);
            K k = e.kind == Expr::SetOf ? K::SetOf : (e.text == "all" ? K::All : K::Some);
            auto n = make(k, e.pos, {bound, body});
            n->var = v;
            return n;
        }
    }
    throw Error(e.pos, "this expression is not supported yet");
}

void Program::load(const Source& source) {
    file_ = source.path;
    for (const Decl& d : source.decls) {
        switch (d.kind) {
            case Decl::Use:
            case Decl::FormAlias: break;
            case Decl::ExternType: {
                NameInfo info{NameInfo::ExternType, d.name, d.pos};
                info.fol = d.fol_name;
                declare(std::move(info));
                break;
            }
            case Decl::Extern:
            case Decl::TypeAlias:
            case Decl::Define: {
                NameInfo info{d.kind == Decl::Extern ? NameInfo::Extern : NameInfo::Alias, d.name, d.pos};
                Scope sc;
                for (const Param& p : d.params) {
                    VarId v = new_var(p.name, nullptr);
                    if (p.type && p.type->kind == Expr::Name && globals_.count(p.type->text) &&
                        names[globals_[p.type->text].v].kind == NameInfo::Structure) {
                        vars[v.v].structure = globals_[p.type->text];
                        vars[v.v].of_structure = true;
                    } else if (p.type && !(p.type->kind == Expr::Name && p.type->text == "type")) {
                        vars[v.v].bound = resolve(*p.type, &sc);
                    }
                    sc.names[p.name] = var_node(v, p.pos);
                    info.params.push_back(v);
                }
                info.fol = d.fol_name;
                if (d.body) info.body = resolve(*d.body, &sc);
                declare(std::move(info));
                break;
            }
            case Decl::Enum: {
                auto count = make(K::Num, d.pos);
                count->num = d.cases.size();
                NodeP range = make(K::Range, d.pos, {make(K::Num, d.pos), count});
                NameId e = declare(NameInfo{NameInfo::Alias, d.name, d.pos, {}, range});
                for (size_t i = 0; i < d.cases.size(); ++i) {
                    auto value = make(K::Num, d.pos);
                    value->num = i;
                    NameInfo c{NameInfo::Alias, d.cases[i], d.pos, {}, value};
                    c.enum_of = e;
                    c.is_case = true;
                    declare(std::move(c));
                }
                break;
            }
            case Decl::Structure: {
                NameId sid = declare(NameInfo{NameInfo::Structure, d.name, d.pos});
                Scope sc;
                uint32_t index = 0;
                auto add = [&](const Param& p) {
                    NodeP type;
                    if (p.type && !(p.type->kind == Expr::Name && p.type->text == "type")) type = resolve(*p.type, &sc);
                    FieldId f = new_field(p.name, index++, type);
                    names[sid.v].fields.push_back(f);
                    sc.names[p.name] = comp_node(sid, f, p.pos);
                };
                for (const Param& p : d.params) add(p);
                for (const Param& p : d.fields) add(p);
                for (const auto& [name, cond] : d.conditions) names[sid.v].conditions.push_back({name, resolve(*cond, &sc)});
                break;
            }
            case Decl::Instance: instance(d); break;
            case Decl::Theorem: {
                Scope sc;
                std::vector<VarId> ps = parameters(d.params, sc);
                theorems.push_back(Theorem{d.name, d.pos, resolve(*d.body, &sc), ps});
                break;
            }
        }
    }
}

std::vector<VarId> Program::parameters(const std::vector<Param>& ps, Scope& sc) {
    std::vector<VarId> out;
    for (const Param& p : ps) {
        VarId v = new_var(p.name, nullptr);
        if (p.type && p.type->kind == Expr::Name && globals_.count(p.type->text) &&
            names[globals_[p.type->text].v].kind == NameInfo::Structure) {
            vars[v.v].structure = globals_[p.type->text];
            vars[v.v].of_structure = true;
        } else if (p.type && !(p.type->kind == Expr::Name && p.type->text == "type")) {
            vars[v.v].bound = resolve(*p.type, &sc);
        }
        sc.names[p.name] = var_node(v, p.pos);
        out.push_back(v);
    }
    return out;
}

// An enum whose cases carry fields: each case a constructor of a record of its fields.
NodeP Program::enum_type(const Expr& e, const Scope* sc) {
    auto n = make(K::EnumType, e.pos);
    for (size_t k = 0; k < e.args.size(); ++k) {
        const Expr& c = *e.args[k];
        auto rec = make(K::RecordType, c.pos);
        for (size_t i = 0; i < c.args.size(); ++i) {
            NodeP type = resolve(*c.args[i], sc);
            rec->parts.push_back(new_field(c.names[i], static_cast<uint32_t>(i), type));
            rec->kids.push_back(type);
        }
        NameInfo info{NameInfo::Constructor, c.text, c.pos};
        info.body = rec;
        info.index = static_cast<uint32_t>(k);
        NameId id = declare(std::move(info));
        n->cases.push_back(id);
        n->kids.push_back(rec);
    }
    return n;
}

// A rule's pattern on its port: a constructor's field named by an unknown name binds it, over the field's type.
NodeP Program::pattern(const Expr& e, Scope& sc, std::vector<VarId>& binders) {
    if (e.kind != Expr::Call || e.args[0]->kind != Expr::Name || !globals_.count(e.args[0]->text) ||
        names[globals_[e.args[0]->text].v].kind != NameInfo::Constructor)
        return resolve(e, &sc);
    NameId id = globals_[e.args[0]->text];
    const NodeP rec = names[id.v].body;
    if (e.args.size() - 1 != rec->kids.size()) throw Error(e.pos, "'" + e.args[0]->text + "' has " + std::to_string(rec->kids.size()) + " fields");
    std::vector<NodeP> kids;
    for (size_t k = 1; k < e.args.size(); ++k) {
        const Expr& a = *e.args[k];
        if (a.kind == Expr::Name && !sc.lookup(a.text) && !globals_.count(a.text)) {
            VarId v = new_var(a.text, rec->kids[k - 1]);
            sc.names[a.text] = var_node(v, a.pos);
            binders.push_back(v);
            kids.push_back(var_node(v, a.pos));
        } else {
            kids.push_back(resolve(a, &sc));
        }
    }
    auto n = make(K::Case, e.pos, std::move(kids));
    n->name = id;
    return n;
}

void Program::instance(const Decl& d) {
    auto sit = globals_.find(d.structure);
    if (sit == globals_.end() || names[sit->second.v].kind != NameInfo::Structure)
        throw Error(d.pos, "'" + d.structure + "' is not a structure");
    NameInfo info{NameInfo::Instance, d.name, d.pos};
    info.structure = sit->second;
    NameId inst = declare(std::move(info));
    Scope ps;
    std::vector<VarId> params = parameters(d.params, ps);
    names[inst.v].params = params;
    const NameInfo structure = names[sit->second.v];
    // A structure's own field in a field's type stands for the instance's.
    auto own = [&](const NodeP& t, FieldId& out) {
        if (!t || t->k != K::Comp || !(t->name == sit->second)) return false;
        out = t->field;
        return true;
    };
    for (const FieldId f : structure.fields) {
        const FieldInfo field = fields[f.v];
        auto it = d.contents.find(field.label);
        const FieldContent* c = it == d.contents.end() ? nullptr : &it->second;
        ComponentDef def;
        if (!field.type) {
            if (c && c->kind != FieldContent::Parts) throw Error(c->pos, field.label + " is a set, written as its parts");
            auto rec = make(K::RecordType, c ? c->pos : d.pos);
            if (c)
                for (size_t i = 0; i < c->parts.size(); ++i) {
                    NodeP type = resolve(*c->parts[i].type, &ps);
                    rec->parts.push_back(new_field(c->parts[i].name, static_cast<uint32_t>(i), type));
                    rec->kids.push_back(type);
                }
            def.kind = ComponentDef::Parts;
            def.set = rec;
        } else if (FieldId of; field.type->k == K::SetType && own(field.type->kids[0], of)) {
            if (!c || c->kind != FieldContent::Condition)
                throw Error(c ? c->pos : d.pos, field.label + " is a set of " + fields[of.v].label + ", written as a condition");
            NodeP bound = comp_node(inst, of, c->pos);
            VarId v = new_var("s", bound);
            Scope sc{&ps, {}};
            for (FieldId p : names[inst.v].components.at(of).set->parts) {
                auto acc = make(K::Field, c->pos, {var_node(v, c->pos)});
                acc->field = p;
                sc.names[fields[p.v].label] = acc;
            }
            auto set = make(K::SetOf, c->pos, {bound, resolve(*c->condition, &sc)});
            set->var = v;
            def.kind = ComponentDef::Condition;
            def.set = set;
        } else if (field.type->k == K::SetType && field.type->kids[0]->k == K::Tuple &&
                   field.type->kids[0]->kids.size() == 4) {
            if (!c || c->kind != FieldContent::Rules)
                throw Error(c ? c->pos : d.pos, field.label + " is a step relation, written as rules");
            def = rules(inst, structure, *c, field.type->kids[0], &ps);
        } else {
            throw Error(d.pos, "no notation writes a field of type " + show(field.type));
        }
        names[inst.v].components[f] = std::move(def);
    }
    for (const auto& [label, c] : d.contents) {
        bool known = false;
        for (FieldId f : structure.fields) known = known || fields[f.v].label == label;
        if (!known) throw Error(c.pos, "a " + structure.text + " has no field '" + label + "'");
    }
    instances.push_back(inst);
}

ComponentDef Program::rules(NameId inst, const NameInfo& structure, const FieldContent& c, const NodeP& tuple,
                            const Scope* outer) {
    ComponentDef def;
    def.kind = ComponentDef::Rules;
    FieldId roles[4];
    for (int i = 0; i < 4; ++i) {
        const NodeP& t = tuple->kids[i];
        if (t->k != K::Comp || !(t->name == globals_.at(structure.text)))
            throw Error(c.pos, "a step relation's tuple must name the structure's own sets");
        roles[i] = t->field;
    }
    if (!(roles[0] == roles[3])) throw Error(c.pos, "a step must start and end in the same set of states");
    def.state = roles[0];
    def.input = roles[1];
    def.output = roles[2];
    const auto& comps = names[inst.v].components;
    const std::vector<FieldId> state = comps.at(def.state).set->parts;
    const std::vector<FieldId> input = comps.at(def.input).set->parts;
    const std::vector<FieldId> output = comps.at(def.output).set->parts;
    def.s = new_var("s", comp_node(inst, def.state, c.pos));
    def.a = new_var("a", comp_node(inst, def.input, c.pos));
    def.b = new_var("b", comp_node(inst, def.output, c.pos));
    def.t = new_var("t", comp_node(inst, def.state, c.pos));
    auto access = [&](VarId v, FieldId p, Pos pos) {
        auto n = make(K::Field, pos, {var_node(v, pos)});
        n->field = p;
        return n;
    };
    auto index_of = [&](const std::vector<FieldId>& parts, const std::string& label) -> int {
        for (size_t i = 0; i < parts.size(); ++i)
            if (fields[parts[i].v].label == label) return static_cast<int>(i);
        return -1;
    };
    for (const Rule& r : c.rules) {
        Scope sc{outer, {}};
        for (FieldId p : state) sc.names[fields[p.v].label] = access(def.s, p, r.pos);
        for (FieldId p : input) sc.names[fields[p.v].label] = access(def.a, p, r.pos);
        RuleDef rd;
        rd.pos = r.pos;
        NodeP when = make(K::True, r.pos);
        if (r.value) {
            int i = r.port.empty() ? (input.size() == 1 ? 0 : -2) : index_of(input, r.port);
            if (i == -2) throw Error(r.pos, "a pattern without its port needs an input of one port");
            if (i < 0) throw Error(r.pos, "'" + r.port + "' is not an input");
            when = make(K::Eq, r.pos, {access(def.a, input[i], r.pos), pattern(*r.value, sc, rd.binders)});
        }
        if (r.guard) when = when->k == K::True ? resolve(*r.guard, &sc) : make(K::And, r.pos, {when, resolve(*r.guard, &sc)});
        rd.when = when;
        rd.next.resize(state.size());
        rd.out.resize(output.size());
        std::vector<const Expr*> eqs;
        std::vector<const Expr*> todo;
        if (r.description) todo.push_back(r.description.get());
        while (!todo.empty()) {
            const Expr* e = todo.back();
            todo.pop_back();
            while (e->kind == Expr::Paren && e->args.size() == 1) e = e->args[0].get();
            if (e->kind == Expr::Binary && e->text == "and") {
                todo.push_back(e->args[1].get());
                todo.push_back(e->args[0].get());
            } else if (e->kind == Expr::Binary && e->text == "=") {
                eqs.push_back(e);
            } else {
                throw Error(e->pos, "a rule's description is a conjunction of equations");
            }
        }
        for (const Expr* e : eqs) {
            const Expr& lhs = *e->args[0];
            NodeP rhs = resolve(*e->args[1], &sc);
            if (lhs.kind == Expr::Next) {
                int i = index_of(state, lhs.text);
                if (i < 0) throw Error(lhs.pos, "'" + lhs.text + "' is not part of the state");
                if (rd.next[i]) throw Error(lhs.pos, "next " + lhs.text + " is given twice");
                rd.next[i] = rhs;
                rd.said.push_back({false, static_cast<size_t>(i)});
            } else if (lhs.kind == Expr::Name && index_of(output, lhs.text) >= 0) {
                int i = index_of(output, lhs.text);
                if (rd.out[i]) throw Error(lhs.pos, lhs.text + " is given twice");
                rd.out[i] = rhs;
                rd.said.push_back({true, static_cast<size_t>(i)});
            } else {
                throw Error(lhs.pos, "an equation in a description sets 'next' of a state part, or an output");
            }
        }
        for (size_t i = 0; i < state.size(); ++i)
            if (!rd.next[i]) rd.next[i] = access(def.s, state[i], r.pos);
        for (size_t i = 0; i < output.size(); ++i)
            if (!rd.out[i]) throw Error(r.pos, "the rule gives no value to output " + fields[output[i].v].label);
        def.rules.push_back(std::move(rd));
    }
    return def;
}

NodeP Program::subst(const NodeP& n, std::map<VarId, NodeP>& map) {
    if (n->k == K::Var) {
        auto it = map.find(n->var);
        return it == map.end() ? n : it->second;
    }
    std::vector<NodeP> kids;
    if (n->k == K::SetOf || n->k == K::All || n->k == K::Some) {
        NodeP bound = subst(n->kids[0], map);
        VarId fresh = new_var(vars[n->var.v].hint, bound);
        NodeP saved;
        if (auto it = map.find(n->var); it != map.end()) saved = it->second;
        map[n->var] = var_node(fresh, n->pos);
        NodeP body = subst(n->kids[1], map);
        if (saved) map[n->var] = saved; else map.erase(n->var);
        auto c = std::make_shared<Node>(*n);
        c->var = fresh;
        c->kids = {bound, body};
        return c;
    }
    for (const NodeP& k : n->kids) kids.push_back(subst(k, map));
    return with_kids(n, std::move(kids));
}

NodeP Program::expand(const NodeP& n, std::vector<std::string>* steps) {
    if (n->k == K::Use) {
        const NameInfo& a = names[n->name.v];
        std::map<VarId, NodeP> map;
        for (size_t i = 0; i < a.params.size(); ++i) map[a.params[i]] = n->kids[i];
        NodeP body = subst(a.body, map);
        if (steps) steps->push_back(show(n) + "  \xe2\x86\x92\xce\xb2  " + show(body));
        return expand(body, steps);
    }
    std::vector<NodeP> kids;
    for (const NodeP& k : n->kids) kids.push_back(expand(k, steps));
    if (n->k == K::Field && kids[0]->k == K::Inst) return comp_node(kids[0]->name, n->field, n->pos);
    return with_kids(n, std::move(kids));
}

NodeP Program::wellformedness(NameId inst) {
    const NameInfo& s = names[names[inst.v].structure.v];
    NameId sid = names[inst.v].structure;
    std::function<NodeP(const NodeP&)> at = [&](const NodeP& n) -> NodeP {
        if (n->k == K::Comp && n->name == sid) return comp_node(inst, n->field, n->pos);
        std::vector<NodeP> kids;
        for (const NodeP& k : n->kids) kids.push_back(at(k));
        return with_kids(n, std::move(kids));
    };
    NodeP all;
    for (const auto& cond : s.conditions) {
        NodeP c = at(cond.second);
        all = all ? make(K::And, c->pos, {all, c}) : c;
    }
    return all ? all : make(K::True, names[inst.v].pos);
}

std::string Program::show(const NodeP& root, const std::set<VarId>* bare, const NameId* own) const {
    std::map<VarId, std::string> label;
    std::set<std::string> used;
    auto name_of = [&](VarId v) {
        auto it = label.find(v);
        if (it != label.end()) return it->second;
        std::string base = vars[v.v].hint, s = base;
        for (int k = 1; used.count(s); ++k) s = base + std::to_string(k);
        used.insert(s);
        return label[v] = s;
    };
    auto prec = [](K k) {
        switch (k) {
            case K::All: case K::Some: return 0;
            case K::Implies: return 1;
            case K::Or: return 2;
            case K::And: return 3;
            case K::Not: return 4;
            default: return 5;
        }
    };
    // An instance with parameters, applied to them.
    auto applied = [&](NameId i) {
        const std::vector<VarId>& ps = names[i.v].params;
        if (names[i.v].kind != NameInfo::Instance || ps.empty()) return std::string();
        std::string s = "(";
        for (size_t k = 0; k < ps.size(); ++k) s += (k ? ", " : "") + vars[ps[k].v].hint;
        return s + ")";
    };
    std::function<std::string(const NodeP&, int)> go = [&](const NodeP& n, int ctx) -> std::string {
        auto list = [&](size_t from) {
            std::string s;
            for (size_t i = from; i < n->kids.size(); ++i) s += (i > from ? ", " : "") + go(n->kids[i], 0);
            return s;
        };
        std::string s;
        switch (n->k) {
            case K::Var: return name_of(n->var);
            case K::Num: return std::to_string(n->num);
            case K::Inst: return names[n->name.v].text + (n->kids.empty() ? applied(n->name) : "(" + list(0) + ")");
            case K::Comp:
                if (own && n->name == *own) return fields[n->field.v].label;
                return names[n->name.v].text + applied(n->name) + "." + fields[n->field.v].label;
            case K::Field:
                if (bare && n->kids[0]->k == K::Var && bare->count(n->kids[0]->var)) return fields[n->field.v].label;
                return go(n->kids[0], 5) + "." + fields[n->field.v].label;
            case K::RecordType:
                s = "(";
                for (size_t i = 0; i < n->parts.size(); ++i)
                    s += (i ? ", " : "") + fields[n->parts[i].v].label + ": " + go(n->kids[i], 0);
                return s + ")";
            case K::Tuple: return "(" + list(0) + ")";
            case K::Range: return go(n->kids[0], 5) + " ..< " + go(n->kids[1], 5);
            case K::SetType: return "set of " + go(n->kids[0], 5);
            case K::SeqType: return "sequence of " + go(n->kids[0], 5);
            case K::SeqLit: return "[" + list(0) + "]";
            case K::Length: return "length(" + list(0) + ")";
            case K::First: return "first(" + list(0) + ")";
            case K::Rest: return "rest(" + list(0) + ")";
            case K::Append: return go(n->kids[0], 5) + " ++ [" + go(n->kids[1], 0) + "]";
            case K::Case: return names[n->name.v].text + (n->kids.empty() ? "" : "(" + list(0) + ")");
            case K::PredType: return names[n->name.v].text;
            case K::EnumType: {
                for (size_t i = 0; i < n->cases.size(); ++i) {
                    s += (i ? " | " : "") + names[n->cases[i].v].text;
                    const NodeP& rec = n->kids[i];
                    for (size_t k = 0; k < rec->parts.size(); ++k)
                        s += (k ? ", " : "(") + fields[rec->parts[k].v].label + ": " + go(rec->kids[k], 0);
                    if (!rec->parts.empty()) s += ")";
                }
                return s;
            }
            case K::SetOf: {
                std::string v = name_of(n->var);
                return "{ " + v + " in " + go(n->kids[0], 0) + " | " + go(n->kids[1], 0) + " }";
            }
            case K::True: return "true";
            case K::Not:
                if (n->kids[0]->k == K::Eq) s = go(n->kids[0]->kids[0], 5) + " \xe2\x89\xa0 " + go(n->kids[0]->kids[1], 5);
                else s = "not " + go(n->kids[0], 4);
                break;
            case K::And: s = go(n->kids[0], 3) + " and " + go(n->kids[1], 4); break;
            case K::Or: s = go(n->kids[0], 2) + " or " + go(n->kids[1], 3); break;
            case K::Implies: s = go(n->kids[0], 2) + " implies " + go(n->kids[1], 1); break;
            case K::Eq: s = go(n->kids[0], 5) + " = " + go(n->kids[1], 5); break;
            case K::In: s = go(n->kids[0], 5) + " in " + go(n->kids[1], 5); break;
            case K::Subset: s = go(n->kids[0], 5) + " \xe2\x8a\x86 " + go(n->kids[1], 5); break;
            case K::Lt: s = go(n->kids[0], 5) + (n->num ? " > " : " < ") + go(n->kids[1], 5); break;
            case K::Le: s = go(n->kids[0], 5) + (n->num ? " \xe2\x89\xa5 " : " \xe2\x89\xa4 ") + go(n->kids[1], 5); break;
            case K::All:
            case K::Some: {
                std::string v = name_of(n->var);
                s = std::string(n->k == K::All ? "all " : "some ") + v + " in " + go(n->kids[0], 5) + ": " + go(n->kids[1], 0);
                break;
            }
            case K::Pred:
            case K::Use:
                s = names[n->name.v].text;
                if (!n->kids.empty() || !names[n->name.v].params.empty()) s += "(" + list(0) + ")";
                return s;
        }
        return prec(n->k) < ctx ? "(" + s + ")" : s;
    };
    return go(root, 0);
}

}  // namespace sys2fol
