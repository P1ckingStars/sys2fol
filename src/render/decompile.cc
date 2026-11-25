#include "src/render/decompile.h"

#include <optional>

namespace sys2fol::render {

namespace {

std::shared_ptr<Node> mk(K k, std::vector<NodeP> kids = {}) {
    auto n = std::make_shared<Node>();
    n->k = k;
    n->kids = std::move(kids);
    return n;
}

NodeP num(uint64_t v) {
    auto n = mk(K::Num);
    n->num = v;
    return n;
}

NodeP var(VarId v) {
    auto n = mk(K::Var);
    n->var = v;
    return n;
}

NodeP range(uint64_t n) { return mk(K::Range, {num(0), num(n)}); }

bool atom(const FP& f, const char* pred, std::initializer_list<int> args) {
    return f->kind == F::Atom && f->pred == pred && f->args == std::vector<int>(args);
}

bool is_atom(const FP& f, const char* pred, size_t n) { return f->kind == F::Atom && f->pred == pred && f->args.size() == n; }

struct Bound {
    int v;
    FP body;
};

// (forall v. (set(v) -> body))
std::optional<Bound> all_set(const FP& f) {
    if (f->kind != F::All || f->kids[0]->kind != F::Implies || !atom(f->kids[0]->kids[0], "set", {f->var})) return {};
    return Bound{f->var, f->kids[0]->kids[1]};
}

// (exists v. (set(v) & body))
std::optional<Bound> ex_set(const FP& f) {
    if (f->kind != F::Ex || f->kids[0]->kind != F::And || !atom(f->kids[0]->kids[0], "set", {f->var})) return {};
    return Bound{f->var, f->kids[0]->kids[1]};
}

// Exactly n conjuncts, nested to the right.
std::optional<std::vector<FP>> conj(const FP& f, size_t n) {
    std::vector<FP> out;
    FP g = f;
    while (out.size() + 1 < n) {
        if (g->kind != F::And) return {};
        out.push_back(g->kids[0]);
        g = g->kids[1];
    }
    out.push_back(g);
    return out;
}

std::vector<FP> disj(const FP& f) {
    if (f->kind == F::False) return {};
    std::vector<FP> out;
    FP g = f;
    for (; g->kind == F::Or; g = g->kids[1]) out.push_back(g->kids[0]);
    out.push_back(g);
    return out;
}

bool among(int v, const std::vector<int>& vs) {
    for (int x : vs)
        if (x == v) return true;
    return false;
}

// The numbers a claim names at its top, by variable (decision 23).
using Nums = std::map<int, uint64_t>;

std::optional<uint64_t> number(const Nums& nums, int v) {
    auto it = nums.find(v);
    if (it == nums.end()) return {};
    return it->second;
}

// f says x is the number n: eq(x, z_n).
std::optional<uint64_t> numeral_of(const Nums& nums, const FP& f, int x) {
    if (!is_atom(f, "eq", 2) || f->args[0] != x) return {};
    return number(nums, f->args[1]);
}

// f says v is the part of r at index i: pmem(z_i, v, r).
struct At {
    int v, r;
    uint32_t i;
};

std::optional<At> at(const Nums& nums, const FP& f) {
    if (!is_atom(f, "pmem", 3) || number(nums, f->args[1]) || number(nums, f->args[2])) return {};
    auto i = number(nums, f->args[0]);
    if (!i) return {};
    return At{f->args[1], f->args[2], static_cast<uint32_t>(*i)};
}

// f says r is the tuple of the returned variables: tuple(r, z_k) and pmem(z_i, x_i, r) for each i below k.
std::optional<std::vector<int>> record(const Nums& nums, const FP& f, int r) {
    if (atom(f, "zero", {r})) return std::vector<int>{};
    if (f->kind != F::And || !is_atom(f->kids[0], "tuple", 2) || f->kids[0]->args[0] != r) return {};
    auto k = number(nums, f->kids[0]->args[1]);
    if (!k || *k == 0) return {};
    auto cs = conj(f, *k + 1);
    if (!cs) return {};
    std::vector<int> xs;
    for (size_t i = 0; i < *k; ++i) {
        const FP& m = (*cs)[i + 1];
        if (!is_atom(m, "pmem", 3) || number(nums, m->args[0]) != i || m->args[2] != r) return {};
        xs.push_back(m->args[1]);
    }
    return xs;
}

// The variables of leading `exists x. (set(x) & ...)`, at most `limit`, and what they surround.
std::vector<int> exists_prefix(FP& f, size_t limit) {
    std::vector<int> xs;
    while (xs.size() < limit) {
        auto b = ex_set(f);
        if (!b) break;
        xs.push_back(b->v);
        f = b->body;
    }
    return xs;
}

// f says v is q without its first entry: the writer's rest(q, v); q returned.
std::optional<int> rest_of(const FP& f, int v) {
    auto n = ex_set(f);
    auto m = n ? ex_set(n->body) : std::nullopt;
    if (!m) return {};
    auto cs = conj(m->body, 4);
    if (!cs || !atom((*cs)[0], "nsucc", {m->v, n->v}) || !is_atom((*cs)[1], "tuple", 2) || (*cs)[1]->args[1] != n->v ||
        !atom((*cs)[2], "tuple", {v, m->v}))
        return {};
    int q = (*cs)[1]->args[0];
    auto i = all_set((*cs)[3]);
    auto j = i ? all_set(i->body) : std::nullopt;
    if (!j || j->body->kind != F::Implies || !atom(j->body->kids[0], "nsucc", {i->v, j->v})) return {};
    auto y = all_set(j->body->kids[1]);
    if (!y || y->body->kind != F::Iff || !atom(y->body->kids[0], "pmem", {j->v, y->v, q}) ||
        !atom(y->body->kids[1], "pmem", {i->v, y->v, v}))
        return {};
    return q;
}

// f says v is q with y appended: (exists n. (set(n) & (tuple(q, n) & snoc(q, n, y, v)))).
std::optional<std::pair<int, int>> append_of(const FP& f, int v) {
    auto n = ex_set(f);
    if (!n || n->body->kind != F::And || !is_atom(n->body->kids[0], "tuple", 2) || n->body->kids[0]->args[1] != n->v) return {};
    int q = n->body->kids[0]->args[0];
    const FP& sn = n->body->kids[1];
    if (!is_atom(sn, "snoc", 4) || sn->args[0] != q || sn->args[1] != n->v || sn->args[3] != v) return {};
    return std::pair<int, int>{q, sn->args[2]};
}

Error unreadable(const FP& f, const std::string& what) {
    std::string s = show(f);
    if (s.size() > 160) s = s.substr(0, 160) + " ...";
    return Error({}, "expected " + what + ", found " + s);
}

}  // namespace

NodeP comp_node(NameId inst, FieldId f) {
    auto n = mk(K::Comp);
    n->name = inst;
    n->field = f;
    return n;
}

ComponentDef::Kind kind_of(const Program& p, NameId inst, FieldId f, FieldId* of, FieldId roles[3]) {
    NameId sid = p.name(inst).structure;
    const NodeP& type = p.field(f).type;
    auto own = [&](const NodeP& t) { return t && t->k == K::Comp && t->name == sid; };
    if (!type) return ComponentDef::Parts;
    if (type->k == K::SetType && own(type->kids[0])) {
        if (of) *of = type->kids[0]->field;
        return ComponentDef::Condition;
    }
    if (type->k == K::SetType && type->kids[0]->k == K::Tuple && type->kids[0]->kids.size() == 4) {
        const auto& t = type->kids[0]->kids;
        if (own(t[0]) && own(t[1]) && own(t[2]) && own(t[3]) && t[0]->field == t[3]->field) {
            if (roles)
                for (int i = 0; i < 3; ++i) roles[i] = t[i]->field;
            return ComponentDef::Rules;
        }
    }
    throw Error({}, "no notation writes the field " + p.field(f).label);
}

Decompiler::Decompiler(Program& p, const Program& hints) : p_(p), hints_(hints) {
    for (uint32_t i = 0; i < p.names.size(); ++i) {
        if (p.names[i].kind == NameInfo::Extern) externs_.emplace(p.names[i].fol, NameId{i});
        if (p.names[i].kind == NameInfo::ExternType) types_.emplace(p.names[i].fol, NameId{i});
    }
}

bool Decompiler::sequence(const NodeP& t) const {
    if (t->k == K::Rest || t->k == K::Append) return true;
    NodeP ty = t->k == K::Var ? p_.vars[t->var.v].bound : t->k == K::Field ? p_.field(t->field).type : nullptr;
    return ty && ty->k == K::SeqType;
}

FP Decompiler::numbers(const FP& f) {
    FP g = f;
    std::vector<int> zs;
    while (auto b = all_set(g)) {
        if (b->body->kind != F::Implies) break;
        const FP& guard = b->body->kids[0];
        if (!(zs.empty() ? atom(guard, "zero", {b->v}) : atom(guard, "nsucc", {zs.back(), b->v}))) break;
        nums_[b->v] = zs.size();
        env[b->v] = num(zs.size());
        zs.push_back(b->v);
        g = b->body->kids[1];
    }
    return g;
}

FP Decompiler::params(const FP& f, const std::vector<VarId>& hints, std::vector<VarId>& out,
                       const std::vector<VarId>* reuse) {
    if (reuse && !reuse->empty() && reuse->size() != hints.size())
        throw Error({}, "a theorem whose parameters are not its instance's, in order, is not read yet");
    FP g = f;
    for (VarId h : hints) {
        auto b = all_set(g);
        if (!b) throw unreadable(g, "the parameter " + hints_.vars[h.v].hint);
        g = b->body;
        NodeP type;
        if (hints_.vars[h.v].bound) {
            if (g->kind != F::Implies) throw unreadable(g, "the type of " + hints_.vars[h.v].hint);
            type = member(g->kids[0], b->v, false);
            if (!type) throw unreadable(g->kids[0], "the type of " + hints_.vars[h.v].hint);
            g = g->kids[1];
        }
        VarId v = reuse && !reuse->empty() ? (*reuse)[out.size()] : p_.new_var(hints_.vars[h.v].hint, type);
        if (reuse && !reuse->empty() && !same(p_.vars[v.v].bound ? p_.vars[v.v].bound : mk(K::True), type ? type : mk(K::True)))
            throw Error({}, "the claims disagree on the type of " + hints_.vars[h.v].hint);
        env[b->v] = var(v);
        out.push_back(v);
    }
    return g;
}

NodeP Decompiler::term(int v, const FP& where) const {
    auto it = env.find(v);
    if (it == env.end()) throw unreadable(where, "a variable the claim has bound");
    return it->second;
}

const std::vector<FieldId>* Decompiler::parts_of(const NodeP& s) const {
    if (!s) return nullptr;
    if (s->k == K::RecordType) return &s->parts;
    if (s->k == K::SetOf) return parts_of(s->kids[0]);
    if (s->k == K::Comp) {
        const auto& cs = p_.name(s->name).components;
        auto it = cs.find(s->field);
        if (it != cs.end() && it->second.kind != ComponentDef::Rules) return parts_of(it->second.set);
    }
    return nullptr;
}

FieldId Decompiler::part(const NodeP& t, uint32_t i, const FP& where) const {
    NodeP set = t->k == K::Var ? p_.vars[t->var.v].bound : t->k == K::Field ? p_.field(t->field).type : nullptr;
    const std::vector<FieldId>* parts = parts_of(set);
    if (!parts || i >= parts->size()) throw unreadable(where, "a part of a record whose parts are known");
    return (*parts)[i];
}

NodeP Decompiler::bind(K k, int x, const NodeP& bound, const FP& body) {
    VarId v = p_.new_var("x", bound);
    auto saved = env.find(x) == env.end() ? nullptr : env[x];
    env[x] = var(v);
    NodeP b = formula(body);
    if (saved) env[x] = saved; else env.erase(x);
    auto n = mk(k, {bound, b});
    n->var = v;
    return n;
}

NodeP Decompiler::predicate(const FP& f) {
    std::vector<NodeP> args;
    for (int a : f->args) args.push_back(term(a, f));
    if (f->pred == "eq" && args.size() == 2) return mk(K::Eq, args);
    if (f->pred == "elem" && args.size() == 2) return mk(K::In, args);
    auto it = externs_.find(f->pred);
    if (it == externs_.end() || p_.name(it->second).params.size() != args.size())
        throw unreadable(f, "a predicate the spec binds with extern");
    auto n = mk(K::Pred, std::move(args));
    n->name = it->second;
    return n;
}

NodeP Decompiler::formula(const FP& f) {
    switch (f->kind) {
        case F::Not: return mk(K::Not, {formula(f->kids[0])});
        case F::And: return mk(K::And, {formula(f->kids[0]), formula(f->kids[1])});
        case F::Or: return mk(K::Or, {formula(f->kids[0]), formula(f->kids[1])});
        case F::Implies:
            if (f->kids[0]->kind == F::False && f->kids[1]->kind == F::False) return mk(K::True);
            return mk(K::Implies, {formula(f->kids[0]), formula(f->kids[1])});
        case F::Atom: return predicate(f);
        case F::All: {
            auto b = all_set(f);
            if (!b || b->body->kind != F::Implies) break;
            NodeP a = member(b->body->kids[0], b->v, false);
            if (!a) break;
            if (NodeP s = member(b->body->kids[1], b->v, false)) return mk(K::Subset, {a, s});
            return bind(K::All, b->v, a, b->body->kids[1]);
        }
        case F::Ex: {
            auto b = ex_set(f);
            if (!b) break;
            if (b->body->kind == F::And) {
                const FP& l = b->body->kids[0];
                const FP& rest = b->body->kids[1];
                auto value = [&](NodeP t) {
                    env[b->v] = std::move(t);
                    NodeP out = formula(rest);
                    env.erase(b->v);
                    return out;
                };
                if (is_atom(l, "tuple", 2) && l->args[1] == b->v && l->args[0] != b->v)
                    return value(mk(K::Length, {term(l->args[0], l)}));
                if (auto q = rest_of(l, b->v)) return value(mk(K::Rest, {term(*q, l)}));
                if (auto ap = append_of(l, b->v)) return value(mk(K::Append, {term(ap->first, l), term(ap->second, l)}));
                if (auto xs = record(nums_, l, b->v); xs && !xs->empty()) {
                    std::vector<NodeP> items;
                    for (int x : *xs) items.push_back(term(x, l));
                    return value(mk(K::SeqLit, std::move(items)));
                }
                if (auto a = at(nums_, l); a && a->v == b->v) {
                    NodeP r = term(a->r, l);
                    if (a->i == 0 && sequence(r)) return value(mk(K::First, {r}));
                    auto fld = mk(K::Field, {r});
                    fld->field = part(r, a->i, l);
                    return value(fld);
                }
            }
            if (NodeP r = record_membership(f)) return r;
            if (b->body->kind == F::And)
                if (NodeP s = member(b->body->kids[0], b->v, false)) return bind(K::Some, b->v, s, b->body->kids[1]);
            break;
        }
        default: break;
    }
    throw unreadable(f, "a formula");
}

// f says x is in the returned set; null when f is no membership of x.
NodeP Decompiler::member(const FP& f, int x, bool record) {
    if (is_atom(f, "elem", 2) && f->args[0] == x && f->args[1] != x) return term(f->args[1], f);
    if (f->kind == F::Atom && f->args == std::vector<int>{x})
        if (auto it = types_.find(f->pred); it != types_.end()) {
            auto n = mk(K::PredType);
            n->name = it->second;
            return n;
        }
    if (record && atom(f, "zero", {x})) return mk(K::RecordType);
    {
        std::vector<FP> ds = disj(f);
        bool ok = true;
        for (size_t i = 0; ok && i < ds.size(); ++i) ok = numeral_of(nums_, ds[i], x) == i;
        if (ok) return range(ds.size());
    }
    if (f->kind == F::Ex) {
        if (NodeP s = sequence_type(f, x)) return s;
        if (NodeP e = enum_type(f, x)) return e;
        return record_type(f, x);
    }
    if (f->kind == F::And) {
        NodeP bound = member(f->kids[0], x, false);
        return bound ? bind(K::SetOf, x, bound, f->kids[1]) : nullptr;
    }
    if (auto b = all_set(f); b && b->body->kind == F::Implies && atom(b->body->kids[0], "elem", {b->v, x}))
        if (NodeP t = member(b->body->kids[1], b->v, false)) return mk(K::SetType, {t});
    return nullptr;
}

// exists n. (set(n) & (Sys.natural(n) & (tuple(x, n) & (forall i y. (pmem(i, y, x) -> y in T))))).
NodeP Decompiler::sequence_type(const FP& f, int x) {
    auto b = ex_set(f);
    if (!b) return nullptr;
    auto cs = conj(b->body, 3);
    if (!cs || !atom((*cs)[0], "Sys.natural", {b->v}) || !atom((*cs)[1], "tuple", {x, b->v})) return nullptr;
    auto i = all_set((*cs)[2]);
    auto y = i ? all_set(i->body) : std::nullopt;
    if (!y || y->body->kind != F::Implies || !atom(y->body->kids[0], "pmem", {i->v, y->v, x})) return nullptr;
    NodeP t = member(y->body->kids[1], y->v, false);
    return t ? mk(K::SeqType, {t}) : nullptr;
}

// exists c p. (x is the tuple of c and p & ((c = 0 & p in R0) | (c = 1 & p in R1) | ...)): its cases not yet named.
NodeP Decompiler::enum_type(const FP& f, int x) {
    auto c = ex_set(f);
    auto q = c ? ex_set(c->body) : std::nullopt;
    if (!q || q->body->kind != F::And) return nullptr;
    auto tup = record(nums_, q->body->kids[0], x);
    if (!tup || *tup != std::vector<int>{c->v, q->v}) return nullptr;
    std::vector<FP> cases = disj(q->body->kids[1]);
    if (cases.size() < 2) return nullptr;
    auto n = mk(K::EnumType);
    for (size_t k = 0; k < cases.size(); ++k) {
        if (cases[k]->kind != F::And || numeral_of(nums_, cases[k]->kids[0], c->v) != k) return nullptr;
        NodeP rec = member(cases[k]->kids[1], q->v, true);
        if (!rec || rec->k != K::RecordType) return nullptr;
        n->kids.push_back(rec);
    }
    return n;
}

// exists x1 ... xk. (x is the tuple of x1 ... xk & x1 in T1 & ... & xk in Tk), its parts not yet named.
NodeP Decompiler::record_type(const FP& f, int x) {
    FP g = f;
    std::vector<int> xs = exists_prefix(g, SIZE_MAX);
    auto cs = conj(g, xs.size() + 1);
    if (xs.empty() || !cs) return nullptr;
    auto rec = record(nums_, (*cs)[0], x);
    if (!rec || *rec != xs) return nullptr;
    auto n = mk(K::RecordType);
    for (size_t i = 0; i < xs.size(); ++i) {
        NodeP t = member((*cs)[i + 1], xs[i], false);
        if (!t) throw unreadable((*cs)[i + 1], "the set a record's part is in");
        n->kids.push_back(t);
    }
    return n;
}

// t in a record type, where t is a variable.
NodeP Decompiler::record_membership(const FP& f) {
    FP g = f;
    std::vector<int> xs = exists_prefix(g, SIZE_MAX);
    auto cs = conj(g, xs.size() + 1);
    if (xs.empty() || !cs) return nullptr;
    const FP& rec = (*cs)[0];
    if (rec->kind != F::And || !is_atom(rec->kids[0], "tuple", 2)) return nullptr;
    int t = rec->kids[0]->args[0];
    if (among(t, xs) || number(nums_, t)) return nullptr;
    NodeP set = record_type(f, t);
    return set ? mk(K::In, {term(t, f), set}) : nullptr;
}

NodeP Decompiler::labelled(const NodeP& rec, CompRef comp) {
    const ComponentDef* hint = nullptr;
    if (auto it = hints_.name(comp.first).components.find(comp.second); it != hints_.name(comp.first).components.end())
        hint = &it->second;
    auto n = std::make_shared<Node>(*rec);
    n->parts.clear();
    for (size_t i = 0; i < rec->kids.size(); ++i) {
        std::string label = "part" + std::to_string(i);
        if (hint && hint->kind == ComponentDef::Parts && i < hint->set->parts.size())
            label = hints_.field(hint->set->parts[i]).label;
        n->parts.push_back(p_.new_field(label, static_cast<uint32_t>(i), rec->kids[i]));
    }
    return n;
}

std::vector<NodeP> Decompiler::values(const FP& f, int r, size_t n) {
    if (n == 0) {
        if (!atom(f, "zero", {r})) throw unreadable(f, "the empty record");
        return {};
    }
    FP g = f;
    std::vector<int> xs = exists_prefix(g, n);
    auto cs = conj(g, n + 1);
    if (xs.size() != n || !cs) throw unreadable(f, "a record of " + std::to_string(n) + " values");
    auto rec = record(nums_, (*cs)[0], r);
    if (!rec || *rec != xs) throw unreadable((*cs)[0], "a record of " + std::to_string(n) + " values");
    std::vector<NodeP> out;
    for (size_t i = 0; i < n; ++i) {
        VarId slot = p_.new_var("x", nullptr);
        env[xs[i]] = var(slot);
        NodeP e = formula((*cs)[i + 1]);
        env.erase(xs[i]);
        auto is_slot = [&](const NodeP& t) { return t->k == K::Var && t->var == slot; };
        if (e->k != K::Eq || !(is_slot(e->kids[0]) || is_slot(e->kids[1]))) throw unreadable((*cs)[i + 1], "a value");
        out.push_back(is_slot(e->kids[0]) ? e->kids[1] : e->kids[0]);
    }
    return out;
}

ComponentDef Decompiler::rules(const FP& m, int q, NameId inst, FieldId f) {
    ComponentDef def;
    def.kind = ComponentDef::Rules;
    FieldId roles[3];
    kind_of(p_, inst, f, nullptr, roles);
    def.state = roles[0];
    def.input = roles[1];
    def.output = roles[2];
    auto in = [&](const FP& g, FieldId role, int& v) -> FP {
        auto b = ex_set(g);
        if (!b || b->body->kind != F::And || !is_atom(b->body->kids[0], "elem", 2) || b->body->kids[0]->args[0] != b->v ||
            !same(term(b->body->kids[0]->args[1], g), comp_node(inst, role)))
            throw unreadable(g, "a value in " + p_.name(inst).text + "." + p_.field(role).label);
        v = b->v;
        return b->body->kids[1];
    };
    int s, a, b, t;
    FP g = in(m, def.state, s);
    g = in(g, def.input, a);
    std::vector<int> bt = exists_prefix(g, 2);
    auto step = g->kind == F::And ? conj(g, 2) : std::nullopt;
    if (bt.size() != 2 || !step) throw unreadable(g, "a step and its rules");
    b = bt[0];
    t = bt[1];
    auto tuple = record(nums_, (*step)[0], q);
    if (!tuple || *tuple != std::vector<int>{s, a, b, t}) throw unreadable((*step)[0], "a step (s, a, b, t)");
    def.s = p_.new_var("s", comp_node(inst, def.state));
    def.a = p_.new_var("a", comp_node(inst, def.input));
    def.b = p_.new_var("b", comp_node(inst, def.output));
    def.t = p_.new_var("t", comp_node(inst, def.state));
    env[s] = var(def.s);
    env[a] = var(def.a);
    env[b] = var(def.b);
    env[t] = var(def.t);
    size_t states = parts_of(comp_node(inst, def.state))->size();
    size_t outputs = parts_of(comp_node(inst, def.output))->size();
    for (FP c : disj((*step)[1])) {
        RuleDef r;
        std::vector<int> bound;
        while (auto pv = ex_set(c)) {
            if (pv->body->kind != F::And) throw unreadable(c, "a rule's pattern variable");
            NodeP type = member(pv->body->kids[0], pv->v, false);
            if (!type) throw unreadable(pv->body->kids[0], "the type of a rule's pattern variable");
            VarId v = p_.new_var("x", type);
            env[pv->v] = var(v);
            r.binders.push_back(v);
            bound.push_back(pv->v);
            c = pv->body->kids[1];
        }
        auto three = conj(c, 3);
        if (!three) throw unreadable(c, "a rule");
        r.when = formula((*three)[0]);
        r.next = values((*three)[1], t, states);
        r.out = values((*three)[2], b, outputs);
        for (int v : bound) env.erase(v);
        def.rules.push_back(std::move(r));
    }
    for (int v : {s, a, b, t}) env.erase(v);
    return def;
}

void Decompiler::characterization(const FP& f, CompRef comp, int c) {
    auto b = all_set(f);
    if (!b || b->body->kind != F::Iff || !atom(b->body->kids[0], "elem", {b->v, c}))
        throw unreadable(f, "a set given by its members");
    const FP& m = b->body->kids[1];
    auto [inst, fid] = comp;
    std::string name = p_.name(inst).text + "." + p_.field(fid).label;
    FieldId of;
    ComponentDef def;
    switch (kind_of(p_, inst, fid, &of)) {
        case ComponentDef::Parts: {
            NodeP set = member(m, b->v, true);
            if (!set || set->k != K::RecordType) throw unreadable(m, name + " as a set of records");
            def.kind = ComponentDef::Parts;
            def.set = labelled(set, comp);
            break;
        }
        case ComponentDef::Condition: {
            NodeP set = member(m, b->v, false);
            if (!set || set->k != K::SetOf || !same(set->kids[0], comp_node(inst, of)))
                throw unreadable(m, name + " as the members of " + p_.name(inst).text + "." + p_.field(of).label + " meeting a condition");
            def.kind = ComponentDef::Condition;
            def.set = set;
            break;
        }
        case ComponentDef::Rules: def = rules(m, b->v, inst, fid); break;
    }
    auto& comps = p_.names[inst.v].components;
    auto it = comps.find(fid);
    if (it == comps.end()) comps.emplace(fid, std::move(def));
    else if (!same(it->second, def)) throw Error({}, "the claims disagree on what " + name + " is");
}

void Decompiler::existence(const FP& f, CompRef comp) {
    auto b = ex_set(f);
    if (!b) throw unreadable(f, "a set that exists");
    characterization(b->body, comp, b->v);
}

FP Decompiler::components(const FP& f, const std::vector<CompRef>& comps) {
    FP g = f;
    std::vector<int> depth;
    for (const CompRef& c : comps) {
        auto b = all_set(g);
        if (!b) throw unreadable(g, "the set " + p_.name(c.first).text + "." + p_.field(c.second).label);
        depth.push_back(b->v);
        env[b->v] = comp_node(c.first, c.second);
        g = b->body;
    }
    for (size_t i = 0; i < comps.size(); ++i) {
        if (g->kind != F::Implies) throw unreadable(g, "what " + p_.name(comps[i].first).text + "." + p_.field(comps[i].second).label + " is");
        characterization(g->kids[0], comps[i], depth[i]);
        g = g->kids[1];
    }
    return g;
}

bool same(const NodeP& a, const NodeP& b, std::map<VarId, VarId>& bound) {
    if (a->k != b->k || a->kids.size() != b->kids.size()) return false;
    switch (a->k) {
        case K::Var: {
            auto it = bound.find(a->var);
            return it != bound.end() ? it->second == b->var : a->var == b->var;
        }
        case K::Num: return a->num == b->num;
        case K::Inst: return a->name == b->name;
        case K::Comp: return a->name == b->name && a->field == b->field;
        case K::Field:
            if (!(a->field == b->field)) return false;
            break;
        case K::Pred:
        case K::Use:
            if (!(a->name == b->name)) return false;
            break;
        case K::SetOf:
        case K::All:
        case K::Some: {
            if (!same(a->kids[0], b->kids[0], bound)) return false;
            bound[a->var] = b->var;
            bool ok = same(a->kids[1], b->kids[1], bound);
            bound.erase(a->var);
            return ok;
        }
        default: break;
    }
    for (size_t i = 0; i < a->kids.size(); ++i)
        if (!same(a->kids[i], b->kids[i], bound)) return false;
    return true;
}

bool same(const NodeP& a, const NodeP& b) {
    std::map<VarId, VarId> bound;
    return same(a, b, bound);
}

bool same(const ComponentDef& a, const ComponentDef& b) {
    if (a.kind != b.kind) return false;
    if (a.kind != ComponentDef::Rules) return same(a.set, b.set);
    if (!(a.state == b.state && a.input == b.input && a.output == b.output) || a.rules.size() != b.rules.size()) return false;
    std::map<VarId, VarId> bound{{a.s, b.s}, {a.a, b.a}, {a.b, b.b}, {a.t, b.t}};
    for (size_t i = 0; i < a.rules.size(); ++i) {
        const RuleDef &x = a.rules[i], &y = b.rules[i];
        if (x.binders.size() != y.binders.size()) return false;
        for (size_t k = 0; k < x.binders.size(); ++k) bound[x.binders[k]] = y.binders[k];
        if (!same(x.when, y.when, bound) || x.next.size() != y.next.size() || x.out.size() != y.out.size()) return false;
        for (size_t k = 0; k < x.next.size(); ++k)
            if (!same(x.next[k], y.next[k], bound)) return false;
        for (size_t k = 0; k < x.out.size(); ++k)
            if (!same(x.out[k], y.out[k], bound)) return false;
    }
    return true;
}

}  // namespace sys2fol::render
