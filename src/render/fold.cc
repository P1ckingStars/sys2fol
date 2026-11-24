#include "src/render/fold.h"

#include <functional>
#include <map>
#include <set>

#include "src/render/decompile.h"

namespace sys2fol::render {

namespace {

std::shared_ptr<Node> copy(const NodeP& n, std::vector<NodeP> kids) {
    auto c = std::make_shared<Node>(*n);
    c->kids = std::move(kids);
    return c;
}

NodeP use(NameId alias, std::vector<NodeP> args) {
    auto n = std::make_shared<Node>();
    n->k = K::Use;
    n->name = alias;
    n->kids = std::move(args);
    return n;
}

// Matches `pat`, an alias's plain body, against `t`, filling the alias's holes.
struct Matcher {
    const Program& p;
    std::set<VarId> holes;
    std::map<VarId, NodeP> filled;
    std::map<VarId, VarId> bound;

    bool fill(VarId h, const NodeP& t) {
        auto it = filled.find(h);
        if (it != filled.end()) return same(it->second, t);
        filled[h] = t;
        return true;
    }

    bool go(const NodeP& pat, const NodeP& t) {
        if (pat->k == K::Var && holes.count(pat->var)) return fill(pat->var, t);
        // m.f for a hole m that is an instance of a structure: the instance's component.
        if (pat->k == K::Field && pat->kids[0]->k == K::Var && holes.count(pat->kids[0]->var) &&
            p.vars[pat->kids[0]->var.v].of_structure) {
            if (t->k != K::Comp || !(t->field == pat->field)) return false;
            auto inst = std::make_shared<Node>();
            inst->k = K::Inst;
            inst->name = t->name;
            return fill(pat->kids[0]->var, inst);
        }
        if (pat->k != t->k || pat->kids.size() != t->kids.size()) return false;
        switch (pat->k) {
            case K::Var: {
                auto it = bound.find(pat->var);
                return it != bound.end() ? it->second == t->var : pat->var == t->var;
            }
            case K::Num: return pat->num == t->num;
            case K::Inst: return pat->name == t->name;
            case K::Comp: return pat->name == t->name && pat->field == t->field;
            case K::Field:
                if (!(pat->field == t->field)) return false;
                break;
            case K::Pred:
            case K::Use:
                if (!(pat->name == t->name)) return false;
                break;
            case K::SetOf:
            case K::All:
            case K::Some: {
                if (!go(pat->kids[0], t->kids[0])) return false;
                bound[pat->var] = t->var;
                bool ok = go(pat->kids[1], t->kids[1]);
                bound.erase(pat->var);
                return ok;
            }
            default: break;
        }
        for (size_t i = 0; i < pat->kids.size(); ++i)
            if (!go(pat->kids[i], t->kids[i])) return false;
        return true;
    }
};

// n with each variable in m renamed.
NodeP renamed(const NodeP& n, const std::map<VarId, VarId>& m) {
    std::vector<NodeP> kids;
    for (const NodeP& k : n->kids) kids.push_back(renamed(k, m));
    auto c = copy(n, std::move(kids));
    if (auto it = m.find(n->var); n->k == K::Var && it != m.end()) c->var = it->second;
    return c;
}

std::shared_ptr<Node> mk(K k, std::vector<NodeP> kids = {}) {
    auto n = std::make_shared<Node>();
    n->k = k;
    n->kids = std::move(kids);
    return n;
}

void binders(const NodeP& n, std::vector<VarId>& out) {
    if (n->k == K::SetOf || n->k == K::All || n->k == K::Some) out.push_back(n->var);
    for (const NodeP& k : n->kids) binders(k, out);
}

}  // namespace

Folder::Folder(Program& p, Program& hints) : p_(p), hints_(hints) {
    for (uint32_t i = 0; i < p.names.size(); ++i) {
        const NameInfo& a = p.names[i];
        if (a.kind == NameInfo::Alias && !a.params.empty() && a.body) defined_.push_back({NameId{i}, p.expand(a.body)});
    }
}

NodeP Folder::type_of(const NodeP& t) const {
    if (t->k == K::Field) return p_.field(t->field).type;
    if (t->k == K::Var) return p_.vars[t->var.v].bound;
    return nullptr;
}

bool Folder::natural(const NodeP& t) const {
    if (t->k == K::Length) return true;
    NodeP type = type_of(t);
    return type && type->k == K::PredType && p_.name(type->name).fol == "Sys.natural";
}

// A value of `type`: a number of an enum's type is that enum's case; the empty set of a sequence's, [].
NodeP Folder::value(const NodeP& v, const NodeP& type) {
    if (type && type->k == K::SeqType && v->k == K::Num && v->num == 0) return mk(K::SeqLit);
    if (type && type->k == K::EnumType && !type->cases.empty() && v->k == K::SeqLit && v->kids.size() == 2 &&
        v->kids[0]->k == K::Num && v->kids[0]->num < type->cases.size()) {
        NameId c = type->cases[v->kids[0]->num];
        const NodeP& rec = p_.name(c).body;
        const NodeP& pay = v->kids[1];
        std::vector<NodeP> args;
        bool fits = rec->kids.empty() ? pay->k == K::Num && pay->num == 0 : pay->k == K::SeqLit && pay->kids.size() == rec->kids.size();
        if (fits) {
            for (size_t i = 0; i < rec->kids.size(); ++i) args.push_back(value(pay->kids[i], p_.field(rec->parts[i]).type));
            auto n = mk(K::Case, std::move(args));
            n->name = c;
            return n;
        }
    }
    if (v->k == K::Num && type && type->k == K::Use && type->kids.empty())
        for (uint32_t i = 0; i < p_.names.size(); ++i) {
            const NameInfo& c = p_.names[i];
            if (c.is_case && c.enum_of == type->name && c.body->num == v->num) return use(NameId{i}, {});
        }
    return fold(v);
}

NodeP Folder::fold_set(const NodeP& set, const NodeP& hint) {
    std::map<VarId, VarId> m = source_vars;
    if (hint && same(hints_.expand(hint), set, m)) return renamed(hint, source_vars);
    std::vector<NameId> fits;
    for (uint32_t i = 0; i < p_.names.size(); ++i) {
        const NameInfo& a = p_.names[i];
        if (a.kind == NameInfo::Alias && a.params.empty() && !a.is_case && a.body && same(p_.expand(a.body), set))
            fits.push_back(NameId{i});
    }
    return fits.size() == 1 ? use(fits[0], {}) : fold(set);
}

void Folder::parts(NameId inst) {
    const auto& source = hints_.name(inst).components;
    for (auto& [f, def] : p_.names[inst.v].components) {
        if (def.kind != ComponentDef::Parts) continue;
        auto h = source.find(f);
        std::vector<NodeP> hinted;
        if (h != source.end() && h->second.kind == ComponentDef::Parts) hinted = h->second.set->kids;
        std::vector<NodeP> kids;
        for (size_t i = 0; i < def.set->kids.size(); ++i) {
            kids.push_back(fold_set(def.set->kids[i], i < hinted.size() ? hinted[i] : nullptr));
            p_.fields[def.set->parts[i].v].type = kids.back();
        }
        def.set = copy(def.set, std::move(kids));
    }
}

void Folder::instance(NameId inst) {
    for (auto& [f, def] : p_.names[inst.v].components) {
        if (def.kind == ComponentDef::Condition) def.set = copy(def.set, {def.set->kids[0], fold(def.set->kids[1])});
        if (def.kind != ComponentDef::Rules) continue;
        const auto& comps = p_.name(inst).components;
        const std::vector<FieldId>& state = comps.at(def.state).set->parts;
        const std::vector<FieldId>& output = comps.at(def.output).set->parts;
        for (RuleDef& r : def.rules) {
            r.when = fold(r.when);
            for (size_t i = 0; i < r.next.size(); ++i) r.next[i] = value(r.next[i], p_.field(state[i]).type);
            for (size_t i = 0; i < r.out.size(); ++i) r.out[i] = value(r.out[i], p_.field(output[i]).type);
        }
        // Each rule read with the source's: its pattern variables' names, and its comparisons' spellings.
        auto src = hints_.name(inst).components.find(f);
        if (src == hints_.name(inst).components.end() || src->second.rules.size() != def.rules.size()) continue;
        const ComponentDef& sd = src->second;
        for (size_t j = 0; j < def.rules.size(); ++j) {
            RuleDef& r = def.rules[j];
            const RuleDef& sr = sd.rules[j];
            std::map<VarId, VarId> bound{{def.s, sd.s}, {def.a, sd.a}, {def.b, sd.b}, {def.t, sd.t}};
            const std::vector<VarId>&ours = p_.name(inst).params, &theirs = hints_.name(inst).params;
            for (size_t k = 0; k < ours.size() && k < theirs.size(); ++k) bound[ours[k]] = theirs[k];
            r.said = sr.said;
            if (r.binders.size() == sr.binders.size())
                for (size_t i = 0; i < r.binders.size(); ++i) {
                    p_.vars[r.binders[i].v].hint = hints_.vars[sr.binders[i].v].hint;
                    bound[r.binders[i]] = sr.binders[i];
                }
            r.when = respell(r.when, sr.when, bound);
        }
    }
}

NodeP Folder::fold(const NodeP& n) {
    for (const auto& [alias, body] : defined_) {
        Matcher m{p_, {}, {}, {}};
        for (VarId v : p_.name(alias).params) m.holes.insert(v);
        if (!m.go(body, n) || m.filled.size() != m.holes.size()) continue;
        std::vector<NodeP> args;
        for (VarId v : p_.name(alias).params) args.push_back(fold(m.filled.at(v)));
        return use(alias, std::move(args));
    }
    if (n->k == K::In && natural(n->kids[1])) return copy(mk(K::Lt), {fold(n->kids[0]), fold(n->kids[1])});
    if (n->k == K::Or && n->kids[0]->k == K::In && n->kids[1]->k == K::Eq && same(n->kids[0]->kids[0], n->kids[1]->kids[0]) &&
        same(n->kids[0]->kids[1], n->kids[1]->kids[1]) && natural(n->kids[0]->kids[1]))
        return copy(mk(K::Le), {fold(n->kids[0]->kids[0]), fold(n->kids[0]->kids[1])});
    if (n->k == K::Eq) return copy(n, {value(n->kids[0], type_of(n->kids[1])), value(n->kids[1], type_of(n->kids[0]))});
    std::vector<NodeP> kids;
    for (const NodeP& k : n->kids) kids.push_back(fold(k));
    return copy(n, std::move(kids));
}

// The same term in the reading and the source: variables as `bound` pairs them, parts by their labels.
bool Folder::alike(const NodeP& r, const NodeP& s, const std::map<VarId, VarId>& bound) const {
    if (r->k != s->k || r->kids.size() != s->kids.size()) return false;
    if (r->k == K::Var) {
        auto it = bound.find(r->var);
        return it != bound.end() ? it->second == s->var : r->var == s->var;
    }
    if (r->k == K::Field && p_.field(r->field).label != hints_.field(s->field).label) return false;
    if ((r->k == K::Num && r->num != s->num) || ((r->k == K::Case || r->k == K::Use || r->k == K::Pred) && !(r->name == s->name)))
        return false;
    for (size_t i = 0; i < r->kids.size(); ++i)
        if (!alike(r->kids[i], s->kids[i], bound)) return false;
    return true;
}

NodeP Folder::respell(const NodeP& r, const NodeP& s, std::map<VarId, VarId> bound) {
    if (!s) return r;
    if ((r->k == K::Lt || r->k == K::Le) && s->k == r->k && s->num == 1 && r->num == 0) {
        if (alike(r->kids[0], s->kids[1], bound) && alike(r->kids[1], s->kids[0], bound)) {
            auto n = copy(r, {r->kids[1], r->kids[0]});
            n->num = 1;
            return n;
        }
    }
    if (r->k != s->k || r->kids.size() != s->kids.size()) return r;
    if (r->k == K::SetOf || r->k == K::All || r->k == K::Some) bound[r->var] = s->var;
    std::vector<NodeP> kids;
    for (size_t i = 0; i < r->kids.size(); ++i) kids.push_back(respell(r->kids[i], s->kids[i], bound));
    return copy(r, std::move(kids));
}

void Folder::name_binders(const NodeP& reading, const NodeP& source) {
    std::vector<VarId> ours, theirs;
    binders(reading, ours);
    binders(source, theirs);
    if (ours.size() != theirs.size()) return;
    for (size_t i = 0; i < ours.size(); ++i) p_.vars[ours[i].v].hint = hints_.vars[theirs[i].v].hint;
}

}  // namespace sys2fol::render
