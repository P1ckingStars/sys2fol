#include "src/render/render.h"

#include <algorithm>
#include <functional>
#include <map>
#include <set>

#include "src/render/decompile.h"
#include "src/render/fold.h"

namespace sys2fol::render {

namespace {

std::string stem(const std::string& path) {
    std::string base = path.substr(path.find_last_of('/') + 1);
    return base.substr(0, base.find('.'));
}

std::string join(const std::vector<std::string>& xs, const std::string& sep) {
    std::string s;
    for (size_t i = 0; i < xs.size(); ++i) s += (i ? sep : "") + xs[i];
    return s;
}

NameId lookup(const Program& p, const std::string& text) {
    for (uint32_t i = 0; i < p.names.size(); ++i)
        if (p.names[i].text == text) return NameId{i};
    throw Error({}, "'" + text + "' is not declared");
}

std::string comp_name(const Program& p, CompRef c) { return p.name(c.first).text + "." + p.field(c.second).label; }

std::vector<CompRef> fields_of(const Program& p, NameId inst) {
    std::vector<CompRef> out;
    for (FieldId f : p.name(p.name(inst).structure).fields) out.push_back({inst, f});
    return out;
}

// The sets an existence claim assumes: those its set is written over.
std::vector<CompRef> deps(const Program& p, NameId inst, FieldId f) {
    FieldId of, roles[3];
    switch (kind_of(p, inst, f, &of, roles)) {
        case ComponentDef::Parts: return {};
        case ComponentDef::Condition: return {{inst, of}};
        case ComponentDef::Rules: return {{inst, roles[0]}, {inst, roles[1]}, {inst, roles[2]}};
    }
    return {};
}

void instances_in(const NodeP& n, std::set<NameId>& out) {
    if (n->k == K::Comp || n->k == K::Inst) out.insert(n->name);
    for (const NodeP& k : n->kids) instances_in(k, out);
}

// The names a reading uses, with every name their definitions use.
void uses(const Program& p, const NodeP& n, std::set<NameId>& out);

void uses_name(const Program& p, NameId id, std::set<NameId>& out) {
    if (!out.insert(id).second) return;
    const NameInfo& info = p.name(id);
    if (info.body) uses(p, info.body, out);
    for (const auto& c : info.conditions) uses(p, c.second, out);
    if (info.kind == NameInfo::Instance) uses_name(p, info.structure, out);
}

void uses(const Program& p, const NodeP& n, std::set<NameId>& out) {
    if (n->k == K::Use || n->k == K::Pred || n->k == K::Inst || n->k == K::Comp) uses_name(p, n->name, out);
    for (const NodeP& k : n->kids) uses(p, k, out);
}

std::string params(const std::vector<Param>& ps) {
    std::string s = "(";
    for (size_t i = 0; i < ps.size(); ++i) {
        s += (i ? ", " : "") + ps[i].name;
        bool last_of_group = i + 1 == ps.size() || ps[i + 1].type != ps[i].type;
        if (ps[i].type && last_of_group) s += ": " + show(*ps[i].type);
    }
    return s + ")";
}

bool is_input_test(const NodeP& e, VarId a) {
    return e->k == K::Eq && e->kids[0]->k == K::Field && e->kids[0]->kids[0]->k == K::Var && e->kids[0]->kids[0]->var == a;
}

// (a: T, b: U), parameters of one type grouped as a declaration writes them.
std::string params_of(const Program& p, const std::vector<VarId>& ps) {
    if (ps.empty()) return "";
    auto type = [&](VarId v) {
        const VarInfo& i = p.vars[v.v];
        return i.of_structure ? p.name(i.structure).text : i.bound ? p.show(i.bound) : std::string("type");
    };
    std::string s = "(";
    for (size_t i = 0; i < ps.size(); ++i) {
        s += (i ? ", " : "") + p.vars[ps[i].v].hint;
        if (i + 1 == ps.size() || type(ps[i + 1]) != type(ps[i])) s += ": " + type(ps[i]);
    }
    return s + ")";
}

std::string rule(const Program& p, const NameInfo& inst, const ComponentDef& def, const RuleDef& r) {
    std::set<VarId> bare{def.s, def.a};
    NodeP test, guard;
    if (is_input_test(r.when, def.a)) {
        test = r.when;
    } else if (r.when->k == K::And && is_input_test(r.when->kids[0], def.a)) {
        test = r.when->kids[0];
        guard = r.when->kids[1];
    } else if (r.when->k != K::True) {
        guard = r.when;
    }
    std::string s = "on " + (test ? p.field(test->kids[0]->field).label + " = " + p.show(test->kids[1], &bare) : "any");
    if (test && test->kids[1]->k == K::Case && inst.components.at(def.input).set->parts.size() == 1)
        s = "on " + p.show(test->kids[1], &bare);
    if (guard) s += " when " + p.show(guard, &bare);
    std::map<std::pair<bool, size_t>, std::string> said;
    const std::vector<FieldId>& state = inst.components.at(def.state).set->parts;
    const std::vector<FieldId>& output = inst.components.at(def.output).set->parts;
    for (size_t i = 0; i < state.size(); ++i) {
        const NodeP& v = r.next[i];
        bool kept = v->k == K::Field && v->field == state[i] && v->kids[0]->k == K::Var && v->kids[0]->var == def.s;
        if (!kept) said[{false, i}] = "next " + p.field(state[i]).label + " = " + p.show(v, &bare);
    }
    for (size_t i = 0; i < output.size(); ++i) said[{true, i}] = p.field(output[i]).label + " = " + p.show(r.out[i], &bare);
    // In the source's order where it gives one, the rest after it.
    std::vector<std::string> items;
    for (const auto& key : r.said)
        if (auto it = said.find(key); it != said.end()) {
            items.push_back(it->second);
            said.erase(it);
        }
    for (bool output_part : {false, true})
        for (const auto& [key, text] : said)
            if (key.first == output_part) items.push_back(text);
    return s + " \xe2\x86\x92 " + (items.empty() ? "unchanged" : join(items, " and "));
}

std::string instance(const Program& p, const Decl& d, const std::vector<Decl>& forms) {
    const Decl* form = nullptr;
    for (const Decl& f : forms)
        if (f.name == d.form) form = &f;
    if (!form) throw Error(d.pos, "no form '" + d.form + "'");
    const NameInfo& info = p.name(lookup(p, d.name));
    std::vector<FieldId> order = p.name(info.structure).fields;
    auto line = [&](FieldId f) {
        auto it = d.contents.find(p.field(f).label);
        return it == d.contents.end() ? std::pair{INT32_MAX, INT32_MAX} : std::pair{it->second.pos.line, it->second.pos.col};
    };
    std::stable_sort(order.begin(), order.end(), [&](FieldId a, FieldId b) { return line(a) < line(b); });
    std::string out = d.form + " " + d.name + params_of(p, info.params);
    for (FieldId f : order) {
        const ComponentDef& def = info.components.at(f);
        std::string keyword;
        for (const auto& [k, field] : form->renames)
            if (field == p.field(f).label) keyword = k;
        switch (def.kind) {
            case ComponentDef::Parts: {
                if (def.set->parts.empty()) break;
                std::vector<std::string> parts;
                for (size_t i = 0; i < def.set->parts.size(); ++i)
                    parts.push_back(p.field(def.set->parts[i]).label + " : " + p.show(def.set->kids[i]));
                out += "\n  " + keyword + " " + join(parts, ", ");
                break;
            }
            case ComponentDef::Condition: {
                std::set<VarId> bare{def.set->var};
                out += "\n  " + keyword + " " + p.show(def.set->kids[1], &bare);
                break;
            }
            case ComponentDef::Rules:
                for (const RuleDef& r : def.rules) out += "\n  " + rule(p, info, def, r);
                break;
        }
    }
    return out;
}

std::string declaration(Program& p, const Decl& d, const std::vector<Decl>& forms) {
    switch (d.kind) {
        case Decl::Use: return "use " + d.name;
        case Decl::Extern: return "extern " + d.name + params(d.params) + " = \"" + p.name(lookup(p, d.name)).fol + "\"";
        case Decl::ExternType: return "extern type " + d.name + " = \"" + p.name(lookup(p, d.name)).fol + "\"";
        case Decl::TypeAlias:
        case Decl::Define:
            return std::string(d.kind == Decl::Define ? "define " : "type ") + d.name + (d.params.empty() ? "" : params(d.params)) +
                   " = " + p.show(p.name(lookup(p, d.name)).body);
        case Decl::Enum: {
            NameId e = lookup(p, d.name);
            std::vector<std::pair<uint64_t, std::string>> cases;
            for (const NameInfo& n : p.names)
                if (n.is_case && n.enum_of == e) cases.push_back({n.body->num, n.text});
            std::sort(cases.begin(), cases.end());
            std::vector<std::string> names;
            for (const auto& c : cases) {
                if (c.first != names.size()) throw Error(d.pos, d.name + "'s case " + c.second + " is not its position");
                names.push_back(c.second);
            }
            const NodeP& body = p.name(e).body;
            if (!(body->k == K::Range && body->kids[0]->k == K::Num && body->kids[0]->num == 0 &&
                  body->kids[1]->k == K::Num && body->kids[1]->num == names.size()))
                throw Error(d.pos, d.name + " is not the set of its cases");
            return "type " + d.name + " = " + join(names, " | ");
        }
        case Decl::Instance: return instance(p, d, forms);
        case Decl::Theorem:
            for (const Theorem& t : p.theorems)
                if (t.name == d.name) return "theorem " + t.name + params_of(p, t.params) + ": " + p.show(t.claim);
            break;
        case Decl::Structure: {
            NameId sid = lookup(p, d.name);
            const NameInfo& st = p.name(sid);
            auto type = [&](size_t i) {
                const NodeP& t = p.field(st.fields[i]).type;
                return t ? p.show(t, nullptr, &sid) : std::string("type");
            };
            std::string out = "structure " + d.name + "(";
            for (size_t i = 0; i < d.params.size(); ++i) {
                out += (i ? ", " : "") + p.field(st.fields[i]).label;
                if (i + 1 == d.params.size() || type(i + 1) != type(i)) out += ": " + type(i);
            }
            out += ")";
            for (size_t i = d.params.size(); i < st.fields.size(); ++i)
                out += "\n  " + p.field(st.fields[i]).label + " : " + type(i);
            if (!st.conditions.empty()) out += "\n  where";
            for (const auto& [name, cond] : st.conditions) out += "\n    " + name + ": " + p.show(cond, nullptr, &sid);
            return out;
        }
        case Decl::FormAlias: {
            std::vector<std::string> renames;
            for (const auto& [keyword, field] : d.renames) renames.push_back(keyword + " for " + field);
            return "alias " + d.name + " = instance of " + d.structure + "\n  " + join(renames, ", ");
        }
    }
    throw Error(d.pos, "the renderer does not print this declaration yet");
}

}  // namespace

std::string render(Program& p, const Source& spec, const std::vector<Decl>& forms, const std::vector<FolClaim>& claims,
                   const std::string& claims_file) {
    Program hints = p;
    for (NameId i : p.instances) {
        p.names[i.v].components.clear();
        p.names[i.v].params.clear();
    }
    for (Theorem& t : p.theorems) {
        t.claim = nullptr;
        t.params.clear();
    }
    // An instance's parameters, read from the first of its claims; the others must agree.
    auto prefix = [&](Decompiler& d, const FP& f, NameId inst) {
        std::vector<VarId> got;
        std::vector<VarId>& est = p.names[inst.v].params;
        FP g = d.params(f, hints.name(inst).params, got, &est);
        if (est.empty()) est = got;
        return g;
    };

    struct Expected {
        enum Kind { Wellformed, Exists, Theorem } kind;
        NameId inst;
        FieldId field;
        size_t theorem = 0;
        bool seen = false;
    };
    const std::string ns = stem(spec.path);
    std::map<std::string, Expected> expected;
    for (NameId i : p.instances) {
        const NameInfo& info = p.name(i);
        expected[ns + "." + info.text + "_wellformed"] = {Expected::Wellformed, i, {}};
        for (FieldId f : p.name(info.structure).fields)
            expected[ns + "." + info.text + "_" + p.field(f).label + "_exists"] = {Expected::Exists, i, f};
    }
    for (size_t k = 0; k < p.theorems.size(); ++k) expected[ns + "." + p.theorems[k].name] = {Expected::Theorem, {}, {}, k};

    std::vector<std::string> said;
    for (const FolClaim& c : claims) {
        auto it = expected.find(c.name);
        if (it == expected.end()) throw Error({}, "the claim " + c.name + " is none the spec makes");
        Expected& e = it->second;
        if (e.seen) throw Error({}, "the claim " + c.name + " is made twice");
        e.seen = true;
        Decompiler d(p, hints);
        try {
            switch (e.kind) {
                case Expected::Wellformed: {
                    NodeP wf = d.formula(d.components(prefix(d, c.formula, e.inst), fields_of(p, e.inst)));
                    if (!same(wf, p.expand(p.wellformedness(e.inst))))
                        throw Error({}, "it says " + p.show(wf) + ", not that " + p.name(e.inst).text + " is well formed");
                    said.push_back(c.name + ": " + p.name(e.inst).text + " is well formed.");
                    break;
                }
                case Expected::Exists:
                    d.existence(d.components(prefix(d, c.formula, e.inst), deps(p, e.inst, e.field)), {e.inst, e.field});
                    said.push_back(c.name + ": the set " + comp_name(p, {e.inst, e.field}) + " exists.");
                    break;
                case Expected::Theorem: {
                    std::set<NameId> insts;
                    instances_in(hints.expand(hints.theorems[e.theorem].claim), insts);
                    std::vector<CompRef> comps;
                    const std::vector<VarId>* reuse = nullptr;
                    for (NameId i : p.instances)
                        if (insts.count(i)) {
                            for (const CompRef& r : fields_of(p, i)) comps.push_back(r);
                            if (!p.name(i).params.empty()) reuse = &p.names[i.v].params;
                        }
                    FP body = d.params(c.formula, hints.theorems[e.theorem].params, p.theorems[e.theorem].params, reuse);
                    p.theorems[e.theorem].claim = d.formula(d.components(body, comps));
                    said.push_back(c.name + ": the theorem " + p.theorems[e.theorem].name + ", below.");
                    break;
                }
            }
        } catch (const Error& err) {
            throw Error({}, "the claim " + c.name + ": " + err.what());
        }
    }
    for (const auto& [name, e] : expected)
        if (!e.seen) throw Error({}, "the claims lack " + name);

    Folder fold(p, hints);
    for (NameId i : p.instances)
        for (size_t k = 0; k < p.name(i).params.size() && k < hints.name(i).params.size(); ++k)
            fold.source_vars[hints.name(i).params[k]] = p.name(i).params[k];
    for (size_t t = 0; t < p.theorems.size(); ++t)
        for (size_t k = 0; k < p.theorems[t].params.size() && k < hints.theorems[t].params.size(); ++k)
            fold.source_vars[hints.theorems[t].params[k]] = p.theorems[t].params[k];
    for (NameId i : p.instances) fold.parts(i);
    for (NameId i : p.instances) fold.instance(i);
    for (size_t k = 0; k < p.theorems.size(); ++k) {
        p.theorems[k].claim = fold.fold(p.theorems[k].claim);
        std::map<VarId, VarId> bound;
        for (size_t i = 0; i < p.theorems[k].params.size() && i < hints.theorems[k].params.size(); ++i)
            bound[p.theorems[k].params[i]] = hints.theorems[k].params[i];
        p.theorems[k].claim = fold.respell(p.theorems[k].claim, hints.theorems[k].claim, bound);
        fold.name_binders(p.theorems[k].claim, hints.theorems[k].claim);
    }

    std::set<std::string> own;
    for (const Decl& d : spec.decls) own.insert(d.name);
    std::set<NameId> used;
    for (NameId i : p.instances) {
        uses_name(p, i, used);
        for (const auto& [f, def] : p.name(i).components) {
            if (def.set) uses(p, def.set, used);
            for (const RuleDef& r : def.rules) {
                uses(p, r.when, used);
                for (const NodeP& v : r.next) uses(p, v, used);
                for (const NodeP& v : r.out) uses(p, v, used);
            }
        }
    }
    for (const Theorem& t : p.theorems) uses(p, t.claim, used);
    std::vector<std::string> library;
    for (NameId id : used) {
        const NameInfo& n = p.name(id);
        if (!own.count(n.text) && !n.is_case) library.push_back(n.text);
    }
    for (const Decl& d : spec.decls)
        if (d.kind == Decl::Instance && !own.count(d.form) &&
            std::find(library.begin(), library.end(), d.form) == library.end())
            library.push_back(d.form);

    std::string out = claims_file.empty() ? "-- Printed by sysrender: the definitions as the language resolves them.\n"
                                          : "-- Read back by sysrender from " + claims_file + ": the spec as its checked claims say it.\n";
    for (const std::string& s : said) out += "-- " + s + "\n";
    if (!library.empty()) out += "-- Read with the library's " + join(library, ", ") + ".\n";
    out += "\n";
    for (const Decl& d : spec.decls) out += declaration(p, d, forms) + "\n";
    return out;
}

std::string difference(const std::string& source, const std::string& printed) {
    std::vector<Token> a = lex(source), b = lex(printed);
    for (size_t i = 0; i < a.size() && i < b.size(); ++i) {
        if (a[i].kind == b[i].kind && a[i].text == b[i].text) continue;
        auto at = [](const Token& t) { return std::to_string(t.pos.line) + ":" + std::to_string(t.pos.col); };
        auto text = [](const Token& t) { return t.kind == Tok::End ? std::string("the end") : "'" + t.text + "'"; };
        return "the source has " + text(a[i]) + " at " + at(a[i]) + ", the print " + text(b[i]) + " at " + at(b[i]);
    }
    return "";
}

}  // namespace sys2fol::render
