#include "src/prove/proof.h"

#include <algorithm>
#include <optional>
#include <stdexcept>

namespace sys2fol::prove {

Proof::Proof(std::string claim, const std::map<std::string, FmP>& known) : claim_(std::move(claim)), known_(known) {
    out_ = "proof " + claim_ + ":\n";
}

void Proof::fail(const std::string& what) const {
    throw std::runtime_error("the proof of " + claim_ + ", step " + std::to_string(steps_.size() + 1) + ": " + what);
}

void Proof::check(H h, const char* rule) const {
    if (h.id < 0 || h.id >= static_cast<int>(steps_.size())) fail(std::string(rule) + " of a step that is not there");
    for (int d : steps_[h.id].deps) {
        bool open = false;
        for (const Scope& s : scopes_) open = open || s.id == d;
        if (!open) fail(std::string(rule) + " of " + name(h) + ", which depends on a closed scope");
    }
}

std::set<int> Proof::var_deps(const FmP& f) const {
    std::set<int> out;
    for (const std::string& v : free_vars(f))
        if (auto it = var_scope_.find(v); it != var_scope_.end()) out.insert(it->second);
    return out;
}

namespace {

// f's text with each bound variable named by its depth, so alpha-equal formulas read alike.
void shape(const FmP& f, std::map<std::string, int>& bound, int depth, std::string& out) {
    switch (f->k) {
        case Fm::Atom:
            out += f->name + "(";
            for (const std::string& a : f->args) {
                auto it = bound.find(a);
                out += it == bound.end() ? a : "#" + std::to_string(it->second);
                out += ",";
            }
            out += ")";
            return;
        case Fm::False: out += "F"; return;
        case Fm::Not:
            out += "~";
            shape(f->a, bound, depth, out);
            return;
        case Fm::Forall:
        case Fm::Exists: {
            auto old = bound.find(f->name);
            std::optional<int> saved;
            if (old != bound.end()) saved = old->second;
            bound[f->name] = depth;
            out += f->k == Fm::Forall ? "A." : "E.";
            shape(f->a, bound, depth + 1, out);
            if (saved) bound[f->name] = *saved;
            else bound.erase(f->name);
            return;
        }
        default:
            out += "(";
            shape(f->a, bound, depth, out);
            out += f->k == Fm::And ? "&" : f->k == Fm::Or ? "|" : f->k == Fm::Imp ? ">" : "=";
            shape(f->b, bound, depth, out);
            out += ")";
    }
}

}  // namespace

bool Proof::live(int id) const {
    for (int d : steps_[id].deps) {
        bool open = false;
        for (const Scope& s : scopes_) open = open || s.id == d;
        if (!open) return false;
    }
    return true;
}

H Proof::derive(FmP f, std::set<int> deps, const std::string& line, Write w) {
    for (int d : var_deps(f)) deps.insert(d);
    std::string key;
    if (w != Write::Let) {
        std::map<std::string, int> bound;
        shape(f, bound, 0, key);
    }
    if (w == Write::Reuse)
        if (auto it = have_.find(key); it != have_.end() && live(it->second)) {
            const std::set<int>& d = steps_[it->second].deps;
            if (std::includes(deps.begin(), deps.end(), d.begin(), d.end())) return H{it->second};
        }
    H h{static_cast<int>(steps_.size())};
    steps_.push_back({std::move(f), std::move(deps)});
    out_ += "    " + name(h) + " = " + line + "\n";
    if (w != Write::Let) have_[key] = h.id;
    return h;
}

const Proof::Scope& Proof::top(Scope::Kind kind, const char* rule) const {
    if (scopes_.empty() || scopes_.back().kind != kind) fail(std::string(rule) + " with no scope of its kind open");
    return scopes_.back();
}

// Pops the top scope; h's dependencies without it.
std::set<int> Proof::close(H h) {
    std::set<int> deps = steps_[h.id].deps;
    deps.erase(scopes_.back().id);
    if (!scopes_.back().var.empty()) var_scope_.erase(scopes_.back().var);
    scopes_.pop_back();
    return deps;
}

void Proof::fix(const std::string& x) {
    if (var_scope_.count(x)) fail("fix " + x + " twice");
    scopes_.push_back({Scope::Fix, next_scope_++, x, nullptr});
    var_scope_[x] = scopes_.back().id;
    out_ += "    fix " + x + "\n";
}

H Proof::assume(FmP f) {
    for (const std::string& v : free_vars(f))
        if (!var_scope_.count(v)) fail("assume of a formula with " + v + " free and not in scope");
    scopes_.push_back({Scope::Assume, next_scope_++, "", f});
    return derive(f, {scopes_.back().id}, "assume " + print(f), Write::Always);
}

H Proof::let(FmP f) { return derive(f, {}, "let " + print(f), Write::Let); }

H Proof::use(const std::string& n) {
    auto it = known_.find(n);
    if (it == known_.end()) fail("use of " + n + ", which is not known");
    return derive(it->second, {}, "use " + n);
}

H Proof::implies_intro(H c) {
    check(c, "implies_intro");
    FmP a = top(Scope::Assume, "implies_intro").formula;
    FmP f = imp(a, fm(c));
    std::string line = "implies_intro " + name(c);
    return derive(f, close(c), line, Write::Always);
}

H Proof::not_intro(H bot) {
    check(bot, "not_intro");
    if (fm(bot)->k != Fm::False) fail("not_intro of " + name(bot) + ", which is not false");
    FmP a = top(Scope::Assume, "not_intro").formula;
    std::string line = "not_intro " + name(bot);
    return derive(neg(a), close(bot), line, Write::Always);
}

H Proof::classical_absurd(H bot) {
    check(bot, "classical_absurd");
    if (fm(bot)->k != Fm::False) fail("classical_absurd of a step that is not false");
    FmP a = top(Scope::Assume, "classical_absurd").formula;
    if (a->k != Fm::Not) fail("classical_absurd under an assumption that is not a negation");
    std::string line = "classical_absurd " + name(bot);
    return derive(a->a, close(bot), line, Write::Always);
}

H Proof::forall_intro(H b) {
    check(b, "forall_intro");
    std::string x = top(Scope::Fix, "forall_intro").var;
    FmP f = forall(x, fm(b));
    std::string line = "forall_intro " + name(b);
    return derive(f, close(b), line, Write::Always);
}

std::pair<std::string, H> Proof::exists_elim(H ex, const std::string& hint) {
    check(ex, "exists_elim");
    const FmP& f = fm(ex);
    if (f->k != Fm::Exists) fail("exists_elim of " + name(ex) + ", which is no exists");
    std::string w = fresh(hint);
    scopes_.push_back({Scope::Exists, next_scope_++, w, nullptr});
    var_scope_[w] = scopes_.back().id;
    std::set<int> deps = steps_[ex.id].deps;
    deps.insert(scopes_.back().id);
    H h = derive(subst(f->a, {{f->name, w}}), deps, "exists_elim " + name(ex) + ", " + w, Write::Always);
    return {w, h};
}

H Proof::exists_close(H c) {
    check(c, "exists_intro");
    std::string w = top(Scope::Exists, "exists_intro").var;
    if (free_vars(fm(c)).count(w)) fail("exists_intro of " + name(c) + ", which mentions the witness " + w);
    FmP f = fm(c);
    std::string line = "exists_intro " + name(c);
    return derive(f, close(c), line, Write::Always);
}

H Proof::forall_elim(H h, const std::string& t) {
    check(h, "forall_elim");
    const FmP& f = fm(h);
    if (f->k != Fm::Forall) fail("forall_elim of " + name(h) + ", which is no forall: " + print(f).substr(0, 200));
    if (!var_scope_.count(t)) fail("forall_elim at " + t + ", which is not in scope");
    return derive(subst(f->a, {{f->name, t}}), steps_[h.id].deps, "forall_elim " + name(h) + ", " + t);
}

H Proof::implies_elim(H i, H a) {
    check(i, "implies_elim");
    check(a, "implies_elim");
    const FmP& f = fm(i);
    if (f->k != Fm::Imp) fail("implies_elim of " + name(i) + ", which is no implication");
    if (!alpha_eq(f->a, fm(a)))
        fail("implies_elim: " + name(a) + " is " + print(fm(a)).substr(0, 300) + ", not " + print(f->a).substr(0, 300));
    std::set<int> deps = steps_[i.id].deps;
    deps.insert(steps_[a.id].deps.begin(), steps_[a.id].deps.end());
    return derive(f->b, deps, "implies_elim " + name(i) + ", " + name(a));
}

H Proof::and_intro(H a, H b) {
    check(a, "and_intro");
    check(b, "and_intro");
    std::set<int> deps = steps_[a.id].deps;
    deps.insert(steps_[b.id].deps.begin(), steps_[b.id].deps.end());
    return derive(conj(fm(a), fm(b)), deps, "and_intro " + name(a) + ", " + name(b));
}

H Proof::and_l(H h) {
    check(h, "and_elim_l");
    if (fm(h)->k != Fm::And) fail("and_elim_l of " + name(h) + ", which is no conjunction");
    return derive(fm(h)->a, steps_[h.id].deps, "and_elim_l " + name(h));
}

H Proof::and_r(H h) {
    check(h, "and_elim_r");
    if (fm(h)->k != Fm::And) fail("and_elim_r of " + name(h) + ", which is no conjunction");
    return derive(fm(h)->b, steps_[h.id].deps, "and_elim_r " + name(h));
}

H Proof::or_intro_l(H a, FmP b) {
    check(a, "or_intro_l");
    H l = let(b);
    return derive(disj(fm(a), b), steps_[a.id].deps, "or_intro_l " + name(a) + ", " + name(l));
}

H Proof::or_intro_r(FmP a, H b) {
    check(b, "or_intro_r");
    H l = let(a);
    return derive(disj(a, fm(b)), steps_[b.id].deps, "or_intro_r " + name(l) + ", " + name(b));
}

H Proof::or_elim(H o, H ac, H bc) {
    for (H h : {o, ac, bc}) check(h, "or_elim");
    const FmP &f = fm(o), &x = fm(ac), &y = fm(bc);
    if (f->k != Fm::Or || x->k != Fm::Imp || y->k != Fm::Imp || !alpha_eq(f->a, x->a) || !alpha_eq(f->b, y->a) ||
        !alpha_eq(x->b, y->b))
        fail("or_elim of " + name(o) + " by " + name(ac) + " and " + name(bc) + ", which do not fit");
    std::set<int> deps;
    for (H h : {o, ac, bc}) deps.insert(steps_[h.id].deps.begin(), steps_[h.id].deps.end());
    return derive(x->b, deps, "or_elim " + name(o) + ", " + name(ac) + ", " + name(bc));
}

H Proof::not_elim(H n, H a) {
    check(n, "not_elim");
    check(a, "not_elim");
    if (fm(n)->k != Fm::Not || !alpha_eq(fm(n)->a, fm(a)))
        fail("not_elim: " + name(n) + " is not the negation of " + name(a) + ": " + print(fm(n)).substr(0, 300) + " / " +
             print(fm(a)).substr(0, 300));
    std::set<int> deps = steps_[n.id].deps;
    deps.insert(steps_[a.id].deps.begin(), steps_[a.id].deps.end());
    return derive(falsum(), deps, "not_elim " + name(n) + ", " + name(a));
}

H Proof::bottom_elim(H bot, FmP f) {
    check(bot, "bottom_elim");
    if (fm(bot)->k != Fm::False) fail("bottom_elim of a step that is not false");
    H l = let(f);
    return derive(f, steps_[bot.id].deps, "bottom_elim " + name(bot) + ", " + name(l));
}

H Proof::iff_intro(H ab, H ba) {
    check(ab, "iff_intro");
    check(ba, "iff_intro");
    const FmP &x = fm(ab), &y = fm(ba);
    if (x->k != Fm::Imp || y->k != Fm::Imp || !alpha_eq(x->a, y->b) || !alpha_eq(x->b, y->a))
        fail("iff_intro of " + name(ab) + " and " + name(ba) + ", which are not converse");
    std::set<int> deps = steps_[ab.id].deps;
    deps.insert(steps_[ba.id].deps.begin(), steps_[ba.id].deps.end());
    return derive(iff(x->a, x->b), deps, "iff_intro " + name(ab) + ", " + name(ba));
}

H Proof::iff_l(H i, H a) {
    check(i, "iff_elim_l");
    check(a, "iff_elim_l");
    if (fm(i)->k != Fm::Iff || !alpha_eq(fm(i)->a, fm(a)))
        fail("iff_elim_l: " + name(a) + " is " + print(fm(a)).substr(0, 300) + ", not the left of " +
             print(fm(i)).substr(0, 300));
    std::set<int> deps = steps_[i.id].deps;
    deps.insert(steps_[a.id].deps.begin(), steps_[a.id].deps.end());
    return derive(fm(i)->b, deps, "iff_elim_l " + name(i) + ", " + name(a));
}

H Proof::iff_r(H i, H b) {
    check(i, "iff_elim_r");
    check(b, "iff_elim_r");
    if (fm(i)->k != Fm::Iff || !alpha_eq(fm(i)->b, fm(b)))
        fail("iff_elim_r: " + name(b) + " is " + print(fm(b)).substr(0, 300) + ", not the right of " +
             print(fm(i)).substr(0, 300));
    std::set<int> deps = steps_[i.id].deps;
    deps.insert(steps_[b.id].deps.begin(), steps_[b.id].deps.end());
    return derive(fm(i)->a, deps, "iff_elim_r " + name(i) + ", " + name(b));
}

H Proof::exists_intro(H body, const std::string& witness) {
    check(body, "exists_intro");
    if (!var_scope_.count(witness)) fail("exists_intro at " + witness + ", which is not in scope");
    return derive(generalize(fm(body), witness), steps_[body.id].deps, "exists_intro " + name(body) + ", " + witness);
}

H Proof::ex_intro(FmP target, const std::string& t, H body) {
    check(body, "ex_intro");
    if (target->k != Fm::Exists) fail("ex_intro of a target that is no exists");
    if (!var_scope_.count(t)) fail("ex_intro at " + t + ", which is not in scope");
    const std::string& y = target->name;
    std::string z = fresh("_b");
    FmP inst = forall(z, imp(subst(target->a, {{y, z}}), target));
    for (const std::string& v : free_vars(target))
        if (!var_scope_.count(v)) fail("ex_intro of a target with " + v + " free and not in scope");
    if (alpha_eq(generalize(fm(body), t), target)) return exists_intro(body, t);
    H s = derive(inst, {}, "schema_inst ex_intro { P: \\" + y + ". " + print(target->a) + " }");
    H e = forall_elim(s, t);
    return implies_elim(e, body);
}

H Proof::eq_sym(H h) {
    check(h, "eq_sym");
    const FmP& f = fm(h);
    if (f->k != Fm::Atom || f->name != "eq" || f->args.size() != 2) fail("eq_sym of a step that is no eq");
    return derive(atom("eq", {f->args[1], f->args[0]}), steps_[h.id].deps, "eq_sym " + name(h));
}

H Proof::excluded_middle(FmP f) {
    H l = let(f);
    return derive(disj(f, neg(f)), {}, "excluded_middle " + name(l));
}

H Proof::double_neg_elim(H h) {
    check(h, "double_neg_elim");
    if (fm(h)->k != Fm::Not || fm(h)->a->k != Fm::Not) fail("double_neg_elim of a step that is no double negation");
    return derive(fm(h)->a->a, steps_[h.id].deps, "double_neg_elim " + name(h));
}

void Proof::qed(H h) {
    check(h, "qed");
    if (!scopes_.empty()) fail("qed with scopes open");
    out_ += "    qed " + name(h) + "\n";
}

}  // namespace sys2fol::prove
