#pragma once

#include <map>
#include <memory>
#include <set>
#include <string>
#include <vector>

namespace sys2fol::prove {

// A fol-zfc formula with named variables. Forall and Exists are the plain quantifiers; their set guards are atoms.
struct Fm;
using FmP = std::shared_ptr<const Fm>;

struct Fm {
    enum K { Atom, False, Not, And, Or, Imp, Iff, Forall, Exists };
    K k;
    std::string name;               // Atom: the predicate; Forall, Exists: the bound variable
    std::vector<std::string> args;  // Atom
    FmP a, b;
};

FmP atom(const std::string& p, std::vector<std::string> args);
FmP falsum();
FmP neg(FmP a);
FmP conj(FmP a, FmP b);
FmP disj(FmP a, FmP b);
FmP imp(FmP a, FmP b);
FmP iff(FmP a, FmP b);
FmP forall(const std::string& x, FmP body);
FmP exists(const std::string& x, FmP body);
// (forall x. (set(x) -> body)) and (exists x. (set(x) & body)), as fol-zfc guards a quantifier over sets.
FmP all(const std::string& x, FmP body);
FmP some(const std::string& x, FmP body);
FmP is_set(const std::string& x);
// Right-nested, as the writer folds: a0 op (a1 op (... op an)).
FmP conj(const std::vector<FmP>& xs);
FmP disj(const std::vector<FmP>& xs);

std::string print(const FmP& f);
std::set<std::string> free_vars(const FmP& f);
// Free variables replaced by `m`; a binder that would capture is renamed.
FmP subst(const FmP& f, const std::map<std::string, std::string>& m);
bool alpha_eq(const FmP& a, const FmP& b);
// Every occurrence of the free variable `t` replaced by the bound variable of a new `exists`, as exists_intro does.
FmP generalize(const FmP& body, const std::string& t);

std::string fresh(const std::string& hint);

// The claims and axioms of a fol-zfc header, in order, read by fol-zfc's own parser.
std::vector<std::pair<std::string, FmP>> read_statements(const std::string& text, bool claims_only);

}  // namespace sys2fol::prove
