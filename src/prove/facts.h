#pragma once

#include <functional>
#include <map>
#include <optional>
#include <set>
#include <string>
#include <vector>

#include "src/prove/tactics.h"

namespace sys2fol::prove {

// The steps a proof holds at a point, and proofs of formulas from them: each existential's witness is found by matching
// the formula against the steps, the rest built by the connectives' rules.
class Facts {
public:
    explicit Facts(Tac& t) : t_(t) {}

    void add(H h);
    // The steps added since mark(), dropped when their scope closes.
    size_t mark() const { return facts_.size(); }
    void reset(size_t m) { facts_.resize(m); }

    bool provable(const FmP& f);
    // f proved from the steps; throws if no proof is found.
    H prove(const FmP& f);
    // A step (~ x) whose x is provable: false.
    std::optional<H> contradiction();
    // The witnesses that make the existential f's body provable, and f itself from them.
    std::optional<std::string> witness_of(const FmP& f);
    const std::vector<H>& all() const { return facts_; }

private:
    using Sub = std::map<std::string, std::string>;
    Tac& t_;
    std::vector<H> facts_;
    std::set<std::string> open_;

    bool plan(const FmP& f, const Sub& s, const std::function<bool(const Sub&)>& k, int depth);
    bool unify(const FmP& p, const FmP& g, Sub& s, std::map<std::string, std::string>& bound) const;
    std::string resolve(const Sub& s, const std::string& x) const;
    std::optional<H> known(const FmP& f) const;
};

}  // namespace sys2fol::prove
