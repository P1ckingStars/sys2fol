#pragma once

#include <map>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "src/prove/formula.h"

namespace sys2fol::prove {

// A step of a proof.
struct H {
    int id = -1;
};

// One fol-zfc proof, written step by step. Each rule computes what the checker will derive and the scopes it depends
// on, so a misused step fails here, named, before proof_checker sees it.
// A step whose formula a live earlier step derived, on no scope it lacks, is that step.
class Proof {
public:
    Proof(std::string claim, const std::map<std::string, FmP>& known);

    void fix(const std::string& x);
    H assume(FmP f);
    H let(FmP f);
    H use(const std::string& name);
    H implies_intro(H conclusion);
    H not_intro(H bottom);
    H classical_absurd(H bottom);
    H forall_intro(H body);
    // exists_elim: the witness and what it satisfies, in a scope exists_close ends.
    std::pair<std::string, H> exists_elim(H ex, const std::string& hint);
    H exists_close(H conclusion);

    H forall_elim(H h, const std::string& t);
    H implies_elim(H imp, H ant);
    H and_intro(H a, H b);
    H and_l(H h);
    H and_r(H h);
    H or_intro_l(H a, FmP b);
    H or_intro_r(FmP a, H b);
    H or_elim(H o, H ac, H bc);
    H not_elim(H negation, H a);
    H bottom_elim(H bottom, FmP f);
    H iff_intro(H ab, H ba);
    H iff_l(H iff, H a);
    H iff_r(H iff, H b);
    H exists_intro(H body, const std::string& witness);
    // `target`, (exists y. psi(y)), from psi(t), by base's schema ex_intro: only y's own positions are t.
    H ex_intro(FmP target, const std::string& t, H body);
    H eq_sym(H h);
    H excluded_middle(FmP f);
    H double_neg_elim(H h);
    void qed(H h);

    FmP fm(H h) const { return steps_.at(h.id).f; }
    // An open variable: fixed, or an exists_elim witness.
    bool in_scope(const std::string& x) const { return var_scope_.count(x) > 0; }
    std::string text() const { return out_; }
    size_t size() const { return steps_.size(); }

private:
    struct Scope {
        enum Kind { Fix, Assume, Exists } kind;
        int id;
        std::string var;
        FmP formula;
    };
    struct Step {
        FmP f;
        std::set<int> deps;
    };
    enum class Write { Reuse, Always, Let };

    std::string claim_;
    const std::map<std::string, FmP>& known_;
    std::vector<Scope> scopes_;
    std::vector<Step> steps_;
    std::map<std::string, int> var_scope_;
    std::string out_;
    int next_scope_ = 0;
    std::map<std::string, int> have_;

    [[noreturn]] void fail(const std::string& what) const;
    void check(H h, const char* rule) const;
    H derive(FmP f, std::set<int> deps, const std::string& line, Write w = Write::Reuse);
    bool live(int id) const;
    std::set<int> var_deps(const FmP& f) const;
    std::string name(H h) const { return "_h" + std::to_string(h.id + 1); }
    const Scope& top(Scope::Kind kind, const char* rule) const;
    std::set<int> close(H h);
};

}  // namespace sys2fol::prove
