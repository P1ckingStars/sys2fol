#pragma once

#include <cstdint>
#include <functional>
#include <map>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "src/prove/tactics.h"

namespace sys2fol::prove {

enum class Family { canon, is_canon, below, distinct, num_cong, at, at_fun, at_cong, rec_ex, index_cases };

// A family of facts indexed by sizes, at its sizes: "at 4 3" in a project's lists (DESIGN.md §4).
struct Instance {
    Family family;
    std::vector<uint64_t> sizes;
    bool operator<(const Instance& o) const;
};
std::string base_name(const Instance& in);  // at_4_3
std::string to_line(const Instance& in);
Instance from_line(const std::string& line);

// The facts about numbers and records the spec's proofs cite: the library's (math/systems tuple_facts, natural_facts)
// when they hold for every spec, else instances, each written the first time a proof asks. With a project, an instance
// is the project's: its specs' runs state and list it, and the project's run (prove_instances) proves it.
class Lemmas {
public:
    Lemmas(std::string ns, std::map<std::string, FmP>& known, std::string project = "", bool prove_instances = false)
        : ns_(std::move(ns)), known_(known), project_(std::move(project)), prove_instances_(prove_instances) {}

    std::string canon(uint64_t c);               // chain(c, z => z_c is the numeral c)
    std::string is_canon(uint64_t c);            // a numeral c is z_c of every chain
    std::string below(uint64_t c, uint64_t d);   // c < d: z_c in z_d
    std::string distinct(uint64_t c, uint64_t d);  // c < d: not z_c = z_d
    std::string num_cong(uint64_t c);            // x = y and x the numeral c: y the numeral c
    std::string at(size_t k, size_t i);          // a record's part i is its entry i
    std::string at_fun(size_t k, size_t i);      // ... and no other
    std::string at_cong(size_t i);               // equal records have equal parts
    std::string rec_ex(size_t k);                // every k values make a record
    std::string index_cases(size_t k);           // an index below z_k is one of z_0, ..., z_(k-1)

    std::string pmem_cong1() const { return "g3_pmem_cong1"; }  // the foundation's
    std::string pmem_cong2() const { return "Sys.pmem_cong2"; }
    std::string pmem_cong3() const { return "Sys.pmem_cong3"; }
    std::string tuple_cong1() const { return "Sys.tuple_cong1"; }
    std::string tuple_cong2() const { return "Sys.tuple_cong2"; }
    std::string nsucc_cong2() const { return "Sys.nsucc_cong2"; }
    std::string len_uniq() const { return "Sys.tuple_length_unique"; }
    std::string empty_tuple() const { return "Sys.tuple_length_zero"; }
    std::string pair_pow() const { return "Sys.kpair_pow"; }
    std::string tuple_pow() const { return "Sys.tuple_pow"; }
    std::string nat_cong() const { return "Sys.natural_cong"; }
    std::string natural_zero() const { return "Sys.natural_zero"; }
    std::string natural_succ() const { return "Sys.natural_succ"; }
    std::string natural_elem() const { return "Sys.natural_elem"; }
    std::string natural_pred() const { return "Sys.natural_pred"; }
    std::string natural_index() const { return "Sys.natural_index"; }
    std::string zero_or_succ() const { return "Sys.natural_zero_or_succ"; }
    std::string trichotomy() const { return "Sys.natural_trichotomy"; }
    std::string succ_le() const { return "Sys.natural_succ_le"; }
    std::string pred_le() const { return "Sys.natural_pred_le"; }
    std::string zero_le() const { return "Sys.natural_zero_le"; }
    std::string first_ex() const { return "Sys.tuple_first"; }
    std::string rest_ex() const { return "Sys.tuple_rest"; }

    // A fact about one of the spec's own definitions, proved by `proof`, made the first time a proof asks for it.
    std::string own(const std::string& base, const std::function<FmP()>& statement, const std::function<H(Tac&)>& proof) {
        return make(ns_ + ".lemma." + base, statement, proof);
    }

    std::string prove_instance(const Instance& in);
    const std::set<Instance>& needs() const { return needs_; }
    std::string header() const;
    const std::string& proofs() const { return proofs_; }

private:
    std::string ns_;
    std::map<std::string, FmP>& known_;
    std::string project_;
    bool prove_instances_;
    std::set<Instance> needs_;
    std::map<std::string, bool> made_;
    std::vector<std::pair<std::string, FmP>> claims_;
    std::string proofs_;

    std::string instance(const Instance& in, const std::function<FmP()>& statement,
                         const std::function<H(Tac&)>& proof);
    std::string make(const std::string& name, const std::function<FmP()>& statement,
                     const std::function<H(Tac&)>& proof);
};

// Tactics on numeral chains, shared by the lemmas and the claims' proofs.
// (forall z0. (set(z0) -> (zero(z0) -> ... body))): k + 1 numerals, as enc::chain writes them.
H intro_chain(Tac& t, size_t k, const std::function<H(const std::vector<std::string>&, const std::vector<H>&)>& body);
// A chain fact used at numerals zs, guards their zero and nsucc steps.
H use_chain(Tac& t, H h, const std::vector<std::string>& zs, const std::vector<H>& guards);
// Numerals z0, ..., zk obtained from zero_EX and nsucc_EX around body.
H canonical(Tac& t, size_t k, const std::function<H(const std::vector<std::string>&, const std::vector<H>&)>& body);
// eq(a_i, b_i) for each i <= k, a and b two chains.
std::vector<H> chains_equal(Tac& t, const std::vector<std::string>& a, const std::vector<H>& ga,
                            const std::vector<std::string>& b, const std::vector<H>& gb);
// From nsucc(n, m): forall x. (set(x) -> (elem(x, m) <-> (elem(x, n) | eq(x, n)))).
H succ_unfold(Tac& t, const std::string& n, const std::string& m, H g);
// The disjunct at position j of a right-nested disjunction, from a step proving it.
H inject(Tac& t, H h, const std::vector<FmP>& disjuncts, size_t j);
H refl(Tac& t, const std::string& x);
// psi with x replaced by y, from psi and eq(x, y): each atom moved by its congruence, the rest by the connectives' rules.
H transport(Tac& t, Lemmas& lm, const std::string& x, const std::string& y, H exy, H psi);

}  // namespace sys2fol::prove
