#pragma once

#include <cstdint>
#include <functional>
#include <map>
#include <string>
#include <utility>
#include <vector>

#include "src/prove/tactics.h"

namespace sys2fol::prove {

// The facts about numbers, records and the spec's steps its proofs cite, each a claim with its proof, written the first
// time a proof asks for it. They are the spec's own, under its namespace: the library's equivalents wait for isa2fol.
class Lemmas {
public:
    Lemmas(std::string ns, std::map<std::string, FmP>& known) : ns_(std::move(ns)), known_(known) {}

    std::string canon(uint64_t c);               // chain(c, z => z_c is the numeral c)
    std::string is_canon(uint64_t c);            // a numeral c is z_c of every chain
    std::string below(uint64_t c, uint64_t d);   // c < d: z_c in z_d
    std::string distinct(uint64_t c, uint64_t d);  // c < d: not z_c = z_d
    std::string num_cong(uint64_t c);            // x = y and x the numeral c: y the numeral c
    std::string at(size_t k, size_t i);          // a record's part i is its entry i
    std::string at_fun(size_t k, size_t i);      // ... and no other
    std::string at_cong(size_t i);               // equal records have equal parts
    std::string pmem_cong1();
    std::string tuple_cong2();
    std::string rec_ex(size_t k);                // every k values make a record
    std::string index_cases(size_t k);           // an index below z_k is one of z_0, ..., z_(k-1)
    std::string pair_pow();                      // a pair of members of W is in Pow(Pow(W))
    std::string tuple_pow();                     // a tuple with indices and entries in W is in Pow(Pow(Pow(W)))
    // Natural numbers, from the translated ZF library through Sys.natural_nat.
    std::string nat_cong();                      // eq(n, m) and n natural: m natural
    std::string natural_succ();                  // n natural, nsucc(n, m): m natural
    std::string natural_elem();                  // n natural, m in n: m natural
    std::string natural_pred();                  // n natural, nsucc(m, n): m natural
    std::string natural_zero();
    std::string natural_index();
    std::string nsucc_cong2();                   // eq(m, m2), nsucc(n, m): nsucc(n, m2)
    // n natural: zero(n) or n a successor, from `cases`, the class machine's set { w | zero(w) or w a successor }.
    std::string zero_or_succ(const std::string& cases);
    std::string trichotomy();                    // m, c natural: m in c, m = c or c in m
    std::string succ_le();                       // m < c, nsucc(m, s): s <= c
    std::string pred_le();                       // nsucc(m, n), n <= c: m <= c
    std::string zero_le();                       // zero(z), c natural: z <= c
    // Sequences: a tuple has one length; equals carry into tuple and pmem.
    std::string len_uniq();
    std::string tuple_cong1();
    std::string pmem_cong2();
    std::string pmem_cong3();
    std::string empty_tuple();                   // tuple(v, n), zero(n): zero(v)
    std::string first_ex();                      // tuple(v, n), n natural and not 0: v has an entry at 0
    // tuple(v, n), nsucc(m, n), n natural: v's rest, its entries shifted down by one, from `pairs`, the class machine's
    // set { w in B | w = <i, y>, <i + 1, y> in v }.
    std::string rest_ex(const std::string& pairs);

    // A fact about one of the spec's own definitions, proved by `proof`, made the first time a proof asks for it.
    std::string own(const std::string& base, const std::function<FmP()>& statement, const std::function<H(Tac&)>& proof) {
        return make(base, statement, proof);
    }

    std::string header() const;
    const std::string& proofs() const { return proofs_; }

private:
    std::string ns_;
    std::map<std::string, FmP>& known_;
    std::map<std::string, bool> made_;
    std::vector<std::pair<std::string, FmP>> claims_;
    std::string proofs_;

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
