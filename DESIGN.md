# sys2fol design

sys2fol turns specifications of systems into fol-zfc claims and their proofs. fol-zfc checks every proof
(`~/repos/fol-zfc-comb`) over the NBG library (`~/repos/fol-zfc-comb-lib`: Isabelle/ZF translated by isa2fol); ai-fol
searches for proofs (`~/repos/ai-fol`); rtl2fol turns hardware into claims (`~/repos/rtl2fol`). Only sys2fol knows about
specifications.

## 1. Pipeline

A spec and its proof sketch → the statement compiler → a fol-zfc claim; the proof compiler → obligations → machines →
fol-zfc steps → `proof_checker`.

## 2. Two compilers

| | Produces | Trust |
|---|---|---|
| Statement compiler | the claim | trusted for meaning: small, one translation per construct, and a renderer that prints a claim back in spec syntax for review |
| Proof compiler | obligations, machine calls, steps | untrusted: everything it emits is checked |

A wrong statement compiler proves the wrong claim and every proof still checks, so it stays small enough to review.

## 3. Meaning

A system is a coalgebra `c: S → F(S)` on a set `S`. A Mealy machine with inputs `A` and outputs `B` has
`F(X) = (X×B)^A`: `next(s, a)` and `out(s, a)`, relations in fol-zfc, which has no function symbols.

| Notion | NBG |
|---|---|
| reachable states Q | the least invariant containing the initial states |
| safety | `Q ⊆ P`, proved by an invariant I with `Init ⊆ I ⊆ P` and I closed under steps |
| bisimulation | any `R ⊆ Φ(R)`, where `Φ(R) = {(s,t) | ∀a. out(s,a) = out(t,a) ∧ (next(s,a), next(t,a)) ∈ R}` |
| bisimilarity | `gfp(S×S, Φ)` |
| behaviour | a state's image in the final coalgebra: for Mealy machines, the causal functions `A⁺ → B` |
| refinement | a simulation `R ⊆ S_impl × S_spec`: each implementation step is matched by a spec step, with equal outputs and related successors |

Safety, equivalence and refinement are each a post-fixpoint of a monotone operator: a proof is a witness (I or R) and a
one-step check.

## 4. Library

A system feature of the language is a claim proved once and cited, its class variables instantiated; none is a checker
rule.

| Layer | Holds | State |
|---|---|---|
| lattice | Knaster–Tarski: `Fixedpt.lfp`, `gfp`, `induct`, `coinduct`, `gfp_unfold` | in `@zf//:ZF.Fixedpt` |
| Mealy | the invariance rule, bisimilarity as `gfp`, the final coalgebra, simulation, composition | to build |
| generic | the same for every functor F, F a class | to build |
| theory steps | one lemma per kind of solver step (Farkas for linear arithmetic, ...) | to build |

## 5. Machines

As in ai-fol (`DECODER.md` D22): a machine takes a goal and offers one next state with the fol-zfc steps that reach it.

| Machine | Offers | Steps from |
|---|---|---|
| SAT | a propositional obligation closed | CaDiCaL's LRAT proof, RUP steps only, as resolution steps |
| IC3 / PDR | an inductive invariant, or a counterexample | the invariant's three SAT-checked obligations (initial, step, property) and the invariance rule |
| k-induction, BMC | a proof or a counterexample | SAT obligations |
| SMT | a theory obligation closed | cvc5's proof, each theory step citing its library lemma |
| explicit-state explorer | a counterexample on rich data | the trace, checked by evaluation |
| AI (ai-fol) | an invariant, a refinement mapping, a lemma split, a citation | whatever the obligations it creates close with |

The user writes the spec, its structure, key invariants and citations; AI proposes what is missing; solvers close what
they decide; the checker accepts only steps.

## 6. From TLA+

Taken as semantics, not syntax: stuttering invariance, so an implementation with more steps than its spec can refine
it; implementation as implication; fairness conjoined without constraining safety (machine closure); refinement
mappings as the witness of a refinement. Started from its gaps: composition with interfaces, types, and links to
implementations (RTL through rtl2fol, code).

## 7. First milestone

The invariance rule and bisimilarity as `gfp` for Mealy machines, proved over `ZF.Fixedpt`; then one small spec, its
claim emitted, its invariant given as the cut, every proof on `proof_checker`'s Proved list.

## 8. Not now

The language's syntax, liveness and fairness, the generic layer, up-to techniques, SMT theory steps beyond bit-vectors,
LRAT's RAT steps.

## 9. Open, for the user

- What a spec is in NBG: a coalgebra on a set, a set of behaviours, or both, linked by the final map.
- The core constructs, and stuttering, fairness and composition.
- Where the systems library lives: here, or in fol-zfc-comb-lib's `math/`.
- The Mealy layer first, or the generic layer first.
- A counterexample: checked by evaluation, or proved in fol-zfc as the claim's negation.
- rtl2fol: a front end of sys2fol, or a separate pipeline.
- The machine interface's exact form, shared with ai-fol and rtl2fol.

Tools needed: CaDiCaL (LRAT), abc (PDR), cvc5.
