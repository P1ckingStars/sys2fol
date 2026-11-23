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

A system is a coalgebra `c: S → F(S)` on a set `S`, with inputs `A`, outputs `B` and `F(X) = P⁺(B×X)^A` (decision 1,
§9): in state s on input a it takes one of a nonempty set of steps, each an output b and a next state s′. `step` is a
relation in fol-zfc, which has no function symbols; `Init ⊆ S` is the set of initial states, and `Post(X)` the states a
step leads to from X. A deterministic system, such as rtl2fol's, is the case where every set of steps is a singleton.

A system is written by its components as separate parameters, and its tuples are fol-zfc tuples (decision 2, §9): a
state is the tuple of its variables' values, `step` a set of 4-tuples `⟨s, a, b, s′⟩`, and a relation between states a
set of 2-tuples. Values inside a state, such as integers and lists, are ZF's. Each predicate takes only the parts of a
system its definition uses (decision 7, §9), and a step, `step` containing ⟨s, a, b, s′⟩, is a predicate of its own,
defined once by the tuple encoding (decision 8).

A system is well formed when `Init ⊆ S`, every step lies in `S×A×B×S`, and every s ∈ S has a step on every a ∈ A.
Well-formedness is a predicate of its own, in no notion's definition, and a claim about a system proves it (decision 5,
§9): a claim that assumed it, or a `reach` that held only of well-formed systems, would hold of an ill-formed system
and mean nothing.

| Notion | NBG |
|---|---|
| reachable states Q | `reach(s) ↔ ∀I. set(I) → (I ⊆ S ∧ Init ⊆ I ∧ Post(I) ⊆ I → s ∈ I)`: in every invariant containing the initial states |
| safety | `Q ⊆ P`, proved by an invariant I with `Init ⊆ I ⊆ P` and I closed under steps |
| bisimulation | between two systems (decision 9, §9): any `R ⊆ Φ(R)`, where `(s, t) ∈ Φ(R)` when every step `(b, s′)` of s in the first system on input a is matched by a step `(b, t′)` of t in the second on a with `(s′, t′) ∈ R`, and every step of t by one of s; states of one system are the case of the same system twice |
| bisimilarity | `bisim(s, t) ↔ ∃R. set(R) ∧ R ⊆ S1×S2 ∧ R ⊆ Φ(R) ∧ (s, t) ∈ R`: the union of the bisimulations |
| refines, equivalent | every trace of the implementation is a trace of the spec; the same traces (decision 11) |
| refinement | a simulation `R ⊆ S_impl × S_spec`: each initial implementation state is related to an initial spec state, and each implementation step is matched by a spec step on the same input, with the same output and related successors; a refinement mapping is a simulation that is a function |

Safety, equivalence and refinement are each a post-fixpoint of a monotone operator: a proof is a witness (I or R) and a
one-step check.

Each notion is a `@def` predicate whose quantifiers range over sets only (decision 4, §9), so the class machine builds a class of any
formula that uses it. The bridge (§4) proves `reach` and `bisim` are `Fixedpt`'s `lfp` and `gfp`.

## 4. Library

The systems library is `math/` in fol-zfc-comb-lib, built on `@zf`; its names have the prefix `Sys.` (decision 6, §9).

NBG is the foundation, but the work is in ZFC (decision 3, §9). Classes stand only for the meta level: an operator such
as `Fixedpt`'s h, a predicate a theorem is cited at, and the classes the class machine builds for those. Everything else
is a set: systems, states, relations, invariants, behaviours. Every quantifier in the definition of a notion ranges over
sets; one ranging over classes would also be refused by the class machine. A system feature of the language is a claim proved once and cited, its class variables instantiated; none is a checker
rule.

`forall_elim` instantiates only at a variable, so citing a fixpoint claim at an operator such as Φ needs a variable
for Φ's class, from a proof of its existence. Class existence is a schema in NBG, proved once per defining formula
(isa2fol `docs/FOUNDATION.md` §3); a library definition with the machine as parameters proves it once for every
machine. fol-zfc-comb-lib's class machine (`src/machines/class`) writes these proofs.

| Layer | Holds | State |
|---|---|---|
| lattice | Knaster–Tarski: `Fixedpt.lfp`, `gfp`, `induct`, `coinduct`, `gfp_unfold` | in `@zf//:ZF.Fixedpt` |
| systems | the predicates of §3, the bridge, the invariance rule, simulation, composition, and the tuple lemmas they need (composing relations, the product S1×S2) | `math/systems/`: well-formedness, steps, `reach`, `bisim`, their bridges, the invariance rule, coinduction, simulation, traces and simulation's theorem into them checked; the rest to build |
| systems as values | "M is the system (S, A, B, step, Init)", predicates on M defined through the systems layer's, and each of its theorems restated once over M: for theorems over a varying number of systems, such as compositional refinement | to build |
| generic | the same for every functor F, F a class | to build |
| theory steps | one lemma per kind of solver step (Farkas for linear arithmetic, ...) | to build |

The bridge ties the systems layer to the lattice. When `Init ⊆ S` and every step from a state in S goes to a state in
S, then for every class h with `function(h)` whose value at ⟨X⟩ is the set of u ∈ S with u ∈ Init or a step from a
state in X to u, `reach(s) ↔ s ∈ lfp(S, h)`. The bridge assumes only what its proof uses, and h's value is the GRAPH
shape with bound S; for X ⊆ S it is `Init ∪ Post(X)`. For every set D containing S1×S2, and every g with
`function(g)` whose value at ⟨R⟩ is the set of q ∈ D that are some ⟨x, y⟩ in S1×S2 and match both ways relative to R
for each ⟨x, y⟩ they are, `bisim(s, t) ↔ (s, t) ∈ gfp(D, g)`. It needs no well-formedness: the bound S1×S2 is in g's
value. Stated for every such h and g, it needs no class of Φ from the machine: the
classes `Fixedpt`'s statements quantify over come from `Fixedpt.lfp_CLASS`, `Fixedpt.gfp_CLASS` and one class of
`λX. h(X)`, generic in h. A given machine's h and g are GRAPH claims (class machine `DESIGN.md` §4) with the machine's
components as parameters, proved once for every machine.

The systems layer's predicates (decisions 7 and 8, §9):

| Predicate | Holds when |
|---|---|
| `Sys.tuple4(q, x0, x1, x2, x3)` | q is the 4-tuple ⟨x0, x1, x2, x3⟩: `tuple(q, 4)` and one `pmem` per entry |
| `Sys.transition(step, s, a, b, t)` | some q in step is ⟨s, a, b, t⟩: from s, on input a, output b, to t |
| `Sys.wellformed(S, A, B, step, Init)` | `Init ⊆ S`, every q in step is some ⟨s, a, b, t⟩ in S×A×B×S, and every s in S has a step on every a in A |
| `Sys.reachable(S, step, Init, s)` | s is in every set I with `I ⊆ S`, `Init ⊆ I`, and every step from a state in I going to a state in I |
| `Sys.tuple2(q, x0, x1)` | q is the 2-tuple ⟨x0, x1⟩ |
| `Sys.related(R, x, y)` | some q in R is ⟨x, y⟩ |
| `Sys.bisimulation(step1, step2, R)` | for every x, y related by R, every step of x in the first system is matched by a step of y in the second on the same input, with the same output and related successors, and every step of y by one of x |
| `Sys.bisimilar(S1, step1, S2, step2, s, t)` | some set R, each element some ⟨x, y⟩ in S1×S2, is a bisimulation relating s to t |
| `Sys.simulation(step1, Init1, step2, Init2, R)` | every initial implementation state is related to an initial spec state, and for every related pair each implementation step is matched by a spec step on the same input, with the same output and related successors (decision 10) |
| `Sys.natural(n)` | n is in every inductive set: ZF's `nat`, by the bridge `Sys.natural_nat` |
| `Sys.run(step, Init, n, tr, run)` | tr is a tuple of length n, run one of length n+1, run(0) in Init, and for each i < n, tr(i) is some ⟨a, b⟩ with a step on input a, output b, from run(i) to run(i+1) |
| `Sys.trace(step, Init, tr)` | for some natural number n, some run has `Sys.run(step, Init, n, tr, run)` |
| `Sys.refines(step1, Init1, step2, Init2)`, `Sys.equivalent(...)` | every trace of the first is a trace of the second; each refines the other (decision 11) |

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
| class (fol-zfc-comb-lib) | a class, or a set, defined by a formula | its class-existence proof: built, CLASS, EXACT, VAL and SET |

The user writes the spec, its structure, key invariants and citations; AI proposes what is missing; solvers close what
they decide; the checker accepts only steps.

## 6. From TLA+

Taken as semantics, not syntax: stuttering invariance, so an implementation with more steps than its spec can refine
it; implementation as implication; fairness conjoined without constraining safety (machine closure); refinement
mappings as the witness of a refinement. Started from its gaps: composition with interfaces, types, and links to
implementations (RTL through rtl2fol, code).

## 7. First milestone

Part A, in the library, for a system `(S, A, B, step, Init)` (§3), in this order:

1. Well-formedness, a step predicate and `reach` as `@def` predicates (§3), then the bridge `reach ↔ lfp` (§4):
   checked, `Sys.reachable_lfp`.
2. `bisim` as a `@def` predicate, then the bridge `bisim ↔ gfp`: checked, `Sys.bisimilar_gfp`.
3. The invariance rule `Init ⊆ I ∧ Post(I) ⊆ I ∧ I ⊆ P → reach ⊆ P`, and coinduction
   `R ⊆ Φ(R) ∧ (s, t) ∈ R → bisim(s, t)`, each from its predicate's definition: checked, `Sys.invariance` and
   `Sys.coinduction`.
4. Simulation (§3), and the theorem that every reachable implementation state is related to a reachable spec state:
   it carries a spec's safety property to the implementation. Checked: `Sys.simulation_reach` and
   `Sys.simulation_safety`.
5. Traces (decisions 11, 12): `Sys.trace`, `Sys.refines`, `Sys.equivalent`; a simulation gives `Sys.refines`; `bisim`
   is a bisimulation, and bisimilar initial states give `Sys.equivalent`. Checked: the definitions, the bridge
   `Sys.natural_nat`, and `Sys.simulation_refines`, by induction on the trace's length.

Each bridge comes right after its definition: it checks the predicate means what Knaster–Tarski means before anything
is built on it. Steps 4 and 5 each need a class of a formula, from the class machine (its `DESIGN.md` §7): step 4's,
the states related to a reachable spec state, is checked (`math/systems:related_reachable`).

Part B: rtl2fol's swap example as a deterministic system on `2×2`, its claim the invariance rule at the cut `{(0,0)}`, a set
built by `pairing`, its three obligations closed through SAT and LRAT.

Every claim on `proof_checker`'s Proved list.

## 8. Not now

The language's syntax, liveness and fairness, the generic layer, up-to techniques, SMT theory steps beyond bit-vectors,
LRAT's RAT steps.

## 9. Decided by the user

| # | Decision | Reason |
|---|---|---|
| 1 | A system is nondeterministic and input-enabled: `F(X) = P⁺(B×X)^A`, a deterministic system the case of singletons | A spec that fixes every output is as long as the implementation and no easier to check; a spec allowing a set of outputs stays short, and refinement checks the implementation against it. A step for every input rules out an implementation that meets a spec by refusing inputs. |
| 2 | A system's components are separate parameters, with a systems-as-values layer on top; its tuples are fol-zfc tuples | Separate parameters give each component directly, where one set needs an extraction at each use; the layer on top gives reasoning about a system without its internals, and quantifying over systems needs them to be sets. A fol-zfc tuple is an index map, one lookup for any entry, where nested ZF pairs need one extraction per layer; the cost is proving our own tuple lemmas, some of which base has. |
| 3 | NBG is the foundation, but the work is in ZFC: classes only for the meta level, everything else a set (§4) | Over-using NBG is dangerous. |
| 4 | `reach` and `bisim` are `@def` predicates whose quantifiers range over sets, each tied to `Fixedpt`'s `lfp` or `gfp` by a bridge proved right after its definition (§4, §7) | Restricted comprehension: with set quantifiers the class machine builds a class of any formula that uses them, and step 4 cuts from such a class the set it needs, the implementation states related to a reachable spec state. The bridge keeps one formalization instead of two, and proved first it gives confidence early; it needs the system well formed. |
| 5 | Well-formedness is a predicate of its own, in no notion's definition, and a claim about a system proves it (§3) | Assumed, it makes a claim true of an ill-formed system, meaning nothing; inside `reach`, `reach` fails for every state and the claim passes all the same. |
| 6 | The systems library's names have the prefix `Sys.`, and full words after it | Customers never see them: they write the spec language, which the statement compiler turns into claims. |
| 7 | Each predicate takes only the parts of a system its definition uses (§3) | Shorter claims and citations, each predicate showing what it depends on, and a part added to systems changes only the predicates that use it. What is given up is a unified convention: each predicate has its own arguments, which the statement compiler's one translation per construct writes once. |
| 8 | A step is a predicate of its own, `step` containing ⟨s, a, b, s′⟩, defined once by the tuple encoding (§3) | Shorter extraction, and the encoding in one place. Its cost is the lemmas that build and take apart a step, which base has only for tuples in general, and a congruence lemma. A tuple is a function in base's sense, so function properties are there if needed. |
| 9 | A bisimulation relates states of two systems, `R ⊆ S1×S2`; one system is the case of the same system twice (§3) | Within one system, comparing an implementation with its spec needs their disjoint union built, and written into every such claim; between two, the proofs are longer, through tuples, but the claim is cleaner to use. |
| 10 | Refinement's witness is, for now, the lock-step forward simulation (§3); stuttering and backward simulation come later as flavours of their own, each with a theorem into one meaning of "refines", decided with §10 | It guarantees the same input/output pairs, and reachability needs the initial states related. It is strict: an implementation taking more steps per spec step, or choosing later than its spec, needs another flavour. The trusted part stays small: one meaning, the flavours untrusted proof material. |
| 11 | "Refines" is inclusion of traces and "equivalent" equality of traces: a trace the finite sequence of input/output pairs a run from an initial state produces. A state's behaviour is its set of traces. Liveness later, as a meaning of its own | Traces have wider acceptance: every flavour of simulation proves them, where branching meanings accept only bisimilarity and forward simulation. Two systems with the same traces are equivalent even when one chooses earlier; no input/output sequence shows that difference. Finite traces cover safety and leave liveness for later. |
| 12 | A trace and a run are fol-zfc tuples indexed by a natural number n: a trace's entries the 2-tuples ⟨a, b⟩, a run's its n+1 states; the sequence lemmas ours, by induction on n | ZF's lists nest: `Cons` takes one extraction per entry, in the style of a typed prover, where an index tuple reaches any entry in one lookup and keeps one encoding with states, steps and relations. |

## 10. Open, for the user

- The core constructs, and stuttering, fairness and composition. Fairness may be a property of runs, stated with the
  systems layer's notions, rather than a component of a system (the user's view); it must then leave a fair run from
  every reachable state, or a liveness claim holds vacuously, as an unproved wf would make a safety claim hold.
  Stuttering is a simulation in which an implementation step that is invisible, its input and output meaning nothing
  happened (a valid bit at 0), may be matched by no spec step; which steps are invisible can be an argument of that
  notion rather than a component of a system.
- The systems layer first, or the generic layer first.
- A counterexample: checked by evaluation, or proved in fol-zfc as the claim's negation.
- rtl2fol: a front end of sys2fol, or a separate pipeline.
- The machine interface's exact form, shared with ai-fol and rtl2fol.
- The arithmetic a spec ranges over: ℤ (in the library), ℚ or ℝ (not yet).

Tools needed: CaDiCaL (LRAT), abc (PDR), cvc5.
