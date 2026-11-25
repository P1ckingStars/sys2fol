# sys2fol design

sys2fol turns specifications of systems into fol-zfc claims and their proofs. fol-zfc checks every proof
(`~/repos/fol-zfc-comb`) over the NBG library (`~/repos/fol-zfc-comb-lib`: Isabelle/ZF translated by isa2fol); ai-fol
searches for proofs (`~/repos/ai-fol`); rtl2fol turns hardware into claims (`~/repos/rtl2fol`). Only sys2fol knows about
specifications.

## 1. Pipeline

A spec and its proof sketch → the statement compiler → a fol-zfc claim; the proof compiler → obligations → machines →
fol-zfc steps → the compression machine → `proof_checker`.

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

A fact a machine's proofs cite lives in the library too when its statement holds whatever the spec is: proved once and
cited, never proved again (decision 21). A fact indexed by a size, a record's arity or a numeral, is a different
sentence at each size, since a first-order sentence quantifies a fixed number of values. The size-free tuple theory is
in base, and each instance is written by the machine whose proof needs it, the first time it does, and cited from then
on.

A project lists its specs, and each instance they cite is proved once for the project (decision 22). Each spec's run of
sysprove (`--project P --needs OUT`) states the instances its proofs cite, names each
`P.instance.<family>_<sizes>`, and lists them by family and sizes, one per line (`at 4 3`), without proving them. The
project's run (`sysprove instances`) proves the union of the lists, each instance once, in a file the compression
machine shortens and `proof_checker` checks once; each spec's checks load it. An edit to a spec that needs no new
instance reruns only that spec's generation and checks; one that does reruns the project's file and every spec's
checks, about 2 seconds each, nearly all of it loading. `test/BUILD.bazel` makes `BoundedQueue` and `Crossing` one
project, `tests`: 31 instances in 2,083 lines (38 KB), where each spec proved its own, 1,646 and 1,710 lines, 15 of them
alike; their lemma files, now each its step typing alone, and the project's file come to 3,958 lines where the two
lemma files were 5,231. A spec in no project proves its own instances in its lemma file.

| Layer | Holds | State |
|---|---|---|
| lattice | Knaster–Tarski: `Fixedpt.lfp`, `gfp`, `induct`, `coinduct`, `gfp_unfold` | in `@zf//:ZF.Fixedpt` |
| systems | the predicates of §3, the bridge, the invariance rule, simulation, composition, and the tuple lemmas they need (composing relations, the product S1×S2) | `math/systems/`: well-formedness, steps, `reach`, `bisim`, Part A checked (§7), and the facts sysprove's proofs cite, `tuple_facts` and `natural_facts` (decision 21); composition, the tuple lemmas beyond Part A's, and the doubling and word theories of decision 23 to build |
| systems as values | "M is the system (S, A, B, step, Init)", predicates on M defined through the systems layer's, and each of its theorems restated once over M: for theorems over a varying number of systems, such as compositional refinement | to build |
| circuits | bits as sets, tuples of bits, the set of all states, and the reduction of obligations to SAT: the theory rtl2fol's claims cite (rtl2fol `DESIGN.md`, decision 2) | to build |
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

A machine takes a closed obligation, such as `∀x⃗. (Γ → G)`, and answers with one of four (decision 13, §9): proved, a
claim and its fol-zfc proof; refuted, a counterexample over the atoms it sees, possibly spurious; refused, with the
reason; or out of time or memory. A caller cites a proved claim, instantiating it at its variables and discharging it
with its hypotheses; ai-fol's search reaches every machine through one adapter that writes those steps (D22).

| Machine | Offers | Steps from |
|---|---|---|
| SAT | a propositional obligation closed | CaDiCaL's LRAT proof, RUP steps only, as resolution steps |
| IC3 / PDR | an inductive invariant, or a counterexample | the invariant's three SAT-checked obligations (initial, step, property) and the invariance rule |
| k-induction, BMC | a proof or a counterexample | SAT obligations |
| SMT | a theory obligation closed | cvc5's proof, each theory step citing its library lemma |
| explicit-state explorer | a counterexample on rich data | the trace, checked by evaluation |
| AI (ai-fol) | an invariant, a refinement mapping, a lemma split, a citation | whatever the obligations it creates close with |
| class (fol-zfc-comb-lib) | a class, or a set, defined by a formula | its class-existence proof: built, CLASS, EXACT, VAL and SET |
| compression (fol-zfc-comb-lib) | a proof file, smaller | the file's own steps: those a kept step reads, renamed (decision 20) |

The user writes the spec, its structure, key invariants and citations; AI proposes what is missing; solvers close what
they decide; the checker accepts only steps.

## 6. From TLA+

Taken as semantics, not syntax: an implementation with more steps than its spec can refine it, here by a link's map
hiding steps (`LANGUAGE.md` L2) rather than by stuttering invariance, which would lose cycle-accurate claims;
implementation as implication; fairness conjoined without constraining safety (machine closure); refinement mappings as
the witness of a refinement. Started from its gaps: composition with interfaces, types, and links to implementations
(RTL through rtl2fol, code).

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
   `Sys.natural_nat`, `Sys.simulation_refines` and `Sys.converse_simulation_refines`, each by induction on the
   trace's length; `Sys.bisimilar_forth` and `Sys.bisimilar_back`, bisimilarity a bisimulation stated pointwise, as
   a predicate is no set (decision 3); and `Sys.bisimilar_equivalent`.

Each bridge comes right after its definition: it checks the predicate means what Knaster–Tarski means before anything
is built on it. Steps 4 and 5 each need a class of a formula, from the class machine (its `DESIGN.md` §7): step 4's,
the states related to a reachable spec state, is checked (`math/systems:related_reachable`).

Part B: rtl2fol's swap example as a deterministic system on `2×2`, its claim the invariance rule at the cut `{(0,0)}`, a set
built by `pairing`, its three obligations closed through SAT and LRAT.

Every claim on `proof_checker`'s Proved list.

Part B waits for the spec language, designed first (decision 15).

Part C, the language's first checked claims, comes before L5 to L9 are designed (the user, 2026-11-23: too much is on
paper). It builds `LANGUAGE.md`'s decided constructs, and as experiments its proposals L4 (types are sets), P4
(aliases) and P5 (the core); what it settles goes back to the user to decide. C++ in this repository, on
fol-zfc-comb-lib's checker and library:

1. The statement compiler and the renderer, on the smallest spec that uses every core construct: two lights at a
   crossing, never both green. Its claim: the system is well formed, and every reachable state is safe. The renderer
   prints the claim back from fol-zfc, and a round-trip test compares the print with the source.
2. The proof compiler's first route: the invariance rule, `Sys.invariance`, each obligation closed by cases over finite
   sets, and the sets from the class machine. Checked: the claim on the Proved list.
3. `BoundedQueue` and `queue_within_capacity`: sequences, natural numbers and an abstract type.

Step 1's compiler is `sysc` (`src/lang`, `src/tools`), with the library's first part in `library/systems.sys`; the
Crossing's seven claims compile in fol-zfc (`//test/crossing:claims`). Its claim shape, for the user to decide: a claim
about a system quantifies over the system's sets, each characterized by its members, and one claim per set states that
it exists; a step relation is bounded only by its state and input sets, so `Sys.wellformed` owes that every rule stays
in its types. Its data, as decision 23 keeps them: an enum's cases are the numbers 0, 1, …; a record is a tuple written
as `Sys.tuple2` and `Sys.tuple4` write theirs, and the empty record is 0; `extern` names a library predicate in the
library's own text. A claim still restates each number at every mention, where decision 23 constructs it once at the
claim's top: that is to build.

Step 1's renderer is `sysrender` (`src/render`). It links fol-zfc's parser and not `sysc`'s writer: it reads each claim
as fol-zfc parses it and inverts the writer's encoding pattern by pattern, refusing any other shape. Instances and
theorems print from the claims, each alias folded back only where its plain body, holes filled, is what the claim says;
definitions print from the source, checked against the notation they print in (an enum's cases are its positions). A
claim has no labels for record parts and does not say which of two equal sets it names (`bit` and `Light` are both
`0 ..< 2`), so those come from the source as hints, taken only where they fit the claim. Three round trips compare a
print with its source token by token: the Crossing, `test/constructs` (every construct the writer writes; its theorems
are not to be proved) and the library's definitions. Twenty mistakes seeded into the writer and the resolver each fail
one. Its choices, for the user to decide: names from the source as hints; where two spellings write one formula, the
print takes one (`all x in A: x in B` prints as `A ⊆ B`, `not x = y` as `x ≠ y`), so a spec in the other spelling
reads back changed in form.

Step 2's proof compiler is `sysprove` (`src/prove`): all seven of the Crossing's claims are on `proof_checker`'s Proved
list (`//test/crossing:proved`, checked by `proved_test`). It writes plain steps through an engine that computes each
step's formula and scopes as the checker does, so a misused step fails as it is written. The sets come from the class
machine as SET claims: `initial` and the theorem's invariant cut from `State`; `State`, `Input` and the step relation
from Pow(Pow(Pow(W))), W a numeral or a union of the indices and the component sets, since a tuple with its indices and
entries in W lies there; `Output`, {0}, by pairing. Every other fact is proved by cases over the values of the records'
entries, each encoded formula evaluated and each value's numeral carried by equalities. `crossing_safe` follows by
`Sys.invariance` with `{ s in Crossing.State | not (s.ns = green and s.ew = green) }` its own invariant, citing
`Crossing_wellformed` for a step's target state. A false theorem gets no proof: for `reachable(Crossing) ⊆ { s in
Crossing.State | s.ns = green }`, sysprove answers that a step leaves the property. The facts about numerals and records
the proofs cite are the library's when they hold for every spec (decision 21), and the project's instances, 26 of
`tests`' 31, when indexed by a size (decision 22). The spec's one lemma, `crossing.lemma.Crossing_step_typed`, is its
system's step typing: every step of its relation a tuple of a state, an input, an output and a state in their sets,
proved once by cases over the rules and cited by the system's well-formedness and by its step relation's set. Sizes, as
checked, through the compression machine (decision 20): 3,087 proof lines (78 KB) for the claims, 576 (18 KB) for the
lemma, and 3,473 (97 KB) from the class machine, 2,215 of them the step relation's set. For the user to decide: a theorem's proof citing the system's
well-formedness, proved first.

Step 3's statements: `sysc` and `sysrender` carry `BoundedQueue` and `queue_within_capacity` (`test/queue`). Its seven
claims compile in fol-zfc and read back as the spec, token for token; thirteen mistakes seeded into the new encodings
each fail the round trip or stop `sysc`. Its claim shape, for the user to decide with L4: a module's and a theorem's
parameters are quantified first in each of their claims, one whose type a library predicate gives (`extern type nat =
"Sys.natural"`) with that predicate as a hypothesis. Its data, as decision 23 keeps them: `sequence of T` is an index
tuple of a natural length with its entries in T (decision 12), `[]` the empty tuple and `[x]` a tuple of one;
`length(q)` is the n with tuple(q, n), `first(q)` the entry at index 0, `rest(q)` the tuple with every entry one index
down, none for `[]`, and `q ++ [x]` is snoc; `<` and `≤` on natural numbers are ∈ and ∈ or =; an enum whose cases carry
fields is the set of pairs ⟨case number, record of its fields⟩, its case names global; a rule's pattern binds a field's
value by an existential over the field's type, around the whole rule. `length`, `first` and `rest` are built into the
compiler, where decision 23 makes them the prelude's extern functions: that is to build. A theorem applies an
instance to its own parameters, in order, and only so yet. The renderer takes the source's order of a rule's equations
and its spelling of a reversed comparison (`a ≥ b` for `b ≤ a`) as hints, where they fit the claim. L3's `none` for an
output a rule does not mention is not built: `sysc` refuses such a rule.

Step 3's proofs: all seven of `BoundedQueue`'s claims are on `proof_checker`'s Proved list, with its step typing, the 20
of `tests`' instances it cites, and six sets (`//test/queue:proved_test` reads every part's list, as Crossing's does). A system with parameters is proved over
symbols, not by cases: each step's parts are typed by how its rule builds each value; every state and input has a step,
by excluded middle on each rule's guard in turn, the first that holds firing, its values built and its step proved by
matching against the steps at hand, and when none holds, cases on the order of the naturals at hand and on the guards'
negated parts make one hold; each set is cut from a tower over the naturals (ZF's nat) and the type parameters'
members, U(i+1) = U(i) ∪ Pow(Pow(Pow(U(i)))), each value at its type's depth. The theorem is the invariance rule at its
own set: a kept queue keeps its length, an append under `length < capacity` stays at most capacity, a rest too, and
`[]` starts so. `rest(q)` and `first(q)` have a value only for a nonempty q, so a rule using them has no step on an
empty q, which another rule must cover; the proof route takes `length(q) ≠ 0` from the rule's guard, and does not yet
split on emptiness without one. `rest` is the library's `Sys.tuple_rest`, whose proof takes two sets from the class
machine, the shifted pairs and the naturals that are 0 or a successor, for the length's predecessor, where append has
`snoc_EX`. The facts about natural numbers are the library's `natural_facts`, from the translated ZF library through
`Sys.natural_nat`. The class
machine takes a parameter only on a membership's right side, `pmem`'s third place being one: elsewhere, as `capacity`
in `capacity ≤ length(queue)`, the request names a variable with the parameter's members, which the proof returns to
the parameter by extensionality. Sizes, as checked: 5,105 proof lines (160 KB) for the claims, 1,299 (39 KB) for the
step typing, and 7,884 (268 KB) from the class machine, 5,618 of them the step relation's set, which `proof_checker` checks
in 1.9 seconds, nearly all of it loading the libraries. `rest`
and `first` with no value on `[]` is the user's decision (`LANGUAGE.md`, L4 in part).

## 8. Not now

Liveness and fairness, the generic layer, up-to techniques, SMT theory steps beyond bit-vectors,
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
| 10 | Refinement's witness is a kind of simulation, each kind with a checked theorem into the one meaning of "refines": first the lock-step forward simulation (§3), then the forward family's path simulation and further families, as `LANGUAGE.md` L2 sets out | It guarantees the same input/output pairs, and reachability needs the initial states related. Lock-step alone is strict: an implementation taking more steps per spec step, or choosing later than its spec, needs another kind. The trusted part stays small: one meaning, the kinds untrusted proof material. |
| 11 | "Refines" is inclusion of traces and "equivalent" equality of traces: a trace the finite sequence of input/output pairs a run from an initial state produces. A state's behaviour is its set of traces. Liveness later, as a meaning of its own | Traces have wider acceptance: every flavour of simulation proves them, where branching meanings accept only bisimilarity and forward simulation. Two systems with the same traces are equivalent even when one chooses earlier; no input/output sequence shows that difference. Finite traces cover safety and leave liveness for later. |
| 12 | A trace and a run are fol-zfc tuples indexed by a natural number n: a trace's entries the 2-tuples ⟨a, b⟩, a run's its n+1 states; the sequence lemmas ours, by induction on n | ZF's lists nest: `Cons` takes one extraction per entry, in the style of a typed prover, where an index tuple reaches any entry in one lookup and keeps one encoding with states, steps and relations. |
| 13 | Every machine shares one interface: a closed obligation in; proved (a claim and its proof), refuted (a counterexample over its atoms), refused (a reason), or out of resources out; ai-fol's search through one adapter (§5) | A proved claim is checked alone and cited by instantiating it under the caller's scope; a machine handles no caller's context. A refutation can be spurious, as SAT does not see the relations between predicates. |
| 14 | Obligations keep the types their spec gives them, and the proof compiler, untrusted, picks each one's reduction: bit-typed values bit-blasted to SAT, integers and words by theory reasoning (SMT), or a whole design by refinement to a spec over integers; Part B builds the bit route | Abstractions of integers save a lot over every bit, and obligations are compiled from the spec. A reduction is a layer above what is trusted, the checker and the statement compiler's meaning. Bits remain for single-wire combinational logic, single-bit registers and ad hoc structures. |
| 15 | The spec language is designed before Part B, one language for circuits and decentralized protocols alike: the user writes a spec, and an implementation refines it (§7) | Much is shared: modules, types, properties and proof hints; one language lets claims cross layers, a node's hardware refining its protocol-level spec. |
| 16 | The language is designed first for how a user reads it, its capabilities and the problem it solves; compiling, proving, machines and interaction come after. It reasons about state machines at the abstract level through refinement chains, spec ⊒ model 1 ⊒ model 2 ⊒ … ⊒ implementation. State machines are its built-in, emphasized construct, but general first-order statements are allowed, so it is complete when needed. Simulatable models, under a well-formedness condition, are kept in mind for later. Its design and decisions are `LANGUAGE.md` | The user's direction (2026-11-23), after the survey of existing languages: learn from them, design from first principles, and solve what they cannot. |
| 17 | User-written material never adds an axiom. Its names, kinds of simulation, families, helper notions and the definitions a claim uses, are abbreviations the compilers expand before fol-zfc, and the sets it needs come from the class machine's proved existence claims. `@def` axioms stay in the library's reviewed meaning layer | fol-zfc checks of a `@def` only that its predicate is new and that the axiom mentions it, so a user's "definition" could be any axiom, even a contradictory one from which every claim follows. Expanded, a user's kind adds nothing to trust: a proof that checks is enough, whoever wrote it (the user, 2026-11-23: trust comes from the checker). |
| 18 | The statement compiler and the renderer, which are trusted, are hand-written C++ in this repository, small enough to review, with no parser or IR framework in them; the round-trip test checks them. Frameworks serve only untrusted parts: slang or Yosys for importing RTL, tree-sitter and a language server for editors, solvers as machines. Isabelle/ZF with isa2fol is evaluated as the way to prove library theorems before any is written by hand | The user's choice (2026-11-23), after the frameworks were laid out: a framework in the statement compiler puts its code in what is trusted, since a bug there changes a claim's meaning while every proof still checks; Clang, Swift, Rust and Go hand-write their parsers too. Untrusted output is checked, so any framework is safe there. isa2fol's proofs are checked by fol-zfc, so Isabelle's automation adds no trust; its cost is a bridge from each Isabelle notion to ours. |
| 19 | The class machine reads a defined predicate through a row, a class proved once, as it reads `zero`, `nsucc` and `snoc`, and unfolds a predicate that has none. The foundation's predicates' rows live in the class machine's package, made by the machine in its build; each library's rows live with that library; a predicate with no row gets one made inside the request, and a row is found by its statement (the user, 2026-11-23, after the machine's output was measured; the class machine's `DESIGN.md`, decisions 3 to 5) | 95% of the machine's lines came from unfolding `tuple` (68%) and `pmem` (27%) at every occurrence; rows cut an estimated 16× of all its lines, and the machine's own run takes seconds where checking its output took 25 minutes. |
| 20 | Proof compression is a standalone machine, and every proof a machine writes goes through it before `proof_checker`: fol-zfc-comb-lib's `src/machines/compress`, beside the class machine, on the checker's public replay. It drops the steps no kept step reads, reads each held fact from the step that set it, and writes short names and only the parentheses needed. The class machine runs it in process; sysprove's proofs go through `fol_compressed_proof` (the user, 2026-11-24) | A proof's size is what the checker parses and what a customer stores and checks again. One machine serves every writer, rtl2fol's included, where each writer would otherwise write its own pass; inside fol-zfc-comb-lib the class machine reaches it, and the checker's tree stays as it is. It is untrusted: each rewritten block is checked before it is kept. |
| 21 | A fact whose statement holds whatever the spec is lives in the systems library, proved once, and every proof a machine writes cites it, never proving it again. The 23 sysprove proved in each spec are `math/systems`' `tuple_facts` and `natural_facts`, with the proofs sysprove wrote, shortened by the compression machine, and base's `g3_pmem_cong1`. A fact whose proof depends on the task, one indexed by a record's arity or a numeral, belongs to the proof generation, which writes it the first time a proof needs it and cites it from then on, so that it is proved once (the user, 2026-11-24) | Every later use of a machine cites such a fact instead of proving it on the instance, as programs use C++'s standard library. These facts were 35% of what sysprove wrote per spec, and 20 were proved identically in both specs. A first-order sentence quantifies a fixed number of values, so a fact over a record of k fields is one sentence per k: base holds the size-free tuple theory, and an instance at a size is part of the proof that needs it. No proof was written by hand: sysprove wrote them, and those on the natural numbers rest on ZF's through `Sys.natural_nat` (decision 18). |
| 22 | The instances a project's specs cite are proved once for the project: each spec's sysprove run states and lists the instances it cites, and the project's run proves their union in one file, which every spec's checks load; a spec in no project proves its own (the user, 2026-11-24, after the design was written into §4) | Decision 21 has the proof generation cache what it proves so that nothing is proved twice, and specs in one build share sizes: `BoundedQueue` and `Crossing` proved 15 instances alike. Per-spec runs keep each spec's generation incremental and parallel, where one run for the whole project would regenerate every spec on any edit; Bazel cannot declare a target per instance, since only sysprove's run learns which instances a spec needs. |
| 23 | Numbers have one encoding, the von Neumann naturals. A claim constructs each number it uses once, at its top: a variable with its defining atoms as hypotheses, one name for every use. Positions and enum cases are built by successor steps; other values by doubling steps (`Sys.double`, `Sys.double_succ`). `nat` is unbounded. `int(w)` and `uint(w)` are ℤ/2^wℤ on the naturals below 2^w; `int(w)` is signed in two's complement and `uint(w)` unsigned. `int8` … `int64`, and `int` as `int32`, are type aliases in the prelude. The language gains extern types with parameters, extern functions each resting on the library's totality and uniqueness theorems, and operators chosen by their operands' types. A range `0 ..< n` is `x ∈ n`. Records, enums, enums with fields, sequences and the order on `nat` stay encoded as they are (the user, 2026-11-24; `LANGUAGE.md`, L4 numbers) | A number's construction, not its encoding, sets the proof's size. Restated at every mention, numbers took 491 of the two specs' 869 quantifiers, and 1,194 of the project's 2,083 instance lines only stepped through them; a literal 10000 took 10,001 atoms, and a circuit of n latches about n²/2. Constructed once, the specs need 48: successor steps give each position, every one of which a claim uses, in one atom, and doubling steps give a value in one atom per bit, 10000 in 15. One theory of ℤ/2^wℤ, proved once for every w, serves machine integers of every width and rtl2fol's signals, and lets a theorem hold for every width. The extensions let the prelude declare the number types, so the compiler knows none by name. |

## 10. Open, for the user

- The core constructs (`LANGUAGE.md`), fairness and composition. Fairness may be a property of runs, stated with the
  systems layer's notions, rather than a component of a system (the user's view); it must then leave a fair run from
  every reachable state, or a liveness claim holds vacuously, as an unproved wf would make a safety claim hold.
- The systems layer first, or the generic layer first.
- A counterexample: checked by evaluation, or proved in fol-zfc as the claim's negation.
- The arithmetic beyond `nat`, `int(w)` and `uint(w)` (decision 23): ℤ unbounded, ZF's `int` behind a bridge; ℚ or ℝ
  (not yet).

Tools needed: CaDiCaL (LRAT), abc (PDR), cvc5.
