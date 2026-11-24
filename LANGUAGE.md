# The sys2fol language

The language a user writes specifications in. Its direction is the user's (`DESIGN.md` §9, decisions 15 and 16): it is
designed first for how a user reads it, its capabilities and the problem it solves; compiling, proving, machines and
interaction come after. The survey behind it is `docs/language-survey.md`.

## 1. The problem

Circuits and distributed protocols are many interacting state machines whose correctness depends on behaviour over
time. Engineers today test them, or verify them in tools that each cover one layer, trust unchecked solvers, and cannot
carry an abstract design down to its implementation through levels; no existing system does all of this together. The
language lets an engineer state what a system must do, refine it step by step to the implementation, and have every step
proved and machine-checked.

The language describes; it does not compute. Each construct means a first-order formula, and is chosen for the FOL it
generates and for how well machines solve the obligations that come from it (the user, 2026-11-23). Running a model is a
later, separate use (decision 16).

## 2. Who reads it

- The engineer who writes specs and models.
- The reviewer or customer who must trust what a claim says: they read the spec, so a spec reads as what it means. The
  statement compiler's renderer prints each claim back for review (`DESIGN.md` §2).
- The tools: the compilers and the machines.

A client never reads fol-zfc: specs, maps, claims, proof hints and failed obligations all read in the language, and
fol-zfc is for the checker (the user, 2026-11-23).

## 3. Capabilities

1. State machines, the built-in construct: modules with typed state, inputs, outputs, initial states and steps,
   nondeterminism allowed (`DESIGN.md` decision 1).
2. Refinement chains: spec ⊒ model 1 ⊒ model 2 ⊒ … ⊒ implementation. Each link says how the lower level maps to the
   upper, and links compose: refinement, inclusion of traces, is transitive.
3. Composition of modules, at every level.
4. Properties: invariants, refines and equivalent (`DESIGN.md` decision 11); liveness later.
5. General first-order statements about anything ZFC speaks of, sets, numbers, states and traces, so the language is
   complete when the built-ins do not fit.
6. Proof: automatic where machines can, SAT, SMT, IC3, the class machine and AI; interactive where they cannot; always
   checked by fol-zfc.
7. Later: simulatable models, a well-formed subset, steps computable among them, that can be run and tested.

## 4. Not now

Code as an input language beyond Verilog, synthesis, liveness and fairness, simulation.

## 5. Trade-offs the decisions weigh

- General statements against automation: full first-order ZFC makes the language complete and invites claims no machine
  proves; the built-ins are where automation lives.
- More levels against fewer: each link of a chain is a proof obligation, but a smaller one, nearer what machines and AI
  do.
- Readable against near the meaning: program-like steps, guards and assignments, read best; a relational step, a
  predicate over before and after, is nearest the meaning and keeps the trusted compiler small.
- Simulation later: a step style whose program-like subset can be run keeps that door open.

## 6. Decisions, in order

Each is the user's, explained with its trade-offs and checked once (`CLAUDE.md` rule 5); each is shown as it would read.

| # | Decision | Builds on |
|---|---|---|
| P1 | The building block: structures, their instances, and theorems proved once for every instance | decision 17 |
| P2 | The systems library written in the language, as its reviewed meaning layer | P1, decision 17 |
| P3 | The declarations, and aliases for sugar such as `module` and `link` | P1 |
| L1 | What is observable: a module's interface, and what a refinement link preserves across a chain | decisions 1, 11 |
| L2 | Granularity: lock-step or stuttering; events or clock ticks | L1, decision 10 |
| L3 | How a step reads: a relational core, a program-like surface, an executable subset | L1 |
| L4 | Types and data, and data refinement between levels | decision 14 |
| L5 | Composition: synchronous, interleaving, hiding; the network | L1, L2 |
| L6 | Parameters: for every n nodes, widths | L4, L5 |
| L7 | Properties, and general first-order statements: how they read and when a claim leaves the automated fragment | decisions 11, 16 |
| L8 | Refinement links: the mapping each states; chains | L1, L2, L4 |
| L9 | Importing implementations: rtl2fol's modules | L1, L4, L5 |
| L10 | Concrete syntax, fixed last, though every decision is shown in a candidate syntax | all |

## 7. Decided by the user

| # | Decision | Reason |
|---|---|---|
| L1 | What is observable. Every module declares typed input and output ports; a trace is the sequence of its (input, output) values, and internal state is never observed. A protocol event is a port value with a `none` case, so events and circuit signals share one vocabulary. Each refinement link states an observation map from the lower level's (input, output) values to the upper level's, and claims that every lower trace, mapped, is an upper trace: decision 11's "refines" with a map, the identity map giving it back. Links compose, their maps composing. The observation map belongs to the claim: a reviewer reads the top spec and the observation maps along the chain. The state map, the simulation, belongs to the proof: fol-zfc checks it, and no one needs to read it | The user's choice (2026-11-23), over one interface at every level with adapter modules: chains from protocol events down to circuit signals are the language's purpose, and adapters would lengthen every chain. Its cost, accepted: a careless map weakens the guarantee and no checker notices, so the renderer prints the maps with the claim. The specs and the maps call for a language that describes state machines (the user), decided in L3 and L4. |
| L2 | How the steps of two levels correspond. A link's map sends each lower step to a sequence of upper observations: empty (a hidden step), one (lock-step) or several (a batch); the claim is that every lower trace, its sequences joined end to end, is an upper trace. Lock-step, stuttering and batching are decided there, in the claim the reviewer reads. A step is a clock tick in a circuit and one atomic event in a protocol. Several lower steps merged into one upper observation are written as separate request and response events, or through an adapter module. In the proof, the forward family is one kind of simulation, path simulation, with options: the relation's shape (any relation, or a function) and invariants assumed at each step, each option sound by a one-step lemma the library proves once. Anyone may add a family (backward, history and prophecy, reduction, liveness): its hints, its one-step obligations and its soundness theorem; a link cites it once that theorem is checked, safe whoever wrote it, since user material never adds an axiom (`DESIGN.md` decision 17). The library ships the forward family first | The user's choice (2026-11-23), from their proposal that kinds of simulation be defined freely, stuttering one of them: sequence maps keep cycle-accurate claims for circuits and let a chain climb to instruction- and protocol-level specs; one forward kind with options leaves clients nothing to prove; trust comes from the checker, not from who wrote a kind. Its cost, accepted: above a link that hides steps, timing and progress are lost, to be stated as properties at a level that sees every step (L7), or as liveness later. |
| L3 | How a step reads. A rule is a pattern on the input (an enum case, a record of ports, a literal, or a variable that matches anything), an optional `when` guard, and a description of the output and the next state as equations and formulas (`next queue = rest(queue)`). Patterns match the shape of data; values are reached through expressions. The step is the union of the rules: each rule one disjunct, readable alone, one obligation each. An output a rule does not mention is `none`, and state it does not mention keeps its value. Choice is written `some` or `or`, or `such that` for a whole step; `on any input a → such that φ` writes any step the logic can state, so the form is complete, and the compiler marks the rules whose obligations may leave the fragments machines decide. Every input must have a rule that applies: an obligation machines close, with coverage checked by syntax as a convenience. No sequential code | The user's choice (2026-11-23): the language describes and does not compute (§1), so each construct is chosen for the FOL it generates and how machines solve it; pattern matching on Swift-style enum cases for the shape of data. Union rather than first match: each rule is a disjunct, where first match is an evaluation order that makes a rule's meaning depend on every earlier one. |
| P1 | The building block. A `structure` declares fields and a well-formedness condition, its wf: the conjunction of its named `where` conditions. An `instance` gives the fields values and owes the wf, each named condition becoming a named obligation; a condition may itself be an instance of a structure, whose wf joins the obligations. Theorems about a structure assume its wf and are proved once for every instance. A `type` says what a value looks like and owes no proof: every value of its shape belongs. Machines prove a wf; the compiler's own checks, that names resolve and types match, need no proof. Nothing asserts that an instance exists, so a wf no instance can meet adds nothing to the logic (`DESIGN.md` decision 17). Systems, kinds of simulation, families and invariants are structures; a module is an instance of `System`, and a link a theorem whose proof makes an instance of a kind | The user's choice (2026-11-23), from the simulation work: a kind of simulation was already a structure with a soundness theorem, and the same form builds the rest in simple terms. Two declarations rather than one `type … where …` as in PVS and Dafny: the keyword marks where proofs are owed, machines get a type as a sort and a wf as obligations, and no condition reaches a state or a port through its type. |
| P3 | The declarations: `type`, `define`, `structure`, `instance`, `theorem`, `use`, `alias`. One keyword instantiates every structure, and the compiler knows no structure by name. An instance writes each field in a notation chosen by the field's type: a list of parts for a type, a condition for a set, L3's rules for a step relation (state, input, output, next state). `module` and `link` are aliases the systems library declares: `module` an instance of `System` whose fields are written `input`, `output`, `state`, `initially` and rules; `link` a theorem whose claim reads `lower refines upper seen as view`. An alias is a checked substitution, as a fol-zfc schema or a Swift generic is: its holes are typed; it is checked once where it is declared, names resolving and types fitting for any arguments of the holes' types; each use is checked against the holes; it expands by substituting syntax trees without capturing names, and never runs a program. Every alias can be expanded and reversed, so the renderer prints any claim with its aliases or in plain form. An alias adds no axiom, and the aliases a claim uses are read like definitions, the library's reviewed once | The user's choice (2026-11-23), over one keyword per structure: sugar such as `module` is written in the library and checked by compiler rules, never a C-style macro that substitutes text. Its cost, accepted: checking makes an expansion well-formed, not truthful (`alias lower refines upper seen as view = refines(lower, upper, view) or true` passes every check), so a reviewer reads the aliases a claim uses, and the plain form shows them for what they are. Macros, programs that make syntax, are left out: they would run user code in the trusted statement compiler, could not always be printed back, and would split clients into dialects. |
| L4, in part | `rest(q)` and `first(q)` have no value for the empty sequence: a rule that uses them has no step on an empty sequence, and well-formedness needs another rule to cover that case (the user, 2026-11-23, after `BoundedQueue`'s proofs). | Every proof that uses `rest` keeps one case, where `rest([])` = `[]` would add one to each; a spec that leaves the empty case uncovered fails its well-formedness proof rather than passing with a step that does nothing; and `first([])` has no value either way, a type having no default member. |
