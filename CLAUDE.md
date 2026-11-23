# Hard rules for Claude in sys2fol

## 1. Only checked proofs count

Every proof is checked by fol-zfc's `proof_checker` (`~/repos/fol-zfc-comb`), over the NBG library in
`~/repos/fol-zfc-comb-lib`. Read its Proved list: the exit status and a `.fol.lib`'s status can report a false claim as
Proved.

## 2. The logic and the checker are fixed

Pure first-order NBG as fol-zfc has it: no function symbols, no built-in equality (`eq` is a predicate), no axiom
schemas: a schema is proved once, its predicate letters open, and instantiated by `schema_inst`.
Never add a rule, a normalizer or a decision procedure to the checker or the logic. Never edit fol-zfc-comb from here.
In fol-zfc-comb-lib, edit only the systems library in `math/` (`DESIGN.md` §4) and the class machine in
`src/machines/class`: never its checker, its foundation, the pinned ZF library, or other work in `math/`. A system feature of the language is a theorem in the library, never a rule.

## 3. Procedures live in machines

SAT, SMT, IC3, model checkers, normalizers and AI provers are machines: given a goal, a machine offers a next state and
writes the plain fol-zfc steps that reach it. No machine is trusted; one that cannot produce checkable steps offers
nothing (ai-fol `DECODER.md` D22).

## 4. Translate by the semantics

Every spec construct has one meaning in NBG and one translation, or is refused at the input gate. Benchmarks catch
bugs; they never scope, simplify or justify a design. Identities in the IR are typed handles, never names or strings.

## 5. Production designs are the user's, decided after a test

sys2fol is a commercial product. A production design is one a customer sees or relies on, or one other work is built on
and costly to change: what a spec means, the language's constructs and syntax, the NBG representation the theorems rest
on, the interfaces between components (machines, requests, claim shapes and names), and what is trusted. For each:

1. Explain it: the problem, the options, their trade-offs and a recommendation.
2. Check the user followed it: two or three questions on the explanation itself (what the choice commits to, why the
   recommendation, what it costs and leaves open), asking only what making the choice needs, never an exercise. Check the
   answers; explain again what an answer misses, and ask again.
3. The user decides, and the decision goes into `DESIGN.md` as theirs.

Never decide one, never build on one not yet decided, and never take agreement with a recommendation for a passed test.
Any other design is written into `DESIGN.md` and agreed before it is built.

## 6. C++ for anything hot

Compilers, machines and certificate translation are C++ (Bazel), run under a memory cap. Python is glue only.

## 7. Writing

Comments stay under 5% of a change's added lines. Docs state what holds now: delete what no longer holds, silently.

## 8. Work in ZFC

NBG is the foundation, but the work is in ZFC: classes stand only for the meta level (an operator such as `Fixedpt`'s
h, a predicate a theorem is cited at, and the classes the class machine builds for those). Everything a claim is about
is a set: systems, states, signals, relations, invariants, behaviours. Every quantifier in the definition of a notion
ranges over sets. Over-using NBG is dangerous (`DESIGN.md` §9, decision 3).
