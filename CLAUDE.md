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

## 5. Design before code

Write a design into `DESIGN.md` and get the user's agreement before building it. What a spec means and the systems
theory in NBG are the user's decisions: propose, never decide.

## 6. C++ for anything hot

Compilers, machines and certificate translation are C++ (Bazel), run under a memory cap. Python is glue only.

## 7. Writing

Comments stay under 5% of a change's added lines. Docs state what holds now: delete what no longer holds, silently.
