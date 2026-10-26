# TASK: Prove the raw instruction reachability interface

## Meta
Status: planned
Priority: P1
Created: 2026-10-26
Location: venom/codegen/defs

## Theorem Statement (FROZEN)

### venom/codegen/defs/contextReachabilityScript.sml

```sml
(* Least instruction-site reachability for the code-generation package.
 * Entry and block transitions expose states after PHIs; ordinary steps
 * expose the incremented instruction index, including aggregate INVOKE returns.
 *)
Theory contextReachability
Ancestors
  contextCodegenRel contextCodegenRelProps

Inductive raw_inst_reachable:
[~entry:]
  (!initial_vs ctx name fn lbl s1 inst.
    ctx.ctx_entry = SOME name /\
    lookup_function name ctx.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl /\
    enters_block fn
      (initial_vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                         vs_inst_idx := 0 |>) s1 /\
    active_inst fn inst s1 ==>
    raw_inst_reachable initial_vs ctx fn inst s1)
[~next:]
  (!initial_vs ctx fn inst inst' s s' fuel.
    raw_inst_reachable initial_vs ctx fn inst s /\ active_inst fn inst s /\
    ~is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK s' /\
    active_inst fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx) ==>
    raw_inst_reachable initial_vs ctx fn inst'
      (s' with vs_inst_idx := SUC s.vs_inst_idx))
[~block:]
  (!initial_vs ctx fn inst inst' s s' s1 fuel.
    raw_inst_reachable initial_vs ctx fn inst s /\ active_inst fn inst s /\
    is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK s' /\
    ~s'.vs_halted /\ enters_block fn s' s1 /\ active_inst fn inst' s1 ==>
    raw_inst_reachable initial_vs ctx fn inst' s1)
[~callee:]
  (!initial_vs ctx caller inv s nm ops callee args cs s1 inst.
    raw_inst_reachable initial_vs ctx caller inv s /\ active_inst caller inv s /\
    inv.inst_opcode = INVOKE /\ decode_invoke inv = SOME (nm,ops) /\
    lookup_function nm ctx.ctx_functions = SOME callee /\
    eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
    enters_block callee cs s1 /\ active_inst callee inst s1 ==>
    raw_inst_reachable initial_vs ctx callee inst s1)
End

Theorem raw_inst_reachable_active:
  !initial_vs ctx fn inst s.
    raw_inst_reachable initial_vs ctx fn inst s ==> active_inst fn inst s
Proof
  cheat
QED

Theorem raw_inst_reachable_closed:
  reachability_closed (raw_inst_reachable initial_vs) ctx
Proof
  cheat
QED

Theorem raw_inst_reachable_fn_entry:
  ctx.ctx_entry = SOME name /\
  lookup_function name ctx.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl ==>
  fn_entry_inv (raw_inst_reachable initial_vs) ctx fn
    (initial_vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                       vs_inst_idx := 0 |>)
Proof
  cheat
QED

(* An executable entry instruction is not required by the existing package:
 * a valid lookup/label witness may have an empty or failing PHI entry. *)
Theorem raw_inst_reachable_package:
  codegen_reachability_package (raw_inst_reachable initial_vs) ctx initial_vs <=>
  ?name fn lbl.
    ctx.ctx_entry = SOME name /\
    lookup_function name ctx.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl
Proof
  cheat
QED

Theorem raw_inst_reachable_minimal:
  codegen_reachability_package Inv ctx initial_vs ==>
  !fn inst s. raw_inst_reachable initial_vs ctx fn inst s ==> Inv ctx fn inst s
Proof
  cheat
QED

```

### venom/compiler/unitTransformDefsScript.sml

```sml
Theorem raw_unit_memory_ok_iff_raw_reachable:
  raw_unit_memory_ok ctx vs <=>
  (?name fn lbl.
    ctx.ctx_entry = SOME name /\
    lookup_function name ctx.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl) /\
  (!fn inst s. raw_inst_reachable vs ctx fn inst s ==>
    s.vs_alloca_next < dimword (:256) /\ inst_mem_below_frontier inst s)
Proof
  cheat
QED

```

Do not modify these statements or the inductive definition. Prove them as-is, or produce a counterexample. Only proof bodies and necessary helper theorems may change.

## Completion Criteria

All five interface theorems in contextReachability and the memory equivalence in unitTransformDefs build without cheats, axioms, parser warnings or timeout overrides. Preserve every pre-existing proven statement. Generated raw_inst_reachable_ind and named entry/next/block/callee rules remain available. Commit proof changes with a Bot: sol (OpenAI GPT-6.1 Sol) trailer.

## Build

From the project root:
```bash
holbuild -j4 build contextReachabilityTheory unitTransformDefsTheory
```
Only these targets and necessary direct dependencies are authorized; do not run a root build, bytecode parity rollup or full CI suite.

## Background

Issue #641 needs a generic least relation of raw instruction sites matching the codegen reachability package. This interface removes the existential invariant choice from raw_unit_memory_ok, exposing the frontier and footprint obligations for every raw reachable state. Arbitrary contexts may have no entry witness; an empty or failing PHI entry is permitted by the existing package.

## Domain Constraints

No semantics changes, allocation/frontier bounds, budgets, strengthened assumptions, new axioms, remaining cheats, or edits to existing statements. No TRY/ORELSE wrapping proof search. Do not increase tactic timeouts. Use holbuild, never Holmake or an interactive g/e/p session. Keep proofs short and avoid generated variable names. Preserve all other files and do not push or open a PR.

## Available Resources

- venom/codegen/defs/contextCodegenRelScript.sml: active_inst, enters_block, fn_entry_inv, reachability_closed, codegen_reachability_package.
- venom/codegen/proofs/contextCodegenRelPropsScript.sml: introduction/elimination lemmas for the package and all three closure clauses.
- venom/codegen/proofs/contextReachabilityChecksScript.sml: concrete normalization, postincrement, post-PHI, callee entry and aggregate return witnesses.
- venom/compiler/unitTransformDefsScript.sml: inst_mem_below_frontier, raw_unit_memory_ok and new equivalence.
- venom/defs/venomExecSemanticsScript.sml: exact execution semantics.
- venom/compiler/unitShapeDefsScript.sml: existing Inductive declaration and induction proof style.
- AGENTS.md and docs/HOL4_PROOF_CONTROL_LESSONS.md: repository conventions.

## Notes

The definition is generic in the context and initial state. Frontier and footprint proofs are separate consumers and out of scope.
