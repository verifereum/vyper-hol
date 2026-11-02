# TASK: Memory-safe conditional and control statements

## Meta
Status: planned
Priority: P1
Created: 2026-11-02
Location: lowering/stmtControlMemoryScript.sml

## Theorem Statement (FROZEN)

```sml
(* Memory-safe conditional and direct control statements. *)
Theory stmtControlMemory
Ancestors
  bodyMemoryDefs stmtSimIf stmtSim fragExecMem exprSim exprSimHyps
  exprLoweringProps stmtLowering compileEnv venomState venomExecSemantics
  vyperInterpreter vyperTypeSystem list finite_map
Libs
  monadsyntax

Theorem compile_break_frag_mem:
  !d ctx func cx RetQ cenv ty ex inc es.
    stmt_frag_mem d ctx func cx (InLoop ex inc) RetQ cenv
      (stmt_env cenv (InLoop ex inc) ty Break) es (INR BreakException) es
Proof
  cheat
QED

Theorem compile_continue_frag_mem:
  !d ctx func cx RetQ cenv ty ex inc es.
    stmt_frag_mem d ctx func cx (InLoop ex inc) RetQ cenv
      (stmt_env cenv (InLoop ex inc) ty Continue) es (INR ContinueException)
      es
Proof
  cheat
QED

Theorem compile_if_stmt_frag_mem:
  !d ctx func cx lctx RetQ cenv ty c ss1 ss2 es res es'.
    eval_stmt cx (If c ss1 ss2) es = (res, es') /\
    expr_type c = BaseT BoolT /\
    expr_sim_mem ctx func cenv cx (BaseT BoolT) c es /\
    (!sa op sb. lower_value compile_expr cenv (BaseT BoolT) c sa = (op, sb) ==>
                cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    cs_mono (stmts_env cenv lctx ty ss1) /\
    cs_mono (stmts_env cenv lctx ty ss2) /\
    (!b es1 res2 es2.
       (do result <- eval_expr cx c; read_result cx result od) es = (INL (BoolV b), es1) /\
       eval_stmts cx (if b then ss1 else ss2)
         (es1 with scopes := FEMPTY :: es1.scopes) = (res2, es2) ==>
       stmt_frag_mem d ctx func cx lctx RetQ cenv
         (stmts_env cenv lctx ty (if b then ss1 else ss2))
         (es1 with scopes := FEMPTY :: es1.scopes) res2 es2) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty (If c ss1 ss2))
      es res es'
Proof
  cheat
QED

Theorem compile_raise_frag_mem:
  !d ctx func cx lctx RetQ cenv ty rk es res es'.
    (rk = RaiseBare \/ rk = RaiseUnreachable) /\
    eval_stmt cx (Raise rk) es = (res, es') ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty (Raise rk))
      es res es'
Proof
  cheat
QED

Theorem compile_assert_frag_mem:
  !d ctx func cx lctx RetQ cenv ty e ak es res es'.
    (ak = AssertBare \/ ak = AssertUnreachable) /\
    eval_stmt cx (Assert e ak) es = (res, es') /\
    expr_type e = BaseT BoolT /\
    expr_sim_mem ctx func cenv cx (BaseT BoolT) e es /\
    (!sa op sb. lower_value compile_expr cenv (BaseT BoolT) e sa = (op, sb) ==>
                cs_extends sa sb) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty (Assert e ak))
      es res es'
Proof
  cheat
QED

```

Do not modify these statements. Prove them as-is, or produce a counterexample.
The definitions in lowering/bodyMemoryDefsScript.sml are frozen too.

## Completion Criteria

1. `holbuild -j2 build stmtControlMemoryTheory` passes with all five target cheats removed.
2. No new admissions, axioms, changed executable definitions or timeout overrides.
3. Commit only proof sources and build registrations for an essential helper. No task, focus, state, dossier or logs in the proof commit.
4. A false frozen statement must be reported with an exercised counterexample; do not amend it.

## Build

From the project root:
```
holbuild -j2 build stmtControlMemoryTheory
```
Owner performs forced replay, fresh interface inspection and kernel-tag audits afterward. Generated-artifact file searches are not required for this task's completion.

## Background

These are the additive memory-safe counterparts of S1's conditional, break, continue, bare raise and bare assert rules. They retain the approved caller-return-buffer frame at continuing landings and the memory-safe transfer or exit witness. Other body constructor proofs will consume these rules; this task does not assume a whole-body footprint or alter the shared S1 interface.

## Domain Constraints

- Keep all five exact public theorem statements and the body-memory definitions unchanged.
- Preserve existing proof code. No executable-definition changes, no new stage/source premises or supported-subset checks.
- Default 2.5s per tactic; no overrides, no TRY/ORELSE around proof search, no new cheats or axioms.
- Use holbuild, not interactive sessions or explicit loads. Register any essential helper theory declaratively.
- Edit only stmtControlMemoryScript.sml and essential new helper files. Do not edit stmtMemoryScript.sml, fragLoopMemoryScript.sml, fragExecMemScript.sml, bodyMemoryDefsScript.sml or other workers' files. stmtMemory/fragLoopMemory still contain another run's independent scaffolds; they are not dependencies or targets of this task.

## Available Resources

- lowering/bodyMemoryDefsScript.sml: approved stmt_frag_mem d, expr_sim_mem and return-buffer frame transport/jump rules.
- lowering/stmtSimIfScript.sml: exact corresponding S1 conditional/raise/assert rules and producer-layout helpers.
- lowering/stmtSimScript.sml: exact S1 break/continue rules and loop landing/environment facts.
- lowering/fragExecMemScript.sml: safety transfer/exit/abort rules and the approved revert pair rule.
- lowering/instMemFrontierScript.sml: empty-range/control/memory instruction bounds.
- lowering/exprLoweringPropsScript.sml: unconditional compiler monotonicity and state/start helpers.
- lowering/defs/stmtLoweringScript.sml: actual control statement compiler.
- lowering/exprSimScript.sml: expr_post and old-variable/scope/frame clauses.

## Notes

An independent statement audit classified all five exact statements PROVABLE. All five parsed before launch: stmtControlMemoryTheory built with exactly the five expected scaffold CHEATs. The known bounded-ABI preload gap is outside these memory-free control wrappers and expression-hypothesis composition. No additional return-buffer or stage premise is proposed.
