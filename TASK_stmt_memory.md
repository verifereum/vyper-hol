# TASK: Memory-safe statement composition

## Meta
Status: planned
Priority: P1
Created: 2026-11-02
Location: lowering/stmtMemoryScript.sml

## Theorem Statement (FROZEN)

Four statement rules and one loop rule:

```sml
(* Memory-safe counterparts of the statement composition rules. *)
Theory stmtMemory
Ancestors
  bodyMemoryDefs stmtSim fragExecMem compileEnv stmtLowering exprSim
  exprSimHyps exprLoweringProps venomState venomExecSemantics
  vyperInterpreter vyperTypeSystem list finite_map

Theorem compile_pass_frag_mem:
  !d ctx func cx lctx RetQ cenv ty es.
    stmt_frag_mem d ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty Pass) es
      (INL ()) es
Proof
  cheat
QED

Theorem stmt_frag_nil_mem:
  !d ctx func cx lctx RetQ cenv ty es.
    stmt_frag_mem d ctx func cx lctx RetQ cenv (stmts_env cenv lctx ty []) es
      (INL ()) es
Proof
  cheat
QED

Theorem stmt_frag_cons_env_mem:
  !d ctx func cx lctx RetQ cenv ty stmt ss es res es'.
    eval_stmts cx (stmt::ss) es = (res, es') /\
    (!c. cs_mono (compile_stmt c lctx ty stmt)) /\
    (!c. cs_mono (stmts_env c lctx ty ss)) /\
    (!r1 es1. eval_stmt cx stmt es = (r1, es1) ==>
       stmt_frag_mem d ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty stmt)
         es r1 es1) /\
    (!es1 c sa sm. eval_stmt cx stmt es = (INL (), es1) /\
                   stmt_env cenv lctx ty stmt sa = (c, sm) /\
                   cenv_top_ext cenv c es1.scopes ==>
       stmt_frag_mem d ctx func cx lctx RetQ c (stmts_env c lctx ty ss)
         es1 res es') ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv (stmts_env cenv lctx ty (stmt::ss))
      es res es'
Proof
  cheat
QED

Theorem compile_expr_stmt_frag_ok_mem:
  !d ctx func cx lctx RetQ cenv ty e es res es'.
    eval_stmt cx (Expr e) es = (res, es') /\
    expr_vv_sim_mem ctx func cenv cx (expr_type e) e es /\
    (!sa vv sb tv es1.
       storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
       eval_expr cx e es = (INL tv, es1) /\
       compile_expr cenv (expr_type e) e sa = (vv, sb) /\
       ~block_is_terminated sa ==> ~block_is_terminated sb) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty (Expr e))
      es res es'
Proof
  cheat
QED

```

```sml
(* Memory-safe composition of the loop layout emitted by lowering. *)
Theory fragLoopMemory
Ancestors
  fragExecMem fragExec compileEnv emitHelper exprLoweringProps
  venomState venomExecSemantics list

Theorem frag_exec_loop_mem:
  !ctx st0 st1 sth stj st2 stb ste st3 stx hdr body exit cnd
   x0 x1 x2 x3 x4 x5 I J N R.
    emit_inst JMP [Label hdr] [] st0 = (x0, st1) /\
    new_block hdr st1 = (x1, sth) /\
    emit_inst JNZ [cnd; Label exit; Label body] [] stj = (x2, st2) /\
    new_block body st2 = (x3, stb) /\
    emit_inst JMP [Label hdr] [] ste = (x4, st3) /\
    new_block exit st3 = (x5, stx) /\
    cs_extends sth stj /\ cs_extends stb ste /\
    (!k s l. I k s ==> I k (jump_to l s)) /\
    (!k s l. J k s ==> J k (jump_to l s)) /\
    (!k. k <= N ==> frag_exec_mem ctx sth stj (I k) (J k) R) /\
    (!k s. k <= N /\ J k s ==>
           ?w. eval_operand cnd s = SOME w /\ (w = 0w <=> k < N)) /\
    (!k. k < N ==> frag_exec_mem ctx stb ste (J k) (I (SUC k)) R) ==>
    frag_exec_mem ctx st0 stx (I 0) (J N) R
Proof
  cheat
QED

```

Do not modify these statements. Prove them as-is, or produce a counterexample.
The definitions in lowering/bodyMemoryDefsScript.sml are frozen too.

## Completion Criteria

1. `holbuild -j2 build stmtMemoryTheory fragLoopMemoryTheory` passes with all five scaffold cheats removed.
2. No added admissions, axioms, timeout overrides, or changed executable definitions.
3. Commit only the proof source and any essential proof helper theory/build registration. Do not commit task-state, logs, focus, dossier or task files.
4. If a frozen statement is false, report the exercised counterexample and stop rather than changing it.

## Build

From the project root:
```
holbuild -j2 build stmtMemoryTheory fragLoopMemoryTheory
```
Owner performs forced CI-flags replay and kernel dependency audits after completion.

## Background

These rules lift memory-safe expression fragments through effect-only expression statements and compose statement lists while preserving a caller-owned return buffer. They are additive counterparts of existing S1 statement rules. They will support a body induction consumed by the runtime memory-safety proof. They do not assume a whole-body footprint. The currently known ABI preload gap is outside this composition-only task.

## Domain Constraints

- Keep the exact five public theorem statements and the approved body-memory definitions fixed. Helper statements introduced only within this task may be adjusted to prove them.
- Preserve existing proofs and all S1/source/stage assumptions.
- Default 2.5s per tactic. No timeout overrides, no TRY/ORELSE around proof search, no new cheats or axioms.
- No new executable definitions or changes to other theories' semantics.
- No interactive REPL; use holbuild. No explicit loads to repair dependency metadata.
- Do not edit holproject.toml beyond registering a necessary helper theory. Do not touch fragExecMemScript.sml or bodyMemoryDefsScript.sml.

## Available Resources

- lowering/bodyMemoryDefsScript.sml: approved return_buf_frame, its transport helpers, expr_vv_sim_mem and stmt_frag_mem.
- lowering/stmtSimScript.sml: exact S1 rules corresponding to the four frozen statements; stmt_lands, ret_pc_ok, environment and code-splitting helpers.
- lowering/fragExecMemScript.sml: memory-safe fragment and continuation rules.
- lowering/exprSimScript.sml: vv_post and expression invariants.
- lowering/exprLoweringPropsScript.sml: compiler monotonicity including compile_expr_ci_mono.
- lowering/defs/stmtLoweringScript.sml: actual statement compiler.
- lowering/bodySimScript.sml: same-frame and body interfaces.

## Notes

All five exact statements were independently classified PROVABLE against the actual definitions before this task was frozen. They parsed successfully before launch, and parsed again after integrating the approved revert-forward memory boundary. The frame and all-fuel helper kernel audits also passed on that merged boundary. New definitions and theorem hypotheses are outside this task; report a real contradiction rather than amending them.
