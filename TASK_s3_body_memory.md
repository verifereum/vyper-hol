# TASK: Prove body memory safety for S3

## Meta
Status: planned
Priority: P1
Created: 2026-11-02
Locations: lowering/bodyMemoryScript.sml and additive lowering memory proofs

## Theorem Statement (FROZEN)

The actual S3 body consumer, with exactly its existing outer hypotheses:

```sml
Theorem body_stmts_sim_mem:
  !d tops bindings ctx func cenv cx env env' ret_ty lctx RetQ ss es res es'.
    body_inv tops ctx cenv cx /\ supported_stmts tops bindings ss /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmts env ret_ty ss = SOME env' /\
    EVERY (stmt_exprs_ok cenv) ss /\
    call_evaluation_safe cx (int_calls_stmts ss) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
    eval_stmts cx ss es = (res, es') ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmts_env cenv lctx ret_ty ss) es res es'
```

The approved memory judgments are frozen:

```sml
Definition expr_sim_mem_def:
  expr_sim_mem ctx func cenv cx ty e es <=>
    !sa sb op res es' s0.
      lower_value compile_expr cenv ty e sa = (op, sb) /\
      (do result <- eval_expr cx e; read_result cx result od) es = (res, es') /\
      expr_res_ok res /\ fn_has_code sa sb func /\
      res <> INR (Error (RuntimeError "convert empty bytes to signed")) /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa ==>
      frag_exec_mem ctx sa sb
        (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\
             alloca_history func s)
        (\s. ?v. res = INL v /\
          expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
          s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s)
        (expr_exit res)
End

Definition expr_vv_sim_mem_def:
  expr_vv_sim_mem ctx func cenv cx ty e es <=>
    !sa sb vv res es' s0.
      compile_expr cenv ty e sa = (vv, sb) /\
      eval_expr cx e es = (res, es') /\ expr_vv_res_ok res /\
      res <> INR (Error (RuntimeError "convert empty bytes to signed")) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa ==>
      frag_exec_mem ctx sa sb
        (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\
             alloca_history func s)
        (\s. ?tv. res = INL tv /\
          vv_post ctx func cenv cx e es sa sb s0 es' tv vv s /\
          s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s)
        (expr_exit res)
End

Definition stmt_frag_mem_def:
  stmt_frag_mem d ctx func cx lctx RetQ cenv
    (m : compile_env compiler) es res es' <=>
    !sa sb s0 cenv'.
      m sa = (cenv', sb) /\ fn_has_code sa sb func /\
      fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
      return_buf_frame d cenv sa s0 /\
      ~block_is_terminated sa /\ stmt_res_ok lctx res /\
      res <> INR (Error (RuntimeError "convert empty bytes to signed")) /\
      stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\
      ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      (?s cenv''.
         stmt_lands lctx sb res s /\ ~s.vs_halted /\
         (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv') /\
         cenv_top_ext cenv cenv'' es'.scopes /\
         stmt_state_rel ctx func cenv'' cx es' s /\ alloca_history func s /\
         (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
                lookup_var x s = SOME w) /\
         (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                  FLOOKUP s.vs_allocas aid = SOME b) /\
         return_buf_frame d cenv'' sb s /\
         s0.vs_alloca_next <= s.vs_alloca_next /\
         !fuel r. run_from fuel ctx func s = r /\ (!e. r <> Error e) ==>
                  ?fuel'. run_from fuel' ctx func s0 = r /\
                    (mem_safe_run fuel ctx func s ==>
                     mem_safe_run fuel' ctx func s0)) \/
      (?fuel r. run_from fuel ctx func s0 = r /\ exit_result r /\
                stmt_exit RetQ es' res r /\ mem_safe_run fuel ctx func s0)
End
```

These ten already-proved public composition/control statements remain frozen;
repair their proofs under the approved definitions and preserve all existing
successful proof code:

```sml
Theorem compile_pass_frag_mem:
  !d ctx func cx lctx RetQ cenv ty es.
    stmt_frag_mem d ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty Pass) es
      (INL ()) es

Theorem stmt_frag_nil_mem:
  !d ctx func cx lctx RetQ cenv ty es.
    stmt_frag_mem d ctx func cx lctx RetQ cenv (stmts_env cenv lctx ty []) es
      (INL ()) es

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

Theorem compile_break_frag_mem:
  !d ctx func cx RetQ cenv ty ex inc es.
    stmt_frag_mem d ctx func cx (InLoop ex inc) RetQ cenv
      (stmt_env cenv (InLoop ex inc) ty Break) es (INR BreakException) es

Theorem compile_continue_frag_mem:
  !d ctx func cx RetQ cenv ty ex inc es.
    stmt_frag_mem d ctx func cx (InLoop ex inc) RetQ cenv
      (stmt_env cenv (InLoop ex inc) ty Continue) es (INR ContinueException)
      es

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

Theorem compile_raise_frag_mem:
  !d ctx func cx lctx RetQ cenv ty rk es res es'.
    (rk = RaiseBare \/ rk = RaiseUnreachable) /\
    eval_stmt cx (Raise rk) es = (res, es') ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty (Raise rk))
      es res es'

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

```

Do not modify these statements. Prove them as-is, or produce a counterexample.
The return_buf_frame and frame_ret_ok_mem definitions are also unchanged.

## Completion Criteria

1. Prove body_stmts_sim_mem through actual compiled expression/target/statement,
   loop and internal-call execution footprints. This theorem must consume the
   body proofs; adding a body-footprint assumption or renaming an admission
   does not deliver it.
2. bodyMemoryTheory, bodyMemoryDefsTheory, stmtMemoryTheory,
   stmtControlMemoryTheory and fragLoopMemoryTheory build with all existing
   kernel guards intact. No newly admitted helpers or changed public premises.
3. Keep every frozen statement and definition exactly unchanged. Preserve
   existing successful proofs, except the narrowly scoped dependency repair
   authorized in Domain Constraints below. Commit only proof sources and
   necessary roots.
4. No change to functional S1 judgments, source semantics, executable compiler
   definitions, supported-program checks, top-level S3 assumptions or GAS
   counting judgments. No new axiom, timeout override, TRY/ORELSE search wrapper.

## Build

`holbuild -j2 build bodyMemoryTheory stmtMemoryTheory stmtControlMemoryTheory fragLoopMemoryTheory`

## Background

This is the body half of S3. Entry/halt/FMP and final whole-run composition are
owned separately. The body consumer is copied from loweringMemCorrect's named
body admission, including arbitrary caller buffer descriptor d and RetQ.
Its actual S3 consumer instantiates d=NONE and RetQ=(\v es r. T).

The approved memory sibling judgments carry a caller-owned return-buffer frame,
frontier monotonicity and allocation history at the actual entry and every
continuing landing. The inner result guard excludes only the existing exempt
empty-bytes-to-signed RuntimeError. The outer body statement is unchanged.
The generic control proofs need the same history and guard plumbing.

## Domain Constraints

- Scope: additive memory proof theories, existing memory composition proof
  repairs and required holproject build roots. S1 functional files are read-only
  except for the proof of slice_bytes_builtin_success_type in
  semantics/prop/vyperTypeBuiltinsScript.sml: split the repeated timed-out gvs
  at lines 1258–1260 into smaller simplification steps. This proof-only exception
  preserves its theorem statement, all definitions and the default 2.5s budget.
  Edit no other S1 proof. Build vyperTypeBuiltinsTheory, commit this repair
  separately, and report its exact hunk for the shared load-timeout record
  before continuing the conditional-expression consumer.
- Keep shared definitions frozen. Shared helper contexts use records/tuples,
  never let in a theorem statement. Private local lemma contracts can be fixed
  if their intended statements are false, but report each change.
- No new body/expression/target/loop/call safety premise. Establish footprints
  from actual producers, allocation provenance, typing and state relations.
- Do not edit allocation-history producer dependency files in this task;
  their proofs are owned separately. An unchecked dependency is not permission
  to remove an existing kernel guard or import a circular memory admission.
- Pre-existing functional admissions outside this task may remain dependencies;
  identify them honestly. Do not use lower_vyper_runtime_unit_run_mem_safe,
  lower_vyper_runtime_unit_memory_ok, body_stmts_sim_mem from another theory,
  or any newly admitted memory theorem to prove this theorem.
- Terminal callee Halt/Abort/Error need no caller history post. Normal caller
  continuation and internal returns must retain cross-frame buffer provenance.
- Safety covers every executed prefix including Error/stuck paths. Conditional
  frag_exec_mem normal-continuation transfer alone does not establish this;
  the final body result must support the actual S3 continuation composition.
- Use the default 2.5-second budget. Do not modify checked public leaf proofs
  except the explicit slice_bytes_builtin_success_type proof-only repair above.

## Available Resources

- lowering/bodyMemoryDefsScript.sml: approved return frame, frontier/history,
  expression/statement/return memory siblings.
- lowering/stmtMemoryScript.sml, stmtControlMemoryScript.sml,
  fragLoopMemoryScript.sml: ten checked prior generic rules, to migrate.
- lowering/fragExecMemScript.sml and venom/compiler/memSafeRunScript.sml:
  prefix/fuel and fragment memory transfer.
- lowering/instMemFrontierScript.sml and
  lowering/allocaFootprintScript.sml: opcode, buffer/local/return leaf tools.
- venom/proofs/allocaHistoryScript.sml and
  lowering/allocaHistoryFragmentScript.sml: actual cursor/allocation-history
  producer closure (separate owner dependency).
- lowering/builtinBytesMemoryScript.sml and concatMemoryScript.sml:
  checked byte builtins and fixed/dynamic Concat chunks.
- lowering/bodySimScript.sml, bodySimMainScript.sml,
  bodySimStmtCasesScript.sml, bodySimDeclCasesScript.sml,
  exprSimHypsScript.sml: read-only functional
  context, typing and producer facts. Reuse them rather than duplicating S1.
- lowering/defs/exprLoweringScript.sml, lowering/defs/stmtLoweringScript.sml:
  actual compiled producers, read-only.

## Notes

Owner performs exact frozen-statement comparisons, export checks and
dependency auditing after completion. Before each push, perform one
`holbuild -j4 build --skip-checkpoints` of the edited theories at the default
step limit, with proof steps and cache enabled; no second forced or CI-flag
replay is required. This supersedes the
stopped TASK_body_history_thread.md by including the approved guard and actual
body consumer on the current integration base. The old task is not amended.

Independent audit on the fresh merged source: the exact outer body theorem
is UNKNOWN, all ten public composition/control rules are PROVABLE at definition
level. Guard placement is correct for normal values/control outcomes and
excludes only the exact exempt RuntimeError. No validated full-premise body
counterexample was found; producer ranges and frame/call transport remain owed.

Parser status: bodyMemoryDefs with the approved guard parsed successfully.
The new body theorem has not yet been reached: the actual body-target build
stops in compile_expr_stmt_frag_ok_mem on propagation of the new result guard.
This is local migration work, not an external precondition. Preserve all
existing generic proofs and repair them.

The allocation-history dependency at88f21f48d is now merged. Its two definitions
and all nine principal producer/adapter statements are unchanged from the
independently audited freeze. Owner forced replay of allocaHistoryTheory and
allocaHistoryFragmentTheory passed114.508s with all nine principal exports
freshly saved/exported, nine clean kernel guards and no CHEAT. Execution,
block/run, callee-entry and normalized raw-sequence history facts are available
as checked dependencies. Preserve their proofs and kernel guards unchanged.
Report genuine blocking producer defects with an exercised witness rather than
adding premises, exclusions or definition workarounds.

The mutating-array loop diagnostic was independently audited: it is not a
complete refutation of the frozen body theorem because full source/frame/entry
hypotheses and both fragment branches were not certified. Actual pinned Python
9362e36b rejects the shown xs[1] assignment inside iteration over xs with
ImmutableViolation. Argon approved matching that active-iterator write policy
in type_stmt's For guard, keeping supported/body/stage hypotheses unchanged.
A separate worker delivered that checker repair in PR944, now merged into
this tree with the current integration dependencies at cdcd1bba8. These
executable sources remain read-only here. Continue body proof work without a new premise;
do not spend this task completing a refutation using a Python-rejected input.
The retired loop diagnostic was removed after its expected typing rejection
was checked; the checker regression remains in PR944. Owner forced replay of
bodyAllocMemoryTheory, bodyCopyMemoryTheory, bodyDeclMemoryTheory and
bodyMemoryPredsTheory passed at 7f3bfea5f with CI flags (585.553s) and default
2.5s steps (508.682s). Preserve their checked proofs, moved-theory imports and
kernel guards. The unfinished declaration wrapper is restored as a working
proof for this run; it is not part of the checked checkpoint.
