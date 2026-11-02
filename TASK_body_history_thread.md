# TASK: Thread allocation history through body memory composition

## Meta
Status: planned
Priority: P1
Created: 2026-11-02
Locations: lowering/bodyMemoryDefsScript.sml, lowering/stmtMemoryScript.sml, lowering/stmtControlMemoryScript.sml

## Theorem Statement (FROZEN)

The three approved shared memory definitions and all ten existing public rule
statements below are frozen. Preserve the existing proofs and repair them;
do not replace proved code with cheats.

```sml
Definition expr_sim_mem_def:
  expr_sim_mem ctx func cenv cx ty e es <=>
    !sa sb op res es' s0.
      lower_value compile_expr cenv ty e sa = (op, sb) /\
      (do result <- eval_expr cx e; read_result cx result od) es = (res, es') /\
      expr_res_ok res /\ fn_has_code sa sb func /\
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
return_buf_frame and frame_ret_ok_mem definitions remain unchanged too.

## Completion Criteria

1. bodyMemoryDefsTheory, stmtMemoryTheory and stmtControlMemoryTheory build
   with their existing kernel guards intact and no added admissions.
2. Keep the public statements byte-for-byte unchanged. No new public premise.
3. No S1/source/compiler/semantics change, no axiom, timeout override or new cheat.
4. Commit only necessary proof changes, not task/harness/dossier files.

## Build

`holbuild -j2 build bodyMemoryDefsTheory stmtMemoryTheory stmtControlMemoryTheory`

## Background

The memory siblings retain allocation order from the actual start to every
continuing landing. The function's history predicate is tied to fixed producer
code; frag_exec_mem still quantifies over functions containing the fragment.
Terminal exits keep their original memory-safe witnesses and need no caller
history on propagated callee Halt/Abort/Error. Existing public composition and
control rules retain their statements. Generic frag_exec_loop_mem is unchanged.

All ten exact public statements were independently audited PROVABLE under the
threaded definitions. Three proof-internal control adapters currently omit the
new property: cond_jump_frag_mem, if_branch_frag_mem and its join variant;
the explicit if-outcome cut also needs history. These local contracts may be
restated to thread initial/continuing history; no public rule is restated.

## Domain Constraints

- Edit stmtMemoryScript.sml and stmtControlMemoryScript.sml, adding ancestors or
  essential local helper lemmas as needed. Keep shared definitions frozen.
- Existing proof-internal local helpers may be restated only to carry history.
- Do not alter return-buffer capacity/identity, frontier monotonicity, terminal
  results or any S1/S3/source premise.
- Keep default 2.5s budget; no TRY/ORELSE around proof search.
- Existing successful proofs stay in place. Never replace them with cheats.
- Do not edit/prove the allocation-history dependency in this worktree.
- No let in theorem statements.

## Available Resources

- venom/proofs/allocaHistoryScript.sml: exact frozen history definitions and
  entry/frame/jump/pair/actual-step/block/return closure statements.
- lowering/allocaHistoryFragmentScript.sml: normalized raw-sequence cursor adapter.
- lowering/bodyMemoryDefsScript.sml: approved shared pre/post threading.
- lowering/stmtMemoryScript.sml and stmtControlMemoryScript.sml: existing proofs.
- lowering/fragLoopMemoryScript.sml: existing generic invariant/jump composition.
- lowering/fragExecMemScript.sml: fragment memory sequencing and terminal witnesses.
- lowering/stmtSimScript.sml: functional composition rules, read-only.

## Notes

Allocation-history proofs are owned by a separate task in another worktree.
Do not remove kernel guards or loop around an admitted-dependency failure:
report it so the owner can merge the checked dependency before continuing.
Owner performs exact-statement comparison and forced replay after completion.
