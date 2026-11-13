(* Memory-safe body judgments.  Caller-owned return buffers survive entry
   into a fresh callee allocation map, so their identity and capacity are
   carried separately from the callee's allocation sites. *)
Theory bodyMemoryDefs
Ancestors
  instMemFrontier
  exprSimMemDefs stmtSimDefs
  loweringPosts
  bodySim stmtSimDefs exprSimDefs exprSimHypsDefs fragExecMem memSafeRun allocaHistory compileEnv loweringStateRelDefs
  exprLowering exprLoweringProps context venomState venomExecSemantics
  intCallFrame fragGasPath fragGasMode fragExec gasSummary gasOutcome venomExecProofs
  vyperInterpreter vyperTypeSystem vyperTypeCallGraph list finite_map words

(* The size in ce_return_buf describes a pointer slot.  Capacity below is
   the actual caller allocation, supplied by the declared return layout. *)

Theorem return_buf_frame_frame:
  !d cenv cenv' sa sb s s'.
    return_buf_frame d cenv sa s /\
    cenv'.ce_return_buf = cenv.ce_return_buf /\
    sa.cs_next_var <= sb.cs_next_var /\
    (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
           lookup_var x s' = SOME w) /\
    s.vs_alloca_next <= s'.vs_alloca_next ==>
    return_buf_frame d cenv' sb s'
Proof
  rpt gen_tac >> Cases_on `d`
  >- simp[return_buf_frame_def] >>
  rename1 `return_buf_frame (SOME pair)` >> PairCases_on `pair` >>
  rw[return_buf_frame_def] >>
  qexistsl_tac [`x`, `slot_size`] >> simp[] >>
  fs[not_fresh_at_def] >> rpt strip_tac >>
  qpat_x_assum `!n. sa.cs_next_var <= n ==> _`
    (qspec_then `n` mp_tac) >> simp[]
QED

(* ===== The caller-buffer frontier along a run ===== *)

Theorem gas_path_edge_alloca_prefix[local]:
  !ctx fn s n t lo.
    gas_path_edge ctx fn s n (OK t) /\ alloca_prefix lo s ==>
    alloca_prefix lo t
Proof
  rw[gas_path_edge_def] >>
  `result_allocas_above lo (step_inst fuel ctx inst s)` by
    (irule step_inst_allocas_above >>
     fs[alloca_prefix_def, allocas_above_def] >> metis_tac[]) >>
  rpt (qpat_x_assum `OK _ = _` (assume_tac o SYM)) >>
  gvs[result_allocas_above_def, exit_result_def] >>
  imp_res_tac eval_phis_preserves_alloca_fields >>
  fs[alloca_prefix_def, allocas_above_def] >> metis_tac[]
QED

Theorem gas_path_alloca_prefix:
  !ctx fn s n r.
    gas_path ctx fn s n r ==>
    !t lo. r = OK t /\ alloca_prefix lo s ==> alloca_prefix lo t
Proof
  Induct_on `gas_path` >> rw[exit_result_def] >>
  metis_tac[gas_path_edge_alloca_prefix]
QED

(* Every allocation a run makes is at or above the frontier it started
   from, so the allocation part of ret_buf_frontier holds wherever a
   fragment's run lands. *)
Theorem gas_marked_exec_alloca_prefix:
  !memory ctx func source es s0 marks res es_end t lo.
    gas_marked_exec memory (ctx, func) source (es, s0) marks res es_end
      (OK t) /\ alloca_prefix lo s0 ==>
    alloca_prefix lo t
Proof
  rw[gas_marked_exec_def] >> drule gas_marked_path_exec >>
  metis_tac[gas_path_alloca_prefix]
QED

(* A run's normal landings keep every allocation-frontier prefix of its
   start. *)
Theorem gas_outcome_alloca_prefix:
  !memory tops ctx func source es s Q R.
    gas_outcome memory tops (ctx,func) source (es,s) Q R ==>
    gas_outcome memory tops (ctx,func) source (es,s)
      (\res ee t. Q res ee t /\
                  !lo. alloca_prefix lo s ==> alloca_prefix lo t) R
Proof
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> BETA_TAC >>
  rpt strip_tac >> qexists_tac `marks` >| [
    disj1_tac >> metis_tac[gas_marked_exec_alloca_prefix],
    disj1_tac >> metis_tac[],
    disj2_tac >> metis_tac[]]
QED

(* Control-flow fields don't touch the frontier. *)
Theorem ret_buf_frontier_control:
  !d cenv s pb cb ix.
    ret_buf_frontier d cenv
      (s with <| vs_prev_bb := pb; vs_current_bb := cb; vs_inst_idx := ix |>) <=>
    ret_buf_frontier d cenv s
Proof
  Cases_on `d` >> simp[ret_buf_frontier_def] >>
  rename1 `SOME pair` >> PairCases_on `pair` >>
  simp[ret_buf_frontier_def, alloca_prefix_def, lookup_var_def]
QED

(* A fragment's landing keeps the frontier: the locals it had keep their
   pointers, and those it declares are allocations of the run. *)
Theorem ret_buf_frontier_post:
  !d cenv cenv'' sa s0 t.
    ret_buf_frontier d cenv s0 /\ local_ptrs_reserved cenv sa /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
           lookup_var x t = SOME w) /\
    (!lo. alloca_prefix lo s0 ==> alloca_prefix lo t) /\
    (!n p sz.
       FLOOKUP cenv''.ce_vars n <> FLOOKUP cenv.ce_vars n /\
       FLOOKUP cenv''.ce_vars n = SOME (PtrVar (Var p) sz) ==>
       ?aid w sz'. lookup_var p t = SOME w /\
                   FLOOKUP t.vs_allocas aid = SOME (w2n w, sz')) ==>
    ret_buf_frontier d cenv'' t
Proof
  rpt gen_tac >> Cases_on `d`
  >- simp[ret_buf_frontier_def] >>
  rename1 `SOME pair` >> PairCases_on `pair` >>
  simp[ret_buf_frontier_def] >> strip_tac >>
  rpt strip_tac >>
  `alloca_prefix (pair1 + w2n pair0) t` by metis_tac[] >>
  Cases_on `FLOOKUP cenv''.ce_vars n = FLOOKUP cenv.ce_vars n`
  >- (`?w. lookup_var p s0 = SOME w /\ pair1 + w2n pair0 <= w2n w` by
        metis_tac[] >>
      `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
      metis_tac[]) >>
  first_x_assum drule_all >> strip_tac >>
  fs[alloca_prefix_def] >> metis_tac[]
QED

(* Two landings in a row: a local new at the second is an allocation of
   the second run, or an allocation of the first that the second kept. *)
Theorem new_locals_alloca_trans:
  !cenv c c2 sm t t'.
    (!n p sz.
       FLOOKUP c.ce_vars n <> FLOOKUP cenv.ce_vars n /\
       FLOOKUP c.ce_vars n = SOME (PtrVar (Var p) sz) ==>
       ?aid w sz'. lookup_var p t = SOME w /\
                   FLOOKUP t.vs_allocas aid = SOME (w2n w, sz')) /\
    (!n p sz.
       FLOOKUP c2.ce_vars n <> FLOOKUP c.ce_vars n /\
       FLOOKUP c2.ce_vars n = SOME (PtrVar (Var p) sz) ==>
       ?aid w sz'. lookup_var p t' = SOME w /\
                   FLOOKUP t'.vs_allocas aid = SOME (w2n w, sz')) /\
    local_ptrs_reserved c sm /\
    (!x w. not_fresh_at sm x /\ lookup_var x t = SOME w ==>
           lookup_var x t' = SOME w) /\
    (!aid b. FLOOKUP t.vs_allocas aid = SOME b ==>
             FLOOKUP t'.vs_allocas aid = SOME b) ==>
    !n p sz.
      FLOOKUP c2.ce_vars n <> FLOOKUP cenv.ce_vars n /\
      FLOOKUP c2.ce_vars n = SOME (PtrVar (Var p) sz) ==>
      ?aid w sz'. lookup_var p t' = SOME w /\
                  FLOOKUP t'.vs_allocas aid = SOME (w2n w, sz')
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  reverse (Cases_on `FLOOKUP c2.ce_vars n = FLOOKUP c.ce_vars n`)
  >- metis_tac[] >>
  `?aid w sz'. lookup_var p t = SOME w /\
               FLOOKUP t.vs_allocas aid = SOME (w2n w, sz')` by
    (`FLOOKUP c.ce_vars n <> FLOOKUP cenv.ce_vars n /\
      FLOOKUP c.ce_vars n = SOME (PtrVar (Var p) sz)` by metis_tac[] >>
     metis_tac[]) >>
  `not_fresh_at sm p` by metis_tac[local_ptrs_reserved_def] >>
  metis_tac[]
QED

Theorem return_buf_frame_jump_to:
  !d cenv sa l s.
    return_buf_frame d cenv sa (jump_to l s) <=>
    return_buf_frame d cenv sa s
Proof
  rpt gen_tac >> Cases_on `d`
  >- simp[return_buf_frame_def] >>
  rename1 `return_buf_frame (SOME pair)` >> PairCases_on `pair` >>
  simp[return_buf_frame_def, lookup_var_def, jump_to_def]
QED

(* Frontier monotonicity also preserves caller buffers absent from the
   callee's allocation map.  The other expression postconditions are S1's. *)


(* The buffer frame applies at concrete entries and at every continuing
   landing, including break and continue.  Terminal exits carry their own
   memory-safe run witness. *)

Definition frame_ret_ok_mem_def:
  frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty <=>
    !cenv' env lctx eo es.
      same_frame cenv cenv' /\ expr_sim_inv cenv' cx env es /\
      stmt_exprs_ok cenv' (Return eo) /\
      IS_SOME (type_stmt env ret_ty (Return eo)) /\
      call_evaluation_safe cx (int_calls_stmt (Return eo)) /\
      (!e ty. eo = SOME e ==>
              expr_sim_mem ctx func cenv' cx ty e es /\
              expr_vv_sim_mem ctx func cenv' cx ty e es) ==>
      stmt_frag_mem d ctx func cx lctx RetQ cenv'
        (stmt_env cenv' lctx ret_ty (Return eo)) (eval_stmt cx (Return eo)) es
End

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_MEMORY_FRAME_AUDIT OK\n"
     else raise Fail "body memory frame inherited admission"
  end) [return_buf_frame_frame, return_buf_frame_jump_to,
        mem_safe_run_all_fuel, frag_exec_mem_complete];

Theorem body_local_region_frontier:
  stmt_state_rel ctx func ce cx es s /\
  local_region ce es.scopes s name b sz ==>
  b + sz <= s.vs_alloca_next
Proof
  pure_rewrite_tac [stmt_state_rel_def, state_rel_def] >>
  rpt strip_tac >>
  qpat_x_assum `local_ptrs_rel _ _ _ _` mp_tac >>
  gvs[local_region_def, local_ptrs_rel_def] >>
  strip_tac >>
  qpat_x_assum `!name entry p sz. _` drule >>
  simp[] >> strip_tac >> gvs[]
QED

Theorem body_local_region_subrange:
  stmt_state_rel ctx func ce cx es s /\
  local_region ce es.scopes s name b sz /\ off + n <= sz ==>
  b + off + n <= s.vs_alloca_next
Proof
  rpt strip_tac >> drule_all body_local_region_frontier >> decide_tac
QED

Theorem body_local_ptr_MLOAD_frontier:
  stmt_state_rel ctx func ce cx es s /\
  local_region ce es.scopes s name b sz /\ 32 <= sz /\
  lookup_var p s = SOME (n2w b) ==>
  inst_mem_below_frontier (mk_inst iid MLOAD [Var p] outs) s
Proof
  rpt strip_tac >>
  drule_all body_local_region_frontier >> strip_tac >>
  `b < dimword (:256)` by
    (fs[local_region_def] >> metis_tac[w2n_lt]) >>
  simp[below_frontier_MLOAD, eval_operand_def] >> decide_tac
QED

