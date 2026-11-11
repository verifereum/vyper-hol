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

