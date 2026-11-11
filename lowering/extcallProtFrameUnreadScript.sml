(* Ordinary head preparation, shared by invariant-carrying unread recursion. *)
Theory extcallProtFrameUnread
Ancestors
  exprExtRequestUnreadCps exprExtRequestStrongCapture exprExtRequestHistory
  exprExtRequestSourceFrame exprExtRequestReadProbe exprExtRequestOperandSafety
  exprOperandVar exprSafeOperand exprLoweringProps loweringPosts exprSimProps
  exprSimWordArgs exprSimSource exprSimHypsDefs exprSimDefs compileEnv
  vyperCallOutcomeFrame vyperInterpreter vyperState gasSummary fragGasMode
  fragGasPath exprExtRequestGasBind stmtSimProps pair finite_map context

Theorem extcall_protframe_unread_head:
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  expr_body_pre ce cx env e es /\ ~expr_has_effect e /\
  ci_mono sa sm /\ local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  stmt_state_rel ctx func ce cx es s0 /\
  vv_post ctx func ce cx e es sa sm s0 (ee with gas_obs := []) r vv t /\
  (!tail. eval_expr cx e (es with gas_obs := used ++ tail) =
     (INL r,ee with gas_obs := tail)) /\
  extrequest_strong_captures ctx func ce cx old_es old_rs old_vvs
    (es with gas_obs := []) sa s0 /\
  (!ty p w tv. vv = LocatedValue ty p /\
    eval_operand p.ptr_operand t = SOME w /\
    evaluate_type (get_tenv cx) ty = SOME tv ==>
    (p.ptr_location = LocStorage ==>
      storage_read_live cx F (get_storage cx (ee with gas_obs := []) F) w tv) /\
    (p.ptr_location = LocTransient ==>
      storage_read_live cx T (get_storage cx (ee with gas_obs := []) T) w tv)) /\
  (!n b sz. local_region ce es.scopes s0 n b sz ==>
    mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s0.vs_memory) /\
  (!off len.
    (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      sa.cs_next_id <= inst.inst_id /\
      FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==>
      compileEnv$regions_disjoint off len b sz) ==>
    mem_bytes_at off len t.vs_memory = mem_bytes_at off len s0.vs_memory) ==>
  stmt_state_rel ctx func ce cx (ee with gas_obs := []) t /\
  vv_post ctx func ce cx e (es with gas_obs := []) sa sm s0
    (ee with gas_obs := []) r vv t /\
  extrequest_read_frame cx (es with gas_obs := []) (ee with gas_obs := []) /\
  wb_frame ce es sa s0 t /\
  extrequest_strong_capture ctx func ce cx e r vv (ee with gas_obs := []) sm t /\
  extrequest_strong_captures ctx func ce cx old_es old_rs old_vvs
    (ee with gas_obs := []) sm t
Proof
  strip_tac >>
  `!l. vv_operand vv <> Label l` by
    (irule (cj 1 extrequest_compiler_nonlabel) >>
     goal_assum (drule_at Any) >> qexists `env` >>
     qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
     simp[expr_body_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    metis_tac[CONJUNCT1 compiler_compile_var] >>
  `safe_operand sm (vv_operand vv)` by simp[safe_operand_def] >>
  `extrequest_strong_capture ctx func ce cx e r vv (ee with gas_obs := []) sm t` by
    (irule extrequest_strong_capture_intro >>
     qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     gvs[ci_mono_def] >> conj_tac
     >- (irule post_value_type_not_int_call >> metis_tac[expr_has_effect_thm]) >>
     Cases_on `vv` >> gvs[vv_operand_def]) >>
  `extrequest_read_frame cx (es with gas_obs := []) (ee with gas_obs := [])` by
    (drule extrequest_pure_expr_read_frame >>
     rewrite_tac[state_rel_frame_result] >>
     disch_then (qspecl_then
       [`cx`, `es with gas_obs := used`, `INL r`, `ee with gas_obs := []`] mp_tac) >>
     qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` assume_tac) >>
     fs[extrequest_read_frame_def]) >>
  `vv_post ctx func ce cx e (es with gas_obs := []) sa sm s0
     (ee with gas_obs := []) r vv t` by simp[vv_post_initial_gas] >>
  `stmt_state_rel ctx func ce cx (ee with gas_obs := []) t /\
   wb_frame ce es sa s0 t` by (gvs[vv_post_def, wb_frame_def, locals_kept_def] >> metis_tac[]) >>
  simp[] >> irule extrequest_strong_captures_extend >>
  qpat_assum `extrequest_strong_captures _ _ _ _ _ _ _ _ sa s0` (irule_at Any) >>
  qpat_assum `vv_post _ _ _ _ _ (es with gas_obs := []) _ _ _ _ _ _ _`
    (irule_at Any) >> gvs[ci_mono_def] >> metis_tac[]
QED
