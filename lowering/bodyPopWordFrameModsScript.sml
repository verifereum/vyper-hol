(* Transport the reached Pop post across its read-only word load. *)
Theory bodyPopWordFrameMods
Ancestors
  bodyFullPostsMods bodyForRangeScalarFrameMods bodyFullUnwrapRun
  bodyPtrSignedConvertSourceFrame bodyPtrDefs exprSimProps exprSimMemDefs
  loweringPosts loweringStateRelDefs freshWrites vyperAST venomState

Theorem pop_word_read_frame_mods:
  valid_horizon cx st0 H ee.storage_trace /\
  vv_post_mods H ctx func ce cx (Pop ann bt) es sa sm s0 ee tv vv s /\
  ghost_inv_at_mods D lo d ce cx ee G tn s /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
  post_value_type ce (Pop ann bt) = t /\ is_word_type t /\
  evaluate_type (get_tenv cx) t = SOME rt /\
  read_result cx tv ee = (INL v,ee) /\ value_has_type rt v /\
  eval_operand op u = SOME (typed_val_to_w256 rt v) /\
  op_taint tf op = {} /\ op_prov Gf op = NONE /\
  local_ptrs_reserved ce sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  u = s with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|> /\
  (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s /\
         FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
  tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm ==>
  expr_post_mods H ctx func ce cx (Pop ann bt) es sa sb s0 ee v op u /\
  ghost_inv_at_mods D lo d ce cx ee Gf tf u /\
  ghost_kept_at lo ce es sa G0 tn0 s0 Gf tf /\
  expr_store_bound cx t v op u /\ ptr_val_ok cx t v op Gf tf u
Proof
  strip_tac >>
  `u.vs_memory = s.vs_memory /\ u.vs_data_section = s.vs_data_section /\
   u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
   u.vs_call_ctx = s.vs_call_ctx /\ u.vs_accounts = s.vs_accounts /\
   u.vs_transient = s.vs_transient /\ u.vs_immutables = s.vs_immutables` by
    (qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => pure_once_rewrite_tac[th] >> simp[])) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  simp[expr_store_bound_word, ptr_val_ok_word] >>
  conj_tac
  >- (qpat_x_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
      `stmt_state_rel H ctx func ce cx ee u` by
        (irule stmt_state_rel_readonly_vars_pc >> qexistsl [`s`,`sm`] >> simp[]) >>
      `immutable_frame_mods func ce cx ee u` by
        (irule immutable_frame_mods_exterior_frame >> qexistsl [`ee`,`s`,`sm`] >> simp[]) >>
      drule_all_then assume_tac locals_kept_mem_tail >>
      `ann = t` by fs[post_value_type_def, expr_type_def] >>
      simp[expr_post_mods_def, expr_post_def, post_value_type_def, expr_type_def,
           expr_val_rel_def, expr_val_at_def] >>
      first_assum ACCEPT_TAC) >>
  conj_tac
  >- (irule ghost_inv_at_mods_exterior_frame >>
      qexistsl [`G`,`ee`,`s`,`sm`,`tn`] >> simp[]) >>
  irule ghost_kept_at_clean_suffix >> qexistsl [`G`,`tn`] >> simp[]
QED
