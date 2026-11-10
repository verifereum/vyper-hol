Theory exprSimAbiEncodeTupleFresh
Ancestors
  exprSimAbiEncodeTupleCompletion exprSimVVFrame abiEncodeArgsSim
  abiDecoderReentry freshWrites varsExt exprSimProps loweringPosts
  compileEnv localPtrsProps finite_map pred_set arithmetic

Theorem abi_encode_local_region_drop_fresh:
  local_ptrs_reserved ce st ==>
  (local_region ce scopes (drop_fresh st s) n b sz <=>
   local_region ce scopes s n b sz)
Proof
  strip_tac >> simp[local_region_def] >>
  eq_tac >> rpt strip_tac >> goal_assum (drule_at Any) >>
  fs[local_ptrs_reserved_def] >> metis_tac[lookup_var_drop_fresh]
QED

Theorem abi_encode_wb_frame_drop_fresh:
  wb_frame ce es es' origin s0 s /\ origin.cs_next_var <= st.cs_next_var ==>
  wb_frame ce es es' origin s0 (drop_fresh st s)
Proof
  simp[wb_frame_def, locals_kept_def, popped_kept_def, drop_fresh_def] >>
  rpt strip_tac >> simp[GSYM drop_fresh_def] >>
  metis_tac[lookup_var_drop_fresh, freshWritesTheory.not_fresh_at_mono]
QED

Theorem abi_encode_expr_values_drop_fresh:
  local_ptrs_reserved ce st /\
  (!x. op = Var x ==> not_fresh_at st x) ==>
  (expr_val_rel cx ty v op (drop_fresh st s) <=> expr_val_rel cx ty v op s) /\
  (expr_val_at ce cx ty origin endst es v op (drop_fresh st s) <=>
   expr_val_at ce cx ty origin endst es v op s)
Proof
  strip_tac >>
  `eval_operand op (drop_fresh st s) = eval_operand op s` by
    (irule eval_operand_drop_fresh >> simp[]) >>
  simp[expr_val_rel_def, expr_val_at_def, abi_encode_local_region_drop_fresh,
       drop_fresh_def]
QED

Theorem abi_encode_args_post_drop_fresh:
  abi_args_post ctx func ce cx es origin st s0 es' args ops vs s /\
  EVERY (abi_decoder_operand_live st.cs_next_var) ops /\
  local_ptrs_reserved ce st /\ origin.cs_next_var <= st.cs_next_var ==>
  abi_args_post ctx func ce cx es origin st s0 es' args ops vs (drop_fresh st s)
Proof
  simp_tac bool_ss [abi_args_post_def] >> strip_tac >>
  conj_tac >- metis_tac[stmt_state_rel_drop_fresh] >>
  reverse conj_tac >- metis_tac[abi_encode_wb_frame_drop_fresh] >>
  qpat_x_assum `LIST_REL _ _ _` mp_tac >>
  qpat_x_assum `EVERY _ _` mp_tac >>
  qid_spec_tac `ops` >> Q.SPEC_TAC (`ZIP (args,vs)`, `evs`) >>
  Induct >> Cases_on `ops` >> simp[] >> rpt strip_tac >>
  `!x. h = Var x ==> not_fresh_at st x` by
    (Cases_on `h` >> fs[abi_decoder_operand_live_def,
      abi_decoder_older_vars_def, not_fresh_at_def, IN_DEF]) >>
  metis_tac[abi_encode_expr_values_drop_fresh]
QED

Theorem abi_encode_drop_final_fresh:
  st.cs_next_var <= final.cs_next_var ==>
  fresh_vars_wrt final (drop_fresh st s)
Proof
  rw[fresh_vars_wrt_def, drop_fresh_def, FDOM_DRESTRICT, IN_INTER,
     IN_DEF, not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]
QED
