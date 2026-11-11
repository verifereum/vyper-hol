Theory exprSimAbiEncodeRelabelBoundary
Ancestors
  exprSimAbiEncodeProducerExecution exprSimAbiEncodeOblivious
  exprLoweringProps loweringPosts compileEnv abiBuiltinEncodeCode exprSimAbiGasBridge
  abiEncoderCounters abiBuiltinEncodeContext venomState venomExecSemantics venomMemDefs fragExec list rich_list

Theorem abi_encode_stmt_rel_current_bb:
  stmt_state_rel ctx func ce cx es (s with vs_current_bb := L) <=>
  stmt_state_rel ctx func ce cx es s
Proof
  `fmp_room ctx func (s with vs_current_bb := L) <=> fmp_room ctx func s` by
    (irule fmp_room_fields_cong >> simp[]) >>
  simp[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def,
    local_region_def, local_backed_def, lookup_var_def, storage_rel_def,
    transient_rel_def, accounts_rel_def, immutables_rel_def, logs_rel_def, call_ctx_rel_def,
    contract_storage_def, contract_transient_def, alloca_inv_def,
    allocas_non_overlapping_def, alloca_next_valid_def, alloca_room_def,
    pending_alloca_size_def, immutable_alloca_sep_def, immutable_base_zero_alt]
QED

Theorem abi_encode_expr_post_relabel:
  expr_post ctx func ce cx e es origin sa s0 es' v op s ==>
  expr_post ctx func ce cx e es origin (start_relabel L ids sa) s0 es' v op
    (s with vs_current_bb := L)
Proof
  Cases_on `op` >>
  simp[expr_post_def, start_relabel_def, abi_encode_stmt_rel_current_bb,
    expr_val_rel_def, expr_val_at_def, local_region_def, lookup_var_def,
    eval_operand_def, locals_kept_def] >>
  strip_tac >> asm_rewrite_tac []
QED

Theorem abi_encode_start_relabel_resources:
  local_ptrs_reserved ce (start_relabel L ids sa) = local_ptrs_reserved ce sa /\
  (!x. not_fresh_at (start_relabel L ids sa) x = not_fresh_at sa x) /\
  (fresh_vars_wrt (start_swap sa L ids sb) (s with vs_current_bb := L) =
    fresh_vars_wrt sb s)
Proof
  simp[start_relabel_def, start_swap_def, local_ptrs_reserved_def,
    not_fresh_at_def, fresh_vars_wrt_def, LET_THM] >>
  IF_CASES_TAC >> simp[]
QED

Theorem abi_encode_start_swap_control:
  sa.cs_blocks <> sb.cs_blocks /\ cs_extends sa sb ==>
  (start_swap sa L ids sb).cs_current_bb = sb.cs_current_bb /\
  LENGTH (start_swap sa L ids sb).cs_current_insts = LENGTH sb.cs_current_insts /\
  (start_swap sa L ids sb).cs_next_var = sb.cs_next_var
Proof
  strip_tac >> gvs[cs_extends_def] >>
  simp[start_swap_def, emitted_blocks_def, LENGTH_APPEND, TAKE_APPEND, LET_THM, NULL_EQ]
QED

Theorem abi_encode_lower_phase_code:
  lower_abi_encode ensure mid src info maxlen sa = (out,sb) /\
  fn_has_code sa sb func ==>
  ?ops ready len body_end.
    abi_builtin_encode_setup mid maxlen sa = (ops,ready) /\
    compile_abi_encode_to_buf (SND ops) src info ready = (len,body_end) /\
    abi_builtin_encode_finish (FST ops) len
      (case mid of NONE => 0 | SOME _ => 4) body_end = ((),sb) /\
    out = FST ops /\
    fn_has_code sa ready func /\ fn_has_code ready body_end func /\
    fn_has_code body_end sb func /\
    ready.cs_blocks = sa.cs_blocks /\ sb.cs_blocks = body_end.cs_blocks /\
    sa.cs_next_var <= ready.cs_next_var /\
    ready.cs_next_var <= body_end.cs_next_var /\
    body_end.cs_next_var <= sb.cs_next_var
Proof
  strip_tac >> drule lower_abi_encode_trace >> strip_tac >>
  drule_all abi_builtin_encode_code >> strip_tac >>
  qexistsl_tac [`ops`, `ready`, `len`, `body_end`] >> asm_rewrite_tac[]
QED
