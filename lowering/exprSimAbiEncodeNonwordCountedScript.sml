Theory exprSimAbiEncodeNonwordCounted
Ancestors
  loweringStateRelDefs
  exprSimAbiEncodeNonwordNoBlock exprSimAbiEncodeRelabelObserver
  exprSimAbiEncodeOblivious exprSimAbiGasBridge
  list words venomState exprSimHash exprSimAbiEncodeExecFrame exprSimAbiEncodeSemantic
  exprSimAbiEncodeRelabelBoundary exprLoweringProps loweringPosts compileEnv venomMemDefs

Theorem abi_encode_stmt_rel_prev_bb[local]:
  stmt_state_rel ctx func ce cx es (s with vs_prev_bb := L) <=>
  stmt_state_rel ctx func ce cx es s
Proof
  `fmp_room ctx func (s with vs_prev_bb := L) <=> fmp_room ctx func s` by
    (irule fmp_room_fields_cong >> simp[]) >>
  simp[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def,
    local_region_def, local_backed_def, lookup_var_def, storage_rel_def,
    transient_rel_def, accounts_rel_def, immutables_rel_def, logs_rel_def, call_ctx_rel_def,
    contract_storage_def, contract_transient_def, alloca_inv_def,
    allocas_non_overlapping_def, alloca_next_valid_def, alloca_room_def,
    pending_alloca_size_def, immutable_alloca_sep_def, immutable_base_zero_alt]
QED

Theorem abi_encode_nonword_counted_suffix:
  expr_post ctx func ce cx e es origin sa s0 es' v op s /\
  expr_body_pre ce cx env e es /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid0) ty [e]) es /\
  mid = OPTION_MAP bytes_method_id_word mid0 /\
  ~is_word_type (expr_type e) /\
  abi_enc_plan (get_tenv cx) (lowered_value_type ce e) ei /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi (get_tenv cx) (lowered_value_type ce e) v = SOME av /\
  lower_abi_encode F mid op ei (abi_size_bound ce.ce_struct_fields (lowered_value_type ce e))
    sa = (out,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  (!l. op <> Label l) /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (sa.cs_blocks = sb.cs_blocks \/ sb.cs_current_insts <> [] \/
   !bb. lookup_block sb.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) ==>
  ?p actual.
    gas_marked_path F ctx func s 0 (OK actual) /\
    let bytes = enc (vyper_to_abi_type (get_tenv cx) (lowered_value_type ce e)) av in
    let m = case mid of NONE => 0 | SOME _ => 4 in
    eval_operand out actual = SOME (n2w p) /\
    mload p actual = n2w (LENGTH bytes+m) /\
    mem_bytes_at (p+32+m) (LENGTH bytes) actual.vs_memory = bytes /\
    (case mid of NONE => T | SOME selector =>
      mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes selector) /\
    ~actual.vs_halted /\ actual.vs_current_bb = sb.cs_current_bb /\
    actual.vs_inst_idx = LENGTH sb.cs_current_insts /\
    stmt_state_rel ctx func ce cx es' actual /\
    LENGTH s.vs_memory <= LENGTH actual.vs_memory /\
    actual.vs_fmp = s.vs_fmp /\ actual.vs_call_ctx = s.vs_call_ctx /\
    actual.vs_data_section = s.vs_data_section /\
    abi_encode_semantic_obs actual = abi_encode_semantic_obs s /\
    (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
      lookup_var x actual = SOME w) /\
    (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==>
      FLOOKUP actual.vs_allocas aid = SOME row) /\
    (!aid off sz. FLOOKUP s.vs_allocas aid = SOME(off,sz) /\ aid < sa.cs_next_id ==>
      mem_bytes_at off sz actual.vs_memory = mem_bytes_at off sz s.vs_memory) /\
    (!name b n. local_region ce es'.scopes s name b n ==>
      mem_bytes_at b n actual.vs_memory = mem_bytes_at b n s.vs_memory) /\
    FLOOKUP actual.vs_allocas sa.cs_next_id =
      SOME(p,32+32*word_size(abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)+(case mid of NONE => 0 | SOME _ => 4))) /\
    p+(32+32*word_size(abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)+(case mid of NONE => 0 | SOME _ => 4))) <= actual.vs_alloca_next /\
    actual.vs_alloca_next < dimword (:256)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all lower_abi_encode_frag_facts >> strip_tac >>
  qabbrev_tac `Q = \actual.
    stmt_state_rel ctx func ce cx es' actual /\
    LENGTH s.vs_memory <= LENGTH actual.vs_memory /\
    actual.vs_fmp = s.vs_fmp /\ actual.vs_call_ctx = s.vs_call_ctx /\
    actual.vs_data_section = s.vs_data_section /\
    abi_encode_semantic_obs actual = abi_encode_semantic_obs s /\
    (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
      lookup_var x actual = SOME w) /\
    (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==>
      FLOOKUP actual.vs_allocas aid = SOME row) /\
    (!aid off sz. FLOOKUP s.vs_allocas aid = SOME(off,sz) /\ aid < sa.cs_next_id ==>
      mem_bytes_at off sz actual.vs_memory = mem_bytes_at off sz s.vs_memory) /\
    (!name b n. local_region ce es'.scopes s name b n ==>
      mem_bytes_at b n actual.vs_memory = mem_bytes_at b n s.vs_memory) /\
    ?p. FLOOKUP actual.vs_allocas sa.cs_next_id =
      SOME(p,32+32*word_size(abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)+(case mid of NONE => 0 | SOME _ => 4))) /\
    p+(32+32*word_size(abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)+(case mid of NONE => 0 | SOME _ => 4))) <= actual.vs_alloca_next /\
    actual.vs_alloca_next < dimword (:256) /\
    eval_operand out actual = SOME (n2w p) /\
    mload p actual = n2w (LENGTH (enc (vyper_to_abi_type (get_tenv cx) (lowered_value_type ce e)) av) +
      (case mid of NONE => 0 | SOME _ => 4)) /\
    mem_bytes_at (p+32+(case mid of NONE => 0 | SOME _ => 4))
      (LENGTH (enc (vyper_to_abi_type (get_tenv cx) (lowered_value_type ce e)) av)) actual.vs_memory =
      enc (vyper_to_abi_type (get_tenv cx) (lowered_value_type ce e)) av /\
    (case mid of NONE => T | SOME selector =>
      mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes selector)` >>
  `(!t rd. Q t ==> Q (t with vs_returndata := rd)) /\
   (!t prev. Q t ==> Q (t with vs_prev_bb := prev))` by
    (Cases_on `out` >> simp[Abbr `Q`, mload_def, eval_operand_def, lookup_var_def,
       hash_returndata_state_rel, abi_encode_stmt_rel_prev_bb,
       abi_encode_semantic_obs_updates] >> metis_tac[]) >>
  Cases_on `sa.cs_blocks = sb.cs_blocks`
  >- suspend "no_blocks" >>
  suspend "blocks"
QED

Resume abi_encode_nonword_counted_suffix[no_blocks]:
  `?t. gas_marked_path F ctx func s 0 (OK t) /\ Q t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts`
    suffices_by
    (strip_tac >> qpat_x_assum `Q t` mp_tac >>
     simp_tac bool_ss [Abbr `Q`] >> strip_tac >>
     qexistsl_tac [`p`, `t`] >> simp_tac bool_ss [LET_THM] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  irule abi_decode_sim_gas_path >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists `sa` >> reverse conj_tac >- metis_tac[] >>
      rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
      drule_all abi_encode_nonword_no_block_observer >>
      simp_tac bool_ss [LET_THM] >> strip_tac >>
      qexists `actual` >> conj_tac
      >- (fs[abi_encode_exec_frame_def] >>
          simp_tac bool_ss [Abbr `Q`] >>
          ntac 10 (conj_tac >- first_assum ACCEPT_TAC) >>
          qexists `p` >> asm_rewrite_tac[]) >>
      gvs[]
QED
Resume abi_encode_nonword_counted_suffix[blocks]:
  `?t. gas_marked_path F ctx func s 0 (OK t) /\ Q t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts`
    suffices_by
    (strip_tac >> qpat_x_assum `Q t` mp_tac >>
     simp_tac bool_ss [Abbr `Q`] >> strip_tac >>
     qexistsl_tac [`p`, `t`] >> simp_tac bool_ss [LET_THM] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  irule abi_decode_sim_gas_path_relabel >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- metis_tac[] >>
  qexists `sa` >> reverse conj_tac >- metis_tac[] >>
      rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
      drule_all abi_encode_nonword_relabel_observer >>
      simp_tac bool_ss [LET_THM] >> strip_tac >>
      qexists `actual` >> conj_tac
      >- (fs[abi_encode_exec_frame_def] >>
          simp_tac bool_ss [Abbr `Q`] >>
          ntac 10 (conj_tac >- first_assum ACCEPT_TAC) >>
          qexists `p` >> asm_rewrite_tac[]) >>
      gvs[]
QED
Finalise abi_encode_nonword_counted_suffix
