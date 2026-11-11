Theory exprSimAbiEncodeTupleCountedFresh
Ancestors
  loweringStateRelDefs
  exprSimAbiEncodeTupleCounted exprSimAbiEncodeObserverExtension
  exprSimAbiEncodeTupleSuccess exprSimAbiEncodeTupleResources
  exprSimAbiEncodeTupleZero exprSimAbiEncodeStagedRawObserver
  exprSimAbiEncodeTranslatedZero abiEncodeArgsSim
  exprSimAbiEncodeStagedObserver exprSimAbiEncodeTranslatedNoBlock
  abiEncoderCounters abiBuiltinEncodeCode abiBuiltinEncodeContext abiBuiltinEncodeWord
  exprSimAbiEncodeRelabelObserver exprLoweringProps
  compileEnv venomState words list
  exprSimAbiEncodeRelabelResources exprSimAbiEncodeRelabelBoundary
  exprSimAbiEncodeObliviousSimulation exprSimAbiEncodeObliviousContext
  abiEncoderWindowContract abiBuiltinAllocation venomInst
  exprSimAbiGasBridge exprSimAbiEncodeSourceRoom exprSimAbiEncodeOblivious
  exprSimAbiEncodeNoBlockBoundary exprSimAbiEncodeNoBlockSafety
  exprSimAbiEncodeNonwordCase

Theorem abi_encode_tuple_relabel_observer_fresh_free:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid0) target args) es /\
  ~(LENGTH args = 1 /\ ~ensure) /\ mid = OPTION_MAP bytes_method_id_word mid0 /\
  eval_exprs cx args es = (INL vs,es') /\
  vyper_to_abi_list (get_tenv cx) (MAP expr_type args) vs = SOME avs /\
  abi_args_post ctx func ce cx es origin st s0 es' args values vs initial /\
  compile_alloc_buffer (abi_tuple_bytes ce (ZIP (values,MAP (lowered_value_type ce) args))) st = (buf,allocated) /\
  compile_store_abi_tuple ce buf.buf_operand 0 (ZIP (values,MAP (lowered_value_type ce) args)) allocated = ((),staged) /\
  s.vs_allocas = (abi_builtin_allocate_state st.cs_next_id
    (abi_tuple_bytes ce (ZIP (values,MAP (lowered_value_type ce) args))) initial).vs_allocas /\
  s.vs_alloca_next = (abi_builtin_allocate_state st.cs_next_id
    (abi_tuple_bytes ce (ZIP (values,MAP (lowered_value_type ce) args))) initial).vs_alloca_next /\
  eval_operand buf.buf_operand s = SOME (n2w sb) /\
  FLOOKUP s.vs_allocas st.cs_next_id = SOME (sb,abi_tuple_bytes ce (ZIP (values,MAP (lowered_value_type ce) args))) /\
  abi_encoder_open_input ei ct rv sb (abi_tuple_bytes ce (ZIP (values,MAP (lowered_value_type ce) args))) s.vs_memory /\
  enc ct rv = enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP expr_type args))) (ListV avs) /\
  lower_abi_encode ensure mid buf.buf_operand ei
    (abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args))) staged = (out,final) /\
  fn_has_code st allocated func /\ fn_has_code staged final func /\
  fn_inst_ids_distinct func /\ fn_inst_ids_distinct obs /\ obs.fn_name = func.fn_name /\
  (!j. MEM j (fn_insts obs) /\ j.inst_opcode <> STOP /\ j.inst_opcode <> NOP ==>
    MEM j (fn_insts func)) /\
  (!j. MEM j (fn_insts obs) ==> j.inst_opcode <> INVOKE) /\
  LENGTH ids = LENGTH staged.cs_current_insts /\
  fn_has_code (start_relabel L ids staged) (start_swap staged L ids final) obs /\
  staged.cs_blocks <> final.cs_blocks /\
  local_ptrs_reserved ce st /\ local_ptrs_reserved ce staged /\
  stmt_state_rel ctx func ce cx es' s /\ abi_encoder_admissible ei /\
  (!x. buf.buf_operand = Var x ==> not_fresh_at staged x) /\
  ~s.vs_halted /\ s.vs_inst_idx = LENGTH staged.cs_current_insts ==>
  ?p actual. abi_decode_sim ctx obs (s with vs_current_bb := L) actual /\
    ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    abi_encode_exec_frame obs (s with vs_current_bb := L) actual /\
    abi_encode_staged_observation ctx func ce cx es' staged out mid
      (32+32*word_size (abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args))+
        (case mid of NONE => 0 | SOME _ => 4))) p ct rv s actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_lower_phase_code >>
  disch_then (qx_choose_then `ops` (qx_choose_then `ready`
    (qx_choose_then `len` (qx_choose_then `body_end`
      (MAP_EVERY assume_tac o CONJUNCTS))))) >>
  drule_all abi_encode_tuple_relabel_resources >>
  disch_then (qspec_then `L` mp_tac) >> simp_tac bool_ss [LET_THM] >>
  disch_then (qx_choose_then `p` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  drule_all abi_encode_args_numerical_capacity >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all abi_encode_relabel_phase_equations >> disch_then (qspec_then `L` strip_assume_tac) >>
  drule_all abi_encode_relabel_finish_equation >> disch_then (qspec_then `L` assume_tac) >>
  qabbrev_tac `rst = start_relabel L ids staged` >>
  qabbrev_tac `rr = start_swap staged L ids ready` >>
  qabbrev_tac `re = start_swap staged L ids body_end` >>
  qabbrev_tac `rf = start_swap staged L ids final` >>
  qabbrev_tac `rs = s with vs_current_bb := L` >>
  `fn_has_code rst rr obs /\ fn_has_code rr re obs /\ fn_has_code re rf obs` by
    (drule_all abi_builtin_encode_code >> strip_tac >> asm_rewrite_tac []) >>
  suspend "phases"
QED

Resume abi_encode_tuple_relabel_observer_fresh_free[phases]:
  `~rs.vs_halted /\ rs.vs_current_bb = rst.cs_current_bb /\
   rs.vs_inst_idx = LENGTH rst.cs_current_insts` by
    (simp_tac (srw_ss()) [Abbr `rs`, Abbr `rst`, start_relabel_def] >> asm_rewrite_tac []) >>
  `rf.cs_current_bb = final.cs_current_bb /\
   LENGTH rf.cs_current_insts = LENGTH final.cs_current_insts` by
    (simp_tac (srw_ss()) [Abbr `rf`] >>
     `cs_extends staged final` by metis_tac[lower_abi_encode_extends] >>
     drule_all abi_encode_start_swap_control >>
     disch_then (qspecl_then [`ids`, `L`] strip_assume_tac) >> asm_rewrite_tac []) >>
  `stmt_state_rel ctx func ce cx es' rs /\ local_ptrs_reserved ce rst` by
    (simp_tac (srw_ss()) [Abbr `rs`, Abbr `rst`,
      abi_encode_stmt_rel_current_bb, abi_encode_start_relabel_resources] >> asm_rewrite_tac []) >>
  `!x. buf.buf_operand = Var x ==> not_fresh_at rst x` by
    (simp_tac (srw_ss()) [Abbr `rst`, abi_encode_start_relabel_resources] >> asm_rewrite_tac []) >>
  qpat_x_assum `abi_builtin_encode_setup _ _ staged = _` kall_tac >>
  qpat_x_assum `compile_abi_encode_to_buf _ _ _ ready = _` kall_tac >>
  qpat_x_assum `abi_builtin_encode_finish _ _ _ body_end = _` kall_tac >>
  drule_all abi_encode_translated_operand_liveness >> strip_tac >>
  `rst.cs_next_var <= rr.cs_next_var /\ rst.cs_next_var <= re.cs_next_var /\
   rr.cs_next_var <= rf.cs_next_var /\ re.cs_next_var <= rf.cs_next_var` by
    (simp_tac (srw_ss()) [Abbr `rst`, Abbr `rr`, Abbr `re`, Abbr `rf`,
      start_relabel_def, abi_encode_start_swap_resource_fields] >> decide_tac) >>
  qpat_x_assum `mid = OPTION_MAP _ _` kall_tac >>
  qpat_x_assum `enc ct rv = _` (fn th => rule_assum_tac (PURE_REWRITE_RULE [GSYM th])) >>
  `eval_operand buf.buf_operand rs = SOME (n2w sb)` by
    (simp_tac (srw_ss()) [Abbr `rs`] >>
     qpat_assum `eval_operand buf.buf_operand s = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `buf.buf_operand` >> simp[eval_operand_def, lookup_var_def]) >>
  `?actual. abi_decode_sim ctx obs rs actual /\ ~actual.vs_halted /\
    actual.vs_current_bb = rf.cs_current_bb /\
    actual.vs_inst_idx = LENGTH rf.cs_current_insts /\
    abi_encode_exec_frame obs rs actual /\
    abi_encode_staged_observation ctx func ce cx es' rst (FST ops) mid
      (32+32*word_size (abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args))+
        (case mid of NONE => 0 | SOME _ => 4))) p ct rv rs actual` by
    (irule abi_encode_staged_observer_no_fresh >>
     qpat_assum `abi_builtin_encode_setup _ _ rst = _` (irule_at Any) >>
     qpat_assum `compile_abi_encode_to_buf _ _ _ rr = _` (irule_at Any) >>
     qpat_assum `abi_builtin_encode_finish _ _ _ re = _` (irule_at Any) >>
     qpat_assum `abi_encoder_window_input _ _ _ _ _ _` (irule_at Any) >>
     qexistsl [`case mid of NONE => 0 | SOME _ => 32`, `rf`,
       `p+32+(case mid of NONE => 0 | SOME _ => 4)`] >>
     asm_rewrite_tac [] >>
     simp_tac (srw_ss()) [Abbr `rs`, eval_operand_def, lookup_var_def] >>
     rpt conj_tac >> decide_tac) >>
  qexistsl [`p`, `actual`] >> asm_rewrite_tac [] >>
  qpat_assum `abi_encode_staged_observation _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [Abbr `rst`, Abbr `rs`] >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp[abi_encode_staged_observation_def, start_relabel_def, not_fresh_at_def,
    local_region_def, lookup_var_def] >> metis_tac[]
QED

Finalise abi_encode_tuple_relabel_observer_fresh_free

Theorem abi_encode_tuple_counted_encoder_fresh_free:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid0) target args) es /\
  ~(LENGTH args = 1 /\ ~ensure) /\ mid = OPTION_MAP bytes_method_id_word mid0 /\
  eval_exprs cx args es = (INL vs,es') /\
  vyper_to_abi_list (get_tenv cx) (MAP expr_type args) vs = SOME avs /\
  abi_args_post ctx func ce cx es origin st s0 es' args values vs initial /\
  compile_alloc_buffer (abi_tuple_bytes ce (ZIP (values,MAP (lowered_value_type ce) args))) st = (buf,allocated) /\
  compile_store_abi_tuple ce buf.buf_operand 0 (ZIP (values,MAP (lowered_value_type ce) args)) allocated = ((),staged) /\
  s.vs_allocas = (abi_builtin_allocate_state st.cs_next_id
    (abi_tuple_bytes ce (ZIP (values,MAP (lowered_value_type ce) args))) initial).vs_allocas /\
  s.vs_alloca_next = (abi_builtin_allocate_state st.cs_next_id
    (abi_tuple_bytes ce (ZIP (values,MAP (lowered_value_type ce) args))) initial).vs_alloca_next /\
  eval_operand buf.buf_operand s = SOME (n2w sb) /\
  FLOOKUP s.vs_allocas st.cs_next_id = SOME (sb,abi_tuple_bytes ce (ZIP (values,MAP (lowered_value_type ce) args))) /\
  abi_encoder_open_input ei ct rv sb (abi_tuple_bytes ce (ZIP (values,MAP (lowered_value_type ce) args))) s.vs_memory /\
  enc ct rv = enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP expr_type args))) (ListV avs) /\
  ei = type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP (lowered_value_type ce) args)) /\
  lower_abi_encode ensure mid buf.buf_operand ei
    (abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args))) staged = (out,final) /\
  fn_has_code st allocated func /\ fn_has_code staged final func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce st /\ local_ptrs_reserved ce staged /\
  stmt_state_rel ctx func ce cx es' s /\ abi_encoder_admissible ei /\
  (!l. buf.buf_operand <> Label l) /\
  (!x. buf.buf_operand = Var x ==> not_fresh_at staged x) /\
  ~s.vs_halted /\ s.vs_current_bb = staged.cs_current_bb /\
  s.vs_inst_idx = LENGTH staged.cs_current_insts ==>
  ?p actual. gas_marked_path F ctx func s 0 (OK actual) /\
    ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    abi_encode_staged_observation ctx func ce cx es' staged out mid
      (32+32*word_size (abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args))+
        (case mid of NONE => 0 | SOME _ => 4))) p ct rv s actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all lower_abi_encode_frag_facts >> strip_tac >>
  qabbrev_tac `Q = \actual. ?p.
    abi_encode_staged_observation ctx func ce cx es' staged out mid
      (32+32*word_size (abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args))+
        (case mid of NONE => 0 | SOME _ => 4))) p ct rv s actual` >>
  `(!t rd. Q t ==> Q (t with vs_returndata := rd)) /\
   (!t prev. Q t ==> Q (t with vs_prev_bb := prev))` by simp[Abbr `Q`] >>
  `?t. gas_marked_path F ctx func s 0 (OK t) /\ Q t /\ ~t.vs_halted /\
    t.vs_current_bb = final.cs_current_bb /\ t.vs_inst_idx = LENGTH final.cs_current_insts`
    suffices_by
    (strip_tac >> qpat_x_assum `Q t` mp_tac >>
     simp_tac bool_ss [Abbr `Q`] >> strip_tac >>
     qexistsl [`p`, `t`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  Cases_on `staged.cs_blocks = final.cs_blocks` >- suspend "no_blocks" >> suspend "blocks"
QED

Resume abi_encode_tuple_counted_encoder_fresh_free[no_blocks]:
  irule abi_decode_sim_gas_path >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists `staged` >> reverse conj_tac >- metis_tac[] >>
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_tuple_no_block_observer >> strip_tac >>
  qexists `actual` >> asm_rewrite_tac [] >>
  simp_tac bool_ss [Abbr `Q`] >> qexists `p` >> first_assum ACCEPT_TAC
QED

Resume abi_encode_tuple_counted_encoder_fresh_free[blocks]:
  irule abi_decode_sim_gas_path_relabel >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- metis_tac[abi_encode_endpoint_nonempty] >>
  qexists `staged` >> reverse conj_tac >- metis_tac[] >>
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_tuple_relabel_observer_fresh_free >> strip_tac >>
  qexists `actual` >> asm_rewrite_tac [] >>
  simp_tac bool_ss [Abbr `Q`] >> qexists `p` >> first_assum ACCEPT_TAC
QED

Finalise abi_encode_tuple_counted_encoder_fresh_free
