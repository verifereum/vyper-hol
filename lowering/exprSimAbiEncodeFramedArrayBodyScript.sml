Theory exprSimAbiEncodeFramedArrayBody
Ancestors
  exprSimAbiEncodeFramedPhases exprSimAbiEncodeFramedBuiltin
  abiEncoderWindowArrayBody abiEncoderArrayBodyCode abiEncoderArrayCode
  abiEncoderWindowArrayInvariant abiEncoderWindowArrayLayout arithmetic
  abiEncoderAdmissible pred_set abiEncoderArrayTail
  abiEncoderWindowSequence abiEncoderWindowPhase abiEncoderWindowContract
  exprSimAbiEncodeExecFrame venomExecSemantics venomState venomMemDefs
  exprLoweringProps emitHelper emitHelperProps compileEnv fragExec
  venomInstProofs1 venomInst list rich_list words abiDecoderDynamicLoopSetup instIdxIndep

Theorem abi_encode_framed_ordinary_pure_sequence:
  window_pure_seq st en s t /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode /\
    ~is_ext_call_op i.inst_opcode /\ i.inst_opcode <> INVOKE /\
    i.inst_opcode <> SETFMP /\ i.inst_opcode <> DALLOCA) (emitted_insts st en) ==>
  abi_encode_exec_frame func s t
Proof
  strip_tac >>
  `run_inst_seq (emitted_insts st en) s = OK t` by
    gvs[window_pure_seq_def, window_seq_def] >>
  `t.vs_fmp = s.vs_fmp` by
    (irule (BETA_RULE (Q.ISPEC `\s:venom_state. s.vs_fmp`
      run_inst_seq_preserves_field)) >>
     qexists_tac `emitted_insts st en` >>
     simp[window_pure_seq_def, window_seq_def] >>
     rpt strip_tac >> irule step_inst_base_preserves_fmp_ordinary >>
     qexists_tac `i` >> simp[] >> fs[EVERY_MEM]) >>
  gvs[window_pure_seq_def, abi_encode_exec_frame_def, pending_alloca_size_def]
QED

Theorem abi_encode_framed_array_addresses_opcodes:
  abi_encode_array_addresses ip src dst asz msz st = (coords,en) ==>
  EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode /\
    ~is_ext_call_op i.inst_opcode /\ i.inst_opcode <> INVOKE /\
    i.inst_opcode <> SETFMP /\ i.inst_opcode <> DALLOCA) (emitted_insts st en)
Proof
  simp[abi_encode_array_addresses_def, abi_decode_array_head_setup_def,
    abi_decode_indexed_coordinates_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def, is_alloca_op_def,
    is_ext_call_op_def]
QED

Theorem abi_encode_framed_array_addresses_phase:
  abi_encode_array_addresses ip src dst asz msz st = (coords,en) /\
  eval_operand ip s = SOME (n2w slot) /\ slot < dimword (:256) /\
  mload slot s = n2w j /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand dst s = SOME (n2w d) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_phase ctx func st en {} [] s t /\
    eval_operand (FST (FST coords)) t = SOME (n2w j) /\
    eval_operand (SND (FST coords)) t = SOME (n2w (sb+32+j*msz)) /\
    eval_operand (FST (SND coords)) t = SOME (n2w (d+32)) /\
    eval_operand (SND (SND coords)) t = SOME (n2w (d+32+j*asz)) /\
    (!x. FST (FST coords) = Var x \/ SND (FST coords) = Var x \/
         FST (SND coords) = Var x \/ SND (SND coords) = Var x ==> not_fresh_at en x) /\
    (!x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s) /\
    abi_encode_exec_frame func s t
Proof
  strip_tac >> drule_all window_array_addresses_pure_observed >> strip_tac >>
  drule abi_encode_framed_array_addresses_opcodes >> strip_tac >>
  `abi_encode_exec_frame func s t` by
    (drule_all abi_encode_framed_ordinary_pure_sequence >> simp[]) >>
  qexists_tac `t with vs_inst_idx := LENGTH en.cs_current_insts` >>
  (conj_tac >- metis_tac[window_pure_seq_phase]) >>
  simp_tac (srw_ss()) [eval_op_inst_idx, lookup_var_def] >>
  asm_rewrite_tac[] >> metis_tac[lookup_var_def]
QED

Theorem abi_encode_framed_array_element_run:
  window_array_root ctx func owner ids ei asz msz active ty avs src dst sb cap d s /\
  j < LENGTH avs /\ owner.cs_next_var <= ready.cs_next_var /\
  window_alloca_sites func (frag_ids ready en) SUBSET ids /\
  fn_has_code ready en func /\
  eval_operand child_src s = SOME (n2w (sb+32+j*msz)) /\
  eval_operand child_dst s = SOME (n2w (d+off)) /\
  (!x. child_src = Var x \/ child_dst = Var x ==> not_fresh_at ready x) /\
  off+LENGTH (enc ty (EL j avs)) <= LENGTH (enc (Array NONE ty) (ListV avs)) /\
  ~s.vs_halted /\ s.vs_current_bb = ready.cs_current_bb /\
  s.vs_inst_idx = LENGTH ready.cs_current_insts /\
  abi_encode_framed_contract ei /\
  compile_abi_encode_to_buf child_dst child_src ei ready = (out,en) ==>
  ?t. window_array_transition ctx func owner
      (window_alloca_sites func (frag_ids ready en))
      [(d+off,LENGTH (enc ty (EL j avs)))] s t /\
    window_strong_result ctx func ready en out ty (EL j avs) (d+off) s t /\
    abi_encode_exec_frame func s t
Proof
  strip_tac >> drule_all window_array_root_live_pre >> strip_tac >>
  qpat_x_assum `abi_encode_framed_contract ei` mp_tac >>
  rewrite_tac[abi_encode_framed_contract_def] >> disch_then drule_all >> strip_tac >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  irule window_array_child_transition >> asm_rewrite_tac[] >> metis_tac[]
QED

Theorem abi_encode_framed_array_static_element_run:
  window_array_root ctx func owner ids ei asz msz F ty avs src dst sb cap d s /\
  abi_encoder_array_prefix ty avs j d s.vs_memory /\ j < LENGTH avs /\
  owner.cs_next_var <= ready.cs_next_var /\
  window_alloca_sites func (frag_ids ready en) SUBSET ids /\
  fn_has_code ready en func /\
  eval_operand child_src s = SOME (n2w (sb+32+j*msz)) /\
  eval_operand child_dst s = SOME (n2w (d+32+j*asz)) /\
  (!x. child_src = Var x \/ child_dst = Var x ==> not_fresh_at ready x) /\
  ~s.vs_halted /\ s.vs_current_bb = ready.cs_current_bb /\
  s.vs_inst_idx = LENGTH ready.cs_current_insts /\
  abi_encode_framed_contract ei /\
  compile_abi_encode_static_info child_dst child_src ei ready = (out,en) ==>
  ?t. window_array_transition ctx func owner
      (window_alloca_sites func (frag_ids ready en))
      [(d+32+j*asz,LENGTH (enc ty (EL j avs)))] s t /\
    window_strong_result ctx func ready en out ty (EL j avs) (d+32+j*asz) s t /\
    abi_encoder_array_prefix ty avs (SUC j) d t.vs_memory /\
    abi_encode_exec_frame func s t
Proof
  strip_tac >>
  `abi_encoder_admissible (AbiDynArray ei asz msz F) /\
   abi_encoder_window_input (AbiDynArray ei asz msz F)
     (Array NONE ty) (ListV avs) sb cap s.vs_memory` by fs[window_array_root_def] >>
  `asz = abi_member_head_size ty /\ ~is_dynamic ty` by
    fs[abiEncoderWindowTheory.abi_encoder_window_array_iff] >>
  `compile_abi_encode_to_buf child_dst child_src ei ready = (out,en)` by
    metis_tac[window_array_static_info_eq] >>
  `32+j*asz+LENGTH (enc ty (EL j avs)) <=
    LENGTH (enc (Array NONE ty) (ListV avs))` by
    (drule_all window_array_prefix_step_geometry >> strip_tac >>
     `j*abi_member_head_size ty+LENGTH (enc ty (EL j avs)) <=
        LENGTH avs*abi_member_head_size ty` by metis_tac[] >>
     drule window_array_layout >> strip_tac >> asm_rewrite_tac[] >>
     qpat_x_assum `j * _ + LENGTH _ <= _` mp_tac >> decide_tac) >>
  `?t. window_array_transition ctx func owner
      (window_alloca_sites func (frag_ids ready en))
      [(d+(32+j*asz),LENGTH (enc ty (EL j avs)))] s t /\
    window_strong_result ctx func ready en out ty (EL j avs) (d+(32+j*asz)) s t /\
    abi_encode_exec_frame func s t` by
    (irule abi_encode_framed_array_element_run >> asm_rewrite_tac[] >>
     qexistsl_tac [`F`, `asz`, `cap`, `child_dst`, `child_src`, `dst`, `ei`,
       `ids`, `msz`, `sb`, `src`] >> asm_rewrite_tac[ADD_ASSOC]) >>
  qexists_tac `t` >> full_simp_tac bool_ss [ADD_ASSOC] >> asm_rewrite_tac[] >>
  irule window_array_prefix_static_advance >>
  `abi_encoder_array_prefix ty avs j d t.vs_memory` by
    (irule window_array_static_prefix_frame >> metis_tac[]) >>
  `mem_bytes_at (d+32+j*abi_member_head_size ty)
      (LENGTH (enc ty (EL j avs))) t.vs_memory = enc ty (EL j avs)` by
    metis_tac[window_strong_result_public, abi_encoder_window_result_output] >>
  metis_tac[]
QED

Theorem abi_encode_framed_array_static_body_run:
  window_array_root ctx func st ids ei asz msz F ty avs src dst sb cap d s /\
  abi_encoder_array_prefix ty avs j d s.vs_memory /\ j < LENGTH avs /\
  eval_operand ip s = SOME (n2w slot) /\ slot < dimword (:256) /\
  mload slot s = n2w j /\
  abi_encode_array_static_body ip src dst ei asz msz st = (out,en) /\
  window_alloca_sites func (frag_ids st en) SUBSET ids /\
  fn_has_code st en func /\ abi_encode_framed_contract ei /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_array_transition ctx func st
      (window_alloca_sites func (frag_ids st en))
      [(d+32+j*asz,LENGTH (enc ty (EL j avs)))] s t /\
    abi_encoder_array_prefix ty avs (SUC j) d t.vs_memory /\
    eval_operand out t = SOME (n2w j) /\
    t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts /\
    abi_encode_exec_frame func s t
Proof
  strip_tac >>
  `abi_encoder_static_leaf ei` by
    fs[window_array_root_def, Once abi_encoder_admissible_def] >>
  drule_all abi_encode_array_static_body_context >> strip_tac >> gvs[] >>
  `?p. window_phase ctx func st prepared {} [] s p /\
    eval_operand (FST (FST coords)) p = SOME (n2w j) /\
    eval_operand (SND (FST coords)) p = SOME (n2w (sb+32+j*msz)) /\
    eval_operand (FST (SND coords)) p = SOME (n2w (d+32)) /\
    eval_operand (SND (SND coords)) p = SOME (n2w (d+32+j*asz)) /\
    (!x. FST (FST coords) = Var x \/ SND (FST coords) = Var x \/
      FST (SND coords) = Var x \/ SND (SND coords) = Var x ==>
      not_fresh_at prepared x) /\
    abi_encode_exec_frame func s p` by
    (full_simp_tac bool_ss [window_array_root_def] >>
     drule_all abi_encode_framed_array_addresses_phase >> metis_tac[]) >>
  `window_array_transition ctx func st {} [] s p` by
    metis_tac[window_array_pure_phase_transition] >>
  `window_array_root ctx func st ids ei asz msz F ty avs src dst sb cap d p` by
    (irule window_array_root_transition >> metis_tac[EMPTY_SUBSET, EVERY_DEF]) >>
  `abi_encoder_array_prefix ty avs j d p.vs_memory` by
    (irule window_array_prefix_registered_frame >>
     reverse conj_tac >- metis_tac[window_array_root_def] >>
     qexistsl_tac [`{}`, `[]`, `s`] >>
     asm_rewrite_tac[EVERY_DEF, NOT_IN_EMPTY] >>
     metis_tac[window_array_root_def, window_array_transition_effect,
       window_array_transition_resources]) >>
  `window_alloca_sites func (frag_ids prepared en) SUBSET ids` by
    (irule SUBSET_TRANS >>
     qexists_tac `window_alloca_sites func (frag_ids st en)` >>
     asm_rewrite_tac[] >> irule window_alloca_sites_mono >>
     simp_tac (srw_ss()) [SUBSET_DEF, abiEncoderPropsTheory.frag_ids_def] >> decide_tac) >>
  `?t. window_array_transition ctx func st
      (window_alloca_sites func (frag_ids prepared en))
      [(d+32+j*asz,LENGTH (enc ty (EL j avs)))] p t /\
    window_strong_result ctx func prepared en ignored ty (EL j avs)
      (d+32+j*asz) p t /\
    abi_encoder_array_prefix ty avs (SUC j) d t.vs_memory /\
    abi_encode_exec_frame func p t` by
    (`st.cs_next_var <= prepared.cs_next_var /\
       ~p.vs_halted /\ p.vs_current_bb = prepared.cs_current_bb /\
       p.vs_inst_idx = LENGTH prepared.cs_current_insts /\
       (!x. SND (FST coords) = Var x \/ SND (SND coords) = Var x ==>
         not_fresh_at prepared x)` by
       (full_simp_tac bool_ss [window_phase_def] >> metis_tac[LESS_EQ_ADD]) >>
     drule_all abi_encode_framed_array_static_element_run >> simp[]) >>
  `window_phase ctx func prepared en
      (window_alloca_sites func (frag_ids prepared en))
      [(d+32+j*asz,LENGTH (enc ty (EL j avs)))] p t` by
    metis_tac[window_phase_strong_result] >>
  `eval_operand (FST (FST coords)) t = SOME (n2w j)` by
    (irule window_phase_eval >> metis_tac[window_phase_labels]) >>
  `window_phase ctx func st en (window_alloca_sites func (frag_ids st en))
      [(d+32+j*asz,LENGTH (enc ty (EL j avs)))] s t` by
    (irule window_phase_chain >>
     qexistsl_tac [`{}`, `[]`, `prepared`,
       `window_alloca_sites func (frag_ids prepared en)`,
       `[(d+32+j*asz,LENGTH (enc ty (EL j avs)))]`, `p`] >>
     asm_rewrite_tac[EMPTY_SUBSET, EVERY_DEF] >> conj_tac
     >- decide_tac >>
     irule window_alloca_sites_mono >>
     simp_tac (srw_ss()) [SUBSET_DEF, abiEncoderPropsTheory.frag_ids_def] >> decide_tac) >>
  `window_array_transition ctx func st (window_alloca_sites func (frag_ids st en))
      [(d+32+j*asz,LENGTH (enc ty (EL j avs)))] s t` by
    (irule window_array_phase_transition >>
     conj_tac >- metis_tac[window_array_transition_sizes] >>
     qexists_tac `en` >> asm_rewrite_tac[]) >>
  qexists_tac `t` >>
  full_simp_tac bool_ss [AC ADD_COMM ADD_ASSOC, MULT_COMM] >>
  metis_tac[window_phase_control, abi_encode_exec_frame_trans]
QED

Theorem abi_encode_framed_array_tail_opcodes:
  abi_encode_array_tail data_op dp st = (ops,en) ==>
  EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode /\
    ~is_ext_call_op i.inst_opcode /\ i.inst_opcode <> INVOKE /\
    i.inst_opcode <> SETFMP /\ i.inst_opcode <> DALLOCA) (emitted_insts st en)
Proof
  simp[abi_encode_array_tail_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def, is_alloca_op_def,
    is_ext_call_op_def]
QED

Theorem abi_encode_framed_array_tail_phase:
  abi_encode_array_tail data_op dp st = (ops,en) /\
  eval_operand dp s = SOME (n2w slot) /\ slot < dimword (:256) /\
  mload slot s = n2w off /\ eval_operand data_op s = SOME (n2w d) /\
  (!x. data_op = Var x ==> not_fresh_at st x) /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_phase ctx func st en {} [] s t /\
    eval_operand (FST ops) t = SOME (n2w off) /\
    eval_operand (SND ops) t = SOME (n2w (d+off)) /\
    (!x. FST ops = Var x \/ SND ops = Var x ==> not_fresh_at en x) /\
    (!x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s) /\
    abi_encode_exec_frame func s t
Proof
  strip_tac >> drule_all window_array_tail_pure_observed >> strip_tac >>
  drule abi_encode_framed_array_tail_opcodes >> strip_tac >>
  `abi_encode_exec_frame func s t` by
    (drule_all abi_encode_framed_ordinary_pure_sequence >> simp[]) >>
  qexists_tac `t with vs_inst_idx := LENGTH en.cs_current_insts` >>
  (conj_tac >- metis_tac[window_pure_seq_phase]) >>
  simp_tac (srw_ss()) [eval_op_inst_idx, lookup_var_def] >>
  asm_rewrite_tac[] >> metis_tac[lookup_var_def]
QED
