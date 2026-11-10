Theory exprSimAbiEncodeFramedArrayBody
Ancestors
  loweringStateRelDefs valueEncodingDefs
  exprSimAbiEncodeFramedPhases exprSimAbiEncodeFramedBuiltin
  exprSimAbiEncodeSemantic
  abiEncoderWindowArrayBody abiEncoderArrayBodyCode abiEncoderArrayCode
  abiEncoderWindowArrayInvariant abiEncoderWindowArrayLayout arithmetic
  abiEncoderAdmissible pred_set abiEncoderArrayTail abiEncoderRegisteredEffect
  abiEncoderArrayDynamicMemory
  valueEncoding valueEncodingProps freshWrites abiEncoderWindowChild abiEncoderWindowCursor
  abiEncoderWindowSequence abiEncoderWindowPhase abiEncoderWindowContract
  exprSimAbiEncodeExecFrame venomExecSemantics venomState venomMemDefs
  exprLoweringProps emitHelper emitHelperProps compileEnv fragExec
  venomInstProofs1 venomInst list rich_list words abiDecoderDynamicLoopSetup instIdxIndep

Theorem abi_encode_framed_ordinary_pure_sequence:
  window_pure_seq st en s t /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode /\
    ~is_ext_call_op i.inst_opcode /\ i.inst_opcode <> INVOKE /\
    i.inst_opcode <> SETFMP /\ i.inst_opcode <> DALLOCA /\
    i.inst_opcode <> ISTORE /\ i.inst_opcode <> CALL /\
    i.inst_opcode <> STATICCALL /\ i.inst_opcode <> DELEGATECALL /\
    i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (emitted_insts st en) ==>
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
  drule_all abi_encode_semantic_ordinary_sequence >> strip_tac >>
  gvs[window_pure_seq_def, abi_encode_exec_frame_def, pending_alloca_size_def]
QED

Theorem abi_encode_framed_array_addresses_opcodes:
  abi_encode_array_addresses ip src dst asz msz st = (coords,en) ==>
  EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode /\
    ~is_ext_call_op i.inst_opcode /\ i.inst_opcode <> INVOKE /\
    i.inst_opcode <> SETFMP /\ i.inst_opcode <> DALLOCA /\
    i.inst_opcode <> ISTORE /\ i.inst_opcode <> CALL /\
    i.inst_opcode <> STATICCALL /\ i.inst_opcode <> DELEGATECALL /\
    i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (emitted_insts st en)
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
    i.inst_opcode <> SETFMP /\ i.inst_opcode <> DALLOCA /\
    i.inst_opcode <> ISTORE /\ i.inst_opcode <> CALL /\
    i.inst_opcode <> STATICCALL /\ i.inst_opcode <> DELEGATECALL /\
    i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (emitted_insts st en)
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

Theorem abi_encode_framed_array_dynamic_prepare:
  window_array_root ctx func st ids ei asz msz T ty avs src dst sb cap d s /\
  eval_operand ip s = SOME (n2w islot) /\ islot < dimword (:256) /\
  mload islot s = n2w j /\
  window_array_cursor T st dp site slot off sb cap d n s /\
  abi_encode_array_addresses ip src dst asz msz st = (coords,addressed) /\
  abi_encode_array_tail (FST (SND coords)) dp addressed = (ops,prepared) /\
  fn_has_code st addressed func /\ fn_has_code addressed prepared func /\
  st.cs_next_var <= addressed.cs_next_var /\
  addressed.cs_next_var <= prepared.cs_next_var /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?q. window_phase ctx func st prepared {} [] s q /\
    window_array_root ctx func st ids ei asz msz T ty avs src dst sb cap d q /\
    eval_operand (FST (FST coords)) q = SOME (n2w j) /\
    eval_operand (SND (FST coords)) q = SOME (n2w (sb+32+j*msz)) /\
    eval_operand (SND (SND coords)) q = SOME (n2w (d+32+j*asz)) /\
    eval_operand (FST ops) q = SOME (n2w off) /\
    eval_operand (SND ops) q = SOME (n2w (d+32+off)) /\
    eval_operand dp q = SOME (n2w slot) /\
    FLOOKUP q.vs_allocas site = SOME (slot,32) /\
    mem_word_at slot q.vs_memory = n2w off /\
    (!x. FST (FST coords) = Var x \/ SND (FST coords) = Var x \/
      SND (SND coords) = Var x \/ FST ops = Var x \/ SND ops = Var x \/
      dp = Var x ==> not_fresh_at prepared x) /\
    abi_encode_exec_frame func s q
Proof
  strip_tac >>
  `?p. window_phase ctx func st addressed {} [] s p /\
    eval_operand (FST (FST coords)) p = SOME (n2w j) /\
    eval_operand (SND (FST coords)) p = SOME (n2w (sb+32+j*msz)) /\
    eval_operand (FST (SND coords)) p = SOME (n2w (d+32)) /\
    eval_operand (SND (SND coords)) p = SOME (n2w (d+32+j*asz)) /\
    (!x. FST (FST coords) = Var x \/ SND (FST coords) = Var x \/
      FST (SND coords) = Var x \/ SND (SND coords) = Var x ==>
      not_fresh_at addressed x) /\
    abi_encode_exec_frame func s p` by
    (full_simp_tac bool_ss [window_array_root_def] >>
     drule_all abi_encode_framed_array_addresses_phase >> metis_tac[]) >>
  `window_array_transition ctx func st {} [] s p` by
    metis_tac[window_array_pure_phase_transition] >>
  `eval_operand dp p = SOME (n2w slot) /\ mload slot p = n2w off` by
    (full_simp_tac bool_ss [window_array_cursor_def] >>
     conj_tac >- (irule window_array_transition_eval >> metis_tac[]) >>
     `mem_word_at slot p.vs_memory = mem_word_at slot s.vs_memory` by
       (irule window_array_transition_cursor_frame >>
        metis_tac[NOT_IN_EMPTY, EVERY_DEF]) >>
     full_simp_tac bool_ss [mload_def, mem_word_at_def, mem_bytes_at_def, LET_THM]) >>
  `?q. window_phase ctx func addressed prepared {} [] p q /\
    eval_operand (FST ops) q = SOME (n2w off) /\
    eval_operand (SND ops) q = SOME (n2w (d+32+off)) /\
    (!x. FST ops = Var x \/ SND ops = Var x ==> not_fresh_at prepared x) /\
    abi_encode_exec_frame func p q` by
    (`alloca_inv p /\ alloca_room ctx func p /\ ~p.vs_halted /\
      p.vs_current_bb = addressed.cs_current_bb /\
      p.vs_inst_idx = LENGTH addressed.cs_current_insts` by
      metis_tac[window_phase_resources, window_phase_control] >>
     `slot < dimword (:256)` by fs[window_array_cursor_def] >>
     `!x. FST (SND coords) = Var x ==> not_fresh_at addressed x` by metis_tac[] >>
     drule_all abi_encode_framed_array_tail_phase >>
     simp_tac bool_ss [AC ADD_COMM ADD_ASSOC] >> metis_tac[]) >>
  `window_phase ctx func st prepared {} [] s q` by
    (irule window_phase_chain >>
     qexistsl_tac [`{}`, `[]`, `addressed`, `{}`, `[]`, `p`] >> simp[EVERY_DEF]) >>
  `window_array_transition ctx func st {} [] s q` by
    metis_tac[window_array_pure_phase_transition] >>
  qexists_tac `q` >> asm_rewrite_tac[] >> rpt conj_tac
  >- (irule window_array_root_transition >> metis_tac[EMPTY_SUBSET, EVERY_DEF])
  >- (irule window_phase_eval >> metis_tac[window_phase_labels])
  >- (irule window_phase_eval >> metis_tac[window_phase_labels])
  >- (irule window_phase_eval >> metis_tac[window_phase_labels])
  >- (irule window_array_transition_eval >>
      full_simp_tac bool_ss [window_array_cursor_def] >> metis_tac[])
  >- metis_tac[window_array_cursor_def, window_phase_effect,
       abi_encoder_registered_effect_allocated]
  >- (`mem_word_at slot q.vs_memory = mem_word_at slot s.vs_memory` by
       (irule window_array_transition_cursor_frame >>
        metis_tac[window_array_cursor_def, NOT_IN_EMPTY, EVERY_DEF]) >>
      fs[window_array_cursor_def])
  >- metis_tac[window_array_cursor_def, not_fresh_at_mono, LESS_EQ_TRANS] >>
  metis_tac[abi_encode_exec_frame_trans]
QED

Theorem abi_encode_framed_emit_add_phase:
  emit_op ADD [left;right] st = (out,en) /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_phase ctx func st en {} [] s t /\
    eval_operand out t = SOME (a+b) /\
    (!x. out = Var x ==> not_fresh_at en x) /\
    t.vs_labels = s.vs_labels /\
    abi_encode_exec_frame func s t
Proof
  strip_tac >> drule_all window_emit_add_pure >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode /\
    ~is_ext_call_op i.inst_opcode /\ i.inst_opcode <> INVOKE /\
    i.inst_opcode <> SETFMP /\ i.inst_opcode <> DALLOCA /\
    i.inst_opcode <> ISTORE /\ i.inst_opcode <> CALL /\
    i.inst_opcode <> STATICCALL /\ i.inst_opcode <> DELEGATECALL /\
    i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (emitted_insts st en)` by
    (drule emitted_insts_emit_op >>
     simp[mk_inst_def, is_terminator_def, is_alloca_op_def, is_ext_call_op_def]) >>
  `abi_encode_exec_frame func s t` by
    (drule_all abi_encode_framed_ordinary_pure_sequence >> simp[]) >>
  qexists_tac `t with vs_inst_idx := LENGTH en.cs_current_insts` >>
  (conj_tac >- metis_tac[window_pure_seq_phase]) >>
  simp_tac (srw_ss()) [eval_op_inst_idx] >> asm_rewrite_tac[] >>
  metis_tac[window_pure_seq_def, window_seq_labels]
QED

Theorem abi_encode_framed_store_eval[local]:
  eval_operand op ((mstore p w s) with vs_inst_idx := idx) = eval_operand op s
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def,
    mstore_def, write_memory_with_expansion_def]
QED

Theorem abi_encode_framed_child_suffix_steps:
  abi_encode_child_suffix head dp offset len st = (out,en) /\
  fn_has_code st en func /\
  eval_operand head s = SOME (n2w h) /\ eval_operand offset s = SOME (n2w off) /\
  eval_operand dp s = SOME (n2w slot) /\ eval_operand len s = SOME (n2w n) /\
  (!x. dp = Var x \/ len = Var x ==> not_fresh_at st x) /\
  FLOOKUP s.vs_allocas site = SOME (slot,32) /\
  h < dimword (:256) /\ slot < dimword (:256) /\
  alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?a b t1 t2 t3.
    window_phase ctx func st a {} [(h,32)] s t1 /\
    window_phase ctx func a b {} [] t1 t2 /\
    window_phase ctx func b en {site} [] t2 t3 /\
    a.cs_next_var = st.cs_next_var /\ b.cs_next_var = a.cs_next_var+1 /\
    t1.vs_memory = (mstore h (n2w off) s).vs_memory /\
    t3 = ((mstore slot (n2w (off+n)) t2) with vs_inst_idx := LENGTH en.cs_current_insts) /\
    out = len /\ eval_operand out t3 = SOME (n2w n) /\
    abi_encode_exec_frame func s t3
Proof
  strip_tac >> drule_all window_child_suffix_context >> strip_tac >>
  qabbrev_tac `t1 = (mstore h (n2w off) s) with vs_inst_idx := LENGTH a.cs_current_insts` >>
  `window_phase ctx func st a {} [(h,32)] s t1` by
    (simp_tac bool_ss [Abbr `t1`] >> irule window_output_store_phase >>
     asm_rewrite_tac[] >> qexistsl_tac [`head`, `offset`] >> asm_rewrite_tac[]) >>
  `eval_operand offset t1 = SOME (n2w off) /\
   eval_operand len t1 = SOME (n2w n) /\ eval_operand dp t1 = SOME (n2w slot)` by
    simp[Abbr `t1`, abi_encode_framed_store_eval] >>
  `alloca_inv t1 /\ alloca_room ctx func t1 /\ ~t1.vs_halted /\
   t1.vs_current_bb = a.cs_current_bb /\ t1.vs_inst_idx = LENGTH a.cs_current_insts` by
    metis_tac[window_phase_resources, window_phase_control] >>
  `?t2. window_phase ctx func a b {} [] t1 t2 /\
    eval_operand next t2 = SOME (n2w (off+n)) /\
    (!x. next = Var x ==> not_fresh_at b x) /\
    t2.vs_labels = t1.vs_labels /\
    abi_encode_exec_frame func t1 t2` by
    (drule_all abi_encode_framed_emit_add_phase >> simp[word_add_n2w]) >>
  `eval_operand dp t2 = SOME (n2w slot) /\ eval_operand len t2 = SOME (n2w n)` by
    (conj_tac >> irule window_phase_eval >> asm_rewrite_tac[] >>
     qexistsl_tac [`ctx`, `b`, `func`, `{}`, `[]`, `t1`, `a`] >>
     asm_rewrite_tac[] >> fs[not_fresh_at_def] >> metis_tac[]) >>
  `alloca_inv t2 /\ alloca_room ctx func t2 /\ ~t2.vs_halted /\
   t2.vs_current_bb = b.cs_current_bb /\ t2.vs_inst_idx = LENGTH b.cs_current_insts` by
    metis_tac[window_phase_resources, window_phase_control] >>
  `FLOOKUP t2.vs_allocas site = SOME (slot,32)` by
    (irule abi_encoder_registered_effect_allocated >>
     qexistsl_tac [`{}`, `[]`, `t1`] >>
     (conj_tac >- simp[Abbr `t1`, mstore_def, write_memory_with_expansion_def]) >>
     metis_tac[window_phase_effect]) >>
  `window_phase ctx func b en {site} [] t2
    ((mstore slot (n2w (off+n)) t2) with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (irule window_cursor_store_phase >> asm_rewrite_tac[] >> metis_tac[]) >>
  `abi_encode_exec_frame func s t1` by
    simp_tac (srw_ss()) [Abbr `t1`, abi_encode_exec_frame_mstore,
      abi_encode_exec_frame_inst_idx] >>
  `abi_encode_exec_frame func t2
    ((mstore slot (n2w (off+n)) t2) with vs_inst_idx := LENGTH en.cs_current_insts)` by
    simp_tac (srw_ss()) [abi_encode_exec_frame_mstore,
      abi_encode_exec_frame_inst_idx] >>
  `abi_encode_exec_frame func s t2` by
    (irule abi_encode_exec_frame_trans >> qexists_tac `t1` >> asm_rewrite_tac[]) >>
  `abi_encode_exec_frame func s
    ((mstore slot (n2w (off+n)) t2) with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (irule abi_encode_exec_frame_trans >> qexists_tac `t2` >> asm_rewrite_tac[]) >>
  qexistsl_tac [`a`, `b`, `t1`, `t2`,
    `(mstore slot (n2w (off+n)) t2) with vs_inst_idx := LENGTH en.cs_current_insts`] >>
  asm_rewrite_tac[] >> simp[abi_encode_framed_store_eval, Abbr `t1`]
QED

Theorem abi_encode_framed_pure_word[local]:
  window_phase ctx func st en {} [] s t ==>
  mem_word_at p t.vs_memory = mem_word_at p s.vs_memory
Proof
  strip_tac >>
  `mem_bytes_at p 32 t.vs_memory = mem_bytes_at p 32 s.vs_memory` by
    (irule abi_encoder_window_effect_bytes >> qexistsl_tac [`{}`, `[]`] >>
     simp[] >> metis_tac[window_phase_effect]) >>
  drule abiEncoderInputFrameTheory.abi_encoder_window_word >>
  disch_then (qspec_then `0` mp_tac) >> simp[]
QED

Theorem abi_encode_framed_array_suffix_run:
  abi_encode_child_suffix head dp offset len st = (out,en) /\
  fn_has_code st en func /\
  eval_operand head s = SOME (n2w h) /\ eval_operand offset s = SOME (n2w off) /\
  eval_operand dp s = SOME (n2w slot) /\ eval_operand len s = SOME (n2w n) /\
  (!x. dp = Var x \/ len = Var x ==> not_fresh_at st x) /\
  FLOOKUP s.vs_allocas site = SOME (slot,32) /\
  h < dimword (:256) /\ slot < dimword (:256) /\
  (h+32 <= slot \/ slot+32 <= h) /\
  alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_array_transition ctx func st {site} [(h,32)] s t /\
    mem_word_at h t.vs_memory = n2w off /\
    mem_word_at slot t.vs_memory = n2w (off+n) /\
    FLOOKUP t.vs_allocas site = SOME (slot,32) /\
    eval_operand out t = SOME (n2w n) /\
    t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts /\
    abi_encode_exec_frame func s t
Proof
  strip_tac >> drule_all abi_encode_framed_child_suffix_steps >> strip_tac >>
  `window_phase ctx func a en {site} [] t1 t3` by
    (irule window_phase_chain >>
     qexistsl_tac [`{}`, `[]`, `b`, `{site}`, `[]`, `t2`] >> simp[]) >>
  `window_phase ctx func st en {site} [(h,32)] s t3` by
    (irule window_phase_chain >>
     qexistsl_tac [`{}`, `[(h,32)]`, `a`, `{site}`, `[]`, `t1`] >> simp[]) >>
  `mem_word_at h t2.vs_memory = n2w off` by
    (`mem_word_at h t2.vs_memory = mem_word_at h t1.vs_memory` by
       metis_tac[abi_encode_framed_pure_word] >>
     asm_rewrite_tac[] >> simp[mstore_mem_word_at_same]) >>
  `mem_word_at h t3.vs_memory = n2w off /\
   mem_word_at slot t3.vs_memory = n2w (off+n)` by
    (asm_rewrite_tac[] >> simp_tac (srw_ss()) [] >>
     metis_tac[mstore_mem_word_at_disjoint, mstore_mem_word_at_same]) >>
  `FLOOKUP t3.vs_allocas site = SOME (slot,32)` by
    metis_tac[window_phase_effect, abi_encoder_registered_effect_allocated] >>
  `window_sizes32 {site} t3` by
    (pure_rewrite_tac[window_sizes32_def] >> simp_tac bool_ss [IN_SING] >>
     rpt strip_tac >> gvs[] >> metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ]) >>
  `t3.vs_current_bb = en.cs_current_bb /\
   t3.vs_inst_idx = LENGTH en.cs_current_insts` by
    metis_tac[window_phase_control] >>
  qexists_tac `t3` >> asm_rewrite_tac[] >>
  metis_tac[window_array_phase_sizes_transition]
QED

Theorem abi_encode_framed_array_dynamic_child_finish:
  window_array_transition ctx func owner child_ids [(b,n)] q r /\
  window_strong_result ctx func prepared child_end child_len ty av b q r /\
  abi_encode_exec_frame func q r /\ n = LENGTH (enc ty av) /\
  eval_operand idx q = SOME (n2w j) /\ eval_operand head q = SOME (n2w h) /\
  eval_operand offset q = SOME (n2w off) /\ eval_operand dp q = SOME (n2w slot) /\
  (!x. idx = Var x \/ head = Var x \/ offset = Var x \/ dp = Var x ==>
    not_fresh_at prepared x) /\
  abi_encode_child_suffix head dp offset child_len child_end = (ignored,en) /\
  fn_has_code child_end en func /\
  (!x. child_len = Var x ==> not_fresh_at child_end x) /\
  FLOOKUP q.vs_allocas site = SOME (slot,32) /\ site NOTIN child_ids /\
  h < dimword (:256) /\ slot < dimword (:256) /\
  (h+32 <= slot \/ slot+32 <= h) /\
  venomMemDefs$regions_disjoint (b,n) (h,32) /\
  venomMemDefs$regions_disjoint (b,n) (slot,32) /\
  owner.cs_next_var <= prepared.cs_next_var /\
  prepared.cs_next_var <= child_end.cs_next_var ==>
  ?t. window_array_transition ctx func owner (child_ids UNION {site})
      [(h,32);(b,n)] q t /\
    mem_bytes_at b n t.vs_memory = enc ty av /\
    mem_word_at h t.vs_memory = n2w off /\
    mem_word_at slot t.vs_memory = n2w (off+n) /\
    eval_operand idx t = SOME (n2w j) /\
    t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts /\
    abi_encode_exec_frame func q t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `window_phase ctx func prepared child_end
     (window_alloca_sites func (frag_ids prepared child_end)) [(b,n)] q r` by
    metis_tac[window_phase_strong_result] >>
  `eval_operand idx r = SOME (n2w j) /\ eval_operand head r = SOME (n2w h) /\
   eval_operand offset r = SOME (n2w off) /\ eval_operand dp r = SOME (n2w slot)` by
    (rpt conj_tac >> irule window_phase_eval >> metis_tac[window_phase_labels]) >>
  `mem_bytes_at b n r.vs_memory = enc ty av /\
   eval_operand child_len r = SOME (n2w n)` by
    metis_tac[window_strong_result_public, abi_encoder_window_result_output] >>
  `FLOOKUP r.vs_allocas site = SOME (slot,32)` by
    metis_tac[window_array_transition_effect, abi_encoder_registered_effect_allocated] >>
  `!x. dp = Var x \/ child_len = Var x ==> not_fresh_at child_end x` by
    metis_tac[not_fresh_at_mono] >>
  `alloca_inv r /\ alloca_room ctx func r /\ ~r.vs_halted /\
   r.vs_current_bb = child_end.cs_current_bb /\
   r.vs_inst_idx = LENGTH child_end.cs_current_insts` by
    metis_tac[window_phase_resources, window_phase_control] >>
  drule_all abi_encode_framed_array_suffix_run >> strip_tac >>
  `window_phase ctx func owner child_end child_ids [(b,n)] q r` by
    metis_tac[window_array_transition_phase] >>
  `window_phase ctx func child_end en {site} [(h,32)] r t` by
    metis_tac[window_array_transition_phase] >>
  `window_phase ctx func owner en (child_ids UNION {site}) [(h,32);(b,n)] q t` by
    (irule window_phase_chain >>
     qexistsl_tac [`child_ids`, `[(b,n)]`, `child_end`, `{site}`, `[(h,32)]`, `r`] >>
     simp[SUBSET_UNION] >> decide_tac) >>
  `mem_bytes_at b n t.vs_memory = mem_bytes_at b n r.vs_memory` by
    (irule abi_encoder_window_effect_bytes >>
     qexistsl_tac [`{site}`, `[(h,32)]`] >> simp[] >>
     metis_tac[window_array_transition_effect, optionTheory.SOME_11, pairTheory.PAIR_EQ]) >>
  `eval_operand idx t = SOME (n2w j)` by
    (irule window_phase_eval >> metis_tac[window_phase_labels, not_fresh_at_mono]) >>
  `abi_encode_exec_frame func q t` by
    (irule abi_encode_exec_frame_trans >> qexists_tac `r` >> asm_rewrite_tac[]) >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  irule window_array_phase_transition >> conj_tac
  >- (gen_tac >> strip_tac >> metis_tac[window_array_transition_sizes]) >>
  qexists_tac `en` >> metis_tac[]
QED

Theorem abi_encode_framed_array_dynamic_body_run:
  window_array_root ctx func st ids ei asz msz T ty avs src dst sb cap d s /\
  abi_encoder_array_prefix ty avs j d s.vs_memory /\ j < LENGTH avs /\
  eval_operand ip s = SOME (n2w islot) /\ islot < dimword (:256) /\
  mload islot s = n2w j /\
  window_array_cursor T st dp site slot off sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) s /\
  off = LENGTH avs * abi_member_head_size ty +
    SUM (MAP (abi_member_tail_size ty) (TAKE j avs)) /\
  abi_encode_array_dynamic_body ip dp src dst ei asz msz st = (out,en) /\
  window_alloca_sites func (frag_ids st en) SUBSET ids /\ site IN ids /\
  site NOTIN window_alloca_sites func (frag_ids st en) /\
  fn_has_code st en func /\ abi_encode_framed_contract ei /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_array_transition ctx func st
      (window_alloca_sites func (frag_ids st en) UNION {site})
      [(d+32+j*abi_member_head_size ty,32);
       (d+32+off,LENGTH (enc ty (EL j avs)))] s t /\
    abi_encoder_array_prefix ty avs (SUC j) d t.vs_memory /\
    mem_word_at slot t.vs_memory = n2w (off+LENGTH (enc ty (EL j avs))) /\
    eval_operand out t = SOME (n2w j) /\
    t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts /\
    abi_encode_exec_frame func s t
Proof
  strip_tac >>
  drule_all abi_encode_array_dynamic_body_context >> strip_tac >>
  qpat_x_assum `out = _` SUBST_ALL_TAC >>
  `st.cs_next_var <= addressed.cs_next_var /\
   addressed.cs_next_var <= prepared.cs_next_var` by decide_tac >>
  drule_all abi_encode_framed_array_dynamic_prepare >> strip_tac >>
  `!x. SND (FST coords) = Var x \/ SND ops = Var x ==> not_fresh_at prepared x` by
    metis_tac[] >>
  `window_alloca_sites func (frag_ids prepared child_end) SUBSET
    window_alloca_sites func (frag_ids st en)` by
    (irule window_alloca_sites_mono >>
     simp_tac (srw_ss()) [SUBSET_DEF, abiEncoderPropsTheory.frag_ids_def] >> decide_tac) >>
  `window_alloca_sites func (frag_ids prepared child_end) SUBSET ids` by
    metis_tac[SUBSET_TRANS] >>
  `abi_encoder_window_input (AbiDynArray ei asz msz T)
    (Array NONE ty) (ListV avs) sb cap s.vs_memory` by
    metis_tac[window_array_root_def] >>
  `asz = abi_member_head_size ty /\ is_dynamic ty` by
    fs[abiEncoderWindowTheory.abi_encoder_window_array_iff] >>
  `32+off+LENGTH (enc ty (EL j avs)) <= LENGTH (enc (Array NONE ty) (ListV avs)) /\
   j*abi_member_head_size ty+32 <= off` by
    (drule_all window_array_prefix_step_geometry >>
     disch_then (mp_tac o CONJUNCT1) >> asm_rewrite_tac[] >>
     strip_tac >> decide_tac) >>
  `?r. window_array_transition ctx func st
      (window_alloca_sites func (frag_ids prepared child_end))
      [(d+(32+off),LENGTH (enc ty (EL j avs)))] q r /\
    window_strong_result ctx func prepared child_end child_len ty (EL j avs)
      (d+(32+off)) q r /\
    abi_encode_exec_frame func q r` by
    (`st.cs_next_var <= prepared.cs_next_var /\
      ~q.vs_halted /\ q.vs_current_bb = prepared.cs_current_bb /\
      q.vs_inst_idx = LENGTH prepared.cs_current_insts` by
      (conj_tac >- decide_tac >> metis_tac[window_phase_control]) >>
     `eval_operand (SND ops) q = SOME (n2w (d+(32+off)))` by
       (qpat_assum `eval_operand (SND ops) q = _` mp_tac >>
        simp_tac bool_ss [ADD_ASSOC]) >>
     drule_all abi_encode_framed_array_element_run >> metis_tac[]) >>
  `d+LENGTH (enc (Array NONE ty) (ListV avs)) < dimword (:256)` by
    (full_simp_tac bool_ss [window_array_root_def, alloca_room_def] >> decide_tac) >>
  `d+32+j*asz < dimword (:256) /\ slot < dimword (:256) /\
   (d+32+j*asz+32 <= slot \/ slot+32 <= d+32+j*asz) /\
   venomMemDefs$regions_disjoint (d+(32+off),LENGTH (enc ty (EL j avs)))
     (d+32+j*asz,32) /\
   venomMemDefs$regions_disjoint (d+(32+off),LENGTH (enc ty (EL j avs))) (slot,32)` by
    (qpat_assum `d + LENGTH _ < _` mp_tac >>
     qpat_assum `32 + off + _ <= _` mp_tac >>
     qpat_assum `j * _ + 32 <= off` mp_tac >>
     qpat_assum `window_array_cursor _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `asz = _` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [window_array_cursor_def, venomMemDefsTheory.regions_disjoint_def] >>
     rpt strip_tac >> full_simp_tac arith_ss [] >> decide_tac) >>
  `!x. child_len = Var x ==> not_fresh_at child_end x` by
    (qpat_x_assum `abi_decoder_operand_live _ child_len` mp_tac >>
     Cases_on `child_len` >>
     simp[abiDecoderReentryTheory.abi_decoder_operand_live_def,
       abiDecoderReentryTheory.abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `!x. FST (FST coords) = Var x \/ SND (SND coords) = Var x \/
    FST ops = Var x \/ dp = Var x ==> not_fresh_at prepared x` by metis_tac[] >>
  `st.cs_next_var <= prepared.cs_next_var` by decide_tac >>
  `window_array_transition ctx func prepared
      (window_alloca_sites func (frag_ids prepared child_end))
      [(d+(32+off),LENGTH (enc ty (EL j avs)))] q r` by
    metis_tac[window_array_child_transition, LESS_EQ_REFL] >>
  `?t. window_array_transition ctx func prepared
      (window_alloca_sites func (frag_ids prepared child_end) UNION {site})
      [(d+32+j*asz,32);(d+(32+off),LENGTH (enc ty (EL j avs)))] q t /\
    mem_bytes_at (d+(32+off)) (LENGTH (enc ty (EL j avs))) t.vs_memory = enc ty (EL j avs) /\
    mem_word_at (d+32+j*asz) t.vs_memory = n2w off /\
    mem_word_at slot t.vs_memory = n2w (off+LENGTH (enc ty (EL j avs))) /\
    eval_operand (FST (FST coords)) t = SOME (n2w j) /\
    t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts /\
    abi_encode_exec_frame func q t` by
    (`site NOTIN window_alloca_sites func (frag_ids prepared child_end)` by
       metis_tac[SUBSET_DEF] >>
     irule abi_encode_framed_array_dynamic_child_finish >>
     qpat_assum `window_strong_result _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `abi_encode_child_suffix _ _ _ _ _ = _` (irule_at Any) >>
     asm_rewrite_tac[LESS_EQ_REFL] >> simp_tac bool_ss [ADD_ASSOC] >>
     asm_rewrite_tac[LESS_EQ_REFL]) >>
  `window_phase ctx func st en
      (window_alloca_sites func (frag_ids st en) UNION {site})
      [(d+32+j*asz,32);(d+(32+off),LENGTH (enc ty (EL j avs)))] s t` by
    (`window_phase ctx func prepared en
       (window_alloca_sites func (frag_ids prepared child_end) UNION {site})
       [(d+32+j*asz,32);(d+(32+off),LENGTH (enc ty (EL j avs)))] q t` by
       metis_tac[window_array_transition_phase] >>
     irule window_phase_chain >>
     qexistsl_tac [`{}`, `[]`, `prepared`,
       `window_alloca_sites func (frag_ids prepared child_end) UNION {site}`,
       `[(d+32+j*asz,32);(d+(32+off),LENGTH (enc ty (EL j avs)))]`, `q`] >>
     asm_rewrite_tac[EMPTY_SUBSET, EVERY_DEF] >>
     metis_tac[UNION_SUBSET, SUBSET_UNION, SUBSET_TRANS]) >>
  `window_array_transition ctx func st
      (window_alloca_sites func (frag_ids st en) UNION {site})
      [(d+32+j*asz,32);(d+(32+off),LENGTH (enc ty (EL j avs)))] s t` by
    (irule window_array_phase_transition >> conj_tac
     >- (gen_tac >> strip_tac >>
         `window_array_transition ctx func st {} [] s q` by
           metis_tac[window_array_pure_phase_transition] >>
         metis_tac[window_array_transition_sizes]) >>
     qexists_tac `en` >> asm_rewrite_tac[]) >>
  `abi_encode_exec_frame func s t` by
    (irule abi_encode_exec_frame_trans >> qexists_tac `q` >> asm_rewrite_tac[]) >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  qpat_assum `window_array_root _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s` mp_tac >>
  qpat_assum `abi_encoder_array_prefix _ _ _ _ s.vs_memory` mp_tac >>
  qpat_assum `j < LENGTH avs` mp_tac >>
  qpat_assum `window_alloca_sites _ (frag_ids st en) SUBSET ids` mp_tac >>
  qpat_assum `site IN ids` mp_tac >>
  qpat_assum `window_array_transition _ _ _ (window_alloca_sites _ (frag_ids st en) UNION {site}) _ s t` mp_tac >>
  qpat_assum `mem_bytes_at _ _ t.vs_memory = _` mp_tac >>
  qpat_assum `mem_word_at (d+32+j*asz) t.vs_memory = _` mp_tac >>
  qpat_assum `asz = _` mp_tac >> qpat_assum `off = _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
  qpat_x_assum `asz = _` SUBST_ALL_TAC >>
  qpat_x_assum `off = _` SUBST_ALL_TAC >>
  full_simp_tac bool_ss [ADD_ASSOC] >> asm_rewrite_tac[] >>
  irule window_array_dynamic_prefix_finish >>
  qpat_assum `window_array_root _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `window_array_transition _ _ _ (window_alloca_sites _ (frag_ids st en) UNION {site}) _ s t`
    (irule_at Any) >>
  asm_rewrite_tac[] >> simp_tac bool_ss [GSYM ADD_ASSOC] >> asm_rewrite_tac[] >>
  metis_tac[UNION_SUBSET, SUBSET_DEF, IN_SING]
QED
