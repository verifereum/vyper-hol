Theory abiEncoderStatic
Ancestors
  abiEncoderAddressReach abiEncoderChildInputs abiEncoderChildCode abiEncoderCorrect
  abiEncoderChildFrames abiEncoderAppend abiEncoderCounters abiEncoder abiDecoderEffect
  abiDecoderArrayInitExec abiDecoderDynamicLoopSetup abiDecoderReentry abiDecoderContract
  abiDecoderLoop fragExec emitHelperProps compileEnv valueEncoding venomState words list
  arithmetic abiEncoderAdmissible abiEncoderCorrectLeaves abiEncoderLeafCode
  abiDecoderAllocation contractABI abiEncoderInput abiEncoderMemory abiStaticAggregateProps
  abiStaticSparseProps valueEncodingProps vyperABI rich_list

(* ===== Child ===== *)

(* Compose actual static-child address setup with the recursive core contract. *)

Theorem abi_encoder_static_child_context:
  compile_abi_encode_child dst src ei F offset dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func ==>
  ?head prepared. emit_op ADD [dst;Lit (n2w offset)] st = (head,prepared) /\
    compile_abi_encode_to_buf head src ei prepared = (out,end_st) /\
    fn_has_code st prepared func /\ fn_has_code prepared end_st func /\
    prepared.cs_next_var = st.cs_next_var+1 /\ prepared.cs_next_id = st.cs_next_id+1 /\
    prepared.cs_blocks = st.cs_blocks /\
    prepared.cs_next_var <= end_st.cs_next_var /\ prepared.cs_next_id <= end_st.cs_next_id /\
    abi_decoder_operand_live prepared.cs_next_var head
Proof
  strip_tac >> drule abi_encode_static_child_trace >> strip_tac >>
  drule abi_encoder_emit_address_shape >> strip_tac >>
  drule cs_extends_abi_encode >> strip_tac >> drule_all fn_has_code_split >> strip_tac >>
  drule abi_encoder_counters >> strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  drule abi_decoder_operand_live_emit >> strip_tac >>
  qexistsl_tac [`head`, `prepared`] >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_static_child_reach:
  abi_encoder_correct ei /\ compile_abi_encode_child dst src ei F offset dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func /\
  (st.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_buffer_pre ei at av st src dst sb source_cap d output_size b cap initial /\
  offset+LENGTH (enc at av) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. mem_bytes_at (d+offset) (LENGTH (enc at av)) t.vs_memory = enc at av /\
    eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
    abi_decode_footprint_frame [(d+offset,LENGTH (enc at av));(b,cap)] initial t /\
    abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial t /\
    t.vs_current_bb = end_st.cs_current_bb /\ t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_static_child_context >> strip_tac >>
  `prepared.cs_next_var <= limit_st.cs_next_var /\ first <= prepared.cs_next_id` by decide_tac >>
  `eval_operand dst initial = SOME (n2w d)` by fs[abi_encoder_buffer_pre_def] >>
  mp_tac (Q.INST [`opc` |-> `ADD`, `lhs` |-> `dst`, `rhs` |-> `Lit (n2w offset)`,
    `a` |-> `n2w d:bytes32`, `b` |-> `n2w offset:bytes32`, `st'` |-> `prepared`, `out` |-> `head`]
    abi_encoder_binary_reach) >>
  impl_tac >- asm_simp_tac (srw_ss()) [eval_operand_def] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  `eval_operand head ready = SOME (n2w (d+offset))` by fs[word_add_n2w] >>
  `st.cs_next_var <= prepared.cs_next_var` by decide_tac >>
  `abi_encoder_pre ei at av prepared src head sb source_cap (d+offset) b cap ready` by
    (mp_tac (Q.INST [`child_st` |-> `prepared`, `child_dst` |-> `head`,
      `actual` |-> `ready:venom_state`] abi_encoder_child_pre_address) >> asm_simp_tac bool_ss []) >>
  `abi_decoder_budget first last b cap ready` by
    (mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `ready:venom_state`]
      abi_decoder_budget_transport) >>
     impl_tac >- fs[abi_decoder_address_frame_def] >> asm_simp_tac bool_ss []) >>
  `abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
    limit_st d output_size b cap initial ready` by
    (irule abi_decoder_address_effect >> asm_simp_tac bool_ss [] >>
     qexists_tac `st.cs_next_var` >> simp[]) >>
  mp_tac (Q.INST [`start` |-> `prepared`, `initial` |-> `ready:venom_state`,
    `dst` |-> `head`, `d` |-> `d+offset`] abi_encoder_correct_run) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func ready actual` >>
  `abi_decode_footprint_frame [(d+offset,LENGTH (enc at av));(b,cap)] initial actual` by
    (mp_tac (Q.INST [`next` |-> `st.cs_next_var`,
      `fp` |-> `[(d+offset,LENGTH (enc at av));(b,cap)]`] abi_encoder_frame_after_address) >>
     impl_tac >- fs[abi_decoder_effect_def] >> simp[]) >>
  `abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
    limit_st d output_size b cap ready actual` by
    (irule abi_decoder_effect_widen >>
     qexistsl_tac [`d+offset`, `end_st.cs_next_id`, `prepared.cs_next_id`,
       `prepared.cs_next_var`, `LENGTH (enc at av)`] >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  `abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
    limit_st d output_size b cap initial actual` by
    (irule abi_decoder_effect_trans >> qexists_tac `ready` >> asm_simp_tac bool_ss []) >>
  `abi_decode_sim ctx func initial actual` by
    (irule abi_decode_sim_trans >> qexists_tac `ready` >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

(* ===== Info ===== *)

(* Execute the real static-array child helper within a larger output buffer. *)

Theorem abi_encoder_static_leaf_correct:
  abi_encoder_static_leaf ei ==> abi_encoder_correct ei
Proof
  rw[abi_encoder_static_leaf_def] >>
  simp[abi_encoder_correct_word, abi_encoder_correct_copy, abi_encoder_correct_empty]
QED

Theorem abi_encoder_buffer_pre_offset:
  abi_encoder_buffer_pre ei at av st src dst sb source_cap d output_size b cap initial /\
  abi_decoder_operand_live st.cs_next_var head /\
  eval_operand head initial = SOME (n2w (d+offset)) /\
  offset+LENGTH (enc at av) <= output_size ==>
  abi_encoder_pre ei at av st src head sb source_cap (d+offset) b cap initial
Proof
  simp_tac bool_ss [abi_encoder_buffer_pre_def, abi_encoder_pre_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> asm_simp_tac bool_ss [] >> decide_tac
QED

Theorem abi_encoder_static_info_reach:
  abi_encoder_static_leaf ei /\ compile_abi_encode_static_info head src ei st = (out,end_st) /\
  fn_has_code st end_st func /\
  abi_encoder_buffer_pre ei at av st src dst sb source_cap d output_size b cap initial /\
  abi_decoder_operand_live st.cs_next_var head /\
  eval_operand head initial = SOME (n2w (d+offset)) /\ offset+LENGTH (enc at av) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. mem_bytes_at (d+offset) (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
    abi_decode_footprint_frame [(d+offset,LENGTH (enc at av));(b,cap)] initial actual /\
    abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_static_leaf_correct >> disch_tac >>
  qpat_assum `abi_encoder_static_leaf ei` (fn th =>
    qpat_assum `compile_abi_encode_static_info _ _ _ _ = _`
      (assume_tac o PURE_REWRITE_RULE [MATCH_MP abi_encode_static_info_agrees th])) >>
  drule_all abi_encode_static_leaf_shape >> strip_tac >>
  drule_all abi_encoder_buffer_pre_offset >> disch_tac >>
  mp_tac (Q.INST [`start` |-> `st`, `dst` |-> `head`, `d` |-> `d+offset`] abi_encoder_correct_run) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  qpat_assum `abi_decoder_effect _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_effect_def]) >>
  `abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
    limit_st d output_size b cap initial actual` by
    (irule abi_decoder_effect_widen >>
     qexistsl_tac [`d+offset`, `end_st.cs_next_id`, `st.cs_next_id`, `st.cs_next_var`,
       `LENGTH (enc at av)`] >> asm_simp_tac bool_ss [] >> decide_tac) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

(* ===== Input ===== *)

(* Establish static array input from every source slot, including default slots. *)

Theorem abi_encoder_static_chunk_lengths:
  !avs. ~is_dynamic ct /\ static_length ct = esz /\ have_type ct avs ==>
    EVERY (\av. LENGTH (enc ct av) = esz) avs
Proof
  Induct >- simp[] >> qx_gen_tac `av` >> simp[has_type_def] >> rpt strip_tac >>
  `LENGTH (enc ct av) = esz` by (drule_all (cj 1 enc_has_static_length) >> simp[]) >>
  simp[]
QED

Theorem abi_encoder_static_chunks_tail:
  (!i. i < LENGTH (av::avs) ==>
    mem_bytes_at (sb+i*esz) esz mem = enc ct (EL i (av::avs))) ==>
  !i. i < LENGTH avs ==>
    mem_bytes_at (sb+esz+i*esz) esz mem = enc ct (EL i avs)
Proof
  strip_tac >> qx_gen_tac `i` >> strip_tac >>
  first_x_assum (qspec_then `SUC i` mp_tac) >>
  simp[MULT_CLAUSES, AC ADD_COMM ADD_ASSOC]
QED

Theorem abi_encoder_static_chunks:
  !avs sb. EVERY (\av. LENGTH (enc ct av) = esz) avs /\
    (!i. i < LENGTH avs ==> mem_bytes_at (sb+i*esz) esz mem = enc ct (EL i avs)) ==>
  mem_bytes_at sb (LENGTH avs * esz) mem = FLAT (MAP (enc ct) avs)
Proof
  Induct_on `avs` >- simp[mem_bytes_at_def] >>
  qx_gen_tac `av` >> rpt gen_tac >> strip_tac >>
  `mem_bytes_at sb esz mem = enc ct av` by
    (qpat_x_assum `!i. i < LENGTH (av::avs) ==> _` (qspec_then `0` mp_tac) >> simp[]) >>
  `EVERY (\av. LENGTH (enc ct av) = esz) avs` by fs[] >>
  drule abi_encoder_static_chunks_tail >> strip_tac >>
  `mem_bytes_at (sb+esz) (LENGTH avs*esz) mem = FLAT (MAP (enc ct) avs)` by
    (qpat_x_assum `!off. EVERY _ avs /\ _ ==> _` irule >>
     asm_simp_tac bool_ss []) >>
  simp[Once abi_encoder_mem_split, MULT_CLAUSES, ADD_ASSOC] >>
  qpat_x_assum `mem_bytes_at (sb+esz) _ mem = _` mp_tac >>
  simp_tac bool_ss [AC ADD_COMM ADD_ASSOC, MULT_COMM]
QED

Theorem abi_encoder_static_array_input:
  has_type (Array (SOME n) ct) (ListV avs) /\ ~is_dynamic ct /\
  static_length ct = esz /\ n*esz <= cap /\
  (!i. i < n ==> mem_bytes_at (sb+i*esz) esz mem = enc ct (EL i avs)) ==>
  abi_encoder_input (AbiCopy (n*esz)) (Array (SOME n) ct) (ListV avs) sb cap mem
Proof
  strip_tac >>
  `LENGTH avs = n /\ have_type ct avs` by fs[has_type_def, valid_length_def] >>
  drule_all abi_encoder_static_chunk_lengths >> strip_tac >>
  `mem_bytes_at sb (n*esz) mem = FLAT (MAP (enc ct) avs)` by
    (mp_tac (Q.INST [`avs` |-> `avs`, `sb` |-> `sb`] (SPEC_ALL abi_encoder_static_chunks)) >>
     asm_simp_tac bool_ss []) >>
  simp[abi_encoder_input_copy_iff, is_dynamic_def, static_length_def, enc_static_array]
QED

Theorem abi_encoder_sparse_default:
  !n sparse avs i.
  vyper_to_abi_sparse env ty tv n sparse = SOME avs /\ i < n /\ ALOOKUP sparse i = NONE ==>
  EL i avs = default_to_abi tv
Proof
  Induct_on `n` >- simp[] >> rpt gen_tac >>
  simp[Once vyper_to_abi_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  imp_res_tac canonical_sparse_length >>
  Cases_on `i = n` >> gvs[EL_APPEND_EQN] >>
  rename1 `vyper_to_abi_sparse env ty tv (LENGTH prefix) sparse = SOME prefix` >>
  `i < LENGTH prefix` by decide_tac >> first_x_assum drule_all >> simp[]
QED

Theorem abi_encoder_sparse_static_input:
  vyper_to_abi_sparse env ty tv n sparse = SOME avs /\
  has_type (Array (SOME n) (vyper_to_abi_type env ty)) (ListV avs) /\
  ~is_dynamic (vyper_to_abi_type env ty) /\ static_length (vyper_to_abi_type env ty) = esz /\
  n*esz <= cap /\
  (!i. i < n ==> mem_bytes_at (sb+i*esz) esz mem =
    (case ALOOKUP sparse i of
       NONE => enc (vyper_to_abi_type env ty) (default_to_abi tv)
     | SOME v => case vyper_to_abi env ty v of
         NONE => [] | SOME av => enc (vyper_to_abi_type env ty) av)) ==>
  abi_encoder_input (AbiCopy (n*esz)) (Array (SOME n) (vyper_to_abi_type env ty))
    (ListV avs) sb cap mem
Proof
  strip_tac >> irule abi_encoder_static_array_input >> asm_simp_tac bool_ss [] >>
  qx_gen_tac `i` >> strip_tac >> Cases_on `ALOOKUP sparse i`
  >- (drule_all abi_encoder_sparse_default >> strip_tac >>
      qpat_x_assum `!i. i < n ==> _` (qspec_then `i` mp_tac) >> asm_simp_tac (srw_ss()) []) >>
  rename1 `ALOOKUP sparse i = SOME elt` >>
  drule_all canonical_sparse_lookup >> strip_tac >>
  qpat_x_assum `!i. i < n ==> _` (qspec_then `i` mp_tac) >> asm_simp_tac (srw_ss()) []
QED
