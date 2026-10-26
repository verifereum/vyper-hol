(* Actual index and tail initialization preserve complete array buffers.
   TOP-LEVEL: abi_scratch_array_index_prepare and abi_scratch_array_tail_prepare
   establish their registered cursors, complete source contracts and owned
   effects without requiring an unrelated parent cursor. *)
Theory abiScratchArrayInitEffects
Ancestors
  abiScratchPrefixEffect abiScratchOwnedPrefix abiScratchArrayTailInput abiScratchInputEffect
  abiScratchEncoderContract abiEncoderArrayInitCode abiEncoderArrayTailInitCode
  abiEncoderComplexPrefix abiEncoderComplexPrefixReach abiEncoderMembersDefs abiEncoderInput
  abiEncoderArrayFrame abiEncoderArrayPrefix abiDecoderAllocation abiDecoderFootprint
  abiDecoderFrame abiDecoderReentry abiDecoderLoop compileEnv valueEncoding contractABI
  venomState words list arithmetic

Theorem abi_scratch_array_index_prepare:
  abi_decode_index_init st = (index_ptr,st') /\ fn_has_code st st' func /\
  abi_scratch_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size first last b cap initial /\
  abi_encoder_array_prefix ty avs 0 d initial.vs_memory /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ st'.cs_next_id <= last /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual slot. abi_scratch_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
      st' src dst sb source_cap d output_size first last b cap actual /\
    abi_encoder_array_prefix ty avs 0 d actual.vs_memory /\
    abi_encoder_cursor T index_ptr st.cs_next_id slot first st.cs_next_id st' 0 actual /\
    abi_scratch_effect first last st.cs_next_id st'.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  `abi_encode_complex_prefix ([]:(abi_enc_info # num # num # bool) list) st = (index_ptr,st')` by
    asm_simp_tac bool_ss [GSYM abi_decode_index_init_complex_prefix] >>
  drule abi_encoder_complex_prefix_shape >> strip_tac >>
  `st.cs_next_id < st'.cs_next_id /\ st.cs_next_var <= st'.cs_next_var` by decide_tac >>
  drule_all abi_scratch_owned_prefix_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  mp_tac (Q.INST [`infos` |-> `[]:(abi_enc_info # num # num # bool) list`, `dyn_ptr` |-> `index_ptr:operand`,
    `next` |-> `st.cs_next_var`, `site` |-> `st.cs_next_id`, `stop` |-> `st'.cs_next_id`,
    `sz` |-> `output_size:num`] abi_scratch_prefix_effect) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  mp_tac (Q.INST [`ei` |-> `AbiDynArray ei asz msz active`, `at` |-> `Array NONE ty`, `av` |-> `ListV avs`,
    `lo` |-> `st.cs_next_id`, `hi` |-> `st'.cs_next_id`, `next` |-> `st.cs_next_var`,
    `sz` |-> `output_size:num`] abi_scratch_input_effect) >>
  impl_tac >- asm_simp_tac bool_ss [LESS_EQ_REFL] >> disch_tac >>
  `has_type (Array NONE ty) (ListV avs)` by
    (qpat_assum `abi_encoder_input (AbiDynArray _ _ _ _) _ _ _ _ _`
       (ACCEPT_TAC o MATCH_MP abi_encoder_input_typed)) >>
  `abi_encoder_array_prefix ty avs 0 d actual.vs_memory` by
    (drule_all abi_encoder_array_prefix_output_frame >> simp[]) >>
  drule_all abi_scratch_prefix_cursor >> strip_tac >>
  rename1 `abi_encoder_cursor T index_ptr st.cs_next_id index_slot first st.cs_next_id st' _ actual` >>
  `abi_scratch_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    st' src dst sb source_cap d output_size first last b cap actual` by
    (irule abi_scratch_input_mono >> qexists_tac `st` >> asm_simp_tac bool_ss []) >>
  qexistsl_tac [`actual`, `index_slot`] >> gvs[]
QED

Theorem abi_scratch_array_tail_prepare:
  abi_encode_array_tail_init count_op asz st = (dyn_ptr,st') /\ fn_has_code st st' func /\
  eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\
  abi_decoder_operand_live st.cs_next_var count_op /\
  abi_scratch_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size first last b cap initial /\
  abi_encoder_array_prefix ty avs 0 d initial.vs_memory /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ st'.cs_next_id <= last /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual slot. abi_scratch_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
      st' src dst sb source_cap d output_size first last b cap actual /\
    abi_encoder_array_prefix ty avs 0 d actual.vs_memory /\
    abi_encoder_cursor T dyn_ptr st.cs_next_id slot first st.cs_next_id st' (LENGTH avs*asz) actual /\
    (!op cursor_site cursor_slot cursor_lo off.
      abi_encoder_cursor T op cursor_site cursor_slot first cursor_lo st off initial ==>
      abi_encoder_cursor T op cursor_site cursor_slot first cursor_lo st' off actual) /\
    abi_scratch_effect first last st.cs_next_id st'.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  mp_tac (Q.INST [`j` |-> `0:num`] abi_scratch_array_tail_input) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  rename1 `abi_encoder_cursor T dyn_ptr st.cs_next_id tail_slot first st.cs_next_id st'
    (LENGTH avs*asz) actual` >>
  drule abi_encode_array_tail_init_shape >> strip_tac >>
  `st.cs_next_id < st'.cs_next_id /\ st.cs_next_var <= st'.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`infos` |-> `[(AbiPrimWord,LENGTH (avs:abi_value list)*asz,0,F)]`,
    `next` |-> `st.cs_next_var`, `site` |-> `st.cs_next_id`, `stop` |-> `st'.cs_next_id`,
    `sz` |-> `output_size:num`] abi_scratch_prefix_effect) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  mp_tac (Q.INST [`ei` |-> `AbiDynArray ei asz msz active`, `at` |-> `Array NONE ty`, `av` |-> `ListV avs`,
    `lo` |-> `st.cs_next_id`, `hi` |-> `st'.cs_next_id`, `next` |-> `st.cs_next_var`,
    `sz` |-> `output_size:num`] abi_scratch_input_effect) >>
  impl_tac >- asm_simp_tac bool_ss [LESS_EQ_REFL] >> disch_tac >>
  `abi_scratch_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    st' src dst sb source_cap d output_size first last b cap actual` by
    (irule abi_scratch_input_mono >> qexists_tac `st` >> asm_simp_tac bool_ss []) >>
  qexistsl_tac [`actual`, `tail_slot`] >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_ARRAY_INIT_EFFECTS_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch actual initializer preparation not kernel closed: " ^ n)
  end) (DB.thms "abiScratchArrayInitEffects");
