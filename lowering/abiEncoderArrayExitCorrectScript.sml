(* Connect both real exit sequences to the completed array invariant. *)
Theory abiEncoderArrayExitCorrect
Ancestors
  abiEncoderArrayExitInputs abiEncoderArrayExitReach abiEncoderArrayLoopInvariant
  abiEncoderArrayFiniteLoop abiEncoderArrayMemory abiEncoderArrayLayout abiEncoderArrayCursor
  abiEncoderMembersDefs abiDecoderEffect abiDecoderDynamicLoopSetup abiDecoderContract
  abiDecoderReentry abiDecoderLoop fragExec compileEnv valueEncoding contractABI venomState words list arithmetic

Theorem abi_encoder_array_exit_reach:
  abi_encoder_array_memory ei asz msz active ty avs owner_st src dst sb source_cap d output_size b cap j initial /\
  abi_encoder_cursor active dyn_ptr cursor_site cursor_slot first site owner_st
    (LENGTH (enc (Array NONE ty) (ListV avs))-32) initial /\
  (if active then abi_encode_array_dynamic_exit src dyn_ptr st = (out,final)
    else abi_encode_array_static_exit src asz st = (out,final)) /\
  fn_has_code st final func /\ owner_st.cs_next_var <= st.cs_next_var /\ owner_st.cs_next_id <= last /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_decoder_budget first last b cap initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    fresh_vars_wrt limit_st actual /\ abi_decoder_address_frame st.cs_next_var initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_array_exit_inputs >> strip_tac >>
  Cases_on `active` >> full_simp_tac bool_ss [COND_CLAUSES]
  >- (drule_all abi_encoder_cursor_bounds >> strip_tac >>
      qpat_assum `abi_encoder_cursor T _ _ _ _ _ _ _ _`
        (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
      `abi_decoder_operand_live st.cs_next_var dyn_ptr` by
        (irule abi_decoder_operand_live_mono >> qexists_tac `owner_st.cs_next_var` >>
         asm_simp_tac bool_ss []) >>
      qpat_assum `32 <= LENGTH _` (assume_tac o MATCH_MP abi_encoder_count_word_length) >>
      mp_tac (Q.INST [`src_word` |-> `n2w sb:bytes32`, `slot` |-> `cursor_slot:num`,
        `offset` |-> `LENGTH (enc (Array NONE ty) (ListV avs))-32`]
        abi_encode_array_dynamic_exit_reach) >>
      impl_tac >- asm_simp_tac bool_ss [] >> asm_simp_tac bool_ss []) >>
  `LENGTH (enc (Array NONE ty) (ListV avs)) = 32+LENGTH avs*asz` by
    (drule_all abi_encoder_array_static_size >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.INST [`cnt` |-> `LENGTH (avs:abi_value list)`] abi_encode_array_static_exit_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_array_loop_scalar_exit:
  abi_encoder_array_loop_inv ei asz msz active ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op label (LENGTH avs) origin initial /\
  (if active then abi_encode_array_dynamic_exit src dyn_ptr st = (out,final)
    else abi_encode_array_static_exit src asz st = (out,final)) /\
  fn_has_code st final func /\ owner_st.cs_next_var <= st.cs_next_var /\ owner_st.cs_next_id <= last /\
  final.cs_next_var <= limit_st.cs_next_var /\
  label = st.cs_current_bb /\ st.cs_current_insts = [] ==>
  ?actual.
    mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory = enc (Array NONE ty) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    abi_decoder_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap origin actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_array_loop_output >> strip_tac >>
  drule abi_encoder_array_loop_inv_facts >> strip_tac >>
  qpat_assum `abi_encoder_array_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_loop_inv_def]) >>
  mp_tac (Q.INST [`j` |-> `LENGTH (avs:abi_value list)`] abi_encoder_array_exit_reach) >>
  impl_tac >- asm_simp_tac (srw_ss()) [] >> strip_tac >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`,
    `next` |-> `owner_st.cs_next_var`, `child_next` |-> `st.cs_next_var`,
    `lo` |-> `site:num`, `sz` |-> `output_size:num`] abi_decoder_address_effect) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_decoder_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap origin actual` by
    (irule abi_decoder_effect_trans >> qexists_tac `initial` >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> full_simp_tac bool_ss [abi_decoder_address_frame_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_EXIT_CORRECT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder array scalar exit not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayExitCorrect");
