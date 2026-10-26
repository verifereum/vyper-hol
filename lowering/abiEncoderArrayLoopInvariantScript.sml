(* Pure observations and accumulated owned effects for finite encoder iteration. *)
Theory abiEncoderArrayLoopInvariant
Ancestors
  abiEncoderArrayMemory abiEncoderArrayCursor abiEncoderMembersDefs abiEncoderDynamicChildCore
  abiDecoderEffect abiDecoderContract abiDecoderReentry compileEnv valueEncoding contractABI
  venomState words list arithmetic

Definition abi_encoder_array_loop_inv_def:
  abi_encoder_array_loop_inv ei asz msz active ty avs owner_st limit_st src dst ip dyn_ptr
      site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op label j origin s <=>
    abi_encoder_array_memory ei asz msz active ty avs owner_st src dst sb source_cap d output_size b cap j s /\
    abi_encoder_cursor T ip site slot first site owner_st j s /\
    abi_encoder_cursor active dyn_ptr cursor_site cursor_slot first site owner_st
      (LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) s /\
    (active ==> site < cursor_site) /\ abi_decoder_operand_live owner_st.cs_next_var count_op /\
    eval_operand count_op s = SOME (n2w (LENGTH avs)) /\
    s.vs_current_bb = label /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    abi_decoder_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap origin s
End

Theorem abi_encoder_array_loop_inv_facts:
  abi_encoder_array_loop_inv ei asz msz active ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op label j origin s ==>
  has_type (Array NONE ty) (ListV avs) /\ j <= LENGTH avs /\ LENGTH avs < dimword (:256) /\
  fresh_vars_wrt limit_st s /\ abi_decoder_budget first last b cap s
Proof
  simp_tac bool_ss [abi_encoder_array_loop_inv_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_array_memory_typed >> strip_tac >>
  qpat_assum `abi_decoder_effect _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_effect_def]) >>
  asm_simp_tac bool_ss []
QED

Theorem abi_encoder_array_loop_inv_advance:
  abi_encoder_array_loop_inv ei asz msz active ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op label j origin initial /\
  abi_decoder_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap initial actual /\
  abi_encoder_array_memory ei asz msz active ty avs owner_st src dst sb source_cap d output_size b cap k actual /\
  abi_encoder_cursor T ip site slot first site owner_st k actual /\
  abi_encoder_cursor active dyn_ptr cursor_site cursor_slot first site owner_st
    (LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE k avs))) actual /\
  actual.vs_current_bb = next_label /\ actual.vs_inst_idx = 0 /\ ~actual.vs_halted ==>
  abi_encoder_array_loop_inv ei asz msz active ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op next_label k origin actual
Proof
  simp_tac bool_ss [abi_encoder_array_loop_inv_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand count_op actual = SOME (n2w (LENGTH avs))` by
    (imp_res_tac abi_encoder_effect_operand >> asm_simp_tac bool_ss []) >>
  `abi_decoder_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap origin actual` by
    (irule abi_decoder_effect_trans >> qexists_tac `initial` >> asm_simp_tac bool_ss []) >>
  asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_LOOP_INVARIANT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder array loop invariant not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayLoopInvariant");
