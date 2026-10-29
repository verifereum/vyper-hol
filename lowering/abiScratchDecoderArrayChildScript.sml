(* Actual array windows and conversion establish the child's physical ownership. *)
Theory abiScratchDecoderArrayChild
Ancestors
  abiScratchDecoderContract abiScratchDecoderSubwindow abiDecoderValidContract
  abiDecoderValidArrayChild abiDecoderValidArrayValues abiDecoderValidArrayWindows
  abiDecoderArrayChildSource abiDecoderArraySlice abiDecoderCoherence abiDecoderTypedContract
  abiDecoderContract abiDecodeRanges abiValidMember abiValidMembers compileEnv valueEncoding
  vyperABI vyperValue contractABI venomState words list arithmetic

Theorem abi_scratch_decoder_array_child_input:
  let at = vyper_to_abi_type env ty;
      ao = j * abi_member_head_size at;
      childbs = abi_decode_member_bytes at (DROP 32 bs) (DROP ao (DROP 32 bs));
      off = 32 + abi_decode_member_offset at (DROP 32 bs) ao in
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) di
    (dec (Array NONE at) bs) (ArrayV (DynArrayV vs)) /\
  valid_enc (Array NONE at) bs /\ j < LENGTH vs /\
  (is_dynamic at ==> !elem. at <> Array (SOME 0) elem) /\
  abi_scratch_decoder_ranges opc hi src dst sb (LENGTH bs)
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) first last b cap s /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc s) = bs /\
  eval_operand childsrc s = SOME (n2w (sb + off)) /\
  eval_operand childdst s = SOME (n2w (d + 32 + j * type_memory_bytes ce ty)) /\
  abi_decoder_operand_live st.cs_next_var childsrc /\
  abi_decoder_operand_live st.cs_next_var childdst /\ abi_decoder_operand_live st.cs_next_var hi ==>
  abi_scratch_decoder_input ce env sf ty tv childbs (EL j vs) st childsrc childdst opc hi
    (sb + off) (d + 32 + j * type_memory_bytes ce ty) first last b cap s
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_valid_dynarray_values >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_valid_array_metadata_child >> strip_tac >>
  `j < abi_head_word bs /\ j < maxn` by (asm_simp_tac bool_ss [] >> decide_tac) >>
  mp_tac (Q.ISPECL [`LENGTH (vs:vyperValue$value list)`, `j:num`,
    `vyper_to_abi_type env ty`, `DROP 32 (bs:word8 list)`, `DROP 32 (bs:word8 list)`]
    abi_decode_array_member_EL) >> impl_tac >- asm_simp_tac bool_ss [] >>
  disch_then (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  `sb + LENGTH bs < dimword (:256)` by fs[abi_scratch_decoder_ranges_def] >>
  drule_all (SIMP_RULE arith_ss [LET_THM] abi_valid_array_child_window) >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `j * type_memory_bytes ce ty + type_memory_bytes ce ty <= maxn * type_memory_bytes ce ty`
    by simp[abi_decoder_array_cell_capacity] >>
  `d + 32 + j * type_memory_bytes ce ty + type_memory_bytes ce ty <=
    d + type_memory_bytes ce (ArrayT ty (Dynamic maxn))` by
    (simp_tac bool_ss [Once type_memory_bytes_def] >> decide_tac) >>
  RULE_ASSUM_TAC (SIMP_RULE arith_ss []) >>
  simp_tac bool_ss [abi_scratch_decoder_input_def] >>
  asm_simp_tac arith_ss [abi_decoder_head_window] >>
  irule abi_scratch_decoder_subwindow_ranges >> asm_simp_tac bool_ss [] >>
  qexistsl_tac [`d`, `dst`, `LENGTH (bs:word8 list)`,
    `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`, `sb`, `src`] >>
  asm_simp_tac arith_ss [GSYM ADD_ASSOC]
QED
