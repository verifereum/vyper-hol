Theory abiDecoderValidArrayChild
Ancestors
  abiDecoderValidArrayWindows abiDecoderValidArrayValues abiDecoderArrayChild
  abiDecoderArrayInvariant abiDecoderCoherence abiDecoderTypedContract abiDecoderContract
  abiValidMembers abiDecodeRanges compileEnv valueEncoding vyperABI vyperValue contractABI
  venomState words list rich_list arithmetic abiDecoderValidContract abiDecoderArrayChildSource
  abiDecoderArraySlice abiValidMember

(* ===== Decoder Valid Array Child ===== *)

(* Select a typed actual-source child at an arbitrary dynamic-array index. *)

Theorem abi_decode_array_member_EL:
  !n j at base hds. j < n ==>
  EL j (abi_decode_members (REPLICATE n at) base hds) =
    dec at (abi_decode_member_bytes at base (DROP (j * abi_member_head_size at) hds))
Proof
  rpt strip_tac >>
  mp_tac (Q.ISPECL [`n:num`, `j:num`, `at:abi_type`] abi_decoder_replicate_member) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  asm_simp_tac (srw_ss()) [abi_decode_members_append, abi_decode_members_def,
    EL_APPEND_EQN, map_replicate, SUM_REPLICATE,
    Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"]
QED

Theorem abi_decoder_valid_array_metadata_child:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) di
    (ListV avs) (ArrayV (DynArrayV vs)) /\ j < LENGTH vs ==>
  abi_decoder_coherent ce env sf ty tv /\
  abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (EL j avs) (EL j vs)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_dynarray_values >> strip_tac >>
  `j < LENGTH avs` by decide_tac >>
  `TAKE j avs ++ EL j avs::DROP (SUC j) avs = avs` by
    (mp_tac (Q.ISPEC `avs:abi_value list` (Q.SPEC `j:num` TAKE_DROP_SUC)) >>
     asm_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]) >>
  `TAKE j vs ++ EL j vs::DROP (SUC j) vs = vs` by
    (mp_tac (Q.ISPEC `vs:vyperValue$value list` (Q.SPEC `j:num` TAKE_DROP_SUC)) >>
     asm_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]) >>
  `LENGTH (TAKE j avs) = j /\ LENGTH (TAKE j vs) = j` by simp[LENGTH_TAKE, MIN_DEF] >>
  mp_tac (Q.INST [`parent_di` |-> `di:abi_dec_info`,
    `pre` |-> `TAKE j (avs:abi_value list)`, `av` |-> `EL j (avs:abi_value list)`,
    `post` |-> `DROP (SUC j) (avs:abi_value list)`, `vpre` |-> `TAKE j (vs:vyperValue$value list)`,
    `v` |-> `EL j (vs:vyperValue$value list)`, `vpost` |-> `DROP (SUC j) (vs:vyperValue$value list)`]
    abi_decoder_dynarray_metadata_child) >>
  asm_simp_tac bool_ss []
QED

(* ===== Pre ===== *)

(* Actual array windows and conversion establish the recursive child's pure input. *)

Theorem abi_decoder_valid_array_child_pre:
  let at = vyper_to_abi_type env ty;
      ao = j * abi_member_head_size at;
      childbs = abi_decode_member_bytes at (DROP 32 bs) (DROP ao (DROP 32 bs));
      off = 32 + abi_decode_member_offset at (DROP 32 bs) ao in
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) di
    (dec (Array NONE at) bs) (ArrayV (DynArrayV vs)) /\
  valid_enc (Array NONE at) bs /\ j < LENGTH vs /\
  (is_dynamic at ==> !elem. at <> Array (SOME 0) elem) /\
  abi_decoder_ranges opc hi src dst sb (LENGTH bs)
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap s /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc s) = bs /\
  eval_operand childsrc s = SOME (n2w (sb + off)) /\
  eval_operand childdst s = SOME (n2w (d + 32 + j * type_memory_bytes ce ty)) /\
  abi_decoder_operand_live st.cs_next_var childsrc /\
  abi_decoder_operand_live st.cs_next_var childdst /\ abi_decoder_operand_live st.cs_next_var hi ==>
  abi_decoder_valid_pre ce env sf ty tv childbs (EL j vs) st childsrc childdst opc hi
    (sb + off) (d + 32 + j * type_memory_bytes ce ty) b cap s
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_valid_dynarray_values >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_valid_array_metadata_child >> strip_tac >>
  `j < abi_head_word bs /\ j < maxn` by (asm_simp_tac bool_ss [] >> decide_tac) >>
  mp_tac (Q.ISPECL [`LENGTH (vs:vyperValue$value list)`, `j:num`,
    `vyper_to_abi_type env ty`, `DROP 32 (bs:word8 list)`, `DROP 32 (bs:word8 list)`]
    abi_decode_array_member_EL) >> impl_tac >- asm_simp_tac bool_ss [] >>
  disch_then (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  `sb + LENGTH bs < dimword (:256)` by fs[abi_decoder_ranges_def] >>
  drule_all (SIMP_RULE arith_ss [LET_THM] abi_valid_array_child_window) >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `j * type_memory_bytes ce ty + type_memory_bytes ce ty <= maxn * type_memory_bytes ce ty`
    by simp[abi_decoder_array_cell_capacity] >>
  `d + 32 + j * type_memory_bytes ce ty + type_memory_bytes ce ty <=
    d + type_memory_bytes ce (ArrayT ty (Dynamic maxn))` by
    (simp_tac bool_ss [Once type_memory_bytes_def] >> decide_tac) >>
  RULE_ASSUM_TAC (SIMP_RULE arith_ss []) >>
  simp_tac bool_ss [abi_decoder_valid_pre_def] >>
  asm_simp_tac arith_ss [abi_decoder_head_window] >>
  irule abi_decoder_subwindow_ranges >> asm_simp_tac bool_ss [] >>
  qexistsl_tac [`d`, `dst`, `LENGTH (bs:word8 list)`,
    `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`, `sb`, `src`] >>
  asm_simp_tac arith_ss [GSYM ADD_ASSOC]
QED
