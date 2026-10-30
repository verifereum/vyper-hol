Theory abiDecoderValidArraySetupInputs
Ancestors
  abiValidAggregateHeads abiValidMembers abiDecoderArrayInvariant abiDecoderCoherence
  abiDecoderTypedContract abiDecoderContract compileEnv valueEncoding vyperABI vyperValue
  contractABI venomState words list rich_list arithmetic abiValidMember
  abiDecoderValidMemberCons abiCanonicalHeadSize abiDecodeRanges abiDecoderArrayAdvance
  abiDecoderValidContract abiDecoderArraySetupInputs abiDecoderArraySlice abiDecoderDynamic
  abiDecoderOffset abiEncoder

(* Successful conversion relates the actual array count and decoded children. *)
Theorem abi_decoder_valid_dynarray_values:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) di
    (dec (Array NONE (vyper_to_abi_type env ty)) bs) (ArrayV (DynArrayV vs)) /\
  vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) bs ==>
  32 <= LENGTH bs /\ abi_head_word bs = LENGTH vs /\ all_have_type tv vs /\ LENGTH vs <= maxn /\
  abi_decoder_coherent ce env sf ty tv /\ type_memory_size tv = type_memory_bytes ce ty /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) di
    (ListV (abi_decode_members (REPLICATE (LENGTH vs) (vyper_to_abi_type env ty))
      (DROP 32 bs) (DROP 32 bs))) (ArrayV (DynArrayV vs)) /\
  vyper_decode_valid_enc_tuple (REPLICATE (LENGTH vs) (vyper_to_abi_type env ty)) (DROP 32 bs) (DROP 32 bs)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_valid_dynamic_array_view >> strip_tac >>
  qpat_assum `dec (Array NONE _) bs = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  drule abi_decoder_dynarray_values >> strip_tac >>
  `abi_head_word bs = LENGTH vs` by
    fs[abi_decode_members_length, LENGTH_REPLICATE, Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  `abi_decoder_coherent ce env sf ty tv` by fs[abi_decoder_coherent_array_iff] >>
  drule abi_decoder_coherent_header >> strip_tac >>
  qpat_assum `abi_decoder_header ce env ty tv`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_header_def]) >>
  qpat_assum `abi_head_word bs = LENGTH vs`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> assume_tac th) >>
  asm_simp_tac bool_ss []
QED

(* Actual dynamic-array child windows, including arbitrary source head offsets. *)
Theorem abi_decoder_replicate_member:
  !n j at. j < n ==>
    REPLICATE n at = REPLICATE j at ++ at::REPLICATE (n - SUC j) at
Proof
  rpt strip_tac >> simp_tac bool_ss [GSYM REPLICATE, REPLICATE_APPEND] >>
  `j + SUC (n - SUC j) = n` by decide_tac >> asm_simp_tac bool_ss []
QED

Theorem abi_valid_array_payload_window:
  vyper_decode_valid_enc (Array NONE at) bs /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc s) = bs /\
  sb + LENGTH bs < dimword (:256) ==>
  32 <= LENGTH bs /\
  vyper_decode_valid_enc_tuple (REPLICATE (abi_head_word bs) at) (DROP 32 bs) (DROP 32 bs) /\
  mem_bytes_at (sb + 32) (LENGTH (DROP 32 bs)) (abi_decode_source opc s) = DROP 32 bs /\
  sb + 32 + LENGTH (DROP 32 bs) < dimword (:256)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_valid_dynamic_array_view >> strip_tac >>
  `32 + LENGTH (DROP 32 bs) = LENGTH bs` by (simp[LENGTH_DROP] >> decide_tac) >>
  asm_simp_tac bool_ss [GSYM ADD_ASSOC] >>
  mp_tac (Q.INST [`off` |-> `32:num`, `n` |-> `LENGTH (DROP 32 (bs:word8 list))`]
    abi_decode_source_window) >> asm_simp_tac (srw_ss()) []
QED

Theorem abi_valid_array_child_window:
  vyper_decode_valid_enc (Array NONE at) bs /\ j < abi_head_word bs /\
  (is_dynamic at ==> !elem. at <> Array (SOME 0) elem) /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc s) = bs /\
  sb + LENGTH bs < dimword (:256) ==>
  let payload = DROP 32 bs;
      ao = j * abi_member_head_size at;
      off = 32 + abi_decode_member_offset at payload ao;
      data = abi_decode_member_bytes at payload (DROP ao payload) in
  vyper_decode_valid_enc at data /\ abi_member_head_size at <= LENGTH data /\
  off + LENGTH data <= LENGTH bs /\ sb + off < dimword (:256) /\
  mem_bytes_at (sb + off) (LENGTH data) (abi_decode_source opc s) = data /\
  (is_dynamic at ==> abi_decode_load opc (n2w (sb + 32 + ao):bytes32) s = n2w (off - 32))
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_valid_array_payload_window >> strip_tac >>
  mp_tac (Q.ISPECL [`abi_head_word (bs:word8 list)`, `j:num`, `at:abi_type`]
    abi_decoder_replicate_member) >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qpat_assum `REPLICATE (abi_head_word bs) at = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  mp_tac (SIMP_RULE bool_ss [LET_THM, map_replicate, SUM_REPLICATE]
    (Q.INST [`bs` |-> `DROP 32 (bs:word8 list)`, `sb` |-> `sb + 32`,
      `pre` |-> `REPLICATE j at`, `ats` |-> `REPLICATE (abi_head_word bs - SUC j) at`]
      abi_valid_member_window)) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_valid_member_readable >> strip_tac >>
  RULE_ASSUM_TAC (SIMP_RULE bool_ss [map_replicate, SUM_REPLICATE]) >>
  asm_simp_tac arith_ss [GSYM ADD_ASSOC] >>
  fs[LENGTH_DROP, Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >> decide_tac
QED

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
    Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"]
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
  vyper_decode_valid_enc (Array NONE at) bs /\ j < LENGTH vs /\
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

(* Source validity justifies the actual dynamic-element offset and bounds guards. *)
Theorem abi_decoder_valid_array_setup_inputs:
  let at = vyper_to_abi_type env ty;
      asz = abi_embedded_static_size ce.ce_struct_fields ty;
      rel = abi_decode_member_offset at (DROP 32 bs) (j * abi_member_head_size at) in
  abi_decoder_coherent ce env sf ty tv /\ is_dynamic at /\
  (!elem. at <> Array (SOME 0) elem) /\
  vyper_decode_valid_enc (Array NONE at) bs /\ j < abi_head_word bs /\
  abi_decoder_ranges opc hi src dst sb (LENGTH bs) d outsz b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc initial) = bs ==>
  abi_decoder_dynamic (type_to_abi_dec_info sf ce ty) /\
  dec_info_needs_offset (type_to_abi_dec_info sf ce ty) /\ abi_decode_source_opcode opc /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decode_load opc (n2w (sb + 32 + j * asz):bytes32) initial = n2w rel /\
  (hi = Lit 0w \/ ?hb. eval_operand hi initial = SOME (n2w hb) /\
    sb + 32 + rel + asz <= hb /\ hb < dimword (:256))
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_coherent_header >> strip_tac >>
  qpat_assum `abi_decoder_header ce env ty tv`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_header_def]) >>
  drule abi_decoder_coherent_dynamic >> strip_tac >>
  drule_all abi_decoder_nonempty_type_offset >> strip_tac >>
  qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_ranges_def]) >>
  mp_tac (SIMP_RULE arith_ss [LET_THM]
    (Q.INST [`at` |-> `vyper_to_abi_type env ty`, `s` |-> `initial:venom_state`]
      abi_valid_array_child_window)) >> impl_tac >- asm_simp_tac bool_ss [] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `is_abi_dynamic ce.ce_struct_fields ty /\
    abi_decoder_dynamic (type_to_abi_dec_info sf ce ty)` by metis_tac[] >>
  RULE_ASSUM_TAC (SIMP_RULE arith_ss []) >>
  asm_simp_tac arith_ss [] >> Cases_on `hi = Lit 0w` >- simp[] >>
  qpat_x_assum `hi = Lit 0w \/ _` mp_tac >> asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `eval_operand hi initial = SOME (n2w hb)` >>
  qexists_tac `hb` >> asm_simp_tac bool_ss [] >> decide_tac
QED
