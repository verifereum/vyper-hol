Theory abiDecoderValidFixed
Ancestors
  vyperABIValid abiDecoderValidContract abiDecoderFixedMembers abiDecoderMembers abiDecoderCoherence
  abiDecoderTypedContract abiDecoderContract abiValidMembers abiValidAggregateHeads
  abiCanonicalHeadSize abiCanonicalArrays compileEnv valueEncoding vyperABI vyperValue
  contractABI venomState words list rich_list abiDecoderFixedMemory abiDecoderValidComplex
  abiDecoderMemberInfos abiDecoderEffect abiDecoderReentry fragExec

(* ===== Inputs ===== *)

(* Fixed arrays use the actual repeated-type member view of source-valid bytes. *)

Theorem abi_decoder_valid_fixed_view:
  vyper_decode_valid_enc (Array (SOME n) at) bs ==>
  vyper_decode_valid_enc_tuple (REPLICATE n at) bs bs /\
  dec (Array (SOME n) at) bs = ListV (abi_decode_members (REPLICATE n at) bs bs)
Proof
  strip_tac >>
  `vyper_decode_valid_enc_tuple (REPLICATE n at) bs bs` by
    fs[Once vyper_decode_valid_enc_def, vyper_decode_valid_enc_tuple_REPLICATE, Excl "dec_def"] >>
  asm_simp_tac (srw_ss()) [Once dec_def, LET_THM, abi_decode_array_members, abi_decode_members_value,
    Excl "dec_def", Excl "enc_def", Excl "vyper_decode_valid_enc_def"]
QED

Theorem abi_decoder_valid_fixed_array_inputs:
  abi_decoder_valid_pre ce env sf (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n))
    bs v st src dst opc hi sb d b cap initial ==>
  ?vs. v = ArrayV (SArrayV (enumerate_static_array (default_value tv) 0 vs)) /\ LENGTH vs = n /\
    abi_decoder_members ce env sf (REPLICATE n ty) (REPLICATE n tv)
      (abi_decode_members (MAP (vyper_to_abi_type env) (REPLICATE n ty)) bs bs) vs /\
    vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) (REPLICATE n ty)) bs bs /\
    type_memory_bytes ce (ArrayT ty (Fixed n)) = SUM (MAP (type_memory_bytes ce) (REPLICATE n ty)) /\
    abi_decoder_ranges opc hi src dst sb (LENGTH bs)
      d (SUM (MAP (type_memory_bytes ce) (REPLICATE n ty))) b cap initial /\
    mem_bytes_at sb (LENGTH bs) (abi_decode_source opc initial) = bs /\
    abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
    abi_decoder_operand_live st.cs_next_var hi
Proof
  simp_tac bool_ss [abi_decoder_valid_pre_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_fixed_array_values >> strip_tac >>
  `type_memory_bytes ce (ArrayT ty (Fixed n)) = SUM (MAP (type_memory_bytes ce) (REPLICATE n ty))`
    by simp[Once type_memory_bytes_def, map_replicate, SUM_REPLICATE] >>
  `vyper_decode_valid_enc (Array (SOME n) (vyper_to_abi_type env ty)) bs` by
    (qpat_x_assum `vyper_decode_valid_enc _ bs` mp_tac >> simp_tac bool_ss [Once vyper_to_abi_type_def]) >>
  drule abi_decoder_valid_fixed_view >> strip_tac >>
  gvs[Once vyper_to_abi_type_def, map_replicate,
    Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  qexists_tac `vs` >> asm_simp_tac bool_ss []
QED

(* ===== Decoder Valid Fixed ===== *)

(* Actual-source fixed arrays execute the shared member decoder and recover sparse values. *)

Theorem abi_decoder_valid_correct_fixed_array:
  abi_decoder_valid_correct ce env sf ty tv /\
  (0 < n /\ is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) ==>
  abi_decoder_valid_correct ce env sf (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> simp_tac bool_ss [abi_decoder_valid_correct_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_valid_fixed_array_inputs >> strip_tac >> gvs[Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  (`LIST_REL (abi_decoder_valid_correct ce env sf) (REPLICATE (LENGTH vs) ty) (REPLICATE (LENGTH vs) tv)`
    by simp[LIST_REL_REPLICATE_same] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _`
    (assume_tac o PURE_REWRITE_RULE [abi_decoder_fixed_array_infos]) >>
  mp_tac (SIMP_RULE bool_ss [map_replicate, SUM_REPLICATE]
    (Q.INST [`st` |-> `start`, `final` |-> `end_st`, `tys` |-> `REPLICATE (LENGTH vs) ty`,
      `tvs` |-> `REPLICATE (LENGTH vs) tv`, `dyn` |-> `is_abi_dynamic ce.ce_struct_fields ty`]
      abi_decoder_valid_complex_execute)) >>
  impl_tac >- (asm_simp_tac (srw_ss()) [EVERY_MEM, MEM_REPLICATE,
    Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
    Cases_on `vs` >> gvs[Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"]) >> strip_tac >>
  rename1 `tuple_in_memory vs (REPLICATE (LENGTH vs) tv) d actual.vs_memory` >>
  `val_in_memory (ArrayTV tv (Fixed (LENGTH vs)))
    (ArrayV (SArrayV (enumerate_static_array (default_value tv) 0 vs))) d actual.vs_memory`
    by (irule abi_decoder_fixed_array_memory >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [])
QED
