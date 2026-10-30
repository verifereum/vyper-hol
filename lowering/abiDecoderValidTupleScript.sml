Theory abiDecoderValidTuple
Ancestors
  abiDecoderValidContract abiDecoderTupleInputs abiDecoderMembers abiDecoderMemberInfos
  abiDecoderCoherence abiDecoderTypedContract abiDecoderContract abiValidMembers compileEnv
  valueEncoding vyperABI contractABI venomState words list abiDecoderValidComplex
  abiDecoderValidLeaves abiDecoderEffect abiDecoderReentry fragExec valueEncodingProps
  vyperValue

(* ===== Inputs ===== *)

(* Recover tuple metadata from the actual valid source bytes. *)

Theorem abi_decoder_valid_tuple_inputs:
  abi_decoder_valid_pre ce env sf (TupleT tys) (TupleTV tvs) bs v
    st src dst opc hi sb d b cap initial ==>
  ?vs. v = ArrayV (TupleV vs) /\
    abi_decoder_members ce env sf tys tvs
      (abi_decode_members (MAP (vyper_to_abi_type env) tys) bs bs) vs /\
    vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys) bs bs /\
    type_memory_bytes ce (TupleT tys) = SUM (MAP (type_memory_bytes ce) tys) /\
    abi_decoder_ranges opc hi src dst sb (LENGTH bs)
      d (SUM (MAP (type_memory_bytes ce) tys)) b cap initial /\
    mem_bytes_at sb (LENGTH bs) (abi_decode_source opc initial) = bs /\
    abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
    abi_decoder_operand_live st.cs_next_var hi
Proof
  simp_tac bool_ss [abi_decoder_valid_pre_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `type_memory_bytes ce (TupleT tys) = SUM (MAP (type_memory_bytes ce) tys)`
    by (simp[Once type_memory_bytes_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  `vyper_decode_valid_enc (Tuple (MAP (vyper_to_abi_type env) tys)) bs` by
    (qpat_x_assum `vyper_decode_valid_enc _ bs` mp_tac >>
     simp_tac bool_ss [Once vyper_to_abi_type_def, vyper_to_abi_types_MAP]) >>
  drule abi_valid_tuple_view >> strip_tac >>
  qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
  drule abi_decoder_tuple_values >> strip_tac >>
  gvs[Once vyper_to_abi_type_def, vyper_to_abi_types_MAP,
    Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  drule_all abi_decoder_tuple_members >> strip_tac >>
  asm_simp_tac bool_ss [] >>
  qpat_x_assum `vyper_decode_valid_enc (Tuple _) bs` mp_tac >> simp_tac bool_ss [Once vyper_decode_valid_enc_def]
QED

(* ===== Decoder Valid Tuple ===== *)

(* Tuple decoding follows arbitrary source-valid member offsets and payloads. *)

Theorem abi_decoder_valid_correct_tuple:
  LIST_REL (abi_decoder_valid_correct ce env sf) tys tvs ==>
  abi_decoder_valid_correct ce env sf (TupleT tys) (TupleTV tvs)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  simp_tac bool_ss [abi_decoder_valid_correct_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_valid_tuple_inputs >> strip_tac >>
  gvs[Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _`
    (assume_tac o PURE_REWRITE_RULE [abi_decoder_tuple_infos]) >>
  mp_tac (Q.INST [`st` |-> `start`, `final` |-> `end_st`,
    `dyn` |-> `EXISTS (is_abi_dynamic ce.ce_struct_fields) tys`] abi_decoder_valid_complex_execute) >>
  impl_tac >- asm_simp_tac bool_ss [] >>
  asm_simp_tac bool_ss [val_in_memory_tuple]
QED

Theorem abi_decoder_valid_base_member_nonempty:
  !bt. is_dynamic (vyper_to_abi_type env (BaseT bt)) ==>
    !elem. vyper_to_abi_type env (BaseT bt) <> Array (SOME 0) elem
Proof
  Cases >> simp[vyper_to_abi_type_def] >>
  rename1 `BytesT bound` >> Cases_on `bound` >> simp[]
QED

Theorem abi_decoder_valid_correct_base_tuple:
  !bts. abi_decoder_valid_correct ce env sf
    (TupleT (MAP BaseT bts)) (TupleTV (MAP BaseTV bts))
Proof
  gen_tac >>
  `LIST_REL (abi_decoder_valid_correct ce env sf) (MAP BaseT bts) (MAP BaseTV bts)` by
    (Induct_on `bts` >> simp[abi_decoder_valid_correct_base]) >>
  `EVERY (\ty. is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) (MAP BaseT bts)` by
    (simp_tac bool_ss [EVERY_MAP, EVERY_MEM, combinTheory.o_DEF] >>
     qx_gen_tac `bt` >> strip_tac >>
     MATCH_ACCEPT_TAC (Q.SPEC `bt` abi_decoder_valid_base_member_nonempty)) >>
  irule abi_decoder_valid_correct_tuple >> asm_simp_tac bool_ss []
QED
