(* Recursive default inputs use the real descriptor and semantic memory size.
   The operand list used for tuple assembly is internal to the proof. *)
Theory abiEmptyAggregateInput
Ancestors
  abiEmptyTupleInput abiEmptyInput abiTupleEncodeAssembly abiTupleEncodeMemory abiEncoderInput
  abiDecoderCoherence abiDecoderMembers compileEnv exprLowering valueEncoding vyperABI
  contractABI words list rich_list arithmetic

Theorem abi_empty_infos_zip:
  !tys. abi_tuple_encode_infos sf ce (ZIP (REPLICATE (LENGTH tys) (Lit 0w),tys)) =
    MAP (\ty. (type_to_abi_enc_info sf ce ty,
      abi_embedded_static_size ce.ce_struct_fields ty, type_memory_bytes ce ty,
      is_abi_dynamic ce.ce_struct_fields ty)) tys
Proof
  simp_tac bool_ss [abi_tuple_encode_infos_def] >> Induct >> simp[]
QED

Theorem abi_empty_members_zero:
  LIST_REL (\ty tv. abi_decoder_coherent ce env sf ty tv /\
    (has_type (vyper_to_abi_type env ty) (default_to_abi tv) ==>
      abi_encoder_input (type_to_abi_enc_info sf ce ty) (vyper_to_abi_type env ty)
        (default_to_abi tv) 0 (type_memory_bytes ce ty) [])) tys tvs /\
  abi_encoder_tuple_type at (vyper_to_abi_types env tys) /\
  has_type at (ListV (default_to_abi_list tvs)) ==>
  abi_encoder_input (AbiComplex (MAP (\ty. (type_to_abi_enc_info sf ce ty,
      abi_embedded_static_size ce.ce_struct_fields ty, type_memory_bytes ce ty,
      is_abi_dynamic ce.ce_struct_fields ty)) tys)) at
    (ListV (default_to_abi_list tvs)) p (type_memory_bytes ce (TupleT tys)) []
Proof
  strip_tac >>
  mp_tac (Q.INST [`ops` |-> `REPLICATE (LENGTH tys) (Lit 0w)`]
    abi_empty_complex_zero) >>
  impl_tac >- simp[] >>
  simp[abi_empty_infos_zip, abi_tuple_encode_bytes_zip]
QED

Theorem abi_empty_tuple_default_input:
  abi_decoder_coherent ce env sf (TupleT tys) (TupleTV tvs) /\
  LIST_REL (\ty tv.
    has_type (vyper_to_abi_type env ty) (default_to_abi tv) ==>
      abi_encoder_input (type_to_abi_enc_info sf ce ty) (vyper_to_abi_type env ty)
        (default_to_abi tv) 0 (type_memory_bytes ce ty) []) tys tvs /\
  has_type (vyper_to_abi_type env (TupleT tys)) (default_to_abi (TupleTV tvs)) ==>
  abi_encoder_input (type_to_abi_enc_info sf ce (TupleT tys))
    (vyper_to_abi_type env (TupleT tys)) (default_to_abi (TupleTV tvs))
    0 (type_memory_bytes ce (TupleT tys)) []
Proof
  strip_tac >> Cases_on `is_dynamic (vyper_to_abi_type env (TupleT tys))`
  >- (drule abi_decoder_coherent_header >> strip_tac >>
      `is_abi_dynamic ce.ce_struct_fields (TupleT tys)` by fs[abi_decoder_header_def] >>
      asm_simp_tac bool_ss [Once type_to_abi_enc_info_def,
        vyper_to_abi_type_def, default_to_abi_def] >>
      mp_tac (Q.INST [`tys` |-> `tys`, `tvs` |-> `tvs`, `env` |-> `env`,
        `at` |-> `Tuple (vyper_to_abi_types env tys)`, `p` |-> `0`]
        abi_empty_members_zero) >>
      impl_tac
      >- (fs[abi_encoder_tuple_type_def, LIST_REL_CONJ, ETA_AX,
             abi_decoder_coherent_tuple_iff, default_to_abi_def] >>
          CONV_TAC (DEPTH_CONV ETA_CONV) >> asm_rewrite_tac[]) >>
      simp[]) >>
  irule abi_empty_coherent_static_input >> simp[abi_empty_memory_observation]
QED

Theorem abi_empty_fixed_memory_size:
  type_memory_bytes ce (TupleT (REPLICATE n ty)) =
    type_memory_bytes ce (ArrayT ty (Fixed n))
Proof
  simp[type_memory_bytes_def, map_replicate, SUM_REPLICATE]
QED

Theorem abi_empty_fixed_default_input:
  abi_decoder_coherent ce env sf (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n)) /\
  (has_type (vyper_to_abi_type env ty) (default_to_abi tv) ==>
    abi_encoder_input (type_to_abi_enc_info sf ce ty) (vyper_to_abi_type env ty)
      (default_to_abi tv) 0 (type_memory_bytes ce ty) []) /\
  has_type (vyper_to_abi_type env (ArrayT ty (Fixed n)))
    (default_to_abi (ArrayTV tv (Fixed n))) ==>
  abi_encoder_input (type_to_abi_enc_info sf ce (ArrayT ty (Fixed n)))
    (vyper_to_abi_type env (ArrayT ty (Fixed n))) (default_to_abi (ArrayTV tv (Fixed n)))
    0 (type_memory_bytes ce (ArrayT ty (Fixed n))) []
Proof
  strip_tac >> Cases_on `is_dynamic (vyper_to_abi_type env (ArrayT ty (Fixed n)))`
  >- (drule abi_decoder_coherent_header >> strip_tac >>
      `is_abi_dynamic ce.ce_struct_fields (ArrayT ty (Fixed n))` by
        fs[abi_decoder_header_def] >>
      mp_tac (Q.INST [`tys` |-> `REPLICATE n ty`, `tvs` |-> `REPLICATE n tv`,
        `at` |-> `vyper_to_abi_type env (ArrayT ty (Fixed n))`, `p` |-> `0`]
        abi_empty_members_zero) >>
      impl_tac
      >- (simp[LIST_REL_REPLICATE_same, abi_encoder_tuple_type_def,
            vyper_to_abi_type_def, vyper_to_abi_types_MAP, map_replicate,
            default_to_abi_def, default_to_abi_list_MAP] >>
          fs[abi_decoder_coherent_array_iff, default_to_abi_def, has_type_def,
             valid_length_def, have_type_has_types_REPLICATE]) >>
      asm_simp_tac bool_ss [Once type_to_abi_enc_info_def, default_to_abi_def,
        default_to_abi_list_MAP, map_replicate, GSYM REPLICATE_GENLIST,
        abi_empty_fixed_memory_size]) >>
  irule abi_empty_coherent_static_input >> simp[abi_empty_memory_observation]
QED
