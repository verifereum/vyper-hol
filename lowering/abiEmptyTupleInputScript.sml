(* Assemble recursive default inputs over concrete zero-filled memory.
   Child premises are pure data properties for structural induction. *)
Theory abiEmptyTupleInput
Ancestors
  abiEmptyInput abiTupleEncodeAssembly abiTupleEncodeMemory abiTupleEncodeSourceLayout
  abiEncoderInput abiDecoderCoherence compileEnv exprLowering valueEncoding vyperABI contractABI
  words list rich_list arithmetic

Theorem abi_empty_tuple_type_typed:
  abi_encoder_tuple_type at ats /\ has_type at (ListV avs) ==>
  has_type (Tuple ats) (ListV avs)
Proof
  rw[abi_encoder_tuple_type_def] >>
  gvs[has_type_def, valid_length_def, have_type_has_types_REPLICATE]
QED

Theorem abi_empty_complex_type:
  abi_encoder_input (AbiComplex infos) (Tuple ats) (ListV avs) p cap mem /\
  abi_encoder_tuple_type at ats /\ has_type at (ListV avs) ==>
  abi_encoder_input (AbiComplex infos) at (ListV avs) p cap mem
Proof
  strip_tac >>
  qpat_x_assum `abi_encoder_input _ (Tuple ats) _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss())
      [abi_encoder_complex_input_iff, abi_encoder_tuple_type_def]) >>
  ONCE_REWRITE_TAC [abi_encoder_complex_input_iff] >>
  qexists_tac `ats` >> qexists_tac `avs` >> asm_rewrite_tac[]
QED

Theorem abi_empty_tuple_memory:
  !(ops:operand list) tys tvs p.
  LENGTH ops = LENGTH tys /\
  LIST_REL (\ty tv.
    has_type (vyper_to_abi_type env ty) (default_to_abi tv) ==>
    abi_encoder_input (type_to_abi_enc_info sf ce ty) (vyper_to_abi_type env ty)
      (default_to_abi tv) 0 (type_memory_bytes ce ty) []) tys tvs /\
  has_types (vyper_to_abi_types env tys) (default_to_abi_list tvs) ==>
  abi_tuple_encode_memory (sf:string |-> (string # vyperAST$type # num) list)
    ce (ZIP (ops,tys)) (vyper_to_abi_types env tys)
    (default_to_abi_list tvs) p []
Proof
  Induct_on `ops` >> rpt gen_tac >> Cases_on `tys` >> Cases_on `tvs` >>
  simp[abi_tuple_encode_memory_def, default_to_abi_def, has_type_def] >> strip_tac >>
  FIRST [irule abi_empty_input_zero_address >> first_x_assum irule >> simp[],
    first_x_assum irule >> simp[]]
QED

Theorem abi_empty_complex_zero:
  LENGTH ops = LENGTH tys /\
  LIST_REL (\ty tv. abi_decoder_coherent ce env sf ty tv /\
    (has_type (vyper_to_abi_type env ty) (default_to_abi tv) ==>
      abi_encoder_input (type_to_abi_enc_info sf ce ty) (vyper_to_abi_type env ty)
        (default_to_abi tv) 0 (type_memory_bytes ce ty) [])) tys tvs /\
  abi_encoder_tuple_type at (vyper_to_abi_types env tys) /\
  has_type at (ListV (default_to_abi_list tvs)) ==>
  abi_encoder_input (AbiComplex (abi_tuple_encode_infos sf ce (ZIP (ops,tys))))
    at (ListV (default_to_abi_list tvs)) p (abi_tuple_bytes ce (ZIP (ops,tys))) []
Proof
  simp_tac bool_ss [LIST_REL_CONJ, ETA_AX] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV ETA_CONV)) >>
  drule_all abi_empty_tuple_type_typed >> strip_tac >>
  `has_types (vyper_to_abi_types env tys) (default_to_abi_list tvs)` by
    (qpat_assum `has_type (Tuple _) (ListV _)`
      (ACCEPT_TAC o CONJUNCT2 o ONCE_REWRITE_RULE [has_type_def])) >>
  `abi_tuple_encode_memory sf ce (ZIP (ops,tys)) (vyper_to_abi_types env tys)
     (default_to_abi_list tvs) p []` by
    (mp_tac (Q.SPECL [`ops`, `tys`, `tvs`, `p`] abi_empty_tuple_memory) >>
     impl_tac >- asm_rewrite_tac[] >> simp[]) >>
  drule_all abi_tuple_encode_layout_coherent >> strip_tac >>
  drule_all abi_tuple_encode_complex_input >> strip_tac >>
  drule_all abi_empty_complex_type >> simp[]
QED
