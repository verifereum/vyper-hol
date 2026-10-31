(* Introduce recursive metadata from child coherence and actual type evaluation. *)
Theory abiDecoderConstructors
Ancestors
  abiDecoderCoherence abiDecodeRanges compileEnv valueEncoding vyperABI contractABI
  list

Theorem decoder_caller_array:
  abi_decoder_coherent ce env sf ty tv /\
  evaluate_type env (ArrayT ty bound) = SOME (ArrayTV tv bound) ==>
  abi_decoder_coherent ce env sf (ArrayT ty bound) (ArrayTV tv bound)
Proof
  strip_tac >> drule abi_decoder_coherent_header >> strip_tac >>
  simp[abi_decoder_coherent_array_iff] >>
  Cases_on `bound` >> Cases_on `is_dynamic (vyper_to_abi_type env ty)` >>
  gvs[abi_decoder_header_def, type_memory_size_def, type_memory_bytes_def,
      vyper_to_abi_type_def, is_abi_dynamic_def, abi_embedded_static_size_def,
      abi_static_size_def, abi_member_head_size_def, is_dynamic_def,
      static_length_def]
QED

Theorem abi_decoder_header_list:
  !tys tvs. LIST_REL (abi_decoder_header ce env) tys tvs ==>
  type_memory_size_list tvs = SUM (MAP (type_memory_bytes ce) tys) /\
  any_dynamic (vyper_to_abi_types env tys) =
    EXISTS (is_abi_dynamic ce.ce_struct_fields) tys /\
  (~any_dynamic (vyper_to_abi_types env tys) ==>
    static_length (Tuple (vyper_to_abi_types env tys)) = type_memory_size_list tvs /\
    abi_static_size ce.ce_struct_fields (TupleT tys) = type_memory_size_list tvs)
Proof
  Induct_on `tys`
  >- (Cases_on `tvs` >>
      simp[vyper_to_abi_type_def, type_memory_size_def, abi_static_size_def]) >>
  qx_gen_tac `ty` >> Cases_on `tvs` >> simp[] >>
  rpt gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
  gvs[abi_decoder_header_def, vyper_to_abi_type_def, type_memory_size_def,
      abi_static_size_def, abi_embedded_static_size_def, abi_member_head_size_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem decoder_caller_tuple:
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  evaluate_type env (TupleT tys) = SOME (TupleTV tvs) ==>
  abi_decoder_coherent ce env sf (TupleT tys) (TupleTV tvs)
Proof
  strip_tac >>
  `LIST_REL (abi_decoder_header ce env) tys tvs` by
    (qpat_x_assum `LIST_REL _ _ _` mp_tac >>
     match_mp_tac LIST_REL_mono >> rpt strip_tac >>
     drule_all abi_decoder_coherent_header >> simp[]) >>
  drule abi_decoder_header_list >> strip_tac >>
  simp[abi_decoder_coherent_tuple_iff] >>
  Cases_on `any_dynamic (vyper_to_abi_types env tys)` >>
  gvs[abi_decoder_header_def, type_memory_size_def, type_memory_bytes_def,
      vyper_to_abi_type_def, is_abi_dynamic_def, abi_embedded_static_size_def,
      abi_member_head_size_def, is_dynamic_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM NOT_EXISTS]) >>
  asm_simp_tac bool_ss [GSYM NOT_EXISTS]
QED
