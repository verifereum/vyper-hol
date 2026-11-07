Theory exprSimAbiDecodeConstructorOutcome
Ancestors
  exprSimAbiDecodeConstructorRows exprSimAbiDecodeComplexOutcome
  exprSimAbiDecodeTupleAssembly exprSimAbiDecodeOwnedContext
  abiDecoderCoherence vyperTypeSystem list rich_list

Theorem abi_decode_tuple_owned_contract:
  abi_decoder_coherent ce env ce.ce_struct_fields (TupleT tys) atv /\
  assignable_type env (TupleT tys) /\ abi_decode_bytes_widths env (TupleT tys) /\
  (!ty tv. MEM ty tys /\ abi_decoder_coherent ce env ce.ce_struct_fields ty tv ==>
    abi_decode_owned_child_contract ce env ty tv) ==>
  abi_decode_owned_child_contract ce env (TupleT tys) atv
Proof
  strip_tac >> drule_all abi_decode_tuple_pure_rows >> strip_tac >>
  irule abi_decode_tuple_owned_contract_rows >>
  qexistsl_tac [`EXISTS (is_abi_dynamic ce.ce_struct_fields) tys`, `rows`] >>
  asm_rewrite_tac [] >>
  simp_tac (srw_ss()) [EVERY_MEM] >> gen_tac >> strip_tac >> PairCases_on `e` >>
  `abi_decoder_coherent ce env ce.ce_struct_fields e1 e2` by
    (fs[abi_tuple_rows_schema_def, EVERY_MEM] >>
     first_x_assum drule >> simp[]) >>
  `MEM e1 tys` by
    (asm_rewrite_tac [] >> simp[MEM_MAP] >>
     qexists `(e0,e1,e2,e3,e4)` >> simp[]) >>
  simp[] >> metis_tac[]
QED

Theorem abi_decode_struct_owned_contract:
  abi_decoder_coherent ce env ce.ce_struct_fields (StructT nsid) atv /\
  assignable_type env (StructT nsid) /\ abi_decode_bytes_widths env (StructT nsid) /\
  FLOOKUP ce.ce_struct_fields (nsid_to_string nsid) = SOME fields /\
  (!ty tv. MEM ty (MAP (FST o SND) fields) /\
    abi_decoder_coherent ce (env \\ nsid) (ce.ce_struct_fields \\ nsid_to_string nsid) ty tv ==>
    abi_decode_owned_child_contract ce (env \\ nsid) ty tv) ==>
  abi_decode_owned_child_contract ce env (StructT nsid) atv
Proof
  strip_tac >> drule_all abi_decode_struct_pure_rows >> strip_tac >>
  `fields' = fields` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `fields' = fields` SUBST_ALL_TAC >>
  irule abi_decode_struct_owned_contract_rows >>
  qexistsl_tac [`args`, `fields`, `rows`] >>
  asm_rewrite_tac [] >>
  simp_tac (srw_ss()) [EVERY_MEM] >> gen_tac >> strip_tac >> PairCases_on `e` >>
  `?i. i < LENGTH rows /\ EL i rows = (e0,e1,e2,e3,e4)` by
    metis_tac[MEM_EL] >>
  `abi_decoder_coherent ce (env \\ nsid) (ce.ce_struct_fields \\ nsid_to_string nsid)
     e1 e2` by
    (qpat_x_assum `LIST_REL _ _ _` mp_tac >>
     simp[LIST_REL_EL_EQN, EL_MAP] >> strip_tac >>
     first_x_assum (qspec_then `i` mp_tac) >> simp[]) >>
  `MEM e1 (MAP (FST o SND) fields)` by
    (qpat_x_assum `MAP _ rows = MAP _ fields` (SUBST1_TAC o SYM) >>
     simp[MEM_MAP] >> qexists `(e0,e1,e2,e3,e4)` >> simp[]) >>
  simp[] >> metis_tac[]
QED
