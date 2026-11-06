(* Tuple constructor closure for conditional owned decoder producers. *)
Theory entryReachBodyConditionalTupleClosure
Ancestors
  entryReachBodyConditionalProducer entryReachBodyConditionalMembers
  entryReachBodyCanonicalMembers entryReachBodyCanonicalArrayChild
  abiDecoderMembers abiDecoderCoherence abiDecoderTypedContract abiDecoderMemberInfos
  valueEncodingProps valueEncoding vyperABI vyperTyping vyperValue contractABI
  exprLowering compileEnv abiEncoder

Theorem conditional_tuple_metadata_shape[local]:
  abi_decoder_metadata ce env (TupleT tys) (TupleTV tvs) di av v ==>
  ?avs vs. av = ListV avs /\ v = ArrayV (TupleV vs)
Proof
  Cases_on `av` >> simp_tac bool_ss [abi_decoder_metadata_def] >> strip_tac >>
  gvs[Once vyper_to_abi_type_def, Once has_type_def, Once abi_to_vyper_def,
      AllCaseEqs()]
QED

Theorem conditional_tuple_result[local]:
  canonical_members_effect ctx fn ambient cell sz st s t /\
  canonical_members_frame ctx fn oid root extent ambient b cap site limit_st
    dst src sb cell sz last t /\
  tuple_in_memory vs tvs cell t.vs_memory /\
  abi_encoder_registered_effect ids [(cell,sz)] s t /\
  sz = type_memory_size (TupleTV tvs) ==>
  array_child_result ctx fn oid root extent ambient ids b cap site limit_st
    st last cell (TupleTV tvs) (ArrayV (TupleV vs)) s t
Proof
  simp[canonical_members_effect_def, canonical_members_frame_def,
       array_child_result_def, val_in_memory_tuple] >> rpt strip_tac >> gvs[]
QED

Theorem entry_conditional_tuple_producer:
  abi_decoder_coherent ce env ce.ce_struct_fields (TupleT tys) (TupleTV tvs) /\
  (!i av v. i < LENGTH tys ==> entry_conditional_array_child_producer ce env
    (EL i tys) (EL i tvs) av v ctx fn oid root extent ambient b cap site limit_st) ==>
  entry_conditional_array_child_producer ce env (TupleT tys) (TupleTV tvs)
    pav pv ctx fn oid root extent ambient b cap site limit_st
Proof
  strip_tac >> simp_tac bool_ss [entry_conditional_array_child_producer_def] >>
  rpt gen_tac >> strip_tac >>
  drule conditional_tuple_metadata_shape >> strip_tac >> gvs[Excl "enc_def"] >>
  drule_all abi_decoder_tuple_members >> disch_tac >>
  `type_memory_size (TupleTV tvs) = SUM (MAP (type_memory_bytes ce) tys)` by
    (qpat_assum `abi_decoder_coherent _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_decoder_coherent_tuple_iff] >> strip_tac >> gvs[] >>
     drule abi_decoder_member_infos_layout >> simp[type_memory_size_def]) >>
  `canonical_members_frame ctx fn oid root extent ambient b cap site limit_st
    dst src sb cell (SUM (MAP (type_memory_bytes ce) tys)) st s` by
    (simp[canonical_members_frame_def] >> gvs[Excl "enc_def"]) >>
  `cell+SUM (MAP (type_memory_bytes ce) tys) < dimword (:256)` by gvs[Excl "enc_def"] >>
  `compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w)
    (DecComplex (EXISTS (is_abi_dynamic ce.ce_struct_fields) tys)
      (abi_decoder_member_infos ce.ce_struct_fields ce tys)) st = ((),last)` by
    (qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
     simp[abi_decoder_tuple_infos]) >>
  `(!i. i < LENGTH tys ==> entry_conditional_array_child_producer ce env
    (EL i tys) (EL i tvs) (EL i avs) (EL i vs) ctx fn oid root extent ambient b cap site limit_st)` by simp[] >>
  fs[vyper_to_abi_types_MAP, Excl "enc_def"] >>
  drule_all entry_conditional_local_complex_endpoint >> strip_tac >>
  qexists_tac `t` >> irule conditional_tuple_result >>
  goal_assum (drule_at Any) >> simp[] >> goal_assum (drule_at Any)
QED
