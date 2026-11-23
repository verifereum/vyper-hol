Theory bodyFullExtCallDirectLayout
Ancestors
  abiEncodeValuesSource abiEncodeValuesMetadata abiCallerTupleLayout
  abiDecoderMembers abiTypeBoundProps abiDecodeRanges
  exprSimAbiEncodeArgsPhysicalCapacity exprSimAbiEncodePlanMetadata
  vyperTypeABI vyperABIValid vyperABIRoundtrip vyperTypeArgFits vyperTypeDefaults
  vyperABI vyperValue vyperTyping contractABI context compileEnv list

(* Physical members supply the operands to the encoder. ABI widening
   agrees with the declared signature on both their types and values. *)
Theorem extcall_direct_args_layout:
  LENGTH tys = LENGTH arg_types /\ LENGTH tys = LENGTH vs /\
  LENGTH tys = LENGTH saved /\
  sfields_tenv_consistent sf env /\
  (!i. i < LENGTH tys ==>
    ?tv ftv. evaluate_type env (EL i tys) = SOME tv /\
      evaluate_type env (EL i arg_types) = SOME ftv /\
      arg_type_fits (EL i tys) (EL i arg_types) /\
      value_has_type tv (EL i vs) /\ value_has_type ftv (EL i vs)) ==>
  ?avs ats bytes.
    vyper_to_abi_list env tys vs = SOME avs /\
    ats = vyper_to_abi_types env tys /\
    bytes = enc (Tuple ats) (ListV avs) /\
    build_ext_calldata env fname arg_types vs =
      SOME (function_selector fname (vyper_to_abi_types env arg_types) ++ bytes) /\
    LENGTH bytes <= abi_size_bound sf (TupleT tys) /\
    LIST_REL abi_encoder_layout_valid ats avs /\
    LIST_REL (\row at. abi_embedded_static_size sf (SND row) = abi_member_head_size at)
      (ZIP (saved,tys)) ats
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qabbrev_tac `tvs = MAP (THE o evaluate_type env) tys` >>
  qabbrev_tac `ftvs = MAP (THE o evaluate_type env) arg_types` >>
  `!i. i < LENGTH tys ==>
    evaluate_type env (EL i tys) = SOME (EL i tvs) /\
    evaluate_type env (EL i arg_types) = SOME (EL i ftvs) /\
    arg_type_fits (EL i tys) (EL i arg_types) /\
    value_has_type (EL i tvs) (EL i vs) /\ value_has_type (EL i ftvs) (EL i vs)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!i. _ ==> ?tv ftv. _` (qspec_then `i` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     strip_tac >> fs[Abbr `tvs`, Abbr `ftvs`, EL_MAP]) >>
  `LENGTH tvs = LENGTH tys /\ LENGTH ftvs = LENGTH tys` by simp[Abbr `tvs`,Abbr `ftvs`] >>
  `LIST_REL (\ty tv. evaluate_type env ty = SOME tv) tys tvs /\
    LIST_REL (\ty tv. evaluate_type env ty = SOME tv) arg_types ftvs /\
    values_have_types tvs vs /\ values_have_types ftvs vs /\ arg_types_fit tys arg_types` by
    (asm_simp_tac bool_ss [arg_types_fit_LIST_REL, values_have_types_LIST_REL, LIST_REL_EL_EQN] >>
     metis_tac[]) >>
  `?avs. vyper_to_abi_list env tys vs = SOME avs` by
    metis_tac[cj 2 vyper_to_abi_total] >>
  `vyper_to_abi_types env tys = vyper_to_abi_types env arg_types` by
    metis_tac[cj 2 abi_args_fits_abi_type] >>
  `vyper_to_abi_list env arg_types vs = SOME avs` by
    metis_tac[cj 2 abi_args_fits_conversion] >>
  qpat_assum `vyper_to_abi_list env tys vs = SOME avs`
    (strip_assume_tac o MATCH_MP vyper_to_abi_list_EL) >>
  qabbrev_tac `ats = vyper_to_abi_types env tys` >>
  qabbrev_tac `bytes = enc (Tuple ats) (ListV avs)` >>
  `abi_size_bound sf (TupleT tys) = vyper_abi_size_bound env (TupleT tys)` by
    (irule abi_size_bound_tuple_typed >> asm_rewrite_tac[] >>
     simp[EVERY_EL] >> metis_tac[optionTheory.IS_SOME_EXISTS]) >>
  qexistsl_tac [`avs`,`ats`,`bytes`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY (simp_tac bool_ss [Abbr `bytes`])
  >- (`TAKE (LENGTH vs) arg_types = arg_types` by simp[TAKE_LENGTH_ID_rwt] >>
      asm_simp_tac (srw_ss()) [build_ext_calldata_def, LET_THM])
  >- (simp_tac bool_ss [Abbr `ats`] >>
      metis_tac[cj 2 vyper_to_abi_enc_le_size_bound])
  >- (simp_tac bool_ss [Abbr `ats`, vyper_to_abi_types_MAP, LIST_REL_EL_EQN, LENGTH_MAP] >>
      conj_tac >- decide_tac >>
      qx_gen_tac `i` >> disch_tac >>
      asm_simp_tac bool_ss [EL_MAP] >>
      irule abi_encode_values_typed_layout >>
      qexistsl_tac [`EL i tvs`,`EL i vs`] >>
      metis_tac[abi_caller_static_memory])
  >> simp_tac bool_ss [Abbr `ats`, LIST_REL_EL_EQN, vyper_to_abi_types_MAP, LENGTH_MAP, LENGTH_ZIP] >>
  conj_tac >- simp[] >>
  qx_gen_tac `i` >> disch_tac >>
  `i < LENGTH tys` by fs[LENGTH_ZIP] >>
  `i < LENGTH saved` by decide_tac >>
  asm_simp_tac (srw_ss()) [EL_MAP, EL_ZIP] >>
  metis_tac[abi_encode_translated_head]
QED
