Theory exprSimAbiEncodeArgsPhysicalCapacity
Ancestors
  abiTypeBoundProps vyperTypeArgFits vyperABIValid vyperABIRoundtrip compileEnv
  vyperTypeSystem vyperABI vyperValue vyperTyping vyperTypeValues vyperAST list

(* Bounds erased by ABI types do not change the wire representation. *)
Theorem abi_args_fits_abi_type:
  (!t u. arg_type_fits t u ==>
     vyper_to_abi_type tenv t = vyper_to_abi_type tenv u) /\
  (!ts us. arg_types_fit ts us ==>
     vyper_to_abi_types tenv ts = vyper_to_abi_types tenv us)
Proof
  ho_match_mp_tac arg_type_fits_ind >>
  simp[arg_type_fits_def, vyper_base_to_abi_type_def]
QED

Theorem abi_args_same_conversion_cong[local]:
  (!v. vyper_to_abi tenv t v = vyper_to_abi tenv u v) ==>
  !vs. vyper_to_abi_same tenv t vs = vyper_to_abi_same tenv u vs
Proof
  strip_tac >> Induct >> simp[]
QED

Theorem abi_args_sparse_conversion_cong[local]:
  (!v. vyper_to_abi tenv t v = vyper_to_abi tenv u v) /\
  default_to_abi tv = default_to_abi uv ==>
  !n sp. vyper_to_abi_sparse tenv t tv n sp =
         vyper_to_abi_sparse tenv u uv n sp
Proof
  strip_tac >> Induct >> simp[]
QED

Theorem abi_args_fits_default_encoding:
  (!t u tv uv.
     arg_type_fits t u /\ evaluate_type tenv t = SOME tv /\
     evaluate_type tenv u = SOME uv ==>
     default_to_abi tv = default_to_abi uv) /\
  (!ts us tvs uvs.
     arg_types_fit ts us /\
     LIST_REL (\t tv. evaluate_type tenv t = SOME tv) ts tvs /\
     LIST_REL (\t tv. evaluate_type tenv t = SOME tv) us uvs ==>
     MAP default_to_abi tvs = MAP default_to_abi uvs)
Proof
  ho_match_mp_tac arg_type_fits_ind >> rw[arg_type_fits_def] >>
  imp_res_tac evaluate_type_ArrayT_cases >>
  imp_res_tac evaluate_type_TupleT_cases >>
  gvs[evaluate_type_def, default_to_abi_def, default_to_abi_list_MAP] >>
  metis_tac[]
QED

Theorem abi_args_fits_conversion:
  (!t u tv uv.
     arg_type_fits t u /\ evaluate_type tenv t = SOME tv /\
     evaluate_type tenv u = SOME uv ==>
     !v. vyper_to_abi tenv t v = vyper_to_abi tenv u v) /\
  (!ts us tvs uvs.
     arg_types_fit ts us /\
     LIST_REL (\t tv. evaluate_type tenv t = SOME tv) ts tvs /\
     LIST_REL (\t tv. evaluate_type tenv t = SOME tv) us uvs ==>
     !vs. vyper_to_abi_list tenv ts vs = vyper_to_abi_list tenv us vs)
Proof
  ho_match_mp_tac arg_type_fits_ind >> rw[arg_type_fits_def] >>
  imp_res_tac evaluate_type_ArrayT_cases >>
  imp_res_tac evaluate_type_TupleT_cases >>
  gvs[evaluate_type_def]
  >~ [`vyper_to_abi_base (StringT _) _`]
  >- (Cases_on `v` >> simp[])
  >~ [`vyper_to_abi_base (BytesT _) _`]
  >- (Cases_on `v` >> simp[])
  >~ [`vyper_to_abi _ (ArrayT _ (Dynamic _)) _`]
  >- (drule abi_args_same_conversion_cong >> strip_tac >>
      Cases_on `v` >> simp[] >> rename1 `ArrayV ar` >>
      Cases_on `ar` >> simp[])
  >~ [`vyper_to_abi _ (ArrayT _ (Fixed _)) _`]
  >- (drule abi_args_same_conversion_cong >> strip_tac >>
      `default_to_abi elem_tv' = default_to_abi elem_tv` by
        metis_tac[abi_args_fits_default_encoding] >>
      drule_all abi_args_sparse_conversion_cong >> strip_tac >>
      Cases_on `v` >> simp[] >> rename1 `ArrayV ar` >>
      Cases_on `ar` >> simp[])
  >~ [`vyper_to_abi _ (TupleT _) _`]
  >- (`!vs. vyper_to_abi_list tenv ts vs = vyper_to_abi_list tenv us vs` by
        metis_tac[] >>
      Cases_on `v` >> simp[] >> rename1 `ArrayV ar` >>
      Cases_on `ar` >> simp[]) >>
  `!vs. vyper_to_abi_list tenv ts vs = vyper_to_abi_list tenv us vs` by
    metis_tac[] >>
  Cases_on `vs` >> simp[]
QED

(* The encoder runs at the annotation, but capacity belongs to the physical
   type.  Compatibility is used for representation, never to reverse a bound. *)
Theorem abi_args_physical_encoding_bound:
  arg_type_fits physical source /\
  evaluate_type tenv physical = SOME ptv /\
  evaluate_type tenv source = SOME stv /\
  value_has_type ptv v /\
  vyper_to_abi tenv source v = SOME av /\
  sfields_tenv_consistent sf tenv ==>
  LENGTH (enc (vyper_to_abi_type tenv source) av) <=
    abi_size_bound sf physical
Proof
  strip_tac >>
  `vyper_to_abi tenv physical v = SOME av` by
    metis_tac[abi_args_fits_conversion] >>
  `vyper_to_abi_type tenv source = vyper_to_abi_type tenv physical` by
    metis_tac[abi_args_fits_abi_type] >>
  `abi_size_bound sf physical = vyper_abi_size_bound tenv physical` by
    metis_tac[abi_props_vyper_typed] >>
  metis_tac[vyper_to_abi_enc_le_size_bound]
QED

Theorem abi_args_physical_tuple_encoding_bound:
  arg_types_fit physical source /\
  LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) physical ptvs /\
  LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) source stvs /\
  values_have_types ptvs vs /\
  vyper_to_abi_list tenv source vs = SOME avs /\
  sfields_tenv_consistent sf tenv ==>
  LENGTH (enc (Tuple (vyper_to_abi_types tenv source)) (ListV avs)) <=
    abi_size_bound sf (TupleT physical)
Proof
  strip_tac >>
  `vyper_to_abi_list tenv physical vs = SOME avs` by
    metis_tac[abi_args_fits_conversion] >>
  `vyper_to_abi_types tenv source = vyper_to_abi_types tenv physical` by
    metis_tac[abi_args_fits_abi_type] >>
  `EVERY (\t. IS_SOME (evaluate_type tenv t)) physical` by
    (gvs[LIST_REL_EL_EQN, EVERY_EL] >> metis_tac[optionTheory.IS_SOME_DEF]) >>
  drule_all abi_size_bound_tuple_typed >> strip_tac >>
  metis_tac[vyper_to_abi_enc_le_size_bound]
QED

Theorem abi_args_physical_singleton_capacity:
  arg_type_fits physical source /\
  evaluate_type tenv physical = SOME ptv /\
  evaluate_type tenv source = SOME stv /\
  value_has_type ptv v /\
  evaluate_abi_encode_bytes tenv source v = INL bs /\
  sfields_tenv_consistent sf tenv ==>
  LENGTH (abi_encode_method_id_bytes mid ++ bs) <=
    abi_size_bound sf physical + abi_encode_method_id_size mid
Proof
  simp[evaluate_abi_encode_bytes_def, AllCaseEqs()] >> strip_tac >>
  drule_all abi_args_physical_encoding_bound >> strip_tac >>
  Cases_on `mid` >>
  gvs[abi_encode_method_id_bytes_def, abi_encode_method_id_size_def]
QED

Theorem abi_args_physical_tuple_capacity:
  arg_types_fit physical source /\
  LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) physical ptvs /\
  LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) source stvs /\
  values_have_types ptvs vs /\
  evaluate_abi_encode_bytes tenv (TupleT source) (ArrayV (TupleV vs)) = INL bs /\
  sfields_tenv_consistent sf tenv ==>
  LENGTH (abi_encode_method_id_bytes mid ++ bs) <=
    abi_size_bound sf (TupleT physical) + abi_encode_method_id_size mid
Proof
  simp[evaluate_abi_encode_bytes_def, AllCaseEqs()] >> strip_tac >>
  drule_all abi_args_physical_tuple_encoding_bound >> strip_tac >>
  Cases_on `mid` >>
  gvs[abi_encode_method_id_bytes_def, abi_encode_method_id_size_def]
QED

(* Static ABI shape ignores all permitted bound widening. *)
Theorem abi_args_fits_static_shape:
  (!t u. arg_type_fits t u ==>
     is_abi_dynamic sf t = is_abi_dynamic sf u /\
     abi_static_size sf t = abi_static_size sf u) /\
  (!ts us. arg_types_fit ts us ==>
     EXISTS (is_abi_dynamic sf) ts = EXISTS (is_abi_dynamic sf) us /\
     SUM (MAP (abi_embedded_static_size sf) ts) =
     SUM (MAP (abi_embedded_static_size sf) us))
Proof
  ho_match_mp_tac arg_type_fits_ind >>
  simp[arg_type_fits_def, is_abi_dynamic_def, abi_static_size_def,
       abi_embedded_static_size_def] >> rpt strip_tac >>
  gvs[MAP_MAP_o, combinTheory.o_DEF,
      GSYM abi_embedded_static_size_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Theorem abi_args_embedded_bound_zero[local]:
  abi_embedded_static_size sf t +
    (if is_abi_dynamic sf t then abi_size_bound sf t else 0) = 0 <=>
  abi_embedded_static_size sf t = 0
Proof
  Cases_on `is_abi_dynamic sf t` >> simp[abi_embedded_static_size_def]
QED

Theorem abi_args_fits_zero_bound:
  (!t u. arg_type_fits t u ==>
     (abi_size_bound sf t = 0 <=> abi_size_bound sf u = 0)) /\
  (!ts us. arg_types_fit ts us ==>
     (abi_size_bound sf (TupleT ts) = 0 <=>
      abi_size_bound sf (TupleT us) = 0))
Proof
  ho_match_mp_tac arg_type_fits_ind >>
  simp[arg_type_fits_def, abi_size_bound_def, arithmeticTheory.MULT_EQ_0,
       abi_args_embedded_bound_zero] >> rpt strip_tac >>
  imp_res_tac abi_args_fits_static_shape >>
  gvs[abi_embedded_static_size_def]
QED
