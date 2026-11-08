(* ABI conversion is insensitive to argument-bound widening. *)
Theory exprExtRequestAbiFits
Ancestors
  vyperTypeArgFits vyperTypeSystem vyperTyping vyperValue vyperABI
  vyperABIRoundtrip vyperTypeABI vyperTypeValues vyperTypeDefaults
  vyperAssignPreservesType compileEnv abiTypeBoundProps vyperABIValid
  exprExtRequestTyping memoryLocalRhsProps exprSimHypsDefs list pair

Theorem extrequest_fits_abi_type:
  (!t u. arg_type_fits t u ==>
    vyper_to_abi_type tenv t = vyper_to_abi_type tenv u) /\
  (!ts us. arg_types_fit ts us ==>
    vyper_to_abi_types tenv ts = vyper_to_abi_types tenv us)
Proof
  ho_match_mp_tac arg_type_fits_ind >>
  simp[arg_type_fits_def, vyper_base_to_abi_type_def]
QED

Theorem extrequest_abi_sparse_cong[local]:
  (!v. value_has_type tv v ==> vyper_to_abi tenv t v = vyper_to_abi tenv u v) /\
  default_to_abi tv = default_to_abi tu /\ sparse_has_type tv bound sp ==>
  !n. vyper_to_abi_sparse tenv t tv n sp = vyper_to_abi_sparse tenv u tu n sp
Proof
  strip_tac >> Induct >> simp[Once vyper_to_abi_def] >>
  Cases_on `ALOOKUP sp n` >> simp[] >>
  metis_tac[ALOOKUP_sparse_has_type]
QED

Theorem extrequest_abi_same_cong[local]:
  (!v. value_has_type tv v ==> vyper_to_abi tenv t v = vyper_to_abi tenv u v) ==>
  !vs. all_have_type tv vs ==>
    vyper_to_abi_same tenv t vs = vyper_to_abi_same tenv u vs
Proof
  strip_tac >> Induct >> simp[all_have_type_EVERY] >>
  rpt strip_tac >> simp[]
QED

Theorem extrequest_fits_abi_value:
  (!t u tv tu v.
    arg_type_fits t u /\ evaluate_type tenv t = SOME tv /\
    evaluate_type tenv u = SOME tu /\ value_has_type tv v ==>
    vyper_to_abi tenv t v = vyper_to_abi tenv u v) /\
  (!ts us tvs tus vs.
    arg_types_fit ts us /\
    LIST_REL (\t tv. evaluate_type tenv t = SOME tv) ts tvs /\
    LIST_REL (\t tv. evaluate_type tenv t = SOME tv) us tus /\
    values_have_types tvs vs ==>
    vyper_to_abi_list tenv ts vs = vyper_to_abi_list tenv us vs)
Proof
  ho_match_mp_tac arg_type_fits_ind >> rw[arg_type_fits_def] >>
  imp_res_tac evaluate_type_ArrayT_cases >>
  imp_res_tac evaluate_type_TupleT_cases >>
  gvs[evaluate_type_def]
  >~ [`values_have_types (_::_) _`]
  >- (Cases_on `vs` >> gvs[value_has_type_def] >> metis_tac[])
  >~ [`value_has_type (TupleTV _) _`]
  >- (Cases_on `v` >> gvs[value_has_type_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
      metis_tac[])
  >~ [`value_has_type (ArrayTV _ (Fixed _)) _`]
  >- (Cases_on `v` >> gvs[value_has_type_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
      `default_to_abi elem_tv' = default_to_abi elem_tv` by
        (`value_has_type elem_tv' (default_value elem_tv')` by
           metis_tac[default_value_has_type_thm] >>
         drule_all (cj 1 arg_type_fits_default_value) >> strip_tac >>
         first_x_assum (qspec_then `default_value elem_tv'` mp_tac) >>
         simp[vyper_to_abi_default_value]) >>
      drule_all extrequest_abi_sparse_cong >> simp[])
  >~ [`value_has_type (ArrayTV _ (Dynamic _)) _`]
  >- (Cases_on `v` >> gvs[value_has_type_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
      drule extrequest_abi_same_cong >> disch_then drule >> simp[])
  >> Cases_on `v` >> gvs[value_has_type_def]
QED

Theorem extrequest_bytestring_abi:
  is_bytestring_type t /\ is_bytestring_type u /\
  evaluate_type tenv t = SOME tv /\ evaluate_type tenv u = SOME tu /\
  value_has_type tv v /\ value_has_type tu v ==>
  vyper_to_abi_type tenv t = vyper_to_abi_type tenv u /\
  vyper_to_abi tenv t v = vyper_to_abi tenv u v
Proof
  Cases_on `t` >> Cases_on `u` >>
  simp[is_bytestring_type_def] >>
  rename1 `is_bytestring_type (BaseT bt)` >>
  Cases_on `bt` >> simp[is_bytestring_type_def] >>
  rename1 `is_bytestring_type (BaseT other)` >>
  Cases_on `other` >> simp[is_bytestring_type_def] >>
  rpt strip_tac >>
  gvs[is_bytestring_type_def, AllCaseEqs()] >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >> gvs[value_has_type_def, is_bytestring_type_def]
QED


Theorem extrequest_tuple_abi_capacity:
  sfields_tenv_consistent sf tenv /\
  evaluate_type tenv (TupleT ts) = SOME tv /\ value_has_type tv v ==>
  ?av. vyper_to_abi tenv (TupleT ts) v = SOME av /\
    LENGTH (enc (vyper_to_abi_type tenv (TupleT ts)) av) <=
      abi_size_bound sf (TupleT ts)
Proof
  strip_tac >>
  `EVERY (\t. IS_SOME (evaluate_type tenv t)) ts` by
    (drule evaluate_type_TupleT_cases >> strip_tac >>
     fs[LIST_REL_EL_EQN, EVERY_EL] >> metis_tac[optionTheory.IS_SOME_DEF]) >>
  drule_all abi_size_bound_tuple_typed >> strip_tac >>
  drule_all (cj 1 vyper_to_abi_total) >> strip_tac >>
  qexists_tac `av` >> simp[] >>
  drule_all (cj 1 vyper_to_abi_enc_le_size_bound) >> simp[]
QED

Theorem extrequest_operand_abi_fits:
  expr_sim_inv cenv cx env es /\ tenv = get_tenv cx /\
  well_typed_expr env e /\ ~expr_has_effect e /\
  value_runtime_typed env (expr_type e) v /\
  value_runtime_typed env (lowered_value_type cenv e) v /\
  arg_type_fits (expr_type e) u /\ assignable_type tenv u ==>
  vyper_to_abi_type tenv (lowered_value_type cenv e) = vyper_to_abi_type tenv u /\
  vyper_to_abi tenv (lowered_value_type cenv e) v = vyper_to_abi tenv u v
Proof
  strip_tac >>
  `?tv. evaluate_type tenv (expr_type e) = SOME tv /\ value_has_type tv v` by
    metis_tac[memory_rhs_runtime_layout] >>
  `?lv. evaluate_type tenv (lowered_value_type cenv e) = SOME lv /\ value_has_type lv v` by
    metis_tac[memory_rhs_runtime_layout] >>
  `?uv. evaluate_type tenv u = SOME uv` by
    (drule assignable_type_well_formed >>
     simp[well_formed_type_def, optionTheory.IS_SOME_EXISTS]) >>
  `vyper_to_abi_type tenv (expr_type e) = vyper_to_abi_type tenv u /\
   vyper_to_abi tenv (expr_type e) v = vyper_to_abi tenv u v` by
    metis_tac[extrequest_fits_abi_type, extrequest_fits_abi_value] >>
  drule_all extrequest_lowered_type_compatible >> strip_tac >> simp[] >>
  metis_tac[extrequest_bytestring_abi]
QED

Theorem extrequest_operands_abi_fits:
  !xs ats vs.
  expr_sim_inv cenv cx env es /\ tenv = get_tenv cx /\
  EVERY (well_typed_expr env) xs /\ EVERY (\e. ~expr_has_effect e) xs /\
  LIST_REL (\e v. value_runtime_typed env (expr_type e) v /\
    value_runtime_typed env (lowered_value_type cenv e) v) xs vs /\
  arg_types_fit (MAP expr_type xs) ats /\ EVERY (assignable_type tenv) ats ==>
  vyper_to_abi_types tenv (MAP (lowered_value_type cenv) xs) =
    vyper_to_abi_types tenv ats /\
  vyper_to_abi_list tenv (MAP (lowered_value_type cenv) xs) vs =
    vyper_to_abi_list tenv ats vs
Proof
  Induct >> Cases_on `ats` >> Cases_on `vs` >> simp[arg_type_fits_def] >>
  rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >> simp[] >>
  `vyper_to_abi_type tenv (lowered_value_type cenv h'') = vyper_to_abi_type tenv h /\
   vyper_to_abi tenv (lowered_value_type cenv h'') h' = vyper_to_abi tenv h h'` by
    (irule extrequest_operand_abi_fits >> metis_tac[]) >> gvs[]
QED

Theorem extrequest_positional_calldata:
  expr_sim_inv cenv cx env es /\
  EVERY (well_typed_expr env) xs /\ EVERY (\e. ~expr_has_effect e) xs /\
  LIST_REL (\e v. value_runtime_typed env (expr_type e) v /\
    value_runtime_typed env (lowered_value_type cenv e) v) xs vs /\
  arg_types_fit (MAP expr_type xs) ats /\
  EVERY (assignable_type (get_tenv cx)) ats /\
  evaluate_type (get_tenv cx) (TupleT (MAP (lowered_value_type cenv) xs)) = SOME tv /\
  value_has_type tv (ArrayV (TupleV vs)) ==>
  ?av.
    vyper_to_abi (get_tenv cx) (TupleT (MAP (lowered_value_type cenv) xs))
      (ArrayV (TupleV vs)) = SOME av /\
    LENGTH (enc (vyper_to_abi_type (get_tenv cx)
      (TupleT (MAP (lowered_value_type cenv) xs))) av) <=
      abi_size_bound cenv.ce_struct_fields (TupleT (MAP (lowered_value_type cenv) xs)) /\
    build_ext_calldata (get_tenv cx) fname ats vs =
      SOME (function_selector fname (vyper_to_abi_types (get_tenv cx) ats) ++
        enc (vyper_to_abi_type (get_tenv cx)
          (TupleT (MAP (lowered_value_type cenv) xs))) av)
Proof
  strip_tac >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx)` by
    fs[expr_sim_inv_def] >>
  drule_all extrequest_tuple_abi_capacity >> strip_tac >>
  `vyper_to_abi_types (get_tenv cx) (MAP (lowered_value_type cenv) xs) =
     vyper_to_abi_types (get_tenv cx) ats /\
   vyper_to_abi_list (get_tenv cx) (MAP (lowered_value_type cenv) xs) vs =
     vyper_to_abi_list (get_tenv cx) ats vs` by
    (irule extrequest_operands_abi_fits >> metis_tac[]) >>
  `LENGTH ats = LENGTH vs` by
    (drule arg_types_fit_LENGTH >> simp[] >>
     metis_tac[LIST_REL_LENGTH]) >>
  qexists_tac `av` >> simp[] >>
  gvs[build_ext_calldata_def, AllCaseEqs()] >>
  qpat_x_assum `LENGTH ats = LENGTH vs`
    (fn th => rewrite_tac[GSYM th, TAKE_LENGTH_ID]) >>
  simp[]
QED
