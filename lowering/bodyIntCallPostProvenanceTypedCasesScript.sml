(* Result-type exclusions for raw effect-free argument provenance.
   These facts use typing of the current expression, never eligibility of
   its children. Bytes and strings are BaseTVs, not dynamic arrays. *)
Theory bodyIntCallPostProvenanceTypedCases
Ancestors
  exprSimProps vyperTypeSystem vyperTypeConversions vyperValue
  loweringPosts

Theorem evaluate_base_dynarray_free:
  evaluate_type tenv (BaseT bt) = SOME tv ==> dynarray_free tv
Proof
  metis_tac[evaluate_type_BaseT_SOME, dynarray_free_base]
QED

Theorem evaluate_flag_dynarray_free:
  evaluate_type tenv (FlagT fid) = SOME tv ==> dynarray_free tv
Proof
  simp[evaluate_type_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[dynarray_free_def] >> Cases_on `path` >>
  simp[mem_path_offset_def, AllCaseEqs(), optionTheory.OPTION_MAP_EQ_SOME,
       pairTheory.EXISTS_PROD, PULL_EXISTS] >>
  rpt strip_tac >> drule mem_step_offset_shape >> simp[]
QED

Theorem evaluate_fixed_dynarray_free:
  evaluate_type tenv (ArrayT et (Fixed n)) = SOME tv /\
  (!etv. evaluate_type tenv et = SOME etv ==> dynarray_free etv) ==>
  dynarray_free tv
Proof
  simp[Once evaluate_type_def, AllCaseEqs()] >>
  metis_tac[dynarray_free_fixed]
QED

Theorem typed_binop_base_or_flag:
  well_typed_binop ty bop t1 t2 ==>
  (?bt. ty = BaseT bt) \/ (?fid. ty = FlagT fid)
Proof
  Cases_on `bop` >> Cases_on `ty` >>
  simp[well_typed_binop_def] >> rpt strip_tac >> gvs[]
QED

Theorem typed_builtin_result_shape:
  well_typed_builtin_app ty blt ts /\
  (!et bd. blt <> MakeArray et bd) ==>
  (?bt. ty = BaseT bt) \/ (?fid. ty = FlagT fid) \/
  ty = ArrayT (BaseT (UintT 256)) (Fixed 2)
Proof
  Cases_on `blt` >> simp[well_typed_builtin_app_def] >>
  rpt strip_tac >> gvs[]
  >~ [`well_typed_binop ty bop _ _`]
  >- metis_tac[typed_binop_base_or_flag]
  >~ [`is_bool_type ty`]
  >- (Cases_on `ty` >> gvs[])
  >~ [`is_uint256_type ty`]
  >- (Cases_on `ty` >> gvs[])
  >~ [`is_bytes32_type ty`]
  >- (Cases_on `ty` >> gvs[])
  >~ [`is_flag_type ty`]
  >- (Cases_on `ty` >> gvs[])
  >~ [`is_int_type ty`]
  >- (Cases_on `ty` >> gvs[])
  >~ [`env_item_type item`]
  >- (Cases_on `item` >> gvs[env_item_type_def])
  >> rename1 `account_item_type item` >>
  Cases_on `item` >> gvs[account_item_type_def]
QED

Theorem typed_builtin_dynarray_free:
  well_typed_builtin_app ty blt ts /\
  (!et bd. blt <> MakeArray et bd) /\
  evaluate_type tenv ty = SOME tv ==> dynarray_free tv
Proof
  strip_tac >> drule_all typed_builtin_result_shape >> strip_tac >>
  gvs[]
  >- metis_tac[evaluate_base_dynarray_free]
  >- metis_tac[evaluate_flag_dynarray_free]
  >> irule evaluate_fixed_dynarray_free >>
  metis_tac[evaluate_base_dynarray_free]
QED

Theorem conversion_result_base_or_flag:
  valid_conversion src dst ==>
  (?bt. dst = BaseT bt) \/ (?fid. dst = FlagT fid)
Proof
  Cases_on `dst` >> Cases_on `src` >> simp[valid_conversion_def]
QED

Theorem typed_type_builtin_result_shape:
  type_builtin_result_ok tenv tb ty target ts /\
  well_typed_type_builtin_args tb target ts /\ tb <> Empty /\
  (!unwrap. tb <> AbiDecode unwrap) ==>
  (?bt. ty = BaseT bt) \/ (?fid. ty = FlagT fid)
Proof
  Cases_on `tb` >> simp[type_builtin_result_ok_def,
    well_typed_type_builtin_args_def] >> rpt strip_tac >> gvs[]
  >~ [`valid_conversion _ ty`]
  >- metis_tac[conversion_result_base_or_flag]
  >> Cases_on `target` >> gvs[]
QED

Theorem typed_type_builtin_dynarray_free:
  well_typed_expr env (TypeBuiltin ty tb target args) /\
  tb <> Empty /\ (!unwrap. tb <> AbiDecode unwrap) /\
  evaluate_type tenv ty = SOME tv ==> dynarray_free tv
Proof
  simp[Once well_typed_expr_def] >> strip_tac >>
  drule_all typed_type_builtin_result_shape >> strip_tac >> gvs[] >>
  metis_tac[evaluate_base_dynarray_free, evaluate_flag_dynarray_free]
QED

Theorem typed_literal_result_base:
  well_typed_literal ty lit ==> ?bt. ty = BaseT bt
Proof
  Cases_on `ty` >> Cases_on `lit` >> simp[well_typed_literal_def]
QED

Theorem typed_literal_dynarray_free:
  well_typed_expr env (Literal ty lit) /\
  evaluate_type tenv ty = SOME tv ==> dynarray_free tv
Proof
  simp[Once well_typed_expr_def] >>
  metis_tac[typed_literal_result_base, evaluate_base_dynarray_free]
QED

Theorem typed_flag_member_dynarray_free:
  well_typed_expr env (FlagMember ty fid mid) /\
  evaluate_type tenv ty = SOME tv ==> dynarray_free tv
Proof
  simp[Once well_typed_expr_def] >>
  metis_tac[evaluate_flag_dynarray_free]
QED
