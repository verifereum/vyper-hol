(* Supported storage assignment does not invoke recursive layout normalization. *)
Theory assignBasePtrStorageTypes
Ancestors bodySim exprSimHypsDefs exprSimHyps memoryLocalRhsProps supportedTypes supportedExprs
  exprLowering compileEnv vyperTypeSystem vyperTypeArgFits vyperTyping
  vyperAST vyperInterpreter list finite_map stmtLowering context

Theorem assign_base_storage_scalar_fit_equal[local]:
  !tops fuel t u.
    supported_scalar_type t /\
    supported_nested_type supported_full_word_type fuel tops u /\
    arg_type_fits t u ==> t = u
Proof
  Cases_on `t` >>
  simp[supported_scalar_type_def, supported_word_type_def, supported_string_type_def] >>
  rename1 `supported_word_type (BaseT bt)` >> Cases_on `u` >>
  simp[arg_type_fits_def] >> rename1 `arg_type_fits _ (BaseT ub)` >>
  Cases_on `bt` >> Cases_on `ub` >>
  simp[supported_word_type_def, supported_string_type_def,
       arg_type_fits_def, Once supported_nested_type_def, supported_full_word_type_def] >>
  rpt strip_tac >> gvs[] >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd`) >>
  gvs[arg_type_fits_def, supported_word_type_def, supported_string_type_def]
QED

Theorem assign_base_storage_scalars_fit_equal[local]:
  !ts us tops fuel.
    EVERY supported_scalar_type ts /\
    EVERY (supported_nested_type supported_full_word_type fuel tops) us /\
    arg_types_fit ts us ==> ts = us
Proof
  Induct >> Cases_on `us` >> simp[arg_type_fits_def] >>
  rpt strip_tac >> drule_all assign_base_storage_scalar_fit_equal >> strip_tac >>
  gvs[] >> first_x_assum irule >> metis_tac[]
QED

Theorem assign_base_storage_value_fit_equal[local]:
  !tops t u.
    supported_value_type tops t /\ supported_storage_type tops u /\
    (!et n. u <> ArrayT et (Dynamic n)) /\ arg_type_fits t u ==> t = u
Proof
  rpt gen_tac >> strip_tac >> Cases_on `supported_scalar_type t`
  >- metis_tac[assign_base_storage_scalar_fit_equal, supported_storage_type_def] >>
  Cases_on `t` >> gvs[supported_value_type_def] >> Cases_on `u` >> gvs[arg_type_fits_def]
  >~ [`arg_types_fit ts us`]
  >- (gvs[supported_storage_type_def, Once supported_nested_type_def,
          supported_full_word_type_def] >> metis_tac[assign_base_storage_scalars_fit_equal]) >>
  Cases_on `b` >> Cases_on `b'` >> gvs[arg_type_fits_def] >>
  fs[supported_storage_type_def] >>
  qpat_x_assum `supported_nested_type _ _ _ _` mp_tac >>
  simp[Once supported_nested_type_def, supported_full_word_type_def] >>
  strip_tac >> metis_tac[assign_base_storage_scalar_fit_equal, supported_scalar_type_def]
QED

Theorem assign_base_storage_not_bytestring:
  !tops t. supported_storage_type tops t ==> ~is_bytestring_type t
Proof
  Cases_on `t` >> simp[is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_bytestring_type_def] >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd`) >>
  simp[is_bytestring_type_def, supported_storage_type_def,
       Once supported_nested_type_def, supported_full_word_type_def]
QED

Theorem assign_base_storage_rhs_lowered_type:
  !cenv e tops ctx cx env es.
    body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
    expr_body_pre cenv cx env e es /\ supported_expr tops e /\
    supported_storage_type tops (expr_type e) /\
    (!elem n. expr_type e <> ArrayT elem (Dynamic n)) ==>
    lowered_value_type cenv e = expr_type e
Proof
  ho_match_mp_tac lowered_value_type_ind >> rpt conj_tac
  >- (simp[expr_type_def] >>
      metis_tac[assign_base_storage_not_bytestring, is_bytestring_type_def])
  >- (simp[expr_type_def] >>
      metis_tac[assign_base_storage_not_bytestring, is_bytestring_type_def])
  >- (rpt gen_tac >> strip_tac >>
      `~is_bytestring_type ty` by metis_tac[assign_base_storage_not_bytestring, expr_type_def] >>
      gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def,
         expr_type_def, is_bytestring_type_def])
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
      simp[expr_body_pre_def, well_typed_expr_def,
           type_builtin_result_ok_def, expr_type_def] >> strip_tac >>
      gvs[expr_type_def] >> drule assign_base_storage_not_bytestring >>
      simp[is_bytestring_type_def])
  >- suspend "internal_call" >>
  simp[lowered_value_type_def]
QED

Resume assign_base_storage_rhs_lowered_type[internal_call]:
  rpt gen_tac >> strip_tac >>
  rename1 `expr_body_pre cenv cx env (Call ann (IntCall func_id) args kw) es` >>
  `supported_program tops /\
   cenv.ce_func_return_type = build_func_return_type tops /\
   get_module_code cx NONE = SOME tops` by fs[body_inv_def] >>
  `well_typed_expr env (Call ann (IntCall func_id) args kw)` by gvs[expr_body_pre_def] >>
  qpat_x_assum `supported_expr _ _` mp_tac >>
  simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def] >> strip_tac >>
  Cases_on `kw` >> gvs[supported_effect_expr_def, optionTheory.IS_SOME_EXISTS] >>
  PairCases_on `x` >>
  `?sig. FLOOKUP env.fn_sigs func_id = SOME sig` by
    (Cases_on `func_id` >> gvs[well_typed_expr_def, optionTheory.IS_SOME_EXISTS]) >>
  drule_all supported_internal_signature_return >> strip_tac >>
  drule_all supported_internal_return_admissible >> strip_tac >>
  drule_all supported_internal_return_type >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _` mp_tac >> Cases_on `func_id` >>
  simp[well_typed_expr_def, expr_type_def] >> strip_tac >>
  gvs[lowered_value_type_def, expr_type_def] >>
  gvs[supported_return_type_def, type_widens_to_def]
  >- (Cases_on `ann` >> gvs[arg_type_fits_def]) >>
  metis_tac[assign_base_storage_value_fit_equal]
QED

Finalise assign_base_storage_rhs_lowered_type

(* The actual supported bulk-storage continuation reads its RHS directly. *)
Theorem assign_base_storage_copy_dispatch:
  !cenv e tops ctx cx env es dst src tr loc.
    body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
    expr_body_pre cenv cx env e es /\ supported_expr tops e /\
    supported_storage_type tops (expr_type e) /\ ~is_word_type (expr_type e) /\
    (!elem n. expr_type e <> ArrayT elem (Dynamic n)) ==>
    compile_assign_value cenv dst (if tr then LocTransient else LocStorage)
      src F loc (expr_type e) (lowered_value_type cenv e) NONE
      (type_memory_bytes cenv (expr_type e)) =
    (if type_memory_bytes cenv (expr_type e) <= 32 then
       do loaded <- emit_op MLOAD [src];
          emit_void (if tr then TSTORE else SSTORE) [dst;loaded]
       od
     else
       do (if tr then compile_memory_to_transient src dst
                        (type_memory_bytes cenv (expr_type e) DIV 32)
           else compile_memory_to_storage src dst
                        (type_memory_bytes cenv (expr_type e) DIV 32));
          return ()
       od)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all assign_base_storage_rhs_lowered_type >> strip_tac >>
  drule assign_base_storage_not_bytestring >> strip_tac >>
  Cases_on `tr` >>
  simp[FUN_EQ_THM, compile_assign_value_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def]
QED
