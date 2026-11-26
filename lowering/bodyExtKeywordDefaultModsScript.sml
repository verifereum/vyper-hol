(* The owned, nonword default-return keyword of a linked external call. *)
Theory bodyExtKeywordDefaultMods
Ancestors
  exprLowering exprLoweringProps stmtLoweringMono fragExec compileEnv
  gasShadowState gasShadowCompilePure gasShadowCompileStmtHelpers
  bodyFullPostsMods loweringPosts bodyMemSnapshotSourceLocation abiEncodeMaterialize
  context valueCopyBytes

Theorem ext_kw_default_retag[local]:
  compile_expr ce ty e sa = (vv,sm) /\
  vv_holds_mods ce cx (post_value_type ce e) pv vv ee s /\
  ~is_word_type (expr_type e) /\
  arg_type_fits (lowered_value_type ce e) (expr_type e) ==>
  compile_materialize_vv ce (lowered_value_type ce e)
    (ext_call_arg_value (lowered_value_type ce e) vv) =
  compile_materialize_vv ce (lowered_value_type ce e) vv
Proof
  strip_tac >>
  `post_value_type ce e = lowered_value_type ce e \/
   is_bytestring_type (post_value_type ce e) /\
   is_bytestring_type (lowered_value_type ce e)` by
    simp[materialize_post_lowered_classify] >>
  `post_value_type ce e <> lowered_value_type ce e ==>
   vv_location vv = NONE \/ vv_location vv = SOME LocMemory` by
    metis_tac[snapshot_changed_type_location] >>
  `unwrap_value ce (ext_call_arg_value (lowered_value_type ce e) vv) =
   unwrap_value ce vv` suffices_by simp[compile_materialize_vv_def] >>
  Cases_on `vv` >> simp[ext_call_arg_value_def] >>
  gvs[vv_holds_mods_def, vv_holds_def, vv_location_def] >>
  Cases_on `p.ptr_location = LocCode` >> gvs[] >>
  Cases_on `p.ptr_location = LocMemory` >>
  gvs[unwrap_value_def, is_bytestring_word_type]
QED
Theorem ext_kw_default_code_split[local]:
  compile_expr ce ty e sa = (vv,sm) /\
  compile_materialize_vv ce' dt vv sm = (op,sb) /\
  fn_has_code sa sb func ==>
  fn_has_code sa sm func /\ fn_has_code sm sb func
Proof
  strip_tac >> irule fn_has_code_split >> simp[] >>
  conj_tac
  >- (qspecl_then [`ce`,`ty`,`e`,`sa`] mp_tac (cj 1 ci_mono_compile_expr_sa) >>
      simp[ci_mono_def]) >>
  qspecl_then [`ce'`,`dt`,`vv`,`sm`] mp_tac ci_mono_compile_materialize_vv >>
  simp[ci_mono_def]
QED

Theorem ext_kw_default_compile_cut[local]:
  ~is_word_type rt /\
  compile_ext_call_kwarg compile_expr cenv rt EKDefault e sa = ((op,dt),sb) /\
  compile_ext_call_kwarg compile_expr (gas_shadow_env T cenv) rt EKDefault
    (gas_shadow_expr e) shadow_sa = ((op,dt),shadow_sb) /\
  gas_shadow_state sa shadow_sa /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func ==>
  ?vv sm shadow_sm.
    dt = lowered_value_type cenv e /\
    compile_expr cenv (expr_type e) e sa = (vv,sm) /\
    compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e)
      shadow_sa = (vv,shadow_sm) /\
    compile_materialize_vv cenv dt vv sm = (op,sb) /\
    compile_materialize_vv cenv dt vv shadow_sm = (op,shadow_sb) /\
    gas_shadow_state sm shadow_sm /\
    fn_has_code sa sm func /\ fn_has_code sm sb func /\
    fn_has_code shadow_sa shadow_sm shadow_func /\
    fn_has_code shadow_sm shadow_sb shadow_func
Proof
  strip_tac >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >>
  rename1 `compile_expr cenv (expr_type e) e sa = (vv,sm)` >>
  Cases_on `compile_expr (gas_shadow_env T cenv) (expr_type e)
    (gas_shadow_expr e) shadow_sa` >>
  rename1 `compile_expr _ _ (gas_shadow_expr e) shadow_sa = (sv,shadow_sm)` >>
  `sv = vv /\ gas_shadow_state sm shadow_sm` by
    (`gas_shadow_compiles (compile_expr cenv (expr_type e) e)
        (compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e))` by
       irule gas_shadow_stmt_compile_expr_env >>
     qpat_x_assum `gas_shadow_compiles _ _`
       (qspecl_then [`sa`,`shadow_sa`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
     simp[]) >>
  gvs[] >>
  rename1 `compile_expr cenv (expr_type e) e sa = (child,sm)` >>
  Cases_on `compile_materialize_vv cenv (lowered_value_type cenv e) child sm` >>
  Cases_on `compile_materialize_vv cenv (lowered_value_type cenv e) child shadow_sm` >>
  gvs[compile_ext_call_kwarg_def,comp_bind_def,comp_return_def] >>
  metis_tac[ext_kw_default_code_split]
QED
