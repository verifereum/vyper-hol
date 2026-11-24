(* Qualified Assign evaluates and snapshots the RHS before the target. *)
Theory bodyQualifiedPlaceSnapshotRhsMods
Ancestors
  bodyQualifiedPlaceRhsPostMods gasShadowCompileStmtHelpers gasShadowState
  gasShadowCompileConvert gasShadowCompileBase exprSimUnwrap exprLoweringProps
  exprLowering fragExec loweringHalt context bodyAssignLocalPlaceRoutesMods
  gasShadowCompileStmtBase gasShadowCompileHelpers gasShadow compileEnv

Theorem qualified_place_snapshot_code_mods:
  assign_place_rhs_code_mods ce bt e sa = (saved,sr) /\
  assign_place_rhs_code_mods (gas_shadow_env T ce) (gas_shadow_target bt)
    (gas_shadow_expr e) shadow_sa = (saved,shadow_sr) /\
  ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
  expr_can_mutate ce (target_to_expr bt) /\ gas_shadow_state sa shadow_sa /\
  fn_has_code sa sr func /\ fn_has_code shadow_sa shadow_sr shadow_func ==>
  ?raw vv sm shadow_sm.
    saved = SOME vv /\
    compile_expr ce (expr_type e) e sa = (raw,sm) /\
    compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e)
      shadow_sa = (raw,shadow_sm) /\
    gas_shadow_state sm shadow_sm /\ gas_shadow_state sr shadow_sr /\
    compile_snapshot_vv ce T (vv_with_type (lowered_value_type ce e) raw) sm = (vv,sr) /\
    fn_has_code sa sm func /\ fn_has_code sm sr func /\
    fn_has_code shadow_sa shadow_sm shadow_func /\ fn_has_code shadow_sm shadow_sr shadow_func
Proof
  strip_tac >>
  Cases_on `compile_expr ce (expr_type e) e sa` >> rename1 `_ = (raw,sm)` >>
  Cases_on `compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) shadow_sa` >>
  rename1 `_ = (shadow_raw,shadow_sm)` >>
  `shadow_raw = raw /\ gas_shadow_state sm shadow_sm` by
    (mp_tac (Q.INST [`cenv` |-> `ce`, `sd` |-> `T`, `ty` |-> `expr_type e`]
               gas_shadow_stmt_compile_expr_env) >>
     simp[gas_shadow_compiles_def] >> disch_then drule >> simp[]) >>
  gvs[] >>
  Cases_on `compile_snapshot_vv ce T (vv_with_type (lowered_value_type ce e) raw) sm` >>
  rename1 `_ = (vv,m)` >>
  Cases_on `compile_snapshot_vv ce T (vv_with_type (lowered_value_type ce e) raw) shadow_sm` >>
  rename1 `_ = (shadow_vv,shadow_m)` >>
  `shadow_vv = vv /\ gas_shadow_state m shadow_m` by
    (mp_tac (Q.INST [`cenv` |-> `ce`, `copy_flag` |-> `T`,
                    `vv` |-> `vv_with_type (lowered_value_type ce e) raw`]
               gas_shadow_compiles_snapshot_vv) >>
     simp[gas_shadow_compiles_def] >> disch_then drule >> simp[]) >>
  qpat_x_assum `assign_place_rhs_code_mods ce _ _ _ = _` mp_tac >>
  qpat_x_assum `assign_place_rhs_code_mods (gas_shadow_env _ _) _ _ _ = _` mp_tac >>
  simp[assign_place_rhs_code_mods_def,gas_shadow_is_empty_value_expr,
       gas_shadow_expr_type,gas_shadow_expr_can_mutate,
       comp_bind_def,comp_return_def] >> strip_tac >> strip_tac >> gvs[] >>
  `cs_extends sa sm /\ cs_extends shadow_sa shadow_sm` by
    (conj_tac >> irule (cj 1 compile_expr_extends) >> goal_assum (drule_at Any)) >>
  `cs_extends sm m /\ cs_extends shadow_sm shadow_m` by
    (conj_tac >-
       (qspecl_then [`ce`,`T`,`vv_with_type (lowered_value_type ce e) raw`,`sm`]
          mp_tac ci_mono_compile_snapshot_vv >> simp[ci_mono_def]) >>
     qspecl_then [`ce`,`T`,`vv_with_type (lowered_value_type ce e) raw`,`shadow_sm`]
       mp_tac ci_mono_compile_snapshot_vv >> simp[ci_mono_def]) >>
  `fn_has_code sa sm func /\ fn_has_code sm m func` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code shadow_sa shadow_sm shadow_func /\ fn_has_code shadow_sm shadow_m shadow_func` by
    (irule fn_has_code_split >> simp[]) >>
  simp[]
QED
