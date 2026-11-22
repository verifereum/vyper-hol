(* Static pairing of the scalar operand intervals of create_copy_of. *)
Theory createSizeCopyScalarCode
Ancestors
  gasShadowCompile gasShadowCompileHelpers gasShadowCompileBase gasShadowState gasShadow
  externalEntryShape exprSimSend exprLowering builtinCreate fragExec
  compileEnv emitHelper list option pair

Theorem copy_scalar_shadow_result[local]:
  gas_shadow_compiles f g /\ gas_shadow_state a b /\ f a = (x,a') ==>
  ?b'. g b = (x,b') /\ gas_shadow_state a' b'
Proof
  Cases_on `g b` >> simp[gas_shadow_compiles_def] >>
  strip_tac >> first_x_assum drule >> simp[]
QED

Theorem copy_scalar_code_rows[local]:
  lower_value compile_expr cenv (expr_type target_e) target_e a = (target,a1) /\
  lower_value compile_expr cenv (expr_type value_e) value_e a1 = (value,a2) /\
  compile_create_salt compile_expr cenv salt_e a2 = (salt,a3) /\
  compile_create_copy target value salt rof a3 = (created,b) /\
  fn_has_code a b func ==>
  fn_has_code a a1 func /\ fn_has_code a1 a2 func /\ fn_has_code a2 a3 func
Proof
  strip_tac >>
  `!ce ty e u. cs_extends u (SND (lower_value compile_expr ce ty e u))` by
    simp[lower_value_labels,compile_expr_labels] >>
  `cs_extends a a1 /\ cs_extends a1 a2` by metis_tac[SND] >>
  `cs_extends a2 a3` by
    (mp_tac (Q.SPECL [`compile_expr`,`cenv`,`salt_e`,`a2`] compile_create_salt_labels) >>
     simp[compile_expr_labels]) >>
  `cs_extends a3 b` by metis_tac[compile_create_copy_labels,SND] >>
  `cs_extends a2 b /\ cs_extends a1 b` by metis_tac[cs_extends_trans] >>
  `fn_has_code a a1 func /\ fn_has_code a1 b func` by metis_tac[fn_has_code_split] >>
  `fn_has_code a1 a2 func /\ fn_has_code a2 b func` by metis_tac[fn_has_code_split] >>
  metis_tac[fn_has_code_split]
QED

(* The salt compiler is a scalar row for SOME and an empty interval for NONE. *)
Theorem create_copy_scalar_code:
  has_salt = IS_SOME salt_e /\
  args = target_e::value_e::(case salt_e of NONE => [] | SOME e => [e]) /\
  compile_expr cenv ty (Call ann (CreateTarget CreateCopyOf has_salt rof ks) args d) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Call ann (CreateTarget CreateCopyOf has_salt rof ks) args d))
    shadow_sa = (vv,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ fn_has_code sa sb func /\
  fn_has_code shadow_sa shadow_sb shadow_func /\
  lower_value compile_expr cenv (expr_type target_e) target_e sa = (target,a1) /\
  lower_value compile_expr cenv (expr_type value_e) value_e a1 = (value,a2) /\
  compile_create_salt compile_expr cenv salt_e a2 = (salt,a3) /\
  compile_create_copy target value salt rof a3 = (created,sb) ==>
  ?b1 b2 b3.
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type target_e) (gas_shadow_expr target_e)
      shadow_sa = (target,b1) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type value_e) (gas_shadow_expr value_e)
      b1 = (value,b2) /\
    compile_create_salt compile_expr (gas_shadow_env T cenv) (OPTION_MAP gas_shadow_expr salt_e)
      b2 = (salt,b3) /\
    gas_shadow_state a1 b1 /\ gas_shadow_state a2 b2 /\ gas_shadow_state a3 b3 /\
    fn_has_code sa a1 func /\ fn_has_code a1 a2 func /\ fn_has_code a2 a3 func /\
    fn_has_code shadow_sa b1 shadow_func /\ fn_has_code b1 b2 shadow_func /\
    fn_has_code b2 b3 shadow_func
Proof
  rpt strip_tac >>
  `!ce ty e. gas_shadow_compiles (lower_value compile_expr ce ty e)
      (lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e))` by
    (rpt gen_tac >>
     irule (SRULE [] (Q.INST [`sd` |-> `T`, `sh` |-> `T`] gas_shadow_compiles_lower_value_env)) >>
     simp[cj 1 gas_shadow_compile_expr_env]) >>
  `!ce e. gas_shadow_compiles (compile_create_salt compile_expr ce e)
      (compile_create_salt compile_expr (gas_shadow_env T ce) (OPTION_MAP gas_shadow_expr e))` by
    (rpt gen_tac >>
     irule (SRULE []
       (Q.INST [`sd` |-> `T`, `sh` |-> `T`] gas_shadow_compiles_create_salt)) >>
     simp[cj 1 gas_shadow_compile_expr_env]) >>
  `?b1. lower_value compile_expr (gas_shadow_env T cenv) (expr_type target_e) (gas_shadow_expr target_e)
           shadow_sa = (target,b1) /\ gas_shadow_state a1 b1` by
    (irule copy_scalar_shadow_result >> goal_assum (drule_at Any) >> simp[]) >>
  `?b2. lower_value compile_expr (gas_shadow_env T cenv) (expr_type value_e) (gas_shadow_expr value_e)
           b1 = (value,b2) /\ gas_shadow_state a2 b2` by
    (irule copy_scalar_shadow_result >> goal_assum (drule_at Any) >>
     qexists_tac `lower_value compile_expr cenv (expr_type value_e) value_e` >> simp[]) >>
  `?b3. compile_create_salt compile_expr (gas_shadow_env T cenv) (OPTION_MAP gas_shadow_expr salt_e)
           b2 = (salt,b3) /\ gas_shadow_state a3 b3` by
    (irule copy_scalar_shadow_result >> goal_assum (drule_at Any) >>
     qexists_tac `compile_create_salt compile_expr cenv salt_e` >> simp[]) >>
  `compile_create_copy target value salt rof b3 = (created,shadow_sb)` by
    (qpat_x_assum `compile_expr _ _ (Call _ _ _ _) _ = _` mp_tac >>
     qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
     Cases_on `salt_e` >> gvs[] >>
     simp[gas_shadow_expr_def,exprSimSendTheory.compile_expr_call,compile_call_def,
          compile_create_call_def,comp_bind_def] >>
     Cases_on `compile_create_copy target value salt rof b3` >>
     simp[as_stack_val_def] >> rpt strip_tac >> gvs[]) >>
  drule_all copy_scalar_code_rows >> strip_tac >>
  `fn_has_code shadow_sa b1 shadow_func /\ fn_has_code b1 b2 shadow_func /\
   fn_has_code b2 b3 shadow_func` by
    (irule copy_scalar_code_rows >> rpt (goal_assum (drule_at Any)) >>
     qexistsl_tac [`gas_shadow_expr target_e`,`gas_shadow_expr value_e`] >> simp[]) >>
  qexistsl_tac [`b1`,`b2`,`b3`] >> simp[]
QED
