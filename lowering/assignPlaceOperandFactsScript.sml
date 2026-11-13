(* Syntactic operand probes for the assignment frame interface. *)
Theory assignPlaceOperandFacts
Ancestors
  exprReasonOperand exprSimHypsDefs exprLowering compileEnv
  assignPlaceBuiltinOperand assignPlaceTypeBuiltinOperand exprSafeOperandBuiltins
  context vyperAST exprSafeOperand

Theorem assign_place_stack_operand_not_label:
  expr_body_pre cenv cx env e es /\
  compile_expr cenv (expr_type e) e sa = (StackValue rt op,sm) ==>
  !l. op <> Label l
Proof
  strip_tac >>
  `lower_value compile_expr cenv (expr_type e) e sa = (op,sm)` by
    simp[lower_value_def, comp_bind_def, unwrap_value_def, comp_return_def] >>
  irule lower_compile_expr_not_label >>
  goal_assum (drule_at Any) >>
  qexists_tac `env` >>
  gvs[expr_body_pre_def, expr_sim_inv_def]
QED

Theorem assign_place_operand_not_label:
  expr_body_pre cenv cx env e es /\
  compile_expr cenv (expr_type e) e sa = (vv,sm) ==>
  !l. vv_operand vv <> Label l
Proof
  strip_tac >> Cases_on `vv`
  >- (simp[vv_operand_def] >>
      irule assign_place_stack_operand_not_label >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  rename1 `LocatedValue rt p` >> simp[vv_operand_def] >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  pure_once_rewrite_tac [cj 1 compile_expr_raw_def] >>
  Cases_on `e`
  >~ [`Literal ann lit`]
     >- (simp[compile_expr_body_def, expr_type_def] >>
      metis_tac[reason_compile_literal, reason_result_shape_def])
  >~ [`IfExp ann cond a b`]
     >- (metis_tac[reason_compile_ifexp, reason_result_shape_def])
  >~ [`StructLit ann nm fields`]
     >- (metis_tac[reason_compile_structlit, reason_result_shape_def])
  >~ [`Pop ann bt`]
     >- (metis_tac[reason_compile_pop, reason_result_shape_def])
  >~ [`Call ann tgt args dflt`]
     >- (simp[compile_expr_body_def] >>
      metis_tac[reason_compile_call, reason_result_shape_def])
  >~ [`Attribute ann e fld`]
     >- (simp[compile_expr_body_def] >>
      metis_tac[compile_attribute_safe_operand, safe_operand_def, vv_operand_def])
  >~ [`Subscript ann a b`]
     >- (simp[compile_expr_body_def] >>
      metis_tac[compile_subscript_not_label, vv_operand_def])
  >~ [`Name ann id`]
     >- (simp[compile_expr_body_def] >> strip_tac >>
         `?q sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var q) sz)` by
           (gvs[expr_body_pre_def, expr_sim_inv_def,
                vyperTypeSystemTheory.well_typed_expr_def] >> metis_tac[]) >>
         gvs[compile_name_vv_def, comp_return_def, mk_ptr_def])
  >~ [`FlagMember ann nsid mid`]
     >- simp[compile_expr_body_def]
  >~ [`TopLevelName ann nsid`]
     >- (simp[compile_expr_body_def] >>
         rpt strip_tac >> gvs[AllCaseEqs(), mk_ptr_def] >>
         rpt (pairarg_tac >> gvs[]))
  >~ [`Builtin ann bi args`]
     >- (strip_tac >> drule reason_compile_expr_builtin_shape_classify >>
         simp[reason_result_shape_def] >>
         simp[expr_size_def, expr_type_def] >>
         pure_once_rewrite_tac [cj 2 compile_expr_raw_def] >>
         metis_tac[assign_place_builtin_pointer_not_label])
  >> simp[compile_expr_body_def, expr_size_def, expr_type_def] >>
  pure_once_rewrite_tac [cj 3 compile_expr_raw_def] >>
  simp[] >> metis_tac[assign_place_type_builtin_pointer_not_label]
QED
