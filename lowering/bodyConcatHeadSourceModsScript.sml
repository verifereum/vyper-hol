(* Source facts at the successful forced read of a Concat operand. *)
Theory bodyConcatHeadSourceMods
Ancestors
  bodyFullPredsMods bodyWriteSubscriptSourceMods bodyBranchCellFrameMods
  exprBodyPreTypingProps exprSimSource vyperTypeExtCallCore vyperTypeExprSoundness
  vyperInterpreter vyperState vyperContext vyperValue vyperAST exprSimHypsDefs
Libs monadsyntax

Theorem concat_head_read_source_mods:
  body_exprs_full_ok_mods mods exps cx (e::args) /\
  expr_body_pre_mods mods cenv cx env e st /\
  body_const_cells_agree_mods mods cx env st /\
  bind (eval_expr cx e) (read_result cx) (st with gas_obs := obs) = (INL v,mid) ==>
  body_exprs_full_ok_mods mods exps cx args /\
  expr_sim_inv_mods mods cenv cx env mid /\
  body_const_cells_agree_mods mods cx env mid /\
  (?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
        value_has_type tv v)
Proof
  strip_tac >>
  `expr_body_pre_mods mods cenv cx env e (st with gas_obs := obs) /\
   body_const_cells_agree_mods mods cx env (st with gas_obs := obs)` by simp[] >>
  drule_all_then strip_assume_tac write_index_read_source_mods >>
  simp[] >> conj_tac
  >- (drule (REWRITE_RULE [ETA_AX] eval_expr_read_INL) >> strip_tac >>
      qpat_x_assum `body_exprs_full_ok_mods _ _ _ (_::_)` mp_tac >>
      simp[Once body_exprs_full_ok_mods_def] >> strip_tac >>
      qpat_x_assum `_ ==> body_exprs_full_ok_mods mods exps cx args` irule >>
      rpt (goal_assum (drule_at Any))) >>
  drule_then strip_assume_tac expr_body_pre_mods_runtime_typing >>
  drule_then assume_tac runtime_consistent_get_tenv >>
  gvs[value_runtime_typed_def] >> metis_tac[]
QED
