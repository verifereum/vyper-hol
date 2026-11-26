(* The reached state supplies the dynamic invariant; the Create call
   supplies the static conditions of its operand. *)
Theory bodyCreateOperandPreMods
Ancestors
  exprSimHypsDefs exprSimSource allocLimits supportedExprTraverse
  vyperTypeSystem vyperTypeCallGraph vyperTypeCallStackSoundness vyperAST list

Theorem create_operand_pre_mods:
  expr_body_pre_mods mods cenv cx env
    (Call ann (CreateTarget kind salted rof ks) args dflt) es /\
  MEM e args /\ expr_sim_inv_mods mods cenv cx env ee ==>
  expr_body_pre_mods mods cenv cx env e ee
Proof
  simp[expr_body_pre_mods_def, Once well_typed_expr_def, int_calls_expr_def,
       byte_widths_expr_def, alloc_limits_expr_def, supported_expr_exists_def,
       supported_exprs_exists_every, expr_has_evm_run_thm, EXISTS_MEM] >>
  strip_tac >>
  drule_all_then assume_tac well_typed_exprs_member >>
  drule_all_then assume_tac byte_widths_exprs_mem >>
  drule_all_then assume_tac alloc_limits_exprs_mem >>
  drule_all_then assume_tac call_evaluation_safe_exprs_mem >>
  drule_all_then assume_tac int_calls_exprs_every_mem >>
  simp[] >> metis_tac[]
QED
