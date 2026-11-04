(* Deferred internal-call argument interface probes. *)
Theory bodyIntCallArgLifetime
Ancestors
  exprSimAggregateChildren exprSimAggregateSource exprLowering compileEnv vyperEvalPureExpr vyperPureExpr supportedExprs supportedExprForms
  exprReasonOperand exprSimHyps exprOperandVar exprSafeOperand context venomState exprSim

Theorem compile_multi_vvs_empty:
  compile_multi_vvs cfn cenv [] st = ([],st)
Proof
  simp[compile_multi_vvs_def, comp_return_def]
QED

Theorem compile_stage_intcall_args_empty:
  compile_stage_intcall_args cenv [] flags tys st = ([],st)
Proof
  simp[compile_stage_intcall_args_def, comp_return_def]
QED

Theorem supported_purity_semantic:
  (!tops e. supported_pure_expr tops e ==> pure_expr e) /\
  (!tops es. supported_pure_exprs tops es ==> EVERY pure_expr es) /\
  (!tops fields. supported_pure_fields tops fields ==>
     EVERY pure_expr (MAP SND fields)) /\
  (!tops e. supported_place_expr tops e ==> pure_expr e)
Proof
  ho_match_mp_tac supported_pure_expr_ind >>
  simp[supported_pure_expr_def, pure_expr_def, SF ETA_ss] >>
  rpt conj_tac >> rpt gen_tac >>
  Cases_on `es` >> simp[supported_builtin_form_def]
QED

Theorem supported_pure_eval_expr_state:
  supported_pure_expr tops e /\ eval_expr cx e es = (res,es') ==>
  es' = es
Proof
  metis_tac[supported_purity_semantic, eval_expr_preserves_state]
QED

(* A compiled operand is already reserved at the next compile boundary.
   The semantic invariant rules out label-valued local pointers. *)
Theorem compile_expr_operand_safe:
  expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
  local_ptrs_reserved cenv sa /\ compile_expr cenv ty e sa = (vv,sb) ==>
  safe_operand sb (vv_operand vv)
Proof
  strip_tac >>
  `!id t. FLOOKUP env.var_types id = SOME t ==>
     ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    gvs[expr_sim_inv_def] >>
  drule_all compile_expr_operand_not_label >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sb x` by
    metis_tac[CONJUNCT1 compiler_compile_var] >>
  Cases_on `vv` >> simp[safe_operand_def, vv_operand_def]
QED

Theorem safe_operand_value_preserved:
  safe_operand sa op /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
         lookup_var x s = SOME w) /\
  eval_operand op s0 = SOME w ==>
  eval_operand op s = SOME w
Proof
  Cases_on `op` >> simp[safe_operand_def, eval_operand_def] >>
  metis_tac[]
QED

Theorem vv_post_preserves_compiled_operand:
  expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
  local_ptrs_reserved cenv sa /\ compile_expr cenv ty e sa = (vv,sm) /\
  vv_post ctx func cenv cx e' es0 sm sb s0 es' tv vv' s /\
  eval_operand (vv_operand vv) s0 = SOME w ==>
  eval_operand (vv_operand vv) s = SOME w
Proof
  strip_tac >> irule safe_operand_value_preserved >>
  qexists_tac `s0` >> qexists_tac `sm` >> simp[] >>
  conj_tac >- gvs[vv_post_def] >>
  irule compile_expr_operand_safe >> metis_tac[]
QED
