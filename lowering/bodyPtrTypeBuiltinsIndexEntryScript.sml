Theory bodyPtrTypeBuiltinsIndexEntry
Ancestors
  bodyPtrPreds exprSimSource exprSimHypsDefs allocLimits vyperTypeSystem
  vyperTypeCallStackSoundness vyperInterpreter vyperTypeCallGraph
  supportedExprTraverse vyperState list

Theorem expr_body_pre_type_builtin_arg:
  !cenv cx env ann tb ty args e es es'.
    expr_body_pre cenv cx env (TypeBuiltin ann tb ty args) es /\ MEM e args /\
    expr_sim_inv cenv cx env es' ==>
    expr_body_pre cenv cx env e es'
Proof
  rpt gen_tac >> strip_tac >>
  `alloc_limits_expr cenv e` by
    (irule alloc_limits_exprs_mem >>
     gvs[expr_body_pre_def, alloc_limits_expr_def] >> metis_tac[]) >>
  gvs[expr_body_pre_def, well_typed_expr_def, int_calls_expr_def,
      byte_widths_expr_def, supported_expr_exists_def,
      supported_exprs_exists_every, EXISTS_MEM] >>
  imp_res_tac int_calls_exprs_every_mem >>
  gvs[expr_has_evm_run_thm, listTheory.EXISTS_MEM] >>
  metis_tac[well_typed_exprs_member, byte_widths_exprs_mem,
            call_evaluation_safe_exprs_mem]
QED

Theorem body_exprs_ptr_ok_second:
  !cx src idx es v es'.
    body_exprs_ptr_ok cx [src;idx] /\
    bind (eval_expr cx src) (read_result cx) es = (INL v,es') ==>
    body_expr_ptr_ok cx idx
Proof
  simp[body_exprs_ptr_ok_def, bind_def] >>
  rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem type_builtin_second_expr_sim_ptr:
  !cx src idx es v es' cenv env ann tb typ d PG tops ctx func ty.
    body_exprs_ptr_ok cx [src;idx] /\
    bind (eval_expr cx src) (read_result cx) es = (INL v,es') /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (TypeBuiltin ann tb typ [src;idx]) es /\
    expr_sim_inv cenv cx env es' ==>
    expr_sim_ptr d ctx PG func cenv cx ty idx es'
Proof
  rpt gen_tac >> strip_tac >>
  `body_expr_ptr_ok cx idx` by
    (drule_all body_exprs_ptr_ok_second >> simp[]) >>
  `expr_body_pre cenv cx env idx es'` by
    (irule expr_body_pre_type_builtin_arg >>
     simp[] >> qexistsl_tac [`ann`,`[src;idx]`,`es`,`tb`,`typ`] >> simp[]) >>
  gvs[body_expr_ptr_ok_def] >> metis_tac[]
QED
