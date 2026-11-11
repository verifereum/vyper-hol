Theory bodyPtrTypeBuiltinsIndexEntry
Ancestors
  exprSimExtract32Source bodyPtrPreds exprSimSource exprSimHypsDefs allocLimits vyperTypeSystem
  vyperTypeCallStackSoundness vyperInterpreter vyperTypeCallGraph
  supportedExprTraverse vyperState list

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
     simp[] >> qexistsl_tac [`ann`,`[src;idx]`,`tb`,`es`,`typ`] >> simp[]) >>
  gvs[body_expr_ptr_ok_def] >> metis_tac[]
QED
