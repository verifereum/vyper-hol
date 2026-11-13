Theory bodyPtrBopInLiteralReady
Ancestors exprSimBopInLiteralWord bodyPtrBopInLiteralSource typedWordArgsReadyPtr bodyPtrPreds
  bodySim exprSimHypsDefs exprSimDefs exprSimPrecompiles list

Theorem literal_ptr_args_ready:
  expr_body_pre cenv cx env
    (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems]) es /\
  body_exprs_ptr_ok cx (e1::elems) /\ body_inv tops ctx cenv cx ==>
  ptr_args_ready d ctx PG func cenv cx expr_type
    (expr_sim_inv cenv cx env) (e1::elems)
Proof
  strip_tac >> irule body_exprs_ptr_ok_ready >>
  goal_assum (drule_at Any) >> simp[] >> conj_tac
  >- (qexists_tac `env` >> rpt strip_tac >>
      drule literal_body_operand_pre >> disch_then irule >> simp[]) >>
  qexists_tac `tops` >> simp[]
QED

Theorem literal_semantic_args_ready:
  expr_body_pre cenv cx env
    (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems]) es /\
  (bop = In \/ bop = NotIn) /\ is_word_type (expr_type e1) ==>
  (!e es0. MEM e (e1::elems) /\ expr_sim_inv cenv cx env es0 ==>
    is_word_type (expr_type e) /\
    IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\
    (!rr ee. (do r <- eval_expr cx e; read_result cx r od) es0 = (rr,ee) ==>
      expr_res_ok rr) /\
    (!v ee. (do r <- eval_expr cx e; read_result cx r od) es0 = (INL v,ee) ==>
      expr_sim_inv cenv cx env ee))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `expr_type e = expr_type e1 /\ is_word_type (expr_type e)` by
    metis_tac[literal_operand_word_type] >>
  drule literal_body_evaluate_types >> simp[] >> strip_tac >> simp[] >>
  conj_tac >> rpt strip_tac >> metis_tac[literal_operand_result]
QED
