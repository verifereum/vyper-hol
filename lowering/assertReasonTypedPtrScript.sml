(* Typed reason adapters share one assertion continuation. *)
Theory assertReasonTypedPtr
Ancestors
  stmtAssertReasonPtr reasonDispatchPtr exprSimHypsDefs exprSimDefs
  bodyPtrDefs stmtSimDefs vyperInterpreter vyperState
Libs
  monadsyntax

Theorem compile_assert_typed_reason_frag_ptr:
  expr_type e = BaseT BoolT /\
  expr_sim_ptr d ctx PG fn cenv cx (BaseT BoolT) e es /\
  (!gs es1.
     bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
       (INL (BoolV F),es1) ==>
     expr_body_pre cenv cx env r es1 /\
     expr_vv_sim_ptr d ctx PG fn cenv cx (expr_type r) r es1) ==>
  stmt_frag_ptr d ctx PG fn cx lctx RetQ cenv
    (stmt_env cenv lctx ty (Assert e (AssertReason r)))
    (eval_stmt cx (Assert e (AssertReason r))) es
Proof
  strip_tac >> irule compile_assert_reason_frag_general_ptr >> simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!gs es1. _` (drule_then strip_assume_tac) >>
  Cases_on `?mx str. r = Literal (BaseT (StringT mx)) (StringL str)`
  >- (gvs[] >> irule compile_raise_literal_reason_frag_ptr >>
      goal_assum (drule_at Any)) >>
  irule compile_raise_typed_reason_frag_ptr >> simp[] >>
  conj_tac >- metis_tac[] >> qexists `env` >> simp[]
QED
