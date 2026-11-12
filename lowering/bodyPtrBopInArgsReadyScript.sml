Theory bodyPtrBopInArgsReady
Ancestors
  typedWordArgsReadyPtr gasOutcomeMarkedPtr gasSummaryComposePtr
  fragGasSeqPtr exprSimPrecompiles exprSimDefs exprSimWordArgs gasContext vyperState list

Theorem membership_args_head_admissible:
  (!e es. MEM e args /\ Inv es ==>
    is_word_type (expr_type e) /\
    IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\
    (!rr ee. (do r <- eval_expr cx e; read_result cx r od) es = (rr,ee) ==>
      expr_res_ok rr) /\
    (!v ee. (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) ==>
      Inv ee)) /\
  MEM e args /\ Inv es /\
  (!es gs. Inv es ==> Inv (es with gas_obs := gs)) ==>
  gas_admissible (do r <- eval_expr cx e; read_result cx r od) expr_res_ok es
Proof
  rewrite_tac[gas_admissible_def] >> rpt strip_tac >> metis_tac[]
QED

Theorem membership_args_head_marked_facts:
  (!e es. MEM e (e0::args) /\ Inv es ==>
    is_word_type (expr_type e) /\
    IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\
    (!rr ee. (do r <- eval_expr cx e; read_result cx r od) es = (rr,ee) ==>
      expr_res_ok rr) /\
    (!v ee. (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) ==>
      Inv ee)) /\ Inv es /\
  (!es gs. Inv es ==> Inv (es with gas_obs := gs)) /\
  gas_marked_exec_ptr D (ctx,func) PG
    (do r <- eval_expr cx e0; read_result cx r od)
    (es,s0,G0,tn0) marks (INL v) mid G tn (OK t) /\
  ptr_args_ready d ctx PG func cenv cx arg_ty Inv (e0::args) ==>
  ~t.vs_halted /\ Inv (mid with gas_obs := []) /\
  ptr_args_ready d ctx PG func cenv cx arg_ty Inv args /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes
Proof
  strip_tac >>
  `~t.vs_halted` by
    (fs[gas_marked_exec_ptr_def] >>
     metis_tac[gas_path_ptr_ok_not_halted]) >>
  `Inv (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    metis_tac[] >>
  `((do r <- eval_expr cx e0; read_result cx r od)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
      (INL v,mid with gas_obs := []))` by
    (fs[gas_marked_exec_ptr_def] >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (drule forced_eval_expr_preserves_scopes_dom >> simp[]) >>
  drule_all ptr_args_ready_tail >> simp[] >> metis_tac[MEM]
QED

Theorem membership_args_head_outcome_facts:
  (!e es. MEM e (e0::args) /\ Inv es ==>
    is_word_type (expr_type e) /\
    IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\
    (!rr ee. (do r <- eval_expr cx e; read_result cx r od) es = (rr,ee) ==>
      expr_res_ok rr) /\
    (!v ee. (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) ==>
      Inv ee)) /\ Inv es /\
  (!es gs. Inv es ==> Inv (es with gas_obs := gs)) /\
  ptr_args_ready d ctx PG func cenv cx arg_ty Inv (e0::args) /\
  gas_outcome_ptr D tops (ctx,func) PG
    (do r <- eval_expr cx e0; read_result cx r od) (es,s0,G0,tn0) Q R ==>
  gas_outcome_ptr D tops (ctx,func) PG
    (do r <- eval_expr cx e0; read_result cx r od) (es,s0,G0,tn0)
    (\rr ee G tn t. Q rr ee G tn t /\ ~t.vs_halted /\
      (!v. rr = INL v ==>
        Inv ee /\ ptr_args_ready d ctx PG func cenv cx arg_ty Inv args /\
        MAP FDOM es.scopes = MAP FDOM ee.scopes)) R
Proof
  strip_tac >> irule gas_outcome_ptr_marked_conseq >>
  qexists_tac `Q` >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >> simp[] >> conj_tac
  >- (fs[gas_marked_exec_ptr_def] >> metis_tac[gas_path_ptr_ok_not_halted]) >>
  rpt strip_tac >> gvs[] >>
  drule_all (membership_args_head_marked_facts |> SIMP_RULE (srw_ss()) [MEM]) >> simp[]
QED
