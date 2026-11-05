Theory typedWordArgsSimPtr
Ancestors
  typedWordArgsReadyPtr typedWordArgsPostPtr exprSimPrecompiles
  exprSimWordArgs gasSummaryComposePtr gasContext exprSimDefs
  fragExec bodyPtrDefs exprLoweringProps list gasOutcomeMarkedPtr

Theorem typed_args_ptr_head_admissible:
  typed_args_ready ctx func cenv cx arg_ty Inv (e::args) /\ Inv es /\
  (!es gs. Inv es ==> Inv (es with gas_obs := gs)) ==>
  gas_admissible (do r <- eval_expr cx e; read_result cx r od) expr_res_ok es
Proof
  rewrite_tac[gas_admissible_def] >> rpt strip_tac >>
  `Inv (es with gas_obs := gs)` by metis_tac[] >>
  drule_all typed_args_ready_head >> metis_tac[]
QED

Theorem typed_args_ptr_head_marked_facts:
  typed_args_ready ctx func cenv cx arg_ty Inv (e::args) /\ Inv es /\
  (!es gs. Inv es ==> Inv (es with gas_obs := gs)) /\
  gas_marked_exec_ptr D (ctx,func) PG
    (do r <- eval_expr cx e; read_result cx r od)
    (es,s0,G0,tn0) marks (INL v) mid G tn r /\
  ptr_args_ready d ctx PG func cenv cx arg_ty Inv (e::args) ==>
  Inv (mid with gas_obs := []) /\
  typed_args_ready ctx func cenv cx arg_ty Inv args /\
  ptr_args_ready d ctx PG func cenv cx arg_ty Inv args /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes
Proof
  strip_tac >>
  `Inv (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    metis_tac[] >>
  `((do r <- eval_expr cx e; read_result cx r od)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
      (INL v,mid with gas_obs := []))` by
    (fs[gas_marked_exec_ptr_def] >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (drule forced_eval_expr_preserves_scopes_dom >> simp[]) >>
  drule_all typed_args_ready_head >> strip_tac >>
  drule_all typed_args_ready_tail >>
  drule_all ptr_args_ready_tail >> metis_tac[]
QED


Theorem typed_args_ptr_head_outcome_facts:
  typed_args_ready ctx func cenv cx arg_ty Inv (e::args) /\ Inv es /\
  (!es gs. Inv es ==> Inv (es with gas_obs := gs)) /\
  ptr_args_ready d ctx PG func cenv cx arg_ty Inv (e::args) /\
  gas_outcome_ptr D tops (ctx,func) PG
    (do r <- eval_expr cx e; read_result cx r od) (es,s0,G0,tn0) Q R ==>
  gas_outcome_ptr D tops (ctx,func) PG
    (do r <- eval_expr cx e; read_result cx r od) (es,s0,G0,tn0)
    (\rr ee G tn t. Q rr ee G tn t /\
      (!v. rr = INL v ==>
        Inv ee /\ typed_args_ready ctx func cenv cx arg_ty Inv args /\
        ptr_args_ready d ctx PG func cenv cx arg_ty Inv args /\
        MAP FDOM es.scopes = MAP FDOM ee.scopes)) R
Proof
  strip_tac >> irule gas_outcome_ptr_marked_conseq >>
  qexists_tac `Q` >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >> simp[] >> rpt strip_tac >>
  gvs[] >> drule_all typed_args_ptr_head_marked_facts >> simp[]
QED
