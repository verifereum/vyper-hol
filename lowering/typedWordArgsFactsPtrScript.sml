Theory typedWordArgsFactsPtr
Ancestors
  gasOutcomeMarkedPtr gasSummaryComposePtr fragGasPathPtr fragGasSeqPtr gasSummary
  exprSimSend exprSimPrecompiles exprSimWordArgs exprSimHypsDefs vyperState

Theorem gas_outcome_ptr_source_facts:
  gas_outcome_ptr D tops (ctx,func) PG source (es,s0,G0,tn0) Q R /\
  (!gs rr ee. source (es with gas_obs := gs) = (rr,ee) ==> P rr ee) ==>
  gas_outcome_ptr D tops (ctx,func) PG source (es,s0,G0,tn0)
    (\rr ee G tn t. Q rr ee G tn t /\ P rr ee /\
       ee.gas_obs = [] /\ ~t.vs_halted) R
Proof
  strip_tac >> irule gas_outcome_ptr_marked_conseq >>
  qexists_tac `Q` >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >> simp[] >>
  fs[gas_marked_exec_ptr_def] >>
  `~t.vs_halted` by metis_tac[gas_path_ptr_ok_not_halted] >>
  simp[] >> first_x_assum irule >>
  first_x_assum (qspec_then `[]` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem typed_args_outcome_ptr_facts:
  typed_args_ready ctx func cenv cx expr_type (expr_sim_inv cenv cx env) args /\
  expr_sim_inv cenv cx env es /\
  (!e s. MEM e args /\ expr_sim_inv cenv cx env s ==>
     expr_body_pre cenv cx env e s /\ is_word_type (expr_type e)) /\
  gas_outcome_ptr D tops (ctx,func) PG (eval_exprs cx args) (es,s0,G0,tn0) Q R ==>
  gas_outcome_ptr D tops (ctx,func) PG (eval_exprs cx args) (es,s0,G0,tn0)
    (\rr ee G tn t. Q rr ee G tn t /\
      (!vs. rr = INL vs ==> expr_sim_inv cenv cx env ee /\
        LIST_REL (\e v. ?tv.
          evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
          value_has_type tv v) args vs) /\
      ee.gas_obs = [] /\ ~t.vs_halted) R
Proof
  strip_tac >> ho_match_mp_tac gas_outcome_ptr_source_facts >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> disch_tac >> gen_tac >> disch_tac >> gvs[] >>
  `expr_sim_inv cenv cx env (es with gas_obs := gs)` by simp[] >>
  conj_tac
  >- (drule_all typed_args_ready_inv >> simp[]) >>
  irule stack_args_values_typed_body >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
