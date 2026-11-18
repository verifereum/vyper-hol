(* Transfer the walk's static exit to the same source input as its simulation. *)
Theory gasFocusStaticExitLift
Ancestors
  o1PipelineCompose o1RequestContract o1PassContract ptrDiscipline
  unitMemInv staticAbortDefs stackPlanGen venomExecSemantics passSimulationDefs
  venomState words

Theorem focus_static_exit_lift:
  dead_wf D /\ ctx_sim D A B a b /\ ctx_abort_rq D A B a b /\
  ctx_sim D B C b c /\ ctx_abort_rq D B C b c /\
  (o1_lowered_inv C c \/
   ((?eom. max_live_eom C = SOME eom /\
      mem_inv (\ctx fn inst s. in_static_abort_prefix fn s \/
        lowered_mem_fact eom ctx fn inst s) C c) /\
    !fuel. terminates (run_context fuel B b) ==>
           ?u. run_context fuel B b = Abort ExHalt_abort u)) ==>
  ctx_sim D A C a c /\ ctx_abort_rq D A C a c /\
  (o1_lowered_inv C c \/
   ((?eom. max_live_eom C = SOME eom /\
      mem_inv (\ctx fn inst s. in_static_abort_prefix fn s \/
        lowered_mem_ok eom (w2n s.vs_initial_fmp) ctx fn inst s) C c) /\
    !fuel. terminates (run_context fuel A a) ==>
           ?u. run_context fuel A a = Abort ExHalt_abort u))
Proof
  simp[lowered_mem_fact_def] >> strip_tac >>
  (conj_tac >- metis_tac[ctx_sim_trans]) >>
  (conj_tac >- metis_tac[ctx_abort_rq_trans]) >>
  simp[] >> disj2_tac >>
  rpt strip_tac >>
  qpat_x_assum `ctx_sim D A B a b` (mp_tac o REWRITE_RULE[ctx_sim_def]) >>
  disch_then (qspec_then `fuel` mp_tac) >> simp[] >>
  disch_then (qx_choose_then `walk_fuel` assume_tac) >>
  `terminates (run_context walk_fuel B b)` by
    metis_tac[dead_result_rel_terminates] >>
  qpat_x_assum `!k. terminates (run_context k B b) ==> _`
    (qspec_then `walk_fuel` mp_tac) >> simp[] >> strip_tac >>
  Cases_on `run_context fuel A a` >> gvs[dead_result_rel_def] >>
  rename1 `reason = ExHalt_abort` >>
  Cases_on `reason` >> gvs[]
QED
