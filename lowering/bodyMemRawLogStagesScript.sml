(* Marked source endpoints for the RawLog memory composition. *)
Theory bodyMemRawLogStages
Ancestors
  bodyMemRawLogPrepare bodyArgsMemory bodySimRawLogBodySource
  exprSimRawLog exprSimPrecompiles exprSimWordArgs exprSimHypsDefs
  compileEnv gasSummary fragGasMode fragGasPath vyperState
  vyperEvalExprPreservesScopesDom list

Theorem raw_log_topics_marked_post_mem:
  body_inv tops ctx cenv cx /\ body_exprs_mem_ok cx topics /\
  (!e s. MEM e topics /\ expr_sim_inv cenv cx env s ==>
     expr_body_pre cenv cx env e s /\ expr_type e = BaseT (BytesT (Fixed 32))) /\
  expr_sim_inv cenv cx env es /\
  gas_marked_exec T (ctx,func) (eval_exprs cx topics) (es,s0)
    marks (INL vs) ee r /\
  typed_args_post ctx func cenv cx es sa s0 (ee with gas_obs := []) topics ops vs t ==>
  expr_sim_inv cenv cx env (ee with gas_obs := []) /\
  wb_args_post ctx func cenv cx es sa s0 (ee with gas_obs := []) ops vs t
Proof
  strip_tac >>
  `eval_exprs cx topics
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL vs, ee with gas_obs := [])` by
    (fs[gas_marked_exec_def] >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_sim_inv cenv cx env
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  `typed_args_ready_mem ctx func cenv cx expr_type
     (expr_sim_inv cenv cx env) topics` by
    (irule typed_args_ready_mem_of_body >>
     reverse conj_tac >- metis_tac[] >>
     simp[] >> rpt strip_tac >> res_tac >> simp[is_word_type_def]) >>
  conj_tac
  >- (drule_all typed_args_ready_mem_inv >> simp[]) >>
  drule_all raw_log_body_topics_values >> strip_tac >>
  irule raw_log_topics_post_wb >> simp[] >> qexists_tac `topics` >> simp[]
QED

Theorem raw_log_topics_marked_scopes:
  gas_marked_exec memory (ctx,func) (eval_exprs cx topics) (es,s0)
    marks (INL vs) ee r ==>
  MAP FDOM es.scopes = MAP FDOM (ee with gas_obs := []).scopes
Proof
  simp[gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` mp_tac) >> simp[] >>
  disch_then (mp_then Any mp_tac eval_exprs_preserves_scopes_dom) >> simp[]
QED
