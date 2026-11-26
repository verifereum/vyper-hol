Theory groupedDefaultSuffixReadings
Ancestors
  groupedDefaultOutcome groupedDefaultHorizon groupedDefaultSubstitution
  compileVyper e2eDefs vyperTypeContract vyperInterpreter vyperState
  gasOutcomeFull gasStorage fragExec list

Theorem grouped_default_suffix_readings:
  lower_vyper_runtime_unit tops policy = SOME unit /\
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  check_contract F am.layouts tx.target [(NONE,tops)] = SOME art /\
  well_typed_exprs (artifact_env art [(NONE,tops)] NONE) osrc /\
  es.immutables = am.immutables /\
  cx = initial_evaluation_context am.sources am.layouts tx NONE /\
  ocomp = subst_consts_exprs (module_consts_env tops []) osrc /\
  EVERY (runtime_constant_expr [(NONE,tops)]) ocomp /\ no_sha256_exprs ocomp /\
  storage_trace_domain cx st0 es.storage_trace /\
  gas_outcome_full (DF,lo,explicit,ctx,fn,PG) tops' cx st0
    (eval_exprs cx ocomp) (es,s,G,tn) Q R ==>
  ?marks res ee.
    (!tail. eval_exprs cx osrc
      (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (res,ee with gas_obs := tail)) /\
    ((ee with gas_obs := []) = (es with gas_obs := [])) /\
    ((?r J u.
      !H. valid_horizon cx st0 H ee.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) marks (r,J,u) /\
        ((?t. r = OK t /\ Q H res (ee with gas_obs := []) J u t) \/
         (exit_result r /\ create_size_exit_ok ctx res r /\
          R H res (ee with gas_obs := []) (J,u) r))) \/
     (?err H leaf leaf_pg leaf_g leaf_tn finish.
       res = INR (Error err) /\ unspecified_behaviour_exempt tops' err /\
       valid_horizon cx st0 H es.storage_trace /\
       gas_origin_ptr_focus (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) marks
         (leaf,leaf_pg,leaf_g,leaf_tn,finish)))
Proof
  strip_tac >>
  `ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]` by
    fs[initial_evaluation_context_def, source_deployment_rel_def] >>
  `!gs. ((SND (eval_exprs cx ocomp (es with gas_obs := gs))) with gas_obs := []) =
        (es with gas_obs := [])` by
    (gen_tac >> Cases_on `eval_exprs cx ocomp (es with gas_obs := gs)` >>
     rename1 `eval_exprs _ _ _ = (res,ee)` >> simp[] >>
     drule_all grouped_checked_default_source_frame >> simp[]) >>
  `!gs. (SND (eval_exprs cx ocomp (es with gas_obs := gs))).storage_trace =
        es.storage_trace` by
    (gen_tac >> first_x_assum (qspec_then `gs` (mp_tac o AP_TERM ``evaluation_state_storage_trace``)) >>
     simp[evaluation_state_accfupds]) >>
  drule_all grouped_default_initializer_outcome >>
  disch_then (qx_choosel_then [`marks`,`res`,`ee`]
    (map_every assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`marks`,`res`,`ee`] >>
  `!gs. eval_exprs cx osrc (es with gas_obs := gs) =
        eval_exprs cx ocomp (es with gas_obs := gs)` by
    (gen_tac >> asm_rewrite_tac[] >> irule grouped_substituted_defaults_eval >>
     simp[evaluation_state_accfupds] >> metis_tac[]) >>
  `((ee with gas_obs := []) = (es with gas_obs := []))` by
    (qpat_assum `!gs. (SND _ with gas_obs := []) = _`
       (qspec_then `gas_explicit marks s.vs_gas_readings ++ []` mp_tac) >>
     qpat_assum `!tail. eval_exprs _ ocomp _ = _`
       (qspec_then `[]:bytes32 list` (fn th => pure_rewrite_tac [th])) >>
     simp[evaluation_state_fupdfupds]) >>
  asm_rewrite_tac[]
QED
