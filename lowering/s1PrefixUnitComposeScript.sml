(* Compose the rooted runtime entry path with a body request-prefix certificate. *)
Theory s1PrefixUnitCompose
Ancestors
  s1PrefixCompose s1PrefixProps s1PrefixDefs fragGasOriginPtr
  gasSummary gasExplicitSites e2eRequestCutDefs vyperCall vyperStorageTrace
  vyperState sourceUnitExecution compileUnit venomInst venomState
  ptrDiscipline list finite_map

Theorem unit_prefix_cert_from_body:
  cx = initial_evaluation_context am.sources am.layouts tx NONE /\
  entry = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|> /\
  explicit = gas_explicit_sites unit.cu_context shadow_ctx /\
  unit.cu_context.ctx_entry = SOME "__entry" /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
  t.vs_gas_readings = DROP (LENGTH entry_marks) vs.vs_gas_readings /\
  storage_trace_domain cx (initial_state am []) es.storage_trace /\
  recorded_outcomes_count es.storage_trace = 0 /\ es.requests = [] /\
  storage_trace_frame source /\
  (!H. valid_horizon cx (initial_state am []) H es.storage_trace ==>
    gas_origin_ptr_path (cx_dead H cx, 0, explicit, unit.cu_context, func, [])
      (entry, FEMPTY, entry_taint) entry_marks (OK t, G, tn)) /\
  gas_prefix_full ((\H. cx_dead H cx), 0, explicit, unit.cu_context, func, [])
    cx (initial_state am []) source (es, t, G, tn) /\
  (!gas res am' rqs obs.
    call_external_trace (SOME vs.vs_outcomes)
      (gas_explicit entry_marks vs.vs_gas_readings ++ gas) am tx =
      (res, am', rqs, obs) ==>
    ?ans ee suffix.
      source (es with gas_obs := gas) = (ans, ee) /\
      obs = ee.storage_trace ++ suffix /\ recorded_outcomes_count suffix = 0) ==>
  unit_prefix_cert shadow_ctx tops am tx unit vs
Proof
  strip_tac >>
  qpat_x_assum `gas_prefix_full _ _ _ _ _`
    (qx_choose_then `body_marks`
       (CONJUNCTS_THEN2
          (qx_choosel_then [`body_H`,`body_leaf`,`body_pg`,`body_g`,
                            `body_tn`,`body_finish`] strip_assume_tac)
          assume_tac) o BETA_RULE o ONCE_REWRITE_RULE[gas_prefix_full_def]) >>
  rewrite_tac[unit_prefix_cert_def] >>
  qexistsl_tac [`func`,`entry_marks ++ body_marks`] >> simp[] >> conj_tac
  >- (qexistsl_tac [`body_H`,`body_leaf`,`body_pg`,`body_g`,`body_tn`,`body_finish`] >>
      irule (cj 2 gas_origin_ptr_focus_rules) >> metis_tac[]) >>
  PURE_REWRITE_TAC[gas_explicit_append, GSYM APPEND_ASSOC] >>
  rpt gen_tac >> strip_tac >>
  rename1 `valid_horizon _ _ site_H obs_pre` >>
  qpat_assum `!gas res am' rqs obs. call_external_trace _ _ _ _ = _ ==> _`
    (drule_then (qx_choosel_then [`ans`,`ee`,`suffix`] strip_assume_tac)) >>
  `?body_sfx. ee.storage_trace = obs_pre ++ StorageOutcome rq outcome :: body_sfx` by
    (qpat_assum `_ = ee.storage_trace ++ suffix`
       (mp_then Any strip_assume_tac bind_trace_outcome_split o SYM) >>
     fs[recorded_outcomes_count_def,FILTER_APPEND_DISTRIB]) >>
  drule_all storage_trace_frame_prefix >> strip_tac >>
  `?pre. obs_pre = es.storage_trace ++ pre` by
    (`es.storage_trace ++ observations = obs_pre ++ StorageOutcome rq outcome :: body_sfx` by fs[] >>
     drule bind_trace_outcome_split >> strip_tac >>
     fs[recorded_outcomes_count_def,FILTER_APPEND_DISTRIB]) >>
  `valid_horizon cx (initial_state am []) site_H es.storage_trace` by
    metis_tac[gasOutcomeFullTheory.valid_horizon_append] >>
  gvs[] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _`
    (qspec_then `site_H` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  drule_then irule request_site_prepend_path >>
  qpat_assum `!tail res ee obs_pre rq outcome sfx H. _ ==> request_site _ _ _ _ _ _ _`
    irule >> simp[] >> metis_tac[]
QED
