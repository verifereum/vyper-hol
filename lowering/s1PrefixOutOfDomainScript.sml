(* A query before an outcome cannot follow an out-of-domain input trace. *)
Theory s1PrefixOutOfDomain
Ancestors
  s1PrefixDefs s1PrefixCompose bodyFullExtCallPackingReady vyperStorageTrace
  vyperStorageFootprint gasExplicitSites gasSummary fragGasOriginPtr
  e2eRequestCutDefs vyperCall vyperState sourceUnitExecution compileUnit
  venomInst venomState ptrDiscipline list finite_map

Theorem out_of_domain_unit_prefix_cert:
  cx = initial_evaluation_context am.sources am.layouts tx NONE /\
  entry = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|> /\
  unit.cu_context.ctx_entry = SOME "__entry" /\
  venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
  gas_origin_ptr_focus
    (cx_dead (H0 : (bool # bytes32 # type_value) list # num list) cx, 0,
     gas_explicit_sites unit.cu_context shadow_ctx, unit.cu_context, func, [])
    (entry,FEMPTY,entry_taint) marks (leaf,leaf_pg,leaf_g,leaf_tn,final_vs) /\
  ~storage_trace_domain cx (initial_state am []) es.storage_trace /\
  recorded_outcomes_count es.storage_trace = 0 /\ storage_trace_frame source /\
  (!gas res am' rqs obs.
    call_external_trace (SOME vs.vs_outcomes)
      (gas_explicit marks vs.vs_gas_readings ++ gas) am tx = (res,am',rqs,obs) ==>
    ?ans ee suffix. source (es with gas_obs := gas) = (ans,ee) /\
       obs = ee.storage_trace ++ suffix /\ recorded_outcomes_count suffix = 0) ==>
  unit_prefix_cert shadow_ctx tops am tx unit vs
Proof
  strip_tac >> rewrite_tac[unit_prefix_cert_def] >>
  qexistsl_tac [`func`,`marks`] >> simp[] >> conj_tac
  >- (qexistsl_tac [`H0`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`final_vs`] >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!gas res am' rqs obs. call_external_trace _ _ _ _ = _ ==> _`
    (drule_then (qx_choosel_then [`ans`,`ee`,`suffix`] strip_assume_tac)) >>
  drule_all storage_trace_frame_prefix >>
  disch_then (qx_choose_then `observations` assume_tac) >>
  `es.storage_trace ++ (observations ++ suffix) = obs_pre ++ StorageOutcome rq outcome :: sfx`
    by fs[APPEND_ASSOC] >>
  drule bind_trace_outcome_split >> strip_tac
  >- fs[recorded_outcomes_count_def,FILTER_APPEND_DISTRIB] >>
  drule extcall_packing_observed_domain >>
  simp[] >> metis_tac[storage_trace_domain_prefix]
QED
