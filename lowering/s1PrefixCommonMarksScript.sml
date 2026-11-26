(* Join the full and request-prefix certificates at their common shadow. *)
Theory s1PrefixCommonMarks
Ancestors
  s1PrefixProps sourceUnitExecution s1PrefixDefs fragGasOriginPtr gasSummary rich_list

Theorem unit_prefix_full_common_marks:
  source_unit_execution_correct_with shadow_ctx full_marks tops ret am tx unit vs /\
  unit_prefix_cert shadow_ctx tops am tx unit vs ==>
  ?marks func.
    source_unit_execution_correct_with shadow_ctx marks tops ret am tx unit vs /\
    unit.cu_context.ctx_entry = SOME "__entry" /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
    !tail res am' rqs obs obs_pre rq outcome sfx H.
      call_external_trace (SOME vs.vs_outcomes)
        (gas_explicit marks vs.vs_gas_readings ++ tail) am tx = (res,am',rqs,obs) /\
      obs = obs_pre ++ StorageOutcome rq outcome :: sfx /\
      valid_horizon (initial_evaluation_context am.sources am.layouts tx NONE)
        (initial_state am []) H obs_pre /\
      ~computed_precompile rq ==>
      request_site
        (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE),
         0, gas_explicit_sites unit.cu_context shadow_ctx, unit.cu_context, func, [])
        (initial_evaluation_context am.sources am.layouts tx NONE) H
        (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                    vs_inst_idx := 0 |>, FEMPTY, entry_taint)
        (recorded_outcomes_count obs_pre) rq outcome
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `unit_prefix_cert _ _ _ _ _ _`
    (qx_choose_then `func` (qx_choose_then `pre_marks` strip_assume_tac) o
     REWRITE_RULE [unit_prefix_cert_def]) >>
  Cases_on `isPREFIX pre_marks full_marks`
  >- (qexistsl_tac [`full_marks`, `func`] >> fs[IS_PREFIX_APPEND] >>
      pure_rewrite_tac[gas_explicit_append, GSYM APPEND_ASSOC] >> rpt strip_tac >>
      qpat_assum `!tail res. _` drule_all >> simp[]) >>
  qpat_x_assum `source_unit_execution_correct_with _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [source_unit_execution_correct_with_def]) >>
  gvs[]
  >>~ [`exit_result r`]
  >- (qpat_assum `gas_origin_ptr_focus _ _ pre_marks _`
        (assume_tac o MATCH_MP gas_origin_ptr_focus_origin) >>
      drule_all gas_origin_path_exit_bounds_focus >> simp[]) >>
  `?ext. pre_marks = full_marks ++ ext` by
    (qsuff_tac `isPREFIX full_marks pre_marks` >- simp[IS_PREFIX_APPEND] >>
     qpat_x_assum `gas_origin_ptr_focus _ _ pre_marks _`
       (fn th => qpat_x_assum `gas_origin_ptr_focus _ _ full_marks _`
         (mp_tac o MATCH_MP gas_origin_ptr_focus_marks_comparable o C CONJ th)) >>
     simp[]) >>
  (qexists_tac `pre_marks` >> (reverse conj_tac >- first_assum ACCEPT_TAC) >>
   simp[source_unit_execution_correct_with_def] >>
   qexists_tac `shadow_func` >> simp[])
  >>~ [`!tail. ~call_storage_ok _ _ _ _`]
  >- (disj1_tac >> conj_tac
      >- (pure_rewrite_tac[gas_explicit_append, GSYM APPEND_ASSOC] >>
          qx_gen_tac `tail` >>
          qpat_assum `!tail. ~call_storage_ok _ _ _ _`
            (qspec_then `gas_explicit ext (DROP (LENGTH full_marks) vs.vs_gas_readings) ++ tail`
              ACCEPT_TAC)) >>
      metis_tac[]) >>
  rename1 `!tail. call_external_trace _ (_ ++ tail) _ _ = (res, after, rqs, obs)` >>
  disj2_tac >> qexistsl_tac [`res`, `after`, `rqs`, `obs`] >> simp[] >>
  conj_tac
  >- (pure_rewrite_tac[gas_explicit_append, GSYM APPEND_ASSOC] >>
      gen_tac >> first_x_assum irule) >>
  disj1_tac >> metis_tac[]
QED
