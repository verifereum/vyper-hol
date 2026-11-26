(* Close the source and target request-prefix obligations at one marking. *)
Theory s1RequestPrefix
Ancestors
  s1PrefixRequestCut s1PrefixRuntimeUnit s1PrefixCommonMarks
  s1PrefixFullShadow s1PrefixCallTrace s1PrefixRuntimeCutHyps
  gasShadowRunLowering e2eRequestCutDefs vyperInterpreter whitelistCheckerGate

(* Use the program variable rather than the inherited arithmetic overload. *)
val _ = Parse.temp_clear_overloads_on "tops"

Theorem s1_request_prefix_holds:
  supported_program tops ==> s1_request_prefix tops
Proof
  pure_rewrite_tac[s1_request_prefix_def] >> rpt strip_tac >>
  `?shadow_unit. runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
                 gas_shadow_unit unit shadow_unit` by
    (Cases_on `classify_functions tops` >> PairCases_on `r` >>
     irule runtime_gas_shadow_unit_exists >> fs[]) >>
  qexists_tac `shadow_unit.cu_context` >> rpt strip_tac >>
  drule_all dispatched_full_at_runtime_shadow >>
  disch_then (qx_choose_then `full_marks` assume_tac) >>
  drule_all unit_prefix_cert_holds >> strip_tac >>
  drule_all unit_prefix_full_common_marks >>
  disch_then (qx_choose_then `marks` (qx_choose_then `func` strip_assume_tac)) >>
  qexists_tac `marks` >> conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  drule_all prefix_call_trace_outcome_facts >> strip_tac >>
  conj_tac >- simp[] >>
  strip_tac >> simp[] >>
  qpat_assum `!tail res. _` drule_all >> strip_tac >>
  drule_all runtime_request_cut_entry_hyps >>
  disch_then (qx_choose_then `entry_func` (qx_choose_then `P` strip_assume_tac)) >>
  `entry_func = func` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `entry_func = func` SUBST_ALL_TAC >>
  drule_all request_site_raw_safe_rq_upto >> simp[initial_evaluation_context_def]
QED

Theorem s1_request_prefix_all:
  s1_request_prefix tops
Proof
  Cases_on `supported_program tops`
  >- simp[s1_request_prefix_holds] >>
  rewrite_tac[s1_request_prefix_def] >>
  rpt gen_tac >> strip_tac >>
  qexists_tac `ARB` >> rpt gen_tac >> strip_tac >>
  metis_tac[whitelistCheckerGateTheory.source_typing_ok_supported_program]
QED
