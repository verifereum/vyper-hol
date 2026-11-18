Theory callCodeTrace
Ancestors
  callCodeTraceFromEval callCodeLookup callCodeEval vyperInterpreter
  vyperContext vyperState alist e2eProducers

Theorem call_external_trace_no_self_code_update:
  ALOOKUP am.sources tx.target = SOME [(NONE,tops)] /\
  ~program_reads_self_code tops ==>
  call_external_trace (SOME os) gobs am (tx with code := c) =
  call_external_trace (SOME os) gobs am tx
Proof
  strip_tac >>
  irule call_external_trace_code_update_from_eval >>
  reverse conj_tac >-
    (qexists_tac `tops` >> simp[] >> metis_tac[lookup_function_no_self_code]) >>
  simp[] >>
  gen_tac >> MATCH_MP_TAC (GEN_ALL evaluate_no_self_code_update) >>
  simp[get_module_code_def, initial_evaluation_context_def, ALOOKUP_def,
       lookup_callable_function_def, AllCaseEqs()] >>
  metis_tac[lookup_function_no_self_code]
QED
