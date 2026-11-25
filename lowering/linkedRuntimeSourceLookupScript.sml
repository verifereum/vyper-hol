Theory linkedRuntimeSourceLookup
Ancestors e2eModsDefs vyperInterpreter vyperContext alist option

Theorem linked_runtime_source_lookup:
  source_deployment_rel_mods mods exps am tx /\
  src = ALOOKUP exps tx.function_name /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  ALOOKUP mods src = SOME tops ==>
  find_function_module am tx.target tx.function_name = src /\
  get_module_code cx src = SOME tops /\
  lookup_exported_function cx am tx.function_name =
    vyperInterpreter$lookup_function src tx.function_name External tops
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `source_deployment_rel_mods mods exps am tx`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [source_deployment_rel_mods_def]) >>
  qpat_assum `ALOOKUP am.exports tx.target = SOME exps \/ _`
    (DISJ_CASES_THEN2 assume_tac STRIP_ASSUME_TAC) >>
  FULL_SIMP_TAC (srw_ss()) [initial_evaluation_context_def, find_function_module_def,
    lookup_exported_function_def, get_self_code_def, get_module_code_def] >>
  Cases_on `ALOOKUP exps tx.function_name` >> gvs[]
QED
