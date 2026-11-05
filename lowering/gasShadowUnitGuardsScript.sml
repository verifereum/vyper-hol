Theory gasShadowUnitGuards
Ancestors
  gasShadowUnitObservations gasShadowUnit vyperCompiler venomInst fcgDefs list

Theorem gas_shadow_lookup_function:
  !fs gs name. LIST_REL gas_shadow_function fs gs ==>
    OPTREL gas_shadow_function (lookup_function name fs) (lookup_function name gs)
Proof
  Induct >> Cases_on `gs` >> simp[lookup_function_def, FIND_thm] >>
  rpt strip_tac >>
  `h'.fn_name = h.fn_name` by metis_tac[gas_shadow_function_fields] >>
  simp[] >> IF_CASES_TAC >> simp[] >>
  fs[lookup_function_def]
QED

Theorem gas_shadow_context_entry:
  gas_shadow_context c d ==> c.ctx_entry = d.ctx_entry
Proof
  simp[gas_shadow_context_def] >> strip_tac >>
  qpat_x_assum `_ = c` (SUBST1_TAC o SYM) >> simp[]
QED

Theorem gas_shadow_fcg_visit:
  gas_shadow_context c d ==> fcg_visit c name a = fcg_visit d name a
Proof
  strip_tac >>
  `OPTREL gas_shadow_function (lookup_function name c.ctx_functions)
                            (lookup_function name d.ctx_functions)`
    by (irule gas_shadow_lookup_function >> fs[gas_shadow_context_def]) >>
  Cases_on `lookup_function name c.ctx_functions` >>
  Cases_on `lookup_function name d.ctx_functions` >>
  gvs[fcg_visit_def] >>
  metis_tac[gas_shadow_fcg_scan_function]
QED

Theorem gas_shadow_fcg_dfs:
  !c stack visited a. !d. gas_shadow_context c d ==>
    fcg_dfs c stack visited a = fcg_dfs d stack visited a
Proof
  recInduct fcg_dfs_ind >> rpt strip_tac >- simp[fcg_dfs_def] >>
  `fcg_visit ctx fn_name fcg = fcg_visit d fn_name fcg`
    by metis_tac[gas_shadow_fcg_visit] >>
  simp[Once fcg_dfs_def] >>
  simp[SimpRHS, Once fcg_dfs_def] >>
  Cases_on `MEM fn_name visited` >- simp[] >>
  Cases_on `fcg_visit d fn_name fcg` >> gvs[] >> metis_tac[]
QED

Theorem gas_shadow_fcg_analyze:
  gas_shadow_context c d ==> fcg_analyze c = fcg_analyze d
Proof
  strip_tac >>
  `c.ctx_entry = d.ctx_entry` by metis_tac[gas_shadow_context_entry] >>
  simp[fcg_analyze_def] >> Cases_on `d.ctx_entry` >>
  simp[gas_shadow_fcg_dfs]
QED

Theorem gas_shadow_reachable_fcg_acyclic:
  gas_shadow_context c d ==>
    (reachable_fcg_acyclic c (fcg_analyze c) <=>
     reachable_fcg_acyclic d (fcg_analyze d))
Proof
  strip_tac >>
  `c.ctx_entry = d.ctx_entry` by metis_tac[gas_shadow_context_entry] >>
  `fcg_analyze c = fcg_analyze d` by metis_tac[gas_shadow_fcg_analyze] >>
  simp[reachable_fcg_acyclic_def]
QED

Theorem gas_shadow_lowering_context_ok:
  gas_shadow_context c d ==> (lowering_context_ok c <=> lowering_context_ok d)
Proof
  strip_tac >>
  `ctx_fn_names c = ctx_fn_names d` by metis_tac[gas_shadow_ctx_fn_names] >>
  `wf_invoke_targets_check c <=> wf_invoke_targets_check d`
    by metis_tac[gas_shadow_wf_invoke_targets_check] >>
  `ctx_inst_ids_distinct c <=> ctx_inst_ids_distinct d`
    by metis_tac[gas_shadow_ctx_inst_ids_distinct] >>
  `forced_alloc_inputs_check c <=> forced_alloc_inputs_check d`
    by metis_tac[gas_shadow_forced_alloc_inputs_check] >>
  `unit_alloca_budget c = unit_alloca_budget d`
    by metis_tac[gas_shadow_unit_alloca_budget] >>
  `EVERY (\fn. ALL_DISTINCT (fn_labels fn) /\ fn_has_entry fn) c.ctx_functions <=>
   EVERY (\fn. ALL_DISTINCT (fn_labels fn) /\ fn_has_entry fn) d.ctx_functions`
    by metis_tac[gas_shadow_ctx_labels_entry] >>
  `reachable_fcg_acyclic c (fcg_analyze c) <=> reachable_fcg_acyclic d (fcg_analyze d)`
    by metis_tac[gas_shadow_reachable_fcg_acyclic] >>
  simp[lowering_context_ok_def]
QED
