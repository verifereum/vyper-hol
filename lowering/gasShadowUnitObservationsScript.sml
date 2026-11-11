Theory gasShadowUnitObservations
Ancestors
  gasShadowUnit gasShadowState vyperCompiler venomInst venomWf fcgDefs
  list pair

Theorem gas_shadow_inst_fields:
  gas_shadow_inst i j ==>
    i.inst_id = j.inst_id /\ i.inst_operands = j.inst_operands
Proof
  rw[gas_shadow_inst_def] >> simp[]
QED

Theorem gas_shadow_inst_filter:
  gas_shadow_inst i j /\ (opc = INVOKE \/ opc = ALLOCA) ==>
    (i.inst_opcode = opc <=> j.inst_opcode = opc) /\
    (i.inst_opcode = opc ==> i = j)
Proof
  rw[gas_shadow_inst_def] >> gvs[]
QED

Theorem gas_shadow_list_observe:
  !xs ys. LIST_REL R xs ys ==>
    (!x y. R x y ==> f x = g y) ==> MAP f xs = MAP g ys
Proof
  Induct >> Cases_on `ys` >> simp[] >> metis_tac[]
QED

Theorem gas_shadow_list_filter:
  !xs ys opc. LIST_REL gas_shadow_inst xs ys /\
    (opc = INVOKE \/ opc = ALLOCA) ==>
    FILTER (\i. i.inst_opcode = opc) xs =
    FILTER (\i. i.inst_opcode = opc) ys
Proof
  Induct >> Cases_on `ys` >> simp[] >> rpt strip_tac >>
  `FILTER (\i. i.inst_opcode = opc) xs = FILTER (\i. i.inst_opcode = opc) t`
    by metis_tac[] >>
  `h'.inst_opcode = opc <=> h.inst_opcode = opc`
    by metis_tac[gas_shadow_inst_filter] >>
  IF_CASES_TAC >> gvs[] >> metis_tac[gas_shadow_inst_filter]
QED

Theorem gas_shadow_blocks_insts:
  !bs cs. LIST_REL gas_shadow_block bs cs ==>
    LIST_REL gas_shadow_inst (fn_insts_blocks bs) (fn_insts_blocks cs)
Proof
  Induct >> Cases_on `cs` >> simp[fn_insts_blocks_def] >>
  simp[gas_shadow_block_def] >> metis_tac[LIST_REL_APPEND]
QED

Theorem gas_shadow_function_insts:
  gas_shadow_function f g ==> LIST_REL gas_shadow_inst (fn_insts f) (fn_insts g)
Proof
  simp[gas_shadow_function_def, fn_insts_def, gas_shadow_blocks_insts]
QED

Theorem gas_shadow_function_fields:
  gas_shadow_function f g ==>
    f.fn_name = g.fn_name /\
    f.fn_forced_alloc_positions = g.fn_forced_alloc_positions
Proof
  strip_tac >> fs[gas_shadow_function_def] >>
  qpat_x_assum `_ = f` (SUBST1_TAC o SYM) >> simp[]
QED

Theorem gas_shadow_function_labels:
  gas_shadow_function f g ==> fn_labels f = fn_labels g
Proof
  simp[gas_shadow_function_def, fn_labels_def] >> strip_tac >>
  irule gas_shadow_list_observe >> qexists_tac `gas_shadow_block` >>
  simp[gas_shadow_block_def]
QED

Theorem gas_shadow_list_every:
  !xs ys. LIST_REL R xs ys ==>
    (!x y. R x y ==> (p x <=> q y)) ==> (EVERY p xs <=> EVERY q ys)
Proof
  Induct >> Cases_on `ys` >> simp[] >> metis_tac[]
QED

Theorem gas_shadow_function_filter:
  gas_shadow_function f g /\ (opc = INVOKE \/ opc = ALLOCA) ==>
    FILTER (\i. i.inst_opcode = opc) (fn_insts f) =
    FILTER (\i. i.inst_opcode = opc) (fn_insts g)
Proof
  metis_tac[gas_shadow_function_insts, gas_shadow_list_filter]
QED

Theorem get_invoke_targets_filter:
  !xs. get_invoke_targets xs =
    get_invoke_targets (FILTER (\i. i.inst_opcode = INVOKE) xs)
Proof
  Induct >> simp[get_invoke_targets_def] >>
  gen_tac >> IF_CASES_TAC >> simp[get_invoke_targets_def]
QED

Theorem gas_shadow_fcg_scan_function:
  gas_shadow_function f g ==> fcg_scan_function f = fcg_scan_function g
Proof
  strip_tac >> simp[fcg_scan_function_def] >>
  once_rewrite_tac[get_invoke_targets_filter] >>
  metis_tac[gas_shadow_function_filter]
QED

Theorem gas_shadow_function_entry:
  gas_shadow_function f g ==> (fn_has_entry f <=> fn_has_entry g)
Proof
  simp[gas_shadow_function_def, fn_has_entry_def] >>
  Cases_on `f.fn_blocks` >> Cases_on `g.fn_blocks` >> simp[]
QED

Theorem gas_shadow_function_ids:
  gas_shadow_function f g ==>
    FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) f.fn_blocks) =
    FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) g.fn_blocks)
Proof
  strip_tac >> AP_TERM_TAC >> irule gas_shadow_list_observe >>
  qexists_tac `gas_shadow_block` >>
  reverse conj_tac >- fs[gas_shadow_function_def] >>
  rpt strip_tac >> simp[] >> irule gas_shadow_list_observe >>
  qexists_tac `gas_shadow_inst` >>
  simp[gas_shadow_inst_fields] >> fs[gas_shadow_block_def]
QED

Theorem gas_shadow_invoke_target_ok:
  gas_shadow_inst i j ==> (invoke_target_ok names i <=> invoke_target_ok names j)
Proof
  rw[gas_shadow_inst_def, invoke_target_ok_def] >> simp[]
QED

Theorem gas_shadow_function_invoke_ok:
  gas_shadow_function f g ==>
    (EVERY (\bb. EVERY (invoke_target_ok names) bb.bb_instructions) f.fn_blocks <=>
     EVERY (\bb. EVERY (invoke_target_ok names) bb.bb_instructions) g.fn_blocks)
Proof
  strip_tac >> irule gas_shadow_list_every >> qexists_tac `gas_shadow_block` >>
  reverse conj_tac >- fs[gas_shadow_function_def] >>
  rpt strip_tac >> simp[] >> irule gas_shadow_list_every >> qexists_tac `gas_shadow_inst` >>
  simp[gas_shadow_invoke_target_ok] >> fs[gas_shadow_block_def]
QED

Theorem forced_alloc_key_filter:
  forced_alloc_key_in_function fn id <=>
    ?i. MEM i (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts fn)) /\ i.inst_id = id
Proof
  simp[forced_alloc_key_in_function_def, MEM_FILTER] >> metis_tac[]
QED

Theorem gas_shadow_function_forced_metadata:
  gas_shadow_function f g ==>
    (function_forced_metadata_ok f <=> function_forced_metadata_ok g)
Proof
  strip_tac >>
  `f.fn_forced_alloc_positions = g.fn_forced_alloc_positions`
    by metis_tac[gas_shadow_function_fields] >>
  `FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts f) =
   FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts g)`
    by metis_tac[gas_shadow_function_filter] >>
  simp[function_forced_metadata_ok_def, forced_alloc_key_filter]
QED

Theorem gas_shadow_ctx_fn_names:
  gas_shadow_context c d ==> ctx_fn_names c = ctx_fn_names d
Proof
  simp[gas_shadow_context_def, ctx_fn_names_def] >> strip_tac >>
  irule gas_shadow_list_observe >> qexists_tac `gas_shadow_function` >>
  simp[gas_shadow_function_fields]
QED

Theorem gas_shadow_ctx_inst_ids_distinct:
  gas_shadow_context c d ==> (ctx_inst_ids_distinct c <=> ctx_inst_ids_distinct d)
Proof
  strip_tac >> simp[ctx_inst_ids_distinct_def] >>
  `MAP (\fn. FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) fn.fn_blocks)) c.ctx_functions =
   MAP (\fn. FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) fn.fn_blocks)) d.ctx_functions`
    by (irule gas_shadow_list_observe >> qexists_tac `gas_shadow_function` >>
        simp[gas_shadow_function_ids] >> fs[gas_shadow_context_def]) >> simp[]
QED

Theorem gas_shadow_wf_invoke_targets_check:
  gas_shadow_context c d ==> (wf_invoke_targets_check c <=> wf_invoke_targets_check d)
Proof
  strip_tac >>
  `ctx_fn_names c = ctx_fn_names d` by metis_tac[gas_shadow_ctx_fn_names] >>
  simp[wf_invoke_targets_check_def] >>
  irule gas_shadow_list_every >> qexists_tac `gas_shadow_function` >>
  simp[gas_shadow_function_invoke_ok] >> fs[gas_shadow_context_def]
QED

Theorem gas_shadow_forced_alloc_inputs_check:
  gas_shadow_context c d ==> (forced_alloc_inputs_check c <=> forced_alloc_inputs_check d)
Proof
  strip_tac >> simp[forced_alloc_inputs_check_def] >>
  irule gas_shadow_list_every >> qexists_tac `gas_shadow_function` >>
  simp[gas_shadow_function_forced_metadata] >> fs[gas_shadow_context_def]
QED

Theorem gas_shadow_ctx_labels_entry:
  gas_shadow_context c d ==>
    (EVERY (\fn. ALL_DISTINCT (fn_labels fn) /\ fn_has_entry fn) c.ctx_functions <=>
     EVERY (\fn. ALL_DISTINCT (fn_labels fn) /\ fn_has_entry fn) d.ctx_functions)
Proof
  strip_tac >> irule gas_shadow_list_every >> qexists_tac `gas_shadow_function` >>
  reverse conj_tac >- fs[gas_shadow_context_def] >>
  metis_tac[gas_shadow_function_labels, gas_shadow_function_entry]
QED

Theorem gas_shadow_functions_filter:
  !fs gs opc. LIST_REL gas_shadow_function fs gs /\
    (opc = INVOKE \/ opc = ALLOCA) ==>
    FILTER (\i. i.inst_opcode = opc) (FLAT (MAP fn_insts fs)) =
    FILTER (\i. i.inst_opcode = opc) (FLAT (MAP fn_insts gs))
Proof
  Induct >> Cases_on `gs` >> simp[FILTER_APPEND_DISTRIB] >>
  metis_tac[gas_shadow_function_filter]
QED

Theorem gas_shadow_unit_alloca_budget:
  gas_shadow_context c d ==> unit_alloca_budget c = unit_alloca_budget d
Proof
  strip_tac >>
  `FILTER (\i. i.inst_opcode = INVOKE) (FLAT (MAP fn_insts c.ctx_functions)) =
   FILTER (\i. i.inst_opcode = INVOKE) (FLAT (MAP fn_insts d.ctx_functions))`
    by (irule gas_shadow_functions_filter >> simp[] >> fs[gas_shadow_context_def]) >>
  `FILTER (\i. i.inst_opcode = ALLOCA) (FLAT (MAP fn_insts c.ctx_functions)) =
   FILTER (\i. i.inst_opcode = ALLOCA) (FLAT (MAP fn_insts d.ctx_functions))`
    by (irule gas_shadow_functions_filter >> simp[] >> fs[gas_shadow_context_def]) >>
  simp[unit_alloca_budget_def]
QED
