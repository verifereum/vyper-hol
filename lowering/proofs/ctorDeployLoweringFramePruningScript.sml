Theory ctorDeployLoweringFramePruning
Ancestors
  fcgPruning fcgDefs venomInst list

Theorem get_invoke_targets_no_invoke:
  !xs. EVERY (\i. i.inst_opcode <> INVOKE) xs ==>
       get_invoke_targets xs = []
Proof
  Induct >> simp[get_invoke_targets_def]
QED

Theorem fcg_scan_function_no_invoke:
  EVERY (\i. i.inst_opcode <> INVOKE) (fn_insts fn) ==>
  fcg_scan_function fn = []
Proof
  simp[fcg_scan_function_def, get_invoke_targets_no_invoke]
QED

Theorem fcg_analyze_no_invoke_entry:
  ctx.ctx_entry = SOME name /\
  lookup_function name ctx.ctx_functions = SOME fn /\
  EVERY (\i. i.inst_opcode <> INVOKE) (fn_insts fn) ==>
  (fcg_analyze ctx).fcg_reachable = [name]
Proof
  rpt strip_tac >>
  drule fcg_scan_function_no_invoke >> strip_tac >>
  simp[fcg_analyze_def, Once fcg_dfs_def, fcg_visit_def,
       fcg_record_edges_def] >>
  simp[fcg_dfs_def, fcg_empty_def]
QED

Theorem filter_lookup_distinct_name[local]:
  !fns name fn.
    ALL_DISTINCT (MAP (\f. f.fn_name) fns) /\
    lookup_function name fns = SOME fn ==>
    FILTER (\f. f.fn_name = name) fns = [fn]
Proof
  Induct >> simp[lookup_function_def, FIND_thm] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h.fn_name = name` >> gvs[]
  >- (simp[FILTER_EQ_NIL, EVERY_MEM] >> gvs[MEM_MAP] >> metis_tac[]) >>
  first_x_assum irule >> simp[lookup_function_def]
QED

Theorem prune_no_invoke_entry_singleton:
  unit.cu_context.ctx_entry = SOME name /\
  lookup_function name unit.cu_context.ctx_functions = SOME fn /\
  ALL_DISTINCT (MAP (\f. f.fn_name) unit.cu_context.ctx_functions) /\
  EVERY (\i. i.inst_opcode <> INVOKE) (fn_insts fn) ==>
  (prune_unit_fcg_unreachable unit (fcg_analyze unit.cu_context)).
    cu_context.ctx_functions = [fn]
Proof
  rpt strip_tac >>
  drule_all fcg_analyze_no_invoke_entry >> strip_tac >>
  simp[prune_unit_fcg_unreachable_def, fcg_is_reachable_def] >>
  irule filter_lookup_distinct_name >> simp[]
QED

Theorem prune_no_invoke_entry_call_free:
  unit.cu_context.ctx_entry = SOME name /\
  lookup_function name unit.cu_context.ctx_functions = SOME fn /\
  ALL_DISTINCT (MAP (\f. f.fn_name) unit.cu_context.ctx_functions) /\
  EVERY (\i. i.inst_opcode <> INVOKE) (fn_insts fn) /\
  EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) (fn_insts fn) ==>
  EVERY (\f. EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) (fn_insts f))
    (prune_unit_fcg_unreachable unit (fcg_analyze unit.cu_context)).
      cu_context.ctx_functions
Proof
  rpt strip_tac >>
  drule_all prune_no_invoke_entry_singleton >> strip_tac >> gvs[]
QED
