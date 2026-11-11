(* Acceptance projections for the same __entry function used by checks. *)
Theory entryReachBodyRuntimeResources
Ancestors
  compileVyper vyperCompiler ctorDeployMemoryFrontier allocaFrontierBound
  venomWf venomInst list

Theorem caller_runtime_context_ok:
  lower_vyper_runtime_unit tops policy = SOME unit ==>
  lowering_context_ok unit.cu_context
Proof
  metis_tac[vyperLoweringCorrectTheory.lower_vyper_runtime_unit_context_entry]
QED

Theorem caller_runtime_entry:
  lower_vyper_runtime_unit tops policy = SOME unit ==>
  unit.cu_context.ctx_entry = SOME "__entry" /\
  ?fn. venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn
Proof
  metis_tac[vyperLoweringCorrectTheory.lower_vyper_runtime_unit_context_entry]
QED

Theorem caller_runtime_entry_integrity:
  lower_vyper_runtime_unit tops policy = SOME unit /\
  venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn ==>
  ctx_wf unit.cu_context /\ wf_invoke_targets unit.cu_context /\
  reachable_call_graph_acyclic unit.cu_context /\
  ctx_inst_ids_distinct unit.cu_context /\
  fn_inst_ids_distinct fn /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))
Proof
  strip_tac >>
  drule caller_runtime_context_ok >> strip_tac >>
  drule caller_runtime_entry >> strip_tac >>
  drule_all lowered_unit_entry_facts >> strip_tac >>
  `MEM fn unit.cu_context.ctx_functions` by
    metis_tac[lookup_function_MEM] >>
  drule_all ctx_inst_ids_distinct_fn >> strip_tac >>
  gvs[] >>
  `!bbs. MAP (\i. i.inst_id) (fn_insts_blocks bbs) =
     FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs)` by
    (Induct >> simp[fn_insts_blocks_def]) >>
  fs[fn_inst_ids_distinct_def, fn_insts_def]
QED
