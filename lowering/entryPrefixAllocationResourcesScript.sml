(* Allocation resources before positional registration, uniformly in the PC. *)
Theory entryPrefixAllocationResources
Ancestors
  entryValidatedResources actualEntryAllocationFrame moduleLoweringProps allocaFrontierBound
  allocaBudgetProps contextCodegenRel fcgPostorder fcgCorrectnessProof
  fcgDefs vyperCompiler venomWf venomInst venomMemProofs allocaHistory
  vyperLoweringCorrect exprLoweringProps fragExec arithmetic list

Theorem zero_frontier_alloca_frontier_inv:
  lookup_function func.fn_name ctx.ctx_functions = SOME func /\
  (!g. TC (fn_directly_calls ctx) func.fn_name g ==>
       ~TC (fn_directly_calls ctx) g g) /\
  s.vs_alloca_next = 0 ==>
  alloca_frontier_inv ctx func site s
Proof
  strip_tac >> simp[alloca_frontier_inv_def] >>
  `MEM func ctx.ctx_functions` by metis_tac[lookup_function_MEM] >>
  drule remaining_alloca_budget_frame >>
  disch_then (qspec_then `s` assume_tac) >>
  qmatch_goalsub_abbrev_tac `CARD below * frame` >>
  `CARD below <= LENGTH (FILTER (\i. i.inst_opcode = INVOKE)
     (FLAT (MAP fn_insts ctx.ctx_functions)))` by
    simp[Abbr `below`, call_targets_card] >>
  `CARD below * frame <= LENGTH (FILTER (\i. i.inst_opcode = INVOKE)
     (FLAT (MAP fn_insts ctx.ctx_functions))) * frame` by
    (irule LESS_MONO_MULT >> simp[]) >>
  `remaining_alloca_budget (fn_insts func) s <= frame` by
    simp[Abbr `frame`, unit_alloca_frame_def] >>
  `unit_alloca_budget ctx =
   (1 + LENGTH (FILTER (\i. i.inst_opcode = INVOKE)
      (FLAT (MAP fn_insts ctx.ctx_functions)))) * frame` by
    simp[unit_alloca_budget_def, Abbr `frame`] >>
  qpat_x_assum `unit_alloca_budget ctx = _` (fn th =>
    pure_rewrite_tac[th, RIGHT_ADD_DISTRIB, MULT_CLAUSES]) >>
  decide_tac
QED

Theorem validated_entry_alloca_frontier_inv:
  lowering_context_ok ctx /\ ctx.ctx_entry = SOME name /\
  lookup_function name ctx.ctx_functions = SOME func /\
  s.vs_alloca_next = 0 ==>
  alloca_frontier_inv ctx func site s
Proof
  strip_tac >>
  drule lowering_context_ok_bridge >> strip_tac >>
  drule lowering_context_ok_integrity >> strip_tac >>
  `ctx_wf ctx` by
    (simp[ctx_wf_def, ctx_has_entry_def, ctx_fn_names_def, MEM_MAP] >>
     metis_tac[lookup_function_MEM, lookup_function_result_name]) >>
  `func.fn_name = name` by metis_tac[lookup_function_result_name] >>
  `fcg_is_reachable (fcg_analyze ctx) name` by
    (irule fcg_analyze_reachable_complete_proof >>
     simp[fcg_path_def, ctx_fn_names_def] >>
     metis_tac[lookup_function_mem]) >>
  irule zero_frontier_alloca_frontier_inv >> simp[] >>
  rpt strip_tac >>
  `fcg_is_reachable (fcg_analyze ctx) g` by
    metis_tac[reachable_fcg_acyclic_tc_rank] >>
  metis_tac[reachable_fcg_acyclic_no_reachable_cycle]
QED

Theorem runtime_prefix_allocation_resources:
  lower_vyper_runtime_unit tops pol = SOME unit /\
  initial_venom_state_rel tops am tx vs /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
  vars_pc_only (vs with <| vs_prev_bb := NONE; vs_current_bb := elbl;
                          vs_inst_idx := 0 |>) t ==>
  alloca_inv t /\ alloca_frontier_inv unit.cu_context func site t /\
  t.vs_allocas = FEMPTY /\ t.vs_alloca_next = 0 /\
  (!id. FLOOKUP t.vs_allocas id = NONE)
Proof
  strip_tac >>
  `vs.vs_allocas = FEMPTY /\ vs.vs_alloca_next = 0` by
    gvs[initial_venom_state_rel_def] >>
  `t.vs_allocas = FEMPTY` by
    (drule vars_pc_only_allocas >> simp[]) >>
  `t.vs_alloca_next = 0` by
    (qpat_x_assum `vars_pc_only _ _` mp_tac >>
     simp[vars_pc_only_def] >> strip_tac >>
     pop_assum (mp_tac o Q.AP_TERM `\s. s.vs_alloca_next`) >> simp[]) >>
  simp[alloca_inv_empty_proof] >>
  drule lower_vyper_runtime_unit_run_lowering >> strip_tac >>
  drule run_lowering_context_ok >> strip_tac >>
  drule run_lowering_entry >> strip_tac >> gvs[] >>
  irule validated_entry_alloca_frontier_inv >> simp[] >> metis_tac[]
QED

Theorem runtime_entry_allocation_code_resources:
  lower_vyper_runtime_unit tops pol = SOME unit /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME func ==>
  unit_alloca_budget unit.cu_context < dimword (:256) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts func))
Proof
  strip_tac >>
  drule lower_vyper_runtime_unit_run_lowering >> strip_tac >>
  conj_tac >- (drule run_lowering_alloca_budget >> simp[]) >>
  drule run_lowering_context_ok >> strip_tac >>
  drule lowering_context_ok_static_integrity >> strip_tac >>
  irule ctx_inst_ids_distinct_fn >> simp[] >>
  metis_tac[lookup_function_MEM]
QED

Theorem empty_allocas_history_prefix:
  s.vs_allocas = FEMPTY /\
  (!bb k inst. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    k < s.vs_inst_idx /\ get_instruction bb k = SOME inst ==>
    inst.inst_opcode <> ALLOCA) ==>
  alloca_history func s
Proof
  simp[alloca_history_def, alloca_block_order_def] >> metis_tac[]
QED
