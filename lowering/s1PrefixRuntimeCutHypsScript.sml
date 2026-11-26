(* Static premises of the request cut, independent of the source trace. *)
Theory s1PrefixRuntimeCutHyps
Ancestors
  loweringJointPrefixHistory loweringMemCorrect vyperLoweringCorrect
  entryRejectCode e2eDefs o1PipelineCompose o1PassContract staticLayoutDefs
  ptrDiscipline unitMemInv lowerDloadDefs words list

Theorem runtime_request_cut_entry_hyps:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  initial_venom_state_rel tops am tx vs /\ code_layout_valid vs /\
  vs.vs_fmp = vs.vs_initial_fmp /\
  unit_alloca_budget unit.cu_context + 32 * ctx_dload_count unit.cu_context <=
    w2n vs.vs_initial_fmp ==>
  ?func P.
    unit.cu_context.ctx_entry = SOME "__entry" /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
    fn_entry_label func = SOME "__entry" /\ ~vs.vs_halted /\
    (!f. MEM f unit.cu_context.ctx_functions ==>
      ALL_DISTINCT (fn_labels f) /\
      !bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
    EVERY (\f. fn_ptr_ok P f /\ fn_ptr_ok P (reachable_fn f)) unit.cu_context.ctx_functions /\
    reserved_intervals_wf unit.cu_context.ctx_global_reserved /\
    EVERY (\f. f.fn_eom = NONE) unit.cu_context.ctx_functions /\
    fmp_free_ctx unit.cu_context /\ fixed_region_reserved 0 unit.cu_context /\
    mem_inv dload_headroom_ok unit.cu_context vs /\
    w2n vs.vs_initial_fmp <= w2n vs.vs_fmp /\ code_layout_valid vs
Proof
  strip_tac >>
  drule lower_vyper_runtime_unit_context_entry >> strip_tac >>
  rename1 `lookup_function "__entry" _ = SOME func` >>
  drule_all lower_vyper_runtime_unit_entry_label >> strip_tac >>
  qspecl_then [`tops`, `rpolicy`, `unit`] mp_tac
    lower_vyper_runtime_unit_recorder_shape >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule lower_vyper_runtime_unit_fn_ptr_ok >> strip_tac >>
  rename1 `EVERY (fn_ptr_ok P) _` >>
  `EVERY (\f. fn_ptr_ok P f /\ fn_ptr_ok P (reachable_fn f))
    unit.cu_context.ctx_functions` by fs[EVERY_MEM] >>
  drule lower_vyper_runtime_unit_global_reserved >> strip_tac >>
  drule lower_vyper_runtime_unit_raw_defaults >> strip_tac >>
  `?art. check_contract F am.layouts tx.target [(NONE, tops)] = SOME art` by
    (fs[source_typing_ok_def] >> metis_tac[]) >>
  drule_all lower_vyper_runtime_unit_checked_source_shape >> strip_tac >>
  drule_all source_fmp_free >> strip_tac >>
  `mem_inv dload_headroom_ok unit.cu_context vs` by
    (irule lower_vyper_runtime_unit_dload_headroom_ok >> metis_tac[]) >>
  `~vs.vs_halted` by fs[initial_venom_state_rel_def] >>
  qexistsl_tac [`func`, `P`] >>
  simp[reserved_intervals_wf_def, fixed_region_reserved_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED
