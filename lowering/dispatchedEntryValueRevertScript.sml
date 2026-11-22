(*
 * S1 when the source cannot move the call value, for any calldata
 * dispatching to an external function (vyperCalldata's calldata_dispatch),
 * __default__ included: the entry reaches the payable check, which aborts.
 *
 * TOP-LEVEL:
 *   external_entry_value_revert_dispatched_nr
 *)
Theory dispatchedEntryValueRevert
Ancestors
  vyperLoweringCorrect sourceUnitExecution vyperCalldata supportedProgram
  vyperInterpreter dispatchedValueSource dispatchedValuePrefix
  dispatchedValueSelection dispatchedValueEntry dispatchedValueFallback
  entryStateRel gasShadowUnit gasShadowState
  venomInst vyperCompiler list entryRejectCode compileEnv emitHelper
  entryValueRevertPtr e2eDefs venomWf moduleLoweringProps fragGasOrigin fragGasMode

(* Both source certificates and the raw CREATE-size adapter use this same
   selected guard path, including the classified fallback. *)
Theorem dispatched_value_reject_path:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\
  ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
  source_typing_ok tops am tx /\
  calldata_dispatch tops vs.vs_call_ctx.cc_calldata =
    SOME (tx.function_name, tx.args) /\
  initial_venom_state_rel tops am tx vs /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut, nr, args, [], ret, fbody) /\
  mut <> Payable /\ vs.vs_call_ctx.cc_callvalue <> 0w ==>
  ?fn preabort.
    unit.cu_context.ctx_entry = SOME "__entry" /\
    venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME "__entry" /\ MEM fn unit.cu_context.ctx_functions /\
    (!explicit. gas_origin_path T explicit unit.cu_context fn
      (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>) []
      (Abort Revert_abort (revert_state (set_returndata [] preabort)))) /\
    !D PG G tn fuel. ptr_safe_blocks D 0 fuel unit.cu_context fn PG G tn
      (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>)
Proof
  strip_tac >>
  drule lower_vyper_runtime_unit_context_entry >> strip_tac >>
  rename1 `venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn` >>
  `MEM fn unit.cu_context.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `fn_entry_label fn = SOME "__entry"` by
    (drule_all_then ACCEPT_TAC lower_vyper_runtime_unit_entry_label) >>
  drule source_typing_ok_external_names_distinct >> strip_tac >>
  `?fb ds de opened checked min_cds.
    compile_selector_dispatch_linear
      (MAP (\(sel,lbl,z). (sel,lbl))
        (build_selectors (type_env tops) (FST (classify_functions tops)))) fb ds = ((),de) /\
    fn_has_code ds de fn /\ ds.cs_current_bb = "__entry" /\
    ds.cs_current_insts = [] /\
    compile_entry_checks min_cds F opened = ((),checked) /\
    fn_has_code opened checked fn /\ opened.cs_current_insts = [] /\
    ~block_is_terminated opened /\
    opened.cs_current_bb = linear_dispatch_target vs.vs_call_ctx.cc_calldata
      (MAP (\(sel,lbl,z). (sel,lbl))
        (build_selectors (type_env tops) (FST (classify_functions tops)))) fb` by
    suspend "installed_checks" >>
  qabbrev_tac `ss = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                            vs_inst_idx := 0|>` >>
  `allocas_below_fmp ss` by
    (irule initial_entry_allocas_below_fmp >>
     goal_assum (drule_at Any) >> simp[Abbr `ss`, vars_pc_only_def]) >>
  `fresh_vars_wrt ds ss /\ ~ss.vs_halted /\ allocas_from 0 ss /\
   LENGTH ss.vs_call_ctx.cc_calldata < dimword (:256)` by
    (drule_all initial_entry_dispatch_scalars >>
     disch_then (qspecl_then [`0`, `"__entry"`, `ds`] mp_tac) >>
     simp[Abbr `ss`]) >>
  `ss.vs_call_ctx = vs.vs_call_ctx /\ ss.vs_current_bb = ds.cs_current_bb /\
   ss.vs_inst_idx = 0` by simp[Abbr `ss`] >>
  `?preabort. !explicit. gas_origin_path T explicit unit.cu_context fn ss []
      (Abort Revert_abort (revert_state (set_returndata [] preabort)))` by
    suspend "revert_path" >>
  qexistsl_tac [`fn`,`preabort`] >> simp[GSYM markerTheory.Abbrev_def] >>
  irule installed_dispatch_value_reject_ptr >>
  asm_rewrite_tac[] >>
  qexistsl_tac [`checked`, `fb`, `min_cds`, `opened`,
    `MAP (\(sel,lbl,z). (sel,lbl))
      (build_selectors (type_env tops) (FST (classify_functions tops)))`, `ds`, `de`] >>
  gvs[entryDispatchPropsTheory.linear_selectors_lt]
QED

Resume dispatched_value_reject_path[installed_checks]:
  drule_all source_dispatched_linear_target_nr >> strip_tac
  >- (drule_all source_member_entry_check_code_nr >> strip_tac >>
      qexistsl_tac [`fb`, `ds`, `de`, `opened`, `checked`, `min_cds`] >> gvs[]) >>
  qpat_x_assum `FST (SND (SND _)) = SOME _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  drule_all source_fallback_entry_check_code_nr >> strip_tac >>
  qexistsl_tac [`fb`, `ds`, `de`, `opened`, `checked`, `0`] >> gvs[]
QED

Resume dispatched_value_reject_path[revert_path]:
  `?preabort. vars_pc_only ss preabort /\
    gas_origin_path T {} unit.cu_context fn ss []
      (Abort Revert_abort (revert_state (set_returndata [] preabort)))` by
    (irule installed_dispatch_value_reject_origin >>
     asm_rewrite_tac[] >> conj_tac >- metis_tac[] >>
     qexistsl_tac [`checked`, `fb`, `min_cds`, `opened`,
       `MAP (\(sel,lbl,z). (sel,lbl))
         (build_selectors (type_env tops) (FST (classify_functions tops)))`, `ds`, `de`] >>
     gvs[entryDispatchPropsTheory.linear_selectors_lt]) >>
  qexists_tac `preabort` >>
  drule gas_origin_path_erase >> simp[gas_marked_path_def] >>
  metis_tac[gas_path_mem_zero_origin]
QED

Finalise dispatched_value_reject_path

(* The rejecting prefix is independent of which gas shadow was supplied. *)
Theorem external_entry_value_revert_dispatched_with_nr:
  !tops rpolicy unit am tx ret vs mut nr args fbody env e st shadow_ctx.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata =
      SOME (tx.function_name, tx.args) /\
    initial_venom_state_rel tops am tx vs /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, nr, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INR e, st) /\
    gas_shadow_context unit.cu_context shadow_ctx ==>
    source_unit_execution_correct_with shadow_ctx [] tops ret am tx unit vs
Proof
  rpt strip_tac >>
  drule_all initial_entry_rejected_value >> strip_tac >>
  drule_all dispatched_value_reject_path >>
  disch_then (qx_choosel_then [`fn`,`preabort`] strip_assume_tac) >>
  `?shadow_fn. MEM shadow_fn shadow_ctx.ctx_functions /\
      gas_shadow_function fn shadow_fn` by
    (fs[gas_shadow_context_def] >> metis_tac[LIST_REL_MEM_IMP]) >>
  `value_transfer_ok tx am.accounts` by gvs[initial_venom_state_rel_def] >>
  drule_all source_dispatched_value_reject_trace_nr >> strip_tac >>
  drule_all source_dispatched_value_reject_error_nr >> strip_tac >>
  rewrite_tac[source_unit_execution_correct_with_def] >>
  qexistsl_tac [`fn`, `shadow_fn`] >>
  asm_rewrite_tac[] >> disj2_tac >>
  qexistsl_tac [`INR e`, `am`, `[]`, `[]`] >>
  asm_rewrite_tac[] >> disj2_tac >>
  qexists_tac `Abort Revert_abort (revert_state (set_returndata [] preabort))` >>
  simp[fragExecTheory.exit_result_def,
       vyperStorageFootprintTheory.storage_trace_domain_def,
       vyperStorageFootprintTheory.valid_horizon_def,
       vyperStorageFootprintTheory.storage_observations_ok_def,
       vyperStorageFootprintTheory.storage_trace_horizon_def,
       vyperStorageFootprintTheory.storage_trace_regions_def,
       vyperStorageFootprintTheory.storage_trace_locks_def,
       vyperStorageFootprintTheory.regions_consistent_def,
       vyperStorageFootprintTheory.storage_locks_separated_def,
       vyperStorageFootprintTheory.storage_well_formed_on_def,
       vyperStorageFootprintTheory.storage_roots_fit_def,
       vyperStorageFootprintTheory.storage_trace_backends_well_formed_def,
       external_call_result_rel_def]
QED

Theorem external_entry_value_revert_dispatched_nr:
  !tops rpolicy unit am tx ret vs mut nr args fbody env e st.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata =
      SOME (tx.function_name, tx.args) /\
    initial_venom_state_rel tops am tx vs /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, nr, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INR e, st) ==>
    source_unit_execution_correct tops ret am tx unit vs
Proof
  rpt strip_tac >> simp[source_unit_execution_correct_def, source_unit_execution_correct_at_def] >>
  qexistsl_tac [`[]`, `unit.cu_context`] >>
  `gas_shadow_context unit.cu_context unit.cu_context` by
    simp[gas_shadow_context_def, gas_shadow_function_def, gas_shadow_block_def,
         gas_shadow_inst_def, LIST_REL_refl] >>
  drule_all external_entry_value_revert_dispatched_with_nr >> simp[]
QED

Theorem external_entry_value_revert_dispatched:
  !tops rpolicy unit am tx ret vs mut args fbody env e st.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata =
      SOME (tx.function_name, tx.args) /\
    initial_venom_state_rel tops am tx vs /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INR e, st) ==>
    source_unit_execution_correct tops ret am tx unit vs
Proof
  rpt gen_tac >>
  MATCH_ACCEPT_TAC (Q.INST [`nr` |-> `F`] (SPEC_ALL external_entry_value_revert_dispatched_nr))
QED

Theorem external_entry_value_revert_dispatched_with:
  !tops rpolicy unit am tx ret vs mut args fbody env e st shadow_ctx.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata =
      SOME (tx.function_name, tx.args) /\
    initial_venom_state_rel tops am tx vs /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INR e, st) /\
    gas_shadow_context unit.cu_context shadow_ctx ==>
    source_unit_execution_correct_with shadow_ctx [] tops ret am tx unit vs
Proof
  rpt gen_tac >>
  MATCH_ACCEPT_TAC (Q.INST [`nr` |-> `F`] (SPEC_ALL external_entry_value_revert_dispatched_with_nr))
QED
