(*
 * S1 when the source cannot move the call value, for any calldata
 * dispatching to an external function (vyperCalldata's calldata_dispatch),
 * __default__ included: the entry reaches the payable check, which aborts.
 *
 * TOP-LEVEL:
 *   external_entry_value_revert_dispatched
 *)
Theory dispatchedEntryValueRevert
Ancestors
  vyperLoweringCorrect sourceUnitExecution vyperCalldata supportedProgram
  vyperInterpreter dispatchedValueSource dispatchedValuePrefix
  dispatchedValueSelection dispatchedValueEntry dispatchedValueFallback
  entryStateRel entryReachBodyFmp gasShadowUnit gasShadowState
  venomInst vyperCompiler list runtimeExternalPackageCode compileEnv emitHelper
  entryValueRevertPtr e2eDefs venomWf

Theorem external_entry_value_revert_dispatched:
  !tops rpolicy unit am tx ret vs mut args fbody env e st.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
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
  rpt strip_tac >>
  drule lower_vyper_runtime_unit_context_entry >> strip_tac >>
  rename1 `venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn` >>
  `MEM fn unit.cu_context.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `?elbl. fn_entry_label fn = SOME elbl` by
    (gvs[lowering_context_ok_def, EVERY_MEM, fn_has_entry_def] >>
     `fn.fn_blocks <> []` by metis_tac[] >>
     Cases_on `fn.fn_blocks` >> gvs[fn_entry_label_def, entry_block_def]) >>
  `fn_entry_label fn = SOME "__entry"` by
    (drule_all source_runtime_external_packages >> strip_tac >>
     gvs[fresh_label_def, initial_compile_state_def]) >>
  drule_all initial_entry_rejected_value >> strip_tac >>
  `value_transfer_ok tx am.accounts` by gvs[initial_venom_state_rel_def] >>
  drule_all source_dispatched_value_reject_trace >> strip_tac >>
  drule_all source_dispatched_value_reject_error >> strip_tac >>
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
  `~ctx_has_dalloca unit.cu_context` by metis_tac[entry_runtime_no_dalloca] >>
  qabbrev_tac `ss = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                            vs_inst_idx := 0|>` >>
  `fresh_vars_wrt ds ss /\ ~ss.vs_halted /\ allocas_from 0 ss /\
   LENGTH ss.vs_call_ctx.cc_calldata < dimword (:256)` by
    (drule_all initial_entry_dispatch_scalars >>
     disch_then (qspecl_then [`0`, `"__entry"`, `ds`] mp_tac) >>
     simp[Abbr `ss`]) >>
  `ss.vs_call_ctx = vs.vs_call_ctx /\ ss.vs_current_bb = ds.cs_current_bb /\
   ss.vs_inst_idx = 0` by simp[Abbr `ss`] >>
  `?preabort. vars_pc_only ss preabort /\
    gas_origin_path T (gas_explicit_sites unit.cu_context unit.cu_context)
      unit.cu_context fn ss []
      (Abort Revert_abort (revert_state (set_returndata [] preabort)))` by
    (irule installed_dispatch_value_reject_origin >>
     asm_rewrite_tac[] >> conj_tac >- metis_tac[] >>
     qexistsl_tac [`checked`, `fb`, `min_cds`, `opened`,
       `MAP (\(sel,lbl,z). (sel,lbl))
         (build_selectors (type_env tops) (FST (classify_functions tops)))`, `ds`, `de`] >>
     gvs[entryDispatchPropsTheory.linear_selectors_lt]) >>
  `!D PG G tn fuel. ptr_safe_blocks D 0 fuel unit.cu_context fn PG G tn ss` by
    (irule installed_dispatch_value_reject_ptr >>
     asm_rewrite_tac[] >>
     qexistsl_tac [`checked`, `fb`, `min_cds`, `opened`,
       `MAP (\(sel,lbl,z). (sel,lbl))
         (build_selectors (type_env tops) (FST (classify_functions tops)))`, `ds`, `de`] >>
     gvs[entryDispatchPropsTheory.linear_selectors_lt]) >>
  suspend "joint_certificate"
QED

Resume external_entry_value_revert_dispatched[installed_checks]:
  drule_all source_dispatched_linear_target >> strip_tac
  >- (drule_all source_member_entry_check_code >> strip_tac >>
      qexistsl_tac [`fb`, `ds`, `de`, `opened`, `checked`, `min_cds`] >> gvs[]) >>
  qpat_x_assum `FST (SND (SND _)) = SOME _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  drule_all source_fallback_entry_check_code >> strip_tac >>
  qexistsl_tac [`fb`, `ds`, `de`, `opened`, `checked`, `0`] >> gvs[]
QED

Resume external_entry_value_revert_dispatched[joint_certificate]:
  rewrite_tac[source_unit_execution_correct_def, source_unit_execution_correct_at_def] >>
  qexists_tac `[]` >>
  qexistsl_tac [`unit.cu_context`, `fn`, `fn`] >>
  asm_rewrite_tac[] >>
  `gas_shadow_function fn fn /\ gas_shadow_context unit.cu_context unit.cu_context` by
    simp[gas_shadow_context_def, gas_shadow_function_def, gas_shadow_block_def,
         gas_shadow_inst_def, LIST_REL_refl] >>
  asm_rewrite_tac[] >> disj2_tac >>
  qexistsl_tac [`INR e`, `am`, `[]`, `[]`] >>
  asm_rewrite_tac[] >> disj2_tac >>
  qexists_tac `Abort Revert_abort (revert_state (set_returndata [] preabort))` >>
  simp[GSYM markerTheory.Abbrev_def] >>
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

Finalise external_entry_value_revert_dispatched

(* The rejecting prefix is independent of which gas shadow was supplied. *)
Theorem external_entry_value_revert_dispatched_with:
  !tops rpolicy unit am tx ret vs mut args fbody env e st shadow_ctx.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
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
  rpt strip_tac >>
  drule lower_vyper_runtime_unit_context_entry >> strip_tac >>
  rename1 `venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn` >>
  `MEM fn unit.cu_context.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `?shadow_fn. MEM shadow_fn shadow_ctx.ctx_functions /\
      gas_shadow_function fn shadow_fn` by
    (fs[gas_shadow_context_def] >> metis_tac[LIST_REL_MEM_IMP]) >>
  `?elbl. fn_entry_label fn = SOME elbl` by
    (gvs[lowering_context_ok_def, EVERY_MEM, fn_has_entry_def] >>
     `fn.fn_blocks <> []` by metis_tac[] >>
     Cases_on `fn.fn_blocks` >> gvs[fn_entry_label_def, entry_block_def]) >>
  `fn_entry_label fn = SOME "__entry"` by
    (drule_all source_runtime_external_packages >> strip_tac >>
     gvs[fresh_label_def, initial_compile_state_def]) >>
  drule_all initial_entry_rejected_value >> strip_tac >>
  `value_transfer_ok tx am.accounts` by gvs[initial_venom_state_rel_def] >>
  drule_all source_dispatched_value_reject_trace >> strip_tac >>
  drule_all source_dispatched_value_reject_error >> strip_tac >>
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
  `~ctx_has_dalloca unit.cu_context` by metis_tac[entry_runtime_no_dalloca] >>
  qabbrev_tac `ss = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                            vs_inst_idx := 0|>` >>
  `fresh_vars_wrt ds ss /\ ~ss.vs_halted /\ allocas_from 0 ss /\
   LENGTH ss.vs_call_ctx.cc_calldata < dimword (:256)` by
    (drule_all initial_entry_dispatch_scalars >>
     disch_then (qspecl_then [`0`, `"__entry"`, `ds`] mp_tac) >>
     simp[Abbr `ss`]) >>
  `ss.vs_call_ctx = vs.vs_call_ctx /\ ss.vs_current_bb = ds.cs_current_bb /\
   ss.vs_inst_idx = 0` by simp[Abbr `ss`] >>
  `?preabort. vars_pc_only ss preabort /\
    gas_origin_path T (gas_explicit_sites unit.cu_context shadow_ctx)
      unit.cu_context fn ss []
      (Abort Revert_abort (revert_state (set_returndata [] preabort)))` by
    (irule installed_dispatch_value_reject_origin >>
     asm_rewrite_tac[] >> conj_tac >- metis_tac[] >>
     qexistsl_tac [`checked`, `fb`, `min_cds`, `opened`,
       `MAP (\(sel,lbl,z). (sel,lbl))
         (build_selectors (type_env tops) (FST (classify_functions tops)))`, `ds`, `de`] >>
     gvs[entryDispatchPropsTheory.linear_selectors_lt]) >>
  `!D PG G tn fuel. ptr_safe_blocks D 0 fuel unit.cu_context fn PG G tn ss` by
    (irule installed_dispatch_value_reject_ptr >>
     asm_rewrite_tac[] >>
     qexistsl_tac [`checked`, `fb`, `min_cds`, `opened`,
       `MAP (\(sel,lbl,z). (sel,lbl))
         (build_selectors (type_env tops) (FST (classify_functions tops)))`, `ds`, `de`] >>
     gvs[entryDispatchPropsTheory.linear_selectors_lt]) >>
  suspend "joint_certificate"
QED

Resume external_entry_value_revert_dispatched_with[installed_checks]:
  drule_all source_dispatched_linear_target >> strip_tac
  >- (drule_all source_member_entry_check_code >> strip_tac >>
      qexistsl_tac [`fb`, `ds`, `de`, `opened`, `checked`, `min_cds`] >> gvs[]) >>
  qpat_x_assum `FST (SND (SND _)) = SOME _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  drule_all source_fallback_entry_check_code >> strip_tac >>
  qexistsl_tac [`fb`, `ds`, `de`, `opened`, `checked`, `0`] >> gvs[]
QED

Resume external_entry_value_revert_dispatched_with[joint_certificate]:
  rewrite_tac[source_unit_execution_correct_with_def] >>
  qexistsl_tac [`fn`, `shadow_fn`] >>
  asm_rewrite_tac[] >> disj2_tac >>
  qexistsl_tac [`INR e`, `am`, `[]`, `[]`] >>
  asm_rewrite_tac[] >> disj2_tac >>
  qexists_tac `Abort Revert_abort (revert_state (set_returndata [] preabort))` >>
  simp[GSYM markerTheory.Abbrev_def] >>
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

Finalise external_entry_value_revert_dispatched_with
