(* A piece of S1 (loweringRuntimeCorrect's lower_vyper_runtime_unit_correct). *)
Theory externalEntryValueRevert
Ancestors
  entryValueRejectFacts entrySourcePackages entryRejectCode entryPrefixPtr entryValueRevertPtr
  entryChecksLayout entryChecksPassPtr
  fragGasOriginPtr fragGasOrigin fragGasPathPtr gasEvents gasCount memSafeRun instMemFrontier
  loweringStateRelDefs ptrDiscipline ptrSafeRun actualEntryAllocationFrame
  moduleLoweringProps entryReachBodyFmp
  sourceUnitExecution gasShadowRunLowering gasShadowUnitGuards gasShadowUnit
  gasShadowModuleDefs vyperCall
  list pair fragExec
  compileEnv compileVyper moduleLowering
  e2eDefs supportedProgram vyperLoweringCorrect
  vyperTypeSystem
  vyperInterpreter vyperState vyperContext
  venomInst venomState venomExecSemantics

val _ = Parse.hide "body";

(* The source fails to move the call value only for a nonpayable function
   called with value: value_transfer_ok rules out a failed transfer. *)
Theorem send_call_value_fails[local]:
  !mut srcs layouts tx am env orc e es.
    value_transfer_ok tx am.accounts /\
    send_call_value mut (initial_evaluation_context srcs layouts tx NONE)
      (initial_state am [env] with <| outcomes := orc; requests := [] |>) =
      (INR e, es) ==>
    mut <> Payable /\ tx.value <> 0
Proof
  rpt gen_tac >>
  simp[send_call_value_def, transfer_value_def, value_transfer_ok_def,
       initial_evaluation_context_def, initial_state_def] >>
  rw[] >>
  gvs[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
      vyperStateTheory.return_def, vyperStateTheory.assert_def,
      vyperStateTheory.check_def, get_accounts_def, update_accounts_def,
      AllCaseEqs()]
QED

(* Rejection precedes defaults, argument binding and all storage reads. *)
Theorem external_value_reject_trace[local]:
  source_deployment_rel tops am tx /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut, F, args, [], ret, fbody) /\
  LENGTH tx.args = LENGTH args /\
  mut <> Payable /\ tx.value <> 0 ==>
  !gs. call_external_trace orc gs am tx =
    (INR (Error (RuntimeError "not Payable")), am, [], [])
Proof
  rw[source_deployment_rel_def] >>
  simp[call_external_trace_def, find_function_module_def,
       lookup_exported_function_def, get_self_code_def, get_module_code_def,
       initial_evaluation_context_def, call_external_function_trace_def,
       send_call_value_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.check_def,
       vyperStateTheory.assert_def, vyperStateTheory.raise_def,
       initial_state_def]
QED

Theorem external_value_reject_dispatch[local]:
  lower_vyper_runtime_unit tops rp = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
  initial_venom_state_rel tops am tx vs /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) /\
  send_call_value mut
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [env] with
      <| outcomes := SOME vs.vs_outcomes; requests := [] |>) = (INR e,st) ==>
  ?func opened checked min_cds tt G tn.
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
    fn_entry_label func = SOME "__entry" /\
    ~ctx_has_dalloca unit.cu_context /\
    compile_entry_checks min_cds F opened = ((),checked) /\
    fn_has_code opened checked func /\ opened.cs_current_insts = [] /\
    ~block_is_terminated opened /\ fresh_vars_wrt opened tt /\
    ~tt.vs_halted /\ tt.vs_current_bb = opened.cs_current_bb /\
    tt.vs_inst_idx = 0 /\ allocas_from 0 tt /\
    tt.vs_call_ctx.cc_callvalue <> 0w /\
    (!D explicit. gas_origin_ptr_path
      (D,0,explicit,unit.cu_context,func,[])
      (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                 vs_inst_idx := 0|>,FEMPTY,entry_taint) [] (OK tt,G,tn)) /\
    (!D. (!fuel. ptr_safe_blocks D 0 fuel unit.cu_context func [] G tn tt) ==>
      !fuel. ptr_safe_blocks D 0 fuel unit.cu_context func [] FEMPTY entry_taint
      (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>))
Proof
  strip_tac >>
  drule_all entry_runtime_no_dalloca >> strip_tac >>
  drule lower_vyper_runtime_unit_context_entry >> strip_tac >>
  drule_all entry_value_reject_callvalue >> strip_tac >>
  drule_all lower_runtime_selected_source_packages >> strip_tac >>
  drule_all run_lowering_entry_label >> strip_tac >>
  drule_all run_lowering_selected_entry_code >> strip_tac >>
  drule_all valid_call_linear_dispatch_target >>
  disch_then (qspec_then `fl` assume_tac) >>
  `compile_entry_checks mc F sc = ((),sk)` by
    (qpat_x_assum `compile_entry_checks _ _ _ = _` mp_tac >> simp[]) >>
  drule_all compile_entry_checks_nonpayable_head >> strip_tac >>
  `phi_prefix_length bb.bb_instructions = 0` by
    (Cases_on `bb.bb_instructions` >>
     gvs[get_instruction_def, phi_prefix_length_def]) >>
  qabbrev_tac `ss = vs with <|vs_prev_bb := NONE;
    vs_current_bb := "__entry"; vs_inst_idx := 0|>` >>
  `fresh_vars_wrt sf ss /\ ~ss.vs_halted /\ allocas_from 0 ss /\
   LENGTH ss.vs_call_ctx.cc_calldata < dimword (:256)` by
    (drule_all initial_entry_dispatch_scalars >>
     disch_then (qspecl_then [`0`, `"__entry"`, `sf`] mp_tac) >>
     simp[Abbr `ss`]) >>
  `EVERY (\(sel,lbl). sel < 2 ** 32)
    (MAP (\(sel,lbl,z). (sel,lbl)) sels)` by
    (qspecl_then [`type_env tops`, `FST (classify_functions tops)`]
       mp_tac entryDispatchPropsTheory.linear_selectors_lt >> simp[]) >>
  drule compile_selector_dispatch_linear_ptr_endpoint >>
  disch_then (qspecl_then [`entry_taint`, `ss`, `0`, `fn`] mp_tac) >>
  disch_then (qspecl_then [`unit.cu_context`, `[]`, `FEMPTY`] mp_tac) >>
  (impl_tac >-
    (simp[Abbr `ss`] >> rpt strip_tac >> gvs[])) >>
  strip_tac >>
  `fresh_vars_wrt sc tt` by
    (gvs[fresh_vars_wrt_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `allocas_from 0 tt /\ tt.vs_call_ctx.cc_callvalue <> 0w` by
    (drule vars_pc_only_allocas >>
     drule vars_pc_only_fields >> simp[Abbr `ss`] >>
     fs[allocas_from_def] >> metis_tac[]) >>
  drule_all entryDispatchPtrTheory.compile_selector_dispatch_linear_layout >> strip_tac >>
  qexistsl_tac [`fn`, `sc`, `sk`, `mc`, `tt`, `G'`, `tn'`] >>
  simp[block_is_terminated_def, Abbr `ss`] >>
  rpt strip_tac >>
  irule ptr_safe_blocks_nonphi_run >>
  conj_tac >- metis_tac[] >>
  simp[] >>
  qexistsl_tac [`b0`, `mk_inst sf.cs_next_id CALLDATASIZE []
    [STRING #"%" (toString sf.cs_next_var)]`] >>
  gvs[mk_inst_def]
QED

Theorem nonpayable_check_joint_reject:
  compile_entry_checks m F opened = ((),checked) /\
  fn_has_code opened checked fn /\ opened.cs_current_insts = [] /\
  ~block_is_terminated opened /\ fresh_vars_wrt opened s /\
  ~s.vs_halted /\ s.vs_current_bb = opened.cs_current_bb /\
  s.vs_inst_idx = 0 /\ allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  s.vs_call_ctx.cc_callvalue <> 0w ==>
  ?t G' tn'.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (Abort Revert_abort t,G',tn')) /\
    (!D fuel. ptr_safe_blocks D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  drule_all compile_entry_checks_split >> strip_tac >> fs[] >>
  drule_all compile_entry_checks_value_layout >> strip_tac >>
  qabbrev_tac `cs1 = opened with cs_next_var := SUC opened.cs_next_var` >>
  qabbrev_tac `two = opened with cs_next_var := SUC (SUC opened.cs_next_var)` >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  fs[] >> drule callvalue_ptr_endpoint >>
  disch_then (qspec_then `STRING #"%" (toString opened.cs_next_var)` mp_tac) >>
  disch_then (qspecl_then [`opened.cs_next_id`, `ctx`, `opened`, `cs1`] mp_tac) >>
  disch_then (qspecl_then [`lo`, `PG`, `G`, `tn`] mp_tac) >>
  (impl_tac >- gvs[Abbr `cs1`]) >>
  disch_then (qx_choosel_then [`value_state`, `value_ghost`, `value_taint`]
    strip_assume_tac) >>
  `!fuel. step_inst fuel ctx
     (mk_inst (opened.cs_next_id + 1) ISZERO
       [Var (STRING #"%" (toString opened.cs_next_var))]
       [STRING #"%" (toString (opened.cs_next_var + 1))]) value_state =
     OK (update_var (STRING #"%" (toString (opened.cs_next_var + 1))) 0w value_state)` by
    simp[step_inst_non_invoke, step_inst_base_opcode_eqs, mk_inst_def,
         exec_pure1_def, eval_operand_def, lookup_var_def,
         update_var_def, finite_mapTheory.FLOOKUP_UPDATE, bool_to_word_def] >>
  drule dispatch_scalar_update_ptr_endpoint >>
  disch_then (qspecl_then [`fn`, `bb`] mp_tac) >>
  disch_then (qspecl_then [`cs1`, `two`, `lo`, `PG`, `value_ghost`, `value_taint`] mp_tac) >>
  (impl_tac >- gvs[Abbr `cs1`, Abbr `two`, arithmeticTheory.ADD1]) >>
  disch_then (qx_choosel_then [`check_state`, `check_ghost`, `check_taint`]
    strip_assume_tac) >>
  qpat_x_assum `value_state = _` kall_tac >>
  qpat_x_assum `check_state = _` kall_tac >>
  qpat_x_assum `value_ghost = _` kall_tac >> qpat_x_assum `value_taint = _` kall_tac >>
  qpat_x_assum `check_ghost = _` kall_tac >> qpat_x_assum `check_taint = _` kall_tac >>
  qabbrev_tac `ai = mk_inst (opened.cs_next_id + 2) ASSERT
    [Var (STRING #"%" (toString (opened.cs_next_var + 1)))] []` >>
  `step_inst 0 ctx ai check_state = Abort Revert_abort
    (revert_state (set_returndata [] check_state))` by
    simp[Abbr `ai`, mk_inst_def, step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  `!D explicit. gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG)
    (check_state,check_ghost,check_taint) []
    (Abort Revert_abort (revert_state (set_returndata [] check_state)),check_ghost,check_taint)` by
    (rpt gen_tac >> simp[gas_origin_ptr_edge_def] >>
     conj_tac
     >- (pure_rewrite_tac[gas_origin_edge_def] >>
         conj_tac >- simp[] >>
         qexistsl_tac [`0`, `bb`, `ai`,
           `Abort Revert_abort (revert_state (set_returndata [] check_state))`] >>
         simp[exit_result_def] >>
         conj_tac >- gvs[] >>
         simp[Abbr `ai`, gas_events_step_def, mk_inst_def,
              mem_safe_step_def] >> disj2_tac >>
         irule below_frontier_no_ranges >> simp[]) >>
     simp[gas_path_ptr_edge_def] >>
     qexistsl_tac [`0`, `ai`] >>
     simp[exit_result_def] >> conj_tac >- gvs[] >>
     simp[Abbr `ai`, gas_count_step_def, mk_inst_def,
          ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          codegenRelTheory.source_memory_write_ranges_def,
          contextCodegenRelTheory.source_memory_read_ranges_def]) >>
  qexistsl_tac [`revert_state (set_returndata [] check_state)`, `check_ghost`, `check_taint`] >>
  conj_tac
  >- (rpt gen_tac >>
      `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (check_state,check_ghost,check_taint) []
        (Abort Revert_abort (revert_state (set_returndata [] check_state)),check_ghost,check_taint)` by
        metis_tac[gas_origin_ptr_path_rules, exit_result_def] >>
      metis_tac[gas_origin_ptr_path_append, APPEND_NIL]) >>
  rpt gen_tac >> irule ptr_safe_blocks_nonphi_run >>
  conj_tac
  >- (irule entryChecksPtrTheory.compile_entry_checks_value_revert_ptr_safe >>
      simp[] >> qexistsl_tac [`m`, `opened`, `checked`] >> simp[]) >>
  simp[] >> qexistsl_tac [`mk_inst opened.cs_next_id CALLVALUE []
    [STRING #"%" (toString opened.cs_next_var)]`] >>
  gvs[mk_inst_def]
QED

Theorem external_value_reject_target[local]:
  lower_vyper_runtime_unit tops rp = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
  initial_venom_state_rel tops am tx vs /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) /\
  send_call_value mut
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [env] with
      <| outcomes := SOME vs.vs_outcomes; requests := [] |>) = (INR e,st) ==>
  ?func t G tn.
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
    fn_entry_label func = SOME "__entry" /\
    (!D explicit. gas_origin_ptr_path
      (D,0,explicit,unit.cu_context,func,[])
      (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                 vs_inst_idx := 0|>,FEMPTY,entry_taint) []
      (Abort Revert_abort t,G,tn)) /\
    (!D fuel. ptr_safe_blocks D 0 fuel unit.cu_context func [] FEMPTY entry_taint
      (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                 vs_inst_idx := 0|>))
Proof
  strip_tac >> drule_all external_value_reject_dispatch >> strip_tac >>
  drule_all nonpayable_check_joint_reject >>
  disch_then (qspecl_then [`tn`, `[]`, `G`] mp_tac) >> strip_tac >>
  qexistsl_tac [`func`, `t`, `G'`, `tn'`] >> simp[] >>
  rpt gen_tac >> metis_tac[gas_origin_ptr_path_append, APPEND_NIL]
QED

(* The selected rejection run fixes empty GAS marks and its terminal endpoint
   before any storage horizon is introduced. *)
Theorem external_entry_value_revert:
  !tops rpolicy unit am tx ret vs mut args fbody env e st.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
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
  `value_transfer_ok tx am.accounts` by fs[initial_venom_state_rel_def] >>
  drule_all send_call_value_fails >> strip_tac >>
  `LENGTH tx.args = LENGTH args` by metis_tac[bind_arguments_length] >>
  drule_all external_value_reject_trace >>
  disch_then (qspec_then `SOME vs.vs_outcomes` assume_tac) >>
  drule_all external_value_reject_target >> strip_tac >>
  drule lower_vyper_runtime_unit_context_entry >> strip_tac >>
  drule_all lower_runtime_selected_source_packages >> strip_tac >>
  `OPTREL gas_shadow_unit (SOME unit)
    (run_lowering sels (MAP gas_shadow_external_package exts)
      (MAP gas_shadow_internal_package ints)
      (OPTION_MAP gas_shadow_fallback_package fb) rpolicy 0 0 [] ei "__entry")` by
    (qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = SOME unit`
       (SUBST1_TAC o SYM) >> irule gas_shadow_run_lowering) >>
  Cases_on `run_lowering sels (MAP gas_shadow_external_package exts)
      (MAP gas_shadow_internal_package ints)
      (OPTION_MAP gas_shadow_fallback_package fb) rpolicy 0 0 [] ei "__entry"` >>
  gvs[optionTheory.OPTREL_def] >> rename1 `gas_shadow_unit unit shadow_unit` >>
  `gas_shadow_context unit.cu_context shadow_unit.cu_context` by
    fs[gas_shadow_unit_def] >>
  `OPTREL gas_shadow_function (SOME fn)
    (lookup_function "__entry" shadow_unit.cu_context.ctx_functions)` by
    (qpat_x_assum `lookup_function "__entry" unit.cu_context.ctx_functions = _`
       (SUBST1_TAC o SYM) >>
     irule gas_shadow_lookup_function >> fs[gas_shadow_context_def]) >>
  Cases_on `lookup_function "__entry" shadow_unit.cu_context.ctx_functions` >>
  gvs[optionTheory.OPTREL_def] >>
  rename1 `gas_shadow_function fn shadow_fn` >>
  simp[source_unit_execution_correct_def] >> qexists_tac `[]` >>
  simp[source_unit_execution_correct_at_def] >>
  qexistsl_tac [`shadow_unit.cu_context`, `shadow_fn`] >>
  simp[] >>
  conj_tac >- metis_tac[venomInstTheory.lookup_function_MEM] >>
  conj_tac >- metis_tac[venomInstTheory.lookup_function_MEM] >>
  disj2_tac >> disj2_tac >> qexists_tac `Abort Revert_abort t` >>
  simp[exit_result_def, external_call_result_rel_def] >>
  conj_tac
  >- simp[vyperStorageFootprintTheory.storage_trace_domain_def,
          vyperStorageFootprintTheory.valid_horizon_def,
          vyperStorageFootprintTheory.storage_trace_horizon_def,
          vyperStorageFootprintTheory.storage_trace_regions_def,
          vyperStorageFootprintTheory.storage_trace_locks_def,
          vyperStorageFootprintTheory.storage_observations_ok_def,
          vyperStorageFootprintTheory.regions_consistent_def,
          vyperStorageFootprintTheory.storage_locks_separated_def,
          vyperStorageFootprintTheory.storage_well_formed_on_def,
          vyperStorageFootprintTheory.storage_roots_fit_def,
          vyperStorageFootprintTheory.storage_trace_backends_well_formed_def] >>
  metis_tac[gas_origin_ptr_path_projections]
QED

