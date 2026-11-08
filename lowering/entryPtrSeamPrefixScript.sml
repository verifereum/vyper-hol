(*
 * Seam of external_entry_reaches_body_ptr (loweringPtrCorrect): the entry's
 * prefix, from __entry's first block to the start of the selected external
 * function's argument registration, on a call whose value the source
 * accepted.
 *
 * The prefix is the selector dispatch (compile_selector_dispatch_linear)
 * and the selected function's entry checks (compile_entry_checks: the call
 * value check when it is nonpayable, the calldata size check), which pass:
 * send_call_value returned INL, and valid_vyper_call bounds the calldata
 * size.  They change only variables and the PC and write no memory, so the
 * ghost there carries no memory, storage, transient or immutable taint.
 * Registration (compile_register_positional_args) starts where the checks
 * end, in the same block, and the guarded body where it ends.
 *
 * The conclusion fixes the ghost (G1, tn1) the run actually reaches, not a
 * universal one: the run after it is only known safe from that ghost.
 *)
Theory entryPtrSeamPrefix
Ancestors
  selectedEntryPrefixCode entryChecksPassPtr entryPrefixPtr sourceValueRejection
  entryChecksProps loweringShapeProps loweringShapeSource o1PipelineCorrect
  supportedNames supportedProgramProps loweringShapeDefs unitShapeDefs venomExecProofs list
  entryValueRevertPtr entryDispatchPtr sourceEntryCode selectedBodyCode
  rawEntryCode entryCheckIntervals sourceEntrySelection actualRegistrationCode
  entryLocals actualEntryAllocationFrame
  vyperCompiler selectorDispatch moduleLoweringProps stmtLoweringProps
  exprLoweringProps vyperInterpreter vyperContext venomExecSemantics
  venomState compileEnv e2eDefs supportedProgram compileVyper fragExec
  venomInst contextCodegenRel ptrDiscipline ptrSafeRun vyperLoweringCorrect
  loweringRuntimeCorrect bodyPtrDefs moduleLowering venomWf

(* Entry-to-registration prefix seam.
   Hints (not binding):
   - Code: source_selected_entry_check_code and source_selected_body_code
     come from the same packaged external member; compile_external_fn_bodies
     runs compile_entry_checks and then compile_external_function_body
     (registration, then compile_guarded_body) in that member's block, so
     registration starts at `checked`.  fn_inst_ids_distinct follows from
     lowering_context_ok's ctx_inst_ids_distinct (run_lowering_context_ok);
     local_ptrs_reserved from entryLocals' compile_register_positional_args_reserved.
   - Run: entryDispatchPtr's compile_selector_dispatch_linear_ptr_continuation
     and compile_selector_checks_ptr_continuation take continuations for
     every ghost; this seam needs the actual ghost, so either state ghost-
     specific variants of them or thread ghost_run.  external_entry_value_revert_ptr
     (loweringPtrCorrect) is the rejecting twin of this prefix.
   - The pass path of compile_entry_checks: send_call_value = (INL (), _)
     gives mut = Payable or a zero call value (the converse of
     entryValueRevertPtr's initial_entry_rejected_value); valid_vyper_call's
     calldata_encodes gives the calldata size bound. *)
Theorem external_entry_reaches_registration_ptr:
  !tops rpolicy unit am tx ret vs mut args fbody env es0 efn elbl.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok am tx vs.vs_outcomes /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn /\
    fn_entry_label efn = SOME elbl ==>
    ?lbl cenv0 pos_args min_cds is_payable nkey ut' iv rt st cenv sa st' s1
     G1 tn1.
      set_external_package_target rpolicy.rpol_target
        (package_external_fn tops F (assign_nkeys tops 0)
           (mut, F, lookup_raw_return_or_F (NONE : num option)
                       tx.function_name External tops,
            tx.function_name, args, [], ret, fbody)) =
        (lbl, cenv0, pos_args, min_cds, is_payable, F, nkey, ut', iv, fbody,
         rt) /\
      compile_register_positional_args cenv0 pos_args 4 st = (cenv, sa) /\
      compile_guarded_body cenv F nkey ut' iv fbody rt sa = ((), st') /\
      fn_has_code st sa efn /\ fn_has_code sa st' efn /\
      fn_inst_ids_distinct efn /\
      local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
      cenv.ce_return_buf = NONE /\
      vars_pc_only
        (vs with <| vs_prev_bb := NONE; vs_current_bb := elbl;
                    vs_inst_idx := 0 |>) s1 /\
      fresh_vars_wrt st s1 /\ ~s1.vs_halted /\
      s1.vs_current_bb = st.cs_current_bb /\
      s1.vs_inst_idx = LENGTH st.cs_current_insts /\
      tn1.t_mem = {} /\ tn1.t_stor = {} /\ tn1.t_trans = {} /\
      tn1.t_imm = {} /\
      !D. (!fuel. ptr_safe_run D 0 fuel unit.cu_context efn [] G1 tn1 s1) ==>
          !fuel. ptr_safe_blocks D 0 fuel unit.cu_context efn [] FEMPTY
                   entry_taint
                   (vs with <| vs_prev_bb := NONE; vs_current_bb := elbl;
                               vs_inst_idx := 0 |>)
Proof
  rpt gen_tac >> strip_tac >>
  `tx.function_name <> "__default__"` by fs[valid_vyper_call_def] >>
  qpat_x_assum `source_storage_ok _ _ _` kall_tac >>
  qpat_x_assum `source_deployment_rel _ _ _` kall_tac >>
  qpat_x_assum `call_outcomes_ok _ _ _` kall_tac >>
  `o1_source_unit_ok unit` by
    (irule lower_vyper_runtime_unit_source_unit_ok_shape >>
     goal_assum (drule_at Any) >> conj_tac
     >- (irule supported_names_internal_names_distinct >>
         fs[supported_program_def, supported_declaration_names_def]) >>
     metis_tac[supported_program_runtime_bodies_shape_ok]) >>
  `~ctx_has_dalloca unit.cu_context` by metis_tac[o1_source_unit_ok_no_dalloca] >>
  qabbrev_tac `pkg = set_external_package_target rpolicy.rpol_target
    (package_external_fn tops F (assign_nkeys tops 0)
      (mut, F, lookup_raw_return_or_F (NONE : num option)
        tx.function_name External tops, tx.function_name, args, [], ret, fbody))` >>
  PairCases_on `pkg` >>
  `pkg0 = "fn_" ++ tx.function_name /\ pkg4 = (mut = Payable) /\
   pkg5 = F /\ pkg9 = fbody` by
    (qpat_x_assum `Abbrev _` mp_tac >>
     simp[markerTheory.Abbrev_def, set_external_package_target_def,
          package_external_fn_def] >> strip_tac >> gvs[]) >>
  fs[] >>
  `set_external_package_target rpolicy.rpol_target
    (package_external_fn tops F (assign_nkeys tops 0)
      (mut,F,lookup_raw_return_or_F (NONE:num option) tx.function_name External tops,
       tx.function_name,args,([] : expr list),ret,fbody)) =
    ("fn_" ++ tx.function_name,pkg1,pkg2,pkg3,mut = Payable,F,pkg6,pkg7,pkg8,fbody,pkg10)` by
    (qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
     simp[package_external_fn_def]) >>
  drule_all source_selected_entry_prefix_structure >> strip_tac >>
  suspend "dispatch"
QED

Resume external_entry_reaches_registration_ptr[dispatch]:
  drule_all initial_entry_dispatch_scalars >>
  disch_then (qspecl_then [`0`, `elbl`, `ds`] strip_assume_tac) >>
  qabbrev_tac `ss = vs with <|vs_prev_bb := NONE; vs_current_bb := elbl; vs_inst_idx := 0|>` >>
  qspecl_then [`type_env tops`, `FST (classify_functions tops)`]
    assume_tac entryDispatchPropsTheory.linear_selectors_lt >>
  drule compile_selector_dispatch_linear_ptr_endpoint >>
  disch_then (qspecl_then [`entry_taint`, `ss`, `0`, `efn`, `unit.cu_context`,
    `[]`, `FEMPTY`] mp_tac) >>
  (impl_tac >- simp[Abbr `ss`]) >> strip_tac >>
  rename1 `vars_pc_only ss tt` >> rename1 `tn1.t_mem = entry_taint.t_mem` >>
  rename1 `ptr_safe_blocks _ _ _ _ _ _ G1 tn1 tt` >>
  drule_all source_valid_linear_dispatch_target >> strip_tac >>
  `tt.vs_current_bb = opened.cs_current_bb /\
   tt.vs_call_ctx = vs.vs_call_ctx /\ fresh_vars_wrt opened tt` by
    (imp_res_tac vars_pc_only_fields >> fs[Abbr `ss`] >>
     irule emitHelperPropsTheory.fresh_vars_wrt_mono >>
     qexists_tac `de` >> simp[]) >>
  suspend "checks"
QED

Resume external_entry_reaches_registration_ptr[checks]:
  qabbrev_tac `raw = package_external_fn tops F (assign_nkeys tops 0)
    (mut,F,lookup_raw_return_or_F (NONE:num option) tx.function_name External tops,
     tx.function_name,args,([] : expr list),ret,fbody)` >>
  PairCases_on `raw` >>
  qpat_x_assum `Abbrev ((raw0,_) = _)`
    (assume_tac o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  `raw3 = pkg3` by
    (qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
     asm_rewrite_tac[set_external_package_target_def] >> simp[]) >>
  `pkg3 <= LENGTH vs.vs_call_ctx.cc_calldata` by
    (drule_all valid_vyper_call_min_calldata_size >> simp[]) >>
  `mut = Payable \/ tt.vs_call_ctx.cc_callvalue = 0w` by
    (drule send_call_value_success_condition >>
     simp[initial_evaluation_context_def] >> strip_tac >> simp[] >>
     fs[initial_venom_state_rel_def, venom_env_rel_def, call_ctx_rel_def]) >>
  `allocas_from 0 tt` by
    (drule vars_pc_only_allocas >> fs[allocas_from_def] >> metis_tac[]) >>
  drule compile_entry_checks_ptr_endpoint >>
  disch_then (qspecl_then [`tn1`, `tt`, `0`, `efn`, `unit.cu_context`, `[]`, `G1`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rename1 `vars_pc_only tt u` >> rename1 `tn2.t_mem = tn1.t_mem` >>
  rename1 `ptr_safe_run _ _ _ _ _ _ G2 tn2 u` >>
  qexistsl_tac [`st`, `cenv`, `sa`, `st'`, `u`, `G2`, `tn2`] >>
  simp[entry_taint_def] >>
  (conj_tac >- metis_tac[vars_pc_only_trans]) >>
  all_tac >>
  `cs_extends opened st` by
    (qspec_then `pkg3` (qspec_then `mut = Payable` mp_tac) compile_entry_checks_shape >>
     pure_rewrite_tac[shape_step_def] >>
     disch_then (qspecl_then [`opened`, `()`, `st`] mp_tac) >>
     simp[shape_extends_def]) >>
  drule_all fn_has_code_start >> strip_tac >>
  `MEM efn unit.cu_context.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `!b. lookup_block b efn.fn_blocks <> NONE ==>
       !i. MEM i (THE (lookup_block b efn.fn_blocks)).bb_instructions ==>
           i.inst_opcode <> PHI` by
    (rpt strip_tac >> Cases_on `lookup_block b efn.fn_blocks` >> fs[] >>
     drule lookup_block_fn_insts >> disch_then drule >>
     qpat_x_assum `o1_source_unit_ok unit` mp_tac >>
     simp[o1_source_unit_ok_def, EVERY_MEM, raw_opcode_ok_def] >>
     metis_tac[]) >>
  `phi_prefix_length bb.bb_instructions = 0` by
    (irule no_phis_phi_prefix_length_zero >> simp[EVERY_MEM] >>
     first_x_assum (qspec_then `opened.cs_current_bb` mp_tac) >> simp[]) >>
  gen_tac >> disch_tac >>
  drule_all compile_selector_dispatch_linear_layout >> strip_tac >>
  rename1 `get_instruction entrybb (LENGTH ds.cs_current_insts) =
    SOME (mk_inst ds.cs_next_id CALLDATASIZE [] _)` >>
  irule ptr_safe_blocks_nonphi_run >>
  (reverse conj_tac >-
    (simp[Abbr `ss`] >>
     qexistsl_tac [`entrybb`, `mk_inst ds.cs_next_id CALLDATASIZE []
       [STRING #"%" (toString ds.cs_next_var)]`] >> gvs[mk_inst_def])) >>
  rewrite_tac[GSYM entry_taint_def] >>
  `!fuel. ptr_safe_blocks D 0 fuel unit.cu_context efn [] G1 tn1 tt` suffices_by
    metis_tac[] >>
  irule ptr_safe_blocks_from_phi_free_run >>
  simp[] >>
  qexists_tac `bb` >> gvs[]
QED

Finalise external_entry_reaches_registration_ptr
