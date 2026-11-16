(* The selected dispatch/check prefix depends only on raw hit and head-size facts.
   No canonical calldata encoding or successful argument decoder is required. *)
Theory dispatchedSelectedPrefix
Ancestors
  defaultDispatchRouting registrationRejectMetadata
  selectedEntryPrefixCode entryStateRel entryChecksPassPtr entryPrefixPtr
  sourceValueRejection loweringShapeSource loweringShapeProps o1PipelineCorrect
  supportedNames supportedProgramProps
  loweringShapeDefs unitShapeDefs venomExecProofs entryValueRevertPtr
  entryDispatchPtr sourceEntryCode actualRegistrationCode entryLocals
  actualEntryAllocationFrame runtimeBodyStartDefs entryDispatchProps
  moduleLoweringProps stmtLoweringProps exprLoweringProps vyperInterpreter
  vyperContext venomExecSemantics venomState compileEnv loweringStateRelDefs
  e2eDefs supportedProgram compileVyper fragExec venomInst contextCodegenRel
  ptrDiscipline ptrSafeRun vyperLoweringCorrect bodyPtrDefs moduleLowering
  venomWf fragGasOriginPtr fragGasPathMem arithmetic list

Theorem dispatched_selected_registration_prefix:
  !tops rpolicy unit am tx ret vs mut args fbody env es0 efn elbl tvs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    tx.function_name <> "__default__" /\
    4 <= LENGTH vs.vs_call_ctx.cc_calldata /\
    FIND (\(n,ts). abi_method_id (type_env tops) n ts =
      cd_selector vs.vs_call_ctx.cc_calldata)
      (abi_external_signatures tops) = SOME (tx.function_name,MAP SND args) /\
    OPT_MMAP (evaluate_type (type_env tops)) (MAP SND args) = SOME tvs /\
    4 + SUM (MAP tv_abi_size tvs) <= LENGTH vs.vs_call_ctx.cc_calldata /\
    initial_venom_state_rel tops am tx vs /\
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
    ?pbody lbl cenv0 pos_args min_cds is_payable nkey ut' iv rt st cenv sa st' s1
     G1 tn1.
      pbody = subst_consts_stmts (module_consts_env tops []) fbody /\
      set_external_package_target rpolicy.rpol_target
        (package_external_fn tops T (K global_nonreentrant_slot)
           (subst_consts_fn (module_consts_env tops [])
             (mut, F, lookup_raw_return_or_F (NONE : num option)
                tx.function_name External tops,
              tx.function_name, args, [], ret, fbody))) =
        (lbl, cenv0, pos_args, min_cds, is_payable, F, nkey, ut', iv, pbody, rt) /\
      runtime_selected_body_start tops rpolicy
        (lbl, cenv0, pos_args, min_cds, is_payable, F, nkey, ut', iv, pbody, rt) st /\
      compile_register_positional_args cenv0 pos_args 4 st = (cenv, sa) /\
      compile_guarded_body cenv F nkey ut' iv pbody rt sa = ((), st') /\
      fn_has_code st sa efn /\ fn_has_code sa st' efn /\
      fn_inst_ids_distinct efn /\
      local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
      cenv.ce_return_buf = NONE /\
      gas_path_mem unit.cu_context efn
        (vs with <| vs_prev_bb := NONE; vs_current_bb := elbl;
                    vs_inst_idx := 0 |>) 0 (OK s1) /\
      (!D explicit.
         gas_origin_ptr_path (D, 0, explicit, unit.cu_context, efn, [])
           (vs with <| vs_prev_bb := NONE; vs_current_bb := elbl;
                       vs_inst_idx := 0 |>, FEMPTY, entry_taint)
           [] (OK s1, G1, tn1)) /\
      vars_pc_only
        (vs with <| vs_prev_bb := NONE; vs_current_bb := elbl;
                    vs_inst_idx := 0 |>) s1 /\
      s1.vs_gas_readings = vs.vs_gas_readings /\
      fresh_vars_wrt st s1 /\ ~s1.vs_halted /\
      s1.vs_current_bb = st.cs_current_bb /\
      s1.vs_inst_idx = LENGTH st.cs_current_insts /\
      tn1.t_mem = {} /\ tn1.t_stor = {} /\ tn1.t_trans = {} /\ tn1.t_imm = {} /\
      !D. (!fuel. ptr_safe_run D 0 fuel unit.cu_context efn [] G1 tn1 s1) ==>
          !fuel. ptr_safe_blocks D 0 fuel unit.cu_context efn [] FEMPTY entry_taint
            (vs with <| vs_prev_bb := NONE; vs_current_bb := elbl; vs_inst_idx := 0 |>)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `source_deployment_rel _ _ _` kall_tac >>
  `o1_source_unit_ok unit` by
    (irule lower_vyper_runtime_unit_source_unit_ok_shape >>
     goal_assum (drule_at Any) >> conj_tac
     >- (irule supported_names_internal_names_distinct >>
         fs[supported_program_def, supported_declaration_names_def]) >>
     metis_tac[supported_program_runtime_bodies_shape_ok]) >>
  `~ctx_has_dalloca unit.cu_context` by metis_tac[o1_source_unit_ok_no_dalloca] >>
  qabbrev_tac `pkg = set_external_package_target rpolicy.rpol_target
    (package_external_fn tops T (K global_nonreentrant_slot)
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
    (package_external_fn tops T (K global_nonreentrant_slot)
      (mut,F,lookup_raw_return_or_F (NONE:num option) tx.function_name External tops,
       tx.function_name,args,([] : expr list),ret,fbody)) =
    ("fn_" ++ tx.function_name,pkg1,pkg2,pkg3,mut = Payable,F,pkg6,pkg7,pkg8,fbody,pkg10)` by
    (qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
     simp[package_external_fn_def]) >>
  `ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops))` by
    metis_tac[source_typing_ok_external_names_distinct] >>
  `set_external_package_target rpolicy.rpol_target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (subst_consts_fn (module_consts_env tops [])
        (mut,F,lookup_raw_return_or_F (NONE:num option) tx.function_name External tops,
         tx.function_name,args,([] : expr list),ret,fbody))) =
    ("fn_" ++ tx.function_name,pkg1,pkg2,pkg3,mut = Payable,F,pkg6,pkg7,pkg8,
     subst_consts_stmts (module_consts_env tops []) fbody,pkg10)` by
    (rewrite_tac[GSYM entryDispatchPropsTheory.external_package_subst_consts] >> simp[]) >>
  fs[] >>
  drule_all source_selected_entry_prefix_structure >> strip_tac >>
  suspend "dispatch"
QED

Resume dispatched_selected_registration_prefix[dispatch]:
  drule_all initial_entry_dispatch_scalars >>
  disch_then (qspecl_then [`0`, `elbl`, `ds`] strip_assume_tac) >>
  qabbrev_tac `ss = vs with <|vs_prev_bb := NONE; vs_current_bb := elbl; vs_inst_idx := 0|>` >>
  qspecl_then [`type_env tops`, `FST (classify_functions tops)`]
    assume_tac entryDispatchPropsTheory.linear_selectors_lt >>
  `MEM efn unit.cu_context.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `!b. lookup_block b efn.fn_blocks <> NONE ==>
       !i. MEM i (THE (lookup_block b efn.fn_blocks)).bb_instructions ==>
           i.inst_opcode <> PHI` by
    (rpt strip_tac >> Cases_on `lookup_block b efn.fn_blocks` >> fs[] >>
     drule lookup_block_fn_insts >> disch_then drule >>
     qpat_x_assum `o1_source_unit_ok unit` mp_tac >>
     simp[o1_source_unit_ok_def, EVERY_MEM, raw_opcode_ok_def] >> metis_tac[]) >>
  `!lbl bb. lookup_block lbl efn.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> irule no_phis_phi_prefix_length_zero >> simp[EVERY_MEM] >>
     first_x_assum (qspec_then `lbl` mp_tac) >> simp[]) >>
  drule compile_selector_dispatch_linear_ptr_endpoint >>
  disch_then (qspecl_then [`entry_taint`, `ss`, `0`, `efn`, `unit.cu_context`,
    `[]`, `FEMPTY`] mp_tac) >>
  (impl_tac >- (simp[Abbr `ss`] >> metis_tac[])) >> strip_tac >>
  rename1 `vars_pc_only ss tt` >> rename1 `tn1.t_mem = entry_taint.t_mem` >>
  rename1 `ptr_safe_blocks _ _ _ _ _ _ G1 tn1 tt` >>
  `supported_declaration_headers tops` by fs[supported_program_def] >>
  drule_all supported_headers_external_member >> strip_tac >>
  `ALL_DISTINCT (MAP FST (build_selectors (type_env tops)
      (FST (classify_functions tops))))` by
    fs[supported_program_def, supported_declaration_names_def,
       supported_selectors_distinct_def] >>
  `4 <= LENGTH vs.vs_call_ctx.cc_calldata` by decide_tac >>
  drule_all default_raw_selected_target >> strip_tac >>
  `tt.vs_current_bb = opened.cs_current_bb /\
   tt.vs_call_ctx = vs.vs_call_ctx /\ fresh_vars_wrt opened tt` by
    (imp_res_tac vars_pc_only_fields >> fs[Abbr `ss`] >>
     irule emitHelperPropsTheory.fresh_vars_wrt_mono >>
     qexists_tac `de` >> simp[]) >>
  suspend "checks"
QED

Resume dispatched_selected_registration_prefix[checks]:
  `pkg3 <= LENGTH vs.vs_call_ctx.cc_calldata` by
    (drule_all registration_reject_package_inputs >> strip_tac >>
     gvs[]) >>
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
  `gas_path_mem unit.cu_context efn ss 0 (OK u)` by
    metis_tac[gas_path_mem_then, ADD_0] >>
  `!D explicit. gas_origin_ptr_path (D,0,explicit,unit.cu_context,efn,[])
    (ss,FEMPTY,entry_taint) [] (OK u,G2,tn2)` by
    metis_tac[gas_origin_ptr_path_append, APPEND] >>
  `vars_pc_only ss u` by metis_tac[vars_pc_only_trans] >>
  `u.vs_gas_readings = vs.vs_gas_readings` by
    (qpat_assum `vars_pc_only ss u`
       (mp_tac o MATCH_MP entryPrefixPtrTheory.vars_pc_only_gas_readings) >> simp[Abbr `ss`]) >>
  qpat_x_assum `Abbrev (ss = _)` (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qexistsl_tac [`st`, `cenv`, `sa`, `st'`, `u`, `G2`, `tn2`] >>
  fs[entry_taint_def, stringTheory.STRCAT_EQNS] >>
  `cs_extends opened st` by
    (qspec_then `pkg3` (qspec_then `mut = Payable` mp_tac) compile_entry_checks_shape >>
     pure_rewrite_tac[shape_step_def] >>
     disch_then (qspecl_then [`opened`, `()`, `st`] mp_tac) >>
     simp[shape_extends_def]) >>
  drule_all fn_has_code_start >> strip_tac >>
  `phi_prefix_length bb.bb_instructions = 0` by metis_tac[] >>
  gen_tac >> disch_tac >>
  drule_all compile_selector_dispatch_linear_layout >> strip_tac >>
  rename1 `get_instruction entrybb (LENGTH ds.cs_current_insts) =
    SOME (mk_inst ds.cs_next_id CALLDATASIZE [] _)` >>
  irule ptr_safe_blocks_nonphi_run >>
  (reverse conj_tac >-
    (simp[] >>
     qexistsl_tac [`entrybb`, `mk_inst ds.cs_next_id CALLDATASIZE []
       [STRING #"%" (toString ds.cs_next_var)]`] >> gvs[mk_inst_def])) >>
  rewrite_tac[GSYM entry_taint_def] >>
  `!fuel. ptr_safe_blocks D 0 fuel unit.cu_context efn [] G1 tn1 tt` suffices_by
    (qpat_x_assum `!D. (!fuel. ptr_safe_blocks _ 0 fuel _ _ [] G1 tn1 tt) ==> _`
       (qspec_then `D` mp_tac) >> simp[entry_taint_def]) >>
  irule ptr_safe_blocks_from_phi_free_run >> simp[] >>
  qexists_tac `bb` >> gvs[]
QED
Finalise dispatched_selected_registration_prefix
