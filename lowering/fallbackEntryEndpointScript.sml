(*
 * The runtime entry for calldata dispatching to __default__ (fewer than 4
 * bytes, or a selector matching no signature) reaches the body's endpoint
 * (runtimeEntryEndpoint) at the fallback: the Linear dispatch falls
 * through every selector check to the fallback label, whose payable check
 * is compile_entry_checks at minimum calldata size 4.
 *
 * TOP-LEVEL:
 *   dispatched_entry_endpoint_default
 *)
Theory fallbackEntryEndpoint
Ancestors
  runtimeEntryEndpoint vyperCalldata defaultDispatchFacts defaultEntryResourceInit
  defaultConcreteRegistrationInit defaultConcreteRegistrationEnd
  defaultConcreteWordHead defaultConcreteBytesRegistration
  defaultConcreteRegistrationCapacity defaultGetterArguments entryRuntimePackageLayout
  defaultEntrySourcePreparation defaultEntryEndpointAssembly

Theorem dispatched_entry_endpoint_default:
  !tops rpolicy unit am tx ret vs mut args fbody env es0.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata =
      SOME (tx.function_name, tx.args) /\
    tx.function_name = "__default__" /\
    initial_venom_state_rel tops am tx vs /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) ==>
    runtime_entry_endpoint tops rpolicy unit am tx vs es0 mut args ret fbody
Proof
  rpt gen_tac >> strip_tac >>
  drule vyperLoweringCorrectTheory.lower_vyper_runtime_unit_context_entry >> strip_tac >>
  `?elbl. fn_entry_label fn = SOME elbl` by
    (drule vyperCompilerTheory.lowering_context_ok_bridge >>
     simp[listTheory.EVERY_MEM] >> strip_tac >>
     `fn_has_entry fn` by metis_tac[venomInstTheory.lookup_function_MEM] >>
     Cases_on `fn.fn_blocks` >>
     gvs[venomWfTheory.fn_has_entry_def, venomInstTheory.fn_entry_label_def,
         venomInstTheory.entry_block_def]) >>
  drule_all default_dispatch_cases >> strip_tac >>
  `elbl = "__entry"` by
    (drule emitHelperPropsTheory.fresh_label_props >>
     simp[vyperCompilerTheory.initial_compile_state_def] >> metis_tac[]) >>
  `pay = (mut = Payable)` by
    (qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
     simp[compileVyperTheory.package_external_fn_def,
          compileVyperTheory.set_external_package_target_def]) >>
  drule_at (Pat `compile_selector_dispatch_linear _ _ _ = _`)
    default_entry_prefix_resources >>
  disch_then (drule_at (Pat `new_block _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_external_fn_bodies _ _ = _`)) >>
  disch_then (drule_at (Pat `send_call_value _ _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_entry_checks _ _ _ = _`)) >>
  disch_then (drule_at (Pat `venomInst$lookup_function _ _ = _`)) >>
  simp[] >>
  disch_then (drule_at (Pat `lower_vyper_runtime_unit _ _ = _`)) >>
  simp[] >> disch_then (qspec_then `ARB` strip_assume_tac) >>
  `?types. OPT_MMAP (evaluate_type (type_env tops)) (MAP SND args) = SOME types /\
    calldata_decode_args vs.vs_call_ctx.cc_calldata types 0 = SOME tx.args` by
    metis_tac[vyperCalldataTheory.calldata_decode_args_def,
      listTheory.OPT_MMAP_def, listTheory.MAP] >>
  pop_assum strip_assume_tac >>
  drule_all default_entry_source_preparation >> strip_tac >>
  drule_all default_entry_package_preparation >> strip_tac >>
  `default_registration_invariant tops
     (initial_evaluation_context am.sources am.layouts tx NONE)
     unit.cu_context fn ARB 0 vs ce st args types pa ce' body_st
     ce st 4 pa types s G tn [] /\
   EVERY (\tv. type_memory_size tv < dimword (:256)) types` by
    (Cases_on `ce = ce_ext`
     >- (gvs[] >>
         drule_all default_registration_package_initial >>
         disch_then (qspec_then `G` assume_tac) >>
         drule_at (Pat `default_registration_invariant _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
           default_registration_capacity_from_lowering >>
         disch_then (drule_at (Pat `lower_vyper_runtime_unit _ _ = _`)) >>
         disch_then (drule_at (Pat `set_external_package_target _ _ = _`)) >>
         simp[] >> disch_tac >>
         Cases_on `classify_functions tops` >> PairCases_on `r` >>
         gvs[] >> metis_tac[]) >>
     `args = [] /\ types = [] /\ pa = [] /\ ce.ce_vars = FEMPTY /\
      (ce_ext with <|ce_ret_enc_info := ce.ce_ret_enc_info;
                    ce_ret_dec_info := ce.ce_ret_dec_info;
                    ce_max_return_size := ce.ce_max_return_size|>) = ce` by
       metis_tac[listTheory.OPT_MMAP_def, listTheory.MAP,
         optionTheory.SOME_11] >>
     `ce.ce_module = NONE /\ ~ce.ce_is_ctor /\ ce.ce_imm_alloca = NONE /\
      ce.ce_return_pc = NONE /\ ce.ce_return_buf = NONE /\
      storage_vars_rel ce (initial_evaluation_context am.sources am.layouts tx NONE) /\
      transient_vars_rel ce (initial_evaluation_context am.sources am.layouts tx NONE) /\
      immutable_section_layout ce tops` by
       (qpat_assum `(_ with <|ce_ret_enc_info := _; ce_ret_dec_info := _;
          ce_max_return_size := _|>) = ce`
          (fn th => once_rewrite_tac[GSYM th]) >>
        fs[loweringStateRelDefsTheory.storage_vars_rel_def,
           loweringStateRelDefsTheory.transient_vars_rel_def,
           immutableRelationTheory.immutable_section_layout_def]) >>
     conj_tac
     >- (irule defaultConcreteRegistrationDefsTheory.default_registration_invariant_initial >>
         simp[defaultConcreteRegistrationDefsTheory.default_registration_ptr_reservation_def] >>
         metis_tac[]) >> simp[]) >>
  pop_assum strip_assume_tac >>
  `~ctx_has_dalloca unit.cu_context` by
    metis_tac[entryReachBodyFmpTheory.entry_runtime_no_dalloca] >>
  `fn_inst_ids_distinct fn` by
    (`ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))` by
       metis_tac[allocaFrontierBoundTheory.ctx_inst_ids_distinct_fn,
         vyperCompilerTheory.lowering_context_ok_static_integrity,
         venomInstTheory.lookup_function_MEM] >>
     gvs[venomWfTheory.fn_inst_ids_distinct_def, venomInstTheory.fn_insts_def,
         venomInstIdsPropsTheory.fn_insts_blocks_map_id]) >>
  `fn.fn_name = "__entry"` by
    metis_tac[vyperCompilerTheory.lookup_function_result_name] >>
  drule_at (Pat `default_registration_invariant _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    default_registration_concrete_fold >>
  disch_then (drule_at (Pat `send_call_value _ _ _ = _`)) >>
  disch_then (drule_at (Pat `initial_venom_state_rel _ _ _ _`)) >>
  disch_then (drule_at (Pat `bind_arguments _ _ _ = _`)) >>
  disch_then (drule_at (Pat `calldata_decode_args _ _ _ = _`)) >>
  simp[vyperInterpreterTheory.initial_evaluation_context_def] >>
  disch_then (qspecl_then [`0`,`[]`] mp_tac) >>
  (impl_tac >-
    (rpt gen_tac >> Cases_on `prim` >> strip_tac
     >- (irule default_registration_word_head >> simp[] >>
         goal_assum $ drule_at Any >> simp[]) >>
     irule default_registration_bytes_head >> simp[] >>
     goal_assum $ drule_at Any >> simp[])) >>
  strip_tac >>
  drule default_registration_terminal_reserved >> strip_tac >>
  `default_registration_entry_frame vs out /\
   out.vs_current_bb = body_st.cs_current_bb /\
   out.vs_inst_idx = LENGTH body_st.cs_current_insts` by
    (qpat_x_assum `default_registration_invariant _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ [] [] out _ _ _`
       mp_tac >>
     simp[defaultConcreteRegistrationDefsTheory.default_registration_invariant_def,
          defaultConcreteRegistrationDefsTheory.default_registration_resources_def]) >>
  `~block_is_terminated checks` by
    (drule emitHelperPropsTheory.new_block_props >>
     simp[compileEnvTheory.block_is_terminated_def]) >>
  `~block_is_terminated body_st` by
    metis_tac[entryRegistrationOpenTheory.entry_checks_registration_open] >>
  `?bb. lookup_block "__entry" fn.fn_blocks = SOME bb` by
    (Cases_on `fn.fn_blocks` >>
     gvs[venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def,
         venomInstTheory.lookup_block_def, listTheory.FIND_thm]) >>
  `phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[acceptedContextPhiTheory.lower_vyper_runtime_unit_block_phi] >>
  irule default_entry_endpoint_from_certificates >>
  goal_assum $ drule_at Any >>
  simp[runtimeBodyStartDefsTheory.runtime_entry_body_start_def,
       vyperInterpreterTheory.initial_evaluation_context_def] >>
  goal_assum $ drule_at Any >> simp[] >>
  goal_assum $ drule_at Any >> simp[] >>
  goal_assum $ drule_at Any >> simp[] >>
  goal_assum $ drule_at Any >> simp[] >>
  goal_assum $ drule_at (Pat `compile_register_positional_args _ _ _ _ = _`) >>
  simp[] >>
  goal_assum $ drule_at (Pat `gas_path_mem _ _ _ 0 (OK out)`) >> simp[]
  >- (qexistsl [`G`,`tn`] >> gvs[])
  >- (qexistsl [`G`,`tn`] >> gvs[]) >>
  gvs[] >> qexistsl [`G`,`tn`] >> simp[]
QED
