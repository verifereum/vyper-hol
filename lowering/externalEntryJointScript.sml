(*
 * Runtime joint body entry on finite horizons: one actual body-start state
 * s0 carrying zero-GAS reachability from __entry, its memory-safe twin,
 * the allocation history and frame, and, at every horizon valid for the
 * call's storage trace, the pointer-safety lift, the pointer ghost, the
 * statement state relation and the zero-GAS pointer path from __entry to s0.
 * The endpoint is chosen before any horizon.
 *
 * r4: st is pinned by runtime_selected_body_start.
 *
 * Proof: the prefix seam (external_entry_reaches_registration_ptr) runs
 * __entry to the start s1 of argument registration; the registration seam
 * (register_positional_args_ptr) runs s1 to the body start s0.  Both carry
 * the zero-GAS memory-checked path and the joint pointer path, which
 * compose; the remaining facts at s0 follow from the composed path.
 *
 * TOP-LEVEL:
 *   external_entry_joint
 *   runtime_entry_function_no_phi, entry_path_endpoint_facts
 *)
Theory externalEntryJoint
Ancestors
  compileVyper moduleLowering compileEnv context supportedProgram e2eDefs
  vyperLoweringCorrect vyperInterpreter venomWf venomInst venomExecSemantics
  fragExec fragGasPath fragGasPathMem allocaHistory loweringStateRelDefs
  loweringPosts exprLoweringProps vyperStorageFootprint ptrSafeRun
  ptrDiscipline bodyPtrDefs runtimeBodyStartDefs fragGasOriginPtr
  entryPtrSeamPrefix entryPtrSeamRegister externalEntryChecks entryStateRel
  selectedBodyCode bodyMemAggregatePath fragGasPathFrameMem venomMemProofs
  moduleLoweringProps vyperCompiler nonreentrantEntryPath externalReturnPackage
  vyperTypeContractGetter vyperTypeContractSoundness vyperTypeContractContext

(* Helper: the runtime entry function, its label and its phi-free entry block. *)
Theorem runtime_entry_function_no_phi_nr:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\ name <> "__default__" /\
  ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops)) /\
  vyperInterpreter$lookup_function NONE name External tops =
    SOME (mut,nr,args,[],ret,fbody) ==>
  unit.cu_context.ctx_entry = SOME "__entry" /\
  ?func bb.
    venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
    fn_entry_label func = SOME "__entry" /\
    lookup_block "__entry" func.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >>
  `supported_declaration_headers tops` by fs[supported_program_def] >>
  drule_all external_lookup_raw_package_member >> strip_tac >>
  `?cenv pos_args min_cds is_payable nkey ut iv rt.
     set_external_package_target rpolicy.rpol_target
       (package_external_fn tops T (K global_nonreentrant_slot)
         (mut,nr,lookup_raw_return_or_F (NONE:num option) name External tops,
          name,args,([]:expr list),ret,fbody)) =
     ("fn_" ++ name,cenv,pos_args,min_cds,is_payable,nr,nkey,ut,iv,fbody,rt)` by
    simp[package_external_fn_def, set_external_package_target_def, LET_THM] >>
  pop_assum strip_assume_tac >>
  drule_all source_runtime_entry_checks_code >> strip_tac >>
  `sa.cs_current_bb = "__entry" /\ sa.cs_current_insts = []` by
    (qpat_x_assum `fresh_label _ _ = _` mp_tac >>
     simp[fresh_label_def, initial_compile_state_def, LET_THM] >>
     strip_tac >> gvs[]) >>
  drule_all linear_dispatch_entry_no_phi >> strip_tac >>
  simp[] >> qexists_tac `bb` >>
  gvs[fn_entry_label_def, entry_block_def, listTheory.NULL_EQ]
QED

Theorem runtime_entry_function_no_phi:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\ name <> "__default__" /\
  ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops)) /\
  vyperInterpreter$lookup_function NONE name External tops =
    SOME (mut,F,args,[],ret,fbody) ==>
  unit.cu_context.ctx_entry = SOME "__entry" /\
  ?func bb.
    venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
    fn_entry_label func = SOME "__entry" /\
    lookup_block "__entry" func.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0
Proof
  metis_tac[runtime_entry_function_no_phi_nr]
QED

(* Helper: facts at the end s0 of a zero-GAS memory-checked path from the
   initial __entry state. *)
Theorem entry_path_endpoint_facts:
  initial_venom_state_rel tops am tx vs /\
  fn_inst_ids_distinct func /\
  gas_path_mem ctx func
    (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                vs_inst_idx := 0 |>) 0 (OK s0) ==>
  gas_path ctx func
    (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                vs_inst_idx := 0 |>) 0 (OK s0) /\
  alloca_history func s0 /\
  s0.vs_code = vs.vs_code /\ s0.vs_labels = vs.vs_labels /\
  runs_through ctx func
    (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                vs_inst_idx := 0 |>) s0
Proof
  strip_tac >>
  qabbrev_tac `ss = vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                               vs_inst_idx := 0 |>` >>
  `ss.vs_allocas = FEMPTY /\ ss.vs_inst_idx = 0` by
    fs[Abbr `ss`, initial_venom_state_rel_def] >>
  drule gas_path_mem_exec >> strip_tac >> gvs[fragExecTheory.exit_result_def] >>
  drule gas_path_code_labels >> simp[] >> strip_tac >>
  rpt conj_tac
  >- (irule gas_path_mem_zero_history >> simp[] >>
      qexistsl_tac [`ctx`, `ss`] >> simp[alloca_history_empty] >>
      rpt strip_tac >> irule aggregate_mem_path_alloca_inv >>
      metis_tac[alloca_inv_empty_proof])
  >- fs[Abbr `ss`]
  >- fs[Abbr `ss`] >>
  simp[runs_through_def] >> metis_tac[]
QED


Theorem external_entry_registration_joint:
  !tops rpolicy unit am tx ret vs mut nr args fbody env es0.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, nr, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) ==>
    ?pbody lbl cenv0 pos_args min_cds is_payable nkey ut' iv rt st cenv sa st' func
     s0 G0 tn0.
      pbody = subst_consts_stmts (module_consts_env tops []) fbody /\
      set_external_package_target rpolicy.rpol_target
        (package_external_fn tops T (K global_nonreentrant_slot)
           (subst_consts_fn (module_consts_env tops []) (mut, nr, lookup_raw_return_or_F (NONE : num option)
                       tx.function_name External tops,
            tx.function_name, args, [], ret, fbody))) =
        (lbl, cenv0, pos_args, min_cds, is_payable, nr, nkey, ut', iv, pbody,
         rt) /\
      runtime_selected_body_start tops rpolicy
        (lbl, cenv0, pos_args, min_cds, is_payable, nr, nkey, ut', iv, pbody, rt) st /\
      compile_register_positional_args cenv0 pos_args 4 st = (cenv, sa) /\
      compile_guarded_body cenv nr nkey ut' iv pbody rt sa = ((), st') /\
      fn_has_code sa st' func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
      unit.cu_context.ctx_entry = SOME "__entry" /\
      lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      fn_entry_label func = SOME "__entry" /\
      gas_path unit.cu_context func
        (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                    vs_inst_idx := 0 |>) 0 (OK s0) /\
      gas_path_mem unit.cu_context func
        (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                    vs_inst_idx := 0 |>) 0 (OK s0) /\
      alloca_history func s0 /\ fresh_vars_wrt sa s0 /\
      cenv.ce_return_pc = NONE /\
      return_buf_frame NONE cenv sa s0 /\
      ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
      s0.vs_gas_readings = vs.vs_gas_readings /\
      s0.vs_code = vs.vs_code /\ s0.vs_labels = vs.vs_labels /\
      (!fuel r. run_from fuel unit.cu_context func s0 = r /\
                (!e. r <> Error e) ==>
                ?fuel'. run_context fuel' unit.cu_context vs = r) /\
      (!D.
        (!fuel. ptr_safe_run D 0 fuel unit.cu_context func [] G0 tn0 s0) ==>
        !fuel. ptr_safe_blocks D 0 fuel unit.cu_context func [] FEMPTY entry_taint
          (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                      vs_inst_idx := 0 |>)) /\
      (!H : (bool # bytes32 # type_value) list # num list.
        stmt_state_rel H unit.cu_context func cenv
          (initial_evaluation_context am.sources am.layouts tx NONE) es0 s0 /\
        ghost_inv H NONE cenv
          (initial_evaluation_context am.sources am.layouts tx NONE) es0 G0 tn0 s0) /\
      !D explicit.
        gas_origin_ptr_path (D,0,explicit,unit.cu_context,func,[])
          (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                      vs_inst_idx := 0 |>, FEMPTY, entry_taint)
          [] (OK s0,G0,tn0)
Proof
  rpt gen_tac >> strip_tac >>
  `tx.function_name <> "__default__"` by fs[valid_vyper_call_def] >>
  drule source_typing_ok_external_names_distinct >> strip_tac >>
  drule_all runtime_entry_function_no_phi_nr >> strip_tac >>
  drule_all external_entry_reaches_registration_ptr_nr >> strip_tac >>
  `set_external_package_target rpolicy.rpol_target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (mut,nr,lookup_raw_return_or_F (NONE:num option) tx.function_name External tops,
       tx.function_name,args,([] : expr list),ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,nr,nkey,ut',iv,fbody,rt)` by
    (rewrite_tac[Q.INST [`E` |-> `module_consts_env tops []`]
       entryDispatchPropsTheory.external_package_subst_consts] >> fs[]) >>
  drule_all (INST_TYPE [beta |-> ``:256``] register_positional_args_ptr_nr) >>
  disch_then (qspec_then `G1` strip_assume_tac) >>
  `gas_path_mem unit.cu_context func
     (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                 vs_inst_idx := 0 |>) (0 + 0) (OK s0)` by
    (irule gas_path_mem_then >> qexists_tac `s1` >> simp[]) >>
  gvs[] >>
  drule_all entry_path_endpoint_facts >> strip_tac >>
  qexistsl_tac [`st`, `cenv`, `sa`, `st'`, `s0`, `G0`, `tn0`] >>
  simp[return_buf_frame_def] >>
  conj_tac >-
    (rpt strip_tac >> irule entry_context_continuation >> simp[] >>
     qexistsl_tac [`fuel`, `s0`] >> simp[]) >>
  rpt gen_tac >>
  qpat_x_assum `!D explicit. gas_origin_ptr_path _ (_,FEMPTY,_) _ _`
    (qspecl_then [`D`, `explicit`] assume_tac) >>
  qpat_x_assum `!D explicit. gas_origin_ptr_path _ (s1,G1,tn1) _ _`
    (qspecl_then [`D`, `explicit`] assume_tac) >>
  qpat_x_assum `gas_origin_ptr_path _ (_,FEMPTY,_) _ _`
    (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
  disch_then (qspecl_then [`s1`, `G1`, `tn1`, `[]`, `OK s0`, `G0`, `tn0`] mp_tac) >>
  simp[]
QED

(* Source lookup covers both explicit functions and generated getters. *)
Theorem selected_nonreentrant_lock_metadata:
  source_deployment_rel tops am tx /\ source_typing_ok tops am tx /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,T,args,[],ret,fbody) ==>
  (initial_evaluation_context am.sources am.layouts tx NONE).nonreentrant_slot =
    SOME global_nonreentrant_slot /\
  is_view_mut mut = (mut = View)
Proof
  strip_tac >> drule lookup_function_External_cases >> strip_tac
  >- (conj_tac
      >- (irule layouts_agree_initial_nonreentrant_slot >>
          fs[source_deployment_rel_def] >> metis_tac[]) >>
      drule_all nonreentrantEntryEquivTheory.source_typing_function_header >>
      disch_then
        (mp_tac o MATCH_MP vyperTypeContractTheory.function_header_nonreentrant_view) >>
      simp[is_view_mut_def]) >>
  `?art. check_contract F am.layouts tx.target [(NONE,tops)] = SOME art` by
    fs[source_typing_ok_def] >>
  pop_assum strip_assume_tac >>
  `ALOOKUP [(NONE,tops)] (NONE:num option) = SOME tops` by simp[] >>
  `module_allocated am.layouts tx.target NONE tops` by
    (drule_all check_contract_main_module_allocated >> simp[]) >>
  conj_tac
  >- (simp[initial_evaluation_context_def, global_nonreentrant_slot_def] >>
      drule_all checked_selected_getter_lock_slot >> simp[]) >>
  `mut = View` suffices_by simp[is_view_mut_def] >>
  qpat_x_assum `external_getter_tuple _ _ = _` mp_tac >>
  qpat_x_assum `is_public_getter_decl _ _` mp_tac >>
  Cases_on `decl` >> simp[is_public_getter_decl_def, external_getter_tuple_def] >>
  Cases_on `v` >> simp[is_public_getter_decl_def, external_getter_tuple_def] >>
  TRY (Cases_on `is_ArrayT t` >> simp[]) >>
  simp[vyperGetterTheory.getter_def] >> rpt (pairarg_tac >> simp[])
QED

(* Both the compiled endpoint and its ghost are fixed before choosing H. *)
Theorem selected_entry_after_lock[local]:
  is_view_mut mut = (mut = View) /\
  cx.nonreentrant_slot = SOME nkey /\ nkey < dimword (:256) /\
  lock_if_nr cx T (is_view_mut mut) es0 = (INL (),es_lock) /\
  compile_nonreentrant_lock nkey T (mut = View) sa = ((),sl) /\
  fn_has_code sa sl func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ ~block_is_terminated sa /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  fresh_vars_wrt sa s0 /\ local_ptrs_reserved cenv sa /\
  cenv.ce_return_pc = NONE /\ return_buf_frame NONE cenv sa s0 /\
  alloca_history func s0 /\
  gas_path_mem ctx func ss 0 (OK s0) /\
  (!D explicit. gas_origin_ptr_path (D,0,explicit,ctx,func,[])
    (ss,FEMPTY,entry_taint) [] (OK s0,G0,tn0)) /\
  (!D. (!fuel. ptr_safe_run D 0 fuel ctx func [] G0 tn0 s0) ==>
    !fuel. ptr_safe_blocks D 0 fuel ctx func [] FEMPTY entry_taint ss) /\
  (!H : (bool # bytes32 # type_value) list # num list.
    stmt_state_rel H ctx func cenv cx es0 s0 /\
    ghost_inv H NONE cenv cx es0 G0 tn0 s0) ==>
  ?s G tn.
    gas_path_mem ctx func ss 0 (OK s) /\
    (!D explicit. gas_origin_ptr_path (D,0,explicit,ctx,func,[])
      (ss,FEMPTY,entry_taint) [] (OK s,G,tn)) /\
    (!D. (!fuel. ptr_safe_run D 0 fuel ctx func [] G tn s) ==>
      !fuel. ptr_safe_blocks D 0 fuel ctx func [] FEMPTY entry_taint ss) /\
    alloca_history func s /\ return_buf_frame NONE cenv sl s /\
    local_ptrs_reserved cenv sl /\ fresh_vars_wrt sl s /\
    ~block_is_terminated sl /\ ~s.vs_halted /\
    s.vs_current_bb = sl.cs_current_bb /\
    s.vs_inst_idx = LENGTH sl.cs_current_insts /\
    s.vs_gas_readings = s0.vs_gas_readings /\
    s.vs_code = s0.vs_code /\ s.vs_labels = s0.vs_labels /\
    (mut <> View ==> ~cx.txn.is_static) /\
    !st0 H. valid_horizon cx st0 H es_lock.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es_lock s /\
      ghost_inv H NONE cenv cx es_lock G tn s
Proof
  strip_tac >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa x` by simp[] >>
  drule_all (INST_TYPE [alpha |-> ``:256``]
    nonreentrant_entry_success_joint_with_view) >> strip_tac >>
  `es_lock.storage_trace = es0.storage_trace ++ [StorageLock nkey]` by
    (drule_all nonreentrant_lock_success_source_with_view >> strip_tac >>
     qpat_x_assum `acquire_nonreentrant_lock _ _ _ _ = _` mp_tac >>
     simp[nonreentrantEquivTheory.acquire_nonreentrant_lock_execution] >>
     Cases_on `lookup_storage (n2w nkey) (es0.tStorage cx.txn.target) = 1w` >>
     Cases_on `mut = View` >> simp[] >> strip_tac >> gvs[]) >>
  qexistsl_tac [`s_lock`, `G_lock`, `tn_lock`] >>
  simp[] >> rpt conj_tac
  >- (`gas_path_mem ctx func ss (0 + 0) (OK s_lock)`
        suffices_by simp[] >>
      irule gas_path_mem_then >> qexists_tac `s0` >> simp[])
  >- (rpt gen_tac >>
      qpat_assum `!D explicit. gas_origin_ptr_path _ (ss,_,_) _ _`
        (qspecl_then [`D`, `explicit`] (mp_tac o MATCH_MP gas_origin_ptr_path_append)) >>
      disch_then (qspecl_then [`s0`, `G0`, `tn0`, `[]`,
        `OK s_lock`, `G_lock`, `tn_lock`] mp_tac) >>
      simp[]) >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!H. storage_locks_separated _ _ /\ MEM nkey _ ==> _`
    (match_mp_tac o Q.SPEC `H`) >>
  fs[valid_horizon_def, storage_observations_ok_def,
     storage_trace_locks_def, listTheory.EVERY_APPEND]
QED

Theorem external_entry_locked_joint:
  !tops rpolicy unit am tx ret vs mut args fbody env es0 es_lock.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut,T,args,[],ret,fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <|outcomes := SOME vs.vs_outcomes; requests := []|>) =
      (INL (),es0) /\
    lock_if_nr (initial_evaluation_context am.sources am.layouts tx NONE)
      T (is_view_mut mut) es0 = (INL (),es_lock) ==>
    ?pbody lbl cenv0 pos_args min_cds is_payable rt st cenv sa sl se st' func
       s G tn.
      pbody = subst_consts_stmts (module_consts_env tops []) fbody /\
      set_external_package_target rpolicy.rpol_target
        (package_external_fn tops T (K global_nonreentrant_slot)
          (subst_consts_fn (module_consts_env tops [])
            (mut,T,lookup_raw_return_or_F (NONE:num option)
               tx.function_name External tops,tx.function_name,args,[],ret,fbody))) =
        (lbl,cenv0,pos_args,min_cds,is_payable,T,global_nonreentrant_slot,
          T,mut = View,pbody,rt) /\
      runtime_selected_body_start tops rpolicy
        (lbl,cenv0,pos_args,min_cds,is_payable,T,global_nonreentrant_slot,
          T,mut = View,pbody,rt) st /\
      rt = (if ret = NoneT then NONE else SOME ret) /\
      compile_register_positional_args cenv0 pos_args 4 st = (cenv,sa) /\
      compile_stmts cenv NoLoop (case rt of SOME ty => ty | NONE => BaseT BoolT)
        pbody sl = ((),se) /\
      fn_has_code sl se func /\ fn_has_code se st' func /\
      fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sl /\ ~block_is_terminated sl /\
      unit.cu_context.ctx_entry = SOME "__entry" /\
      lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      fn_entry_label func = SOME "__entry" /\
      gas_path unit.cu_context func
        (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                   vs_inst_idx := 0|>) 0 (OK s) /\
      gas_path_mem unit.cu_context func
        (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                   vs_inst_idx := 0|>) 0 (OK s) /\
      alloca_history func s /\ fresh_vars_wrt sl s /\
      return_buf_frame NONE cenv sl s /\
      ~s.vs_halted /\ s.vs_current_bb = sl.cs_current_bb /\
      s.vs_inst_idx = LENGTH sl.cs_current_insts /\
      s.vs_gas_readings = vs.vs_gas_readings /\
      s.vs_code = vs.vs_code /\ s.vs_labels = vs.vs_labels /\
      (mut <> View ==> ~tx.is_static) /\
      (!fuel r. run_from fuel unit.cu_context func s = r /\
                (!e. r <> Error e) ==>
                ?fuel'. run_context fuel' unit.cu_context vs = r) /\
      !st0 H. valid_horizon
        (initial_evaluation_context am.sources am.layouts tx NONE) st0 H
        es_lock.storage_trace ==>
        ((!fuel. ptr_safe_run
            (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
            0 fuel unit.cu_context func [] G tn s) ==>
          !fuel. ptr_safe_blocks
            (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
            0 fuel unit.cu_context func [] FEMPTY entry_taint
            (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                       vs_inst_idx := 0|>)) /\
        ghost_inv_at
          (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
          0 NONE cenv
          (initial_evaluation_context am.sources am.layouts tx NONE)
          es_lock G tn s /\
        stmt_state_rel H unit.cu_context func cenv
          (initial_evaluation_context am.sources am.layouts tx NONE) es_lock s /\
        !explicit.
          gas_origin_ptr_path
            (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE),
             0,explicit,unit.cu_context,func,[])
            (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                       vs_inst_idx := 0|>,FEMPTY,entry_taint) [] (OK s,G,tn)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all selected_nonreentrant_lock_metadata >> strip_tac >>
  drule_all registration_supported_no_dalloca >> strip_tac >>
  drule_all external_entry_registration_joint >>
  disch_then (qx_choosel_then
    [`pbody`,`lbl`,`cenv0`,`pos_args`,`min_cds`,`is_payable`,`nkey`,`ut'`,
     `iv`,`rt`,`st`,`cenv`,`sa`,`st'`,`func`,`s0`,`G0`,`tn0`] strip_assume_tac) >>
  drule return_package_target_inversion >> strip_tac >>
  qpat_assum `package_external_fn _ _ _ _ = _`
    (assume_tac o SIMP_RULE (srw_ss()) [constSubstTheory.subst_consts_fn_def]) >>
  drule return_package_metadata >> strip_tac >>
  `nkey = global_nonreentrant_slot /\ ut' = T /\ iv = (mut = View)` by
    simp[] >>
  qpat_x_assum `nkey = _` SUBST_ALL_TAC >>
  qpat_x_assum `ut' = _` SUBST_ALL_TAC >>
  qpat_x_assum `iv = _` SUBST_ALL_TAC >>
  drule_all guarded_body_code_from_registration >>
  simp[] >> strip_tac >>
  `global_nonreentrant_slot < dimword (:256)` by
    simp[global_nonreentrant_slot_def, wordsTheory.dimword_def] >>
  drule_all selected_entry_after_lock >> strip_tac >>
  drule_all entry_path_endpoint_facts >> strip_tac >>
  `tx.function_name <> "__default__"` by fs[valid_vyper_call_def] >>
  drule source_typing_ok_external_names_distinct >> strip_tac >>
  drule_all runtime_entry_function_no_phi_nr >> strip_tac >>
  `func' = func` by
    (qpat_assum `venomInst$lookup_function "__entry" _ = SOME func'`
       (fn th => qpat_assum `venomInst$lookup_function "__entry" _ = SOME func`
         (ACCEPT_TAC o REWRITE_RULE [optionTheory.SOME_11] o TRANS (SYM th)))) >>
  qpat_x_assum `func' = func` SUBST_ALL_TAC >>
  `!fuel r. run_from fuel unit.cu_context func s = r /\
             (!e. r <> Error e) ==>
             ?fuel'. run_context fuel' unit.cu_context vs = r` by
    (qspecl_then [`unit.cu_context`, `func`, `vs`, `s`, `bb`]
       (match_mp_tac) entry_context_continuation >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `mut <> View ==> ~tx.is_static` by fs[initial_evaluation_context_def] >>
  qpat_x_assum `pbody = _` SUBST_ALL_TAC >>
  qexistsl_tac [`st`,`cenv`,`sa`,`sl`,`se`,`st'`,`s`,`G`,`tn`] >>
  fs[] >>
  rpt strip_tac >>
  qpat_x_assum `!st0 H. valid_horizon _ _ _ es_lock.storage_trace ==> _`
    drule >> simp[GSYM ghost_inv_cx_dead]
QED

Theorem external_entry_lock_abort_joint:
  !tops rpolicy unit am tx ret vs mut args fbody env es0 exc es_abort.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut,T,args,[],ret,fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
        <|outcomes := SOME vs.vs_outcomes; requests := []|>) = (INL (),es0) /\
    lock_if_nr (initial_evaluation_context am.sources am.layouts tx NONE)
      T (is_view_mut mut) es0 = (INR exc,es_abort) ==>
    ?func a s G tn.
      unit.cu_context.ctx_entry = SOME "__entry" /\
      lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      fn_entry_label func = SOME "__entry" /\
      expr_exit (INR exc : unit + exception) (Abort a s) /\
      (exc = Error (RuntimeError "nonreentrant lock") \/
       exc = Error (RuntimeError "write in static context")) /\
      s.vs_gas_readings = vs.vs_gas_readings /\
      !D explicit.
        gas_origin_ptr_path (D,0,explicit,unit.cu_context,func,[])
          (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                     vs_inst_idx := 0|>,FEMPTY,entry_taint) [] (Abort a s,G,tn)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all selected_nonreentrant_lock_metadata >> strip_tac >>
  drule_all registration_supported_no_dalloca >> strip_tac >>
  drule_all external_entry_registration_joint >>
  disch_then (qx_choosel_then
    [`pbody`,`lbl`,`cenv0`,`pos_args`,`min_cds`,`is_payable`,`nkey`,`ut'`,
     `iv`,`rt`,`st`,`cenv`,`sa`,`st'`,`func`,`s0`,`G0`,`tn0`] strip_assume_tac) >>
  drule return_package_target_inversion >> strip_tac >>
  qpat_assum `package_external_fn _ _ _ _ = _`
    (assume_tac o SIMP_RULE (srw_ss()) [constSubstTheory.subst_consts_fn_def]) >>
  drule return_package_metadata >> strip_tac >>
  `nkey = global_nonreentrant_slot /\ ut' = T /\ iv = (mut = View)` by simp[] >>
  qpat_x_assum `nkey = _` SUBST_ALL_TAC >>
  qpat_x_assum `ut' = _` SUBST_ALL_TAC >>
  qpat_x_assum `iv = _` SUBST_ALL_TAC >>
  drule_all guarded_body_code_from_registration >> simp[] >> strip_tac >>
  `global_nonreentrant_slot < dimword (:256)` by
    simp[global_nonreentrant_slot_def, wordsTheory.dimword_def] >>
  drule_all (INST_TYPE [alpha |-> ``:256``]
    nonreentrant_entry_abort_joint_with_view) >>
  disch_then (qx_choosel_then [`a`,`s_abort`,`G_abort`,`tn_abort`]
    (MAP_EVERY ASSUME_TAC o CONJUNCTS)) >>
  `exc = Error (RuntimeError "nonreentrant lock") \/
    exc = Error (RuntimeError "write in static context")` by
    (qpat_assum `(_ /\ _ /\ exc = _) \/ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> simp[]) >>
  qexistsl_tac [`a`,`s_abort`,`G_abort`,`tn_abort`] >>
  simp[] >>
  rpt gen_tac >>
  qpat_assum `!D explicit. gas_origin_ptr_path _ (_,FEMPTY,_) _ _`
    (qspecl_then [`D`,`explicit`] (mp_tac o MATCH_MP gas_origin_ptr_path_append)) >>
  disch_then (qspecl_then [`s0`,`G0`,`tn0`,`[]`,
    `Abort a s_abort`,`G_abort`,`tn_abort`] mp_tac) >>
  simp[]
QED

Theorem external_entry_subst_consts_joint:
  !tops rpolicy unit am tx ret vs mut args fbody env es0.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) ==>
    ?pbody lbl cenv0 pos_args min_cds is_payable nkey ut' iv rt st cenv sa st' func
     s0 G0 tn0.
      pbody = subst_consts_stmts (module_consts_env tops []) fbody /\
      set_external_package_target rpolicy.rpol_target
        (package_external_fn tops T (K global_nonreentrant_slot)
           (subst_consts_fn (module_consts_env tops []) (mut, F, lookup_raw_return_or_F (NONE : num option)
                       tx.function_name External tops,
            tx.function_name, args, [], ret, fbody))) =
        (lbl, cenv0, pos_args, min_cds, is_payable, F, nkey, ut', iv, pbody,
         rt) /\
      runtime_selected_body_start tops rpolicy
        (lbl, cenv0, pos_args, min_cds, is_payable, F, nkey, ut', iv, pbody, rt) st /\
      compile_register_positional_args cenv0 pos_args 4 st = (cenv, sa) /\
      compile_guarded_body cenv F nkey ut' iv pbody rt sa = ((), st') /\
      fn_has_code sa st' func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
      unit.cu_context.ctx_entry = SOME "__entry" /\
      lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      fn_entry_label func = SOME "__entry" /\
      gas_path unit.cu_context func
        (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                    vs_inst_idx := 0 |>) 0 (OK s0) /\
      gas_path_mem unit.cu_context func
        (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                    vs_inst_idx := 0 |>) 0 (OK s0) /\
      alloca_history func s0 /\
      return_buf_frame NONE cenv sa s0 /\
      ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
      s0.vs_gas_readings = vs.vs_gas_readings /\
      s0.vs_code = vs.vs_code /\ s0.vs_labels = vs.vs_labels /\
      (!fuel r. run_from fuel unit.cu_context func s0 = r /\
                (!e. r <> Error e) ==>
                ?fuel'. run_context fuel' unit.cu_context vs = r) /\
      !st0 H.
        valid_horizon
          (initial_evaluation_context am.sources am.layouts tx NONE) st0 H
          es0.storage_trace ==>
        ((!fuel. ptr_safe_run
            (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
            0 fuel unit.cu_context func [] G0 tn0 s0) ==>
          !fuel. ptr_safe_blocks
            (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
            0 fuel unit.cu_context func [] FEMPTY entry_taint
            (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                        vs_inst_idx := 0 |>)) /\
        ghost_inv_at
          (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
          0 NONE cenv
          (initial_evaluation_context am.sources am.layouts tx NONE) es0
          G0 tn0 s0 /\
        stmt_state_rel H unit.cu_context func cenv
          (initial_evaluation_context am.sources am.layouts tx NONE) es0 s0 /\
        !explicit.
          gas_origin_ptr_path
            (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE),
             0, explicit, unit.cu_context, func, [])
            (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                        vs_inst_idx := 0 |>, FEMPTY, entry_taint)
            [] (OK s0, G0, tn0)
Proof
  rpt gen_tac >> strip_tac >> drule_all external_entry_registration_joint >>
  disch_then (qx_choosel_then
    [`pbody`,`lbl`,`cenv0`,`pos_args`,`min_cds`,`is_payable`,`nkey`,`ut'`,`iv`,
     `rt`,`st`,`cenv`,`sa`,`st'`,`func`,`s0`,`G0`,`tn0`] strip_assume_tac) >>
  qexistsl_tac
    [`pbody`,`lbl`,`cenv0`,`pos_args`,`min_cds`,`is_payable`,`nkey`,`ut'`,`iv`,
     `rt`,`st`,`cenv`,`sa`,`st'`,`func`,`s0`,`G0`,`tn0`] >>
  simp[] >> conj_tac
  >- (gen_tac >> strip_tac >>
      qpat_assum `!fuel r. _ ==> ?fuel'. run_context _ _ _ = r`
        (qspecl_then [`fuel`, `run_from fuel unit.cu_context func s0`] mp_tac) >>
      simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!H. stmt_state_rel _ _ _ _ _ _ _ /\ ghost_inv _ _ _ _ _ _ _ _`
    (qspec_then `H` strip_assume_tac) >>
  simp[GSYM ghost_inv_cx_dead]
QED

Theorem external_entry_joint:
  !tops rpolicy unit am tx ret vs mut args fbody env es0.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) ==>
    ?lbl cenv0 pos_args min_cds is_payable nkey ut' iv rt st cenv sa st' func
     s0 G0 tn0.
      set_external_package_target rpolicy.rpol_target
        (package_external_fn tops T (K global_nonreentrant_slot)
           (mut, F, lookup_raw_return_or_F (NONE : num option)
                       tx.function_name External tops,
            tx.function_name, args, [], ret, fbody)) =
        (lbl, cenv0, pos_args, min_cds, is_payable, F, nkey, ut', iv, fbody,
         rt) /\
      runtime_selected_body_start tops rpolicy
        (lbl, cenv0, pos_args, min_cds, is_payable, F, nkey, ut', iv, fbody, rt) st /\
      compile_register_positional_args cenv0 pos_args 4 st = (cenv, sa) /\
      compile_guarded_body cenv F nkey ut' iv fbody rt sa = ((), st') /\
      fn_has_code sa st' func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
      unit.cu_context.ctx_entry = SOME "__entry" /\
      lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      fn_entry_label func = SOME "__entry" /\
      gas_path unit.cu_context func
        (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                    vs_inst_idx := 0 |>) 0 (OK s0) /\
      gas_path_mem unit.cu_context func
        (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                    vs_inst_idx := 0 |>) 0 (OK s0) /\
      alloca_history func s0 /\
      return_buf_frame NONE cenv sa s0 /\
      ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
      s0.vs_gas_readings = vs.vs_gas_readings /\
      s0.vs_code = vs.vs_code /\ s0.vs_labels = vs.vs_labels /\
      (!fuel r. run_from fuel unit.cu_context func s0 = r /\
                (!e. r <> Error e) ==>
                ?fuel'. run_context fuel' unit.cu_context vs = r) /\
      !st0 H.
        valid_horizon
          (initial_evaluation_context am.sources am.layouts tx NONE) st0 H
          es0.storage_trace ==>
        ((!fuel. ptr_safe_run
            (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
            0 fuel unit.cu_context func [] G0 tn0 s0) ==>
          !fuel. ptr_safe_blocks
            (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
            0 fuel unit.cu_context func [] FEMPTY entry_taint
            (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                        vs_inst_idx := 0 |>)) /\
        ghost_inv_at
          (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
          0 NONE cenv
          (initial_evaluation_context am.sources am.layouts tx NONE) es0
          G0 tn0 s0 /\
        stmt_state_rel H unit.cu_context func cenv
          (initial_evaluation_context am.sources am.layouts tx NONE) es0 s0 /\
        !explicit.
          gas_origin_ptr_path
            (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE),
             0, explicit, unit.cu_context, func, [])
            (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                        vs_inst_idx := 0 |>, FEMPTY, entry_taint)
            [] (OK s0, G0, tn0)
Proof
  rpt gen_tac >> strip_tac >>
  `module_consts_env tops [] = []` by
    (irule (Q.SPECL [`tops`,`tops`,`[]`]
       supportedDeclsTheory.supported_headers_module_consts_env) >>
     fs[supported_program_def, supportedDeclsTheory.supported_declaration_headers_def]) >>
  drule_all external_entry_subst_consts_joint >>
  simp[constSubstTheory.subst_consts_fn_empty,
       constSubstTheory.subst_consts_stmt_empty] >>
  disch_then (qx_choosel_then
    [`lbl`,`cenv0`,`pos_args`,`min_cds`,`is_payable`,`nkey`,`ut'`,`iv`,`rt`,
     `st`,`cenv`,`sa`,`st'`,`func`,`s0`,`G0`,`tn0`] strip_assume_tac) >>
  qexistsl_tac
    [`lbl`,`cenv0`,`pos_args`,`min_cds`,`is_payable`,`nkey`,`ut'`,`iv`,`rt`,
     `st`,`cenv`,`sa`,`st'`,`func`,`s0`,`G0`,`tn0`] >>
  simp[] >> conj_tac >-
    (qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
     simp[package_external_fn_def]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
