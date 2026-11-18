(* The selected entry registers exactly the arguments decoded from the
   incoming call, and hands their concrete and ghost states to the body. *)
Theory dispatchedSelectedEndpoint
Ancestors
  dispatchedSelectedPreparation entryPtrSeamRegister
  selectedAcceptedDecoder selectedAcceptedSingleton selectedAcceptedFold
  defaultEntryEndpointAssembly externalEntryChecks fragGasPathFrameMem
  moduleLoweringProps venomState venomInst list words

Theorem dispatched_selected_registration_joint:
  !tops rpolicy unit am tx ret vs mut nr args fbody env es0.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata =
      SOME (tx.function_name, tx.args) /\
    4 <= LENGTH vs.vs_call_ctx.cc_calldata /\
    (?tys. FIND (\(name,ts). abi_method_id (type_env tops) name ts =
      cd_selector vs.vs_call_ctx.cc_calldata) (abi_external_signatures tops) =
      SOME (tx.function_name,tys)) /\
    initial_venom_state_rel tops am tx vs /\
    vyperInterpreter$lookup_function NONE tx.function_name External tops =
      SOME (mut, nr, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) ==>
    ?lbl cenv0 pos_args min_cds is_payable nkey ut' iv rt st cenv sa st' efn
      s0 G0 tn0.
      set_external_package_target rpolicy.rpol_target
        (package_external_fn tops T (K global_nonreentrant_slot)
          (mut,nr,lookup_raw_return_or_F (NONE:num option) tx.function_name External tops,
           tx.function_name,args,([] : expr list),ret,
             subst_consts_stmts (module_consts_env tops []) fbody)) =
        (lbl,cenv0,pos_args,min_cds,is_payable,nr,nkey,ut',iv,subst_consts_stmts (module_consts_env tops []) fbody,rt) /\
      runtime_selected_body_start tops rpolicy
        (lbl,cenv0,pos_args,min_cds,is_payable,nr,nkey,ut',iv,subst_consts_stmts (module_consts_env tops []) fbody,rt) st /\
      compile_register_positional_args cenv0 pos_args 4 st = (cenv,sa) /\
      compile_guarded_body cenv nr nkey ut' iv (subst_consts_stmts (module_consts_env tops []) fbody) rt sa = ((),st') /\
      fn_has_code sa st' efn /\ fn_inst_ids_distinct efn /\
      local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
      unit.cu_context.ctx_entry = SOME "__entry" /\
      venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn /\
      fn_entry_label efn = SOME "__entry" /\
      (?bb. lookup_block "__entry" efn.fn_blocks = SOME bb /\
        phi_prefix_length bb.bb_instructions = 0) /\
      ~ctx_has_dalloca unit.cu_context /\
      gas_path unit.cu_context efn
        (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                    vs_inst_idx := 0 |>) 0 (OK s0) /\
      gas_path_mem unit.cu_context efn
        (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                    vs_inst_idx := 0 |>) 0 (OK s0) /\
      alloca_history efn s0 /\ fresh_vars_wrt sa s0 /\
      cenv.ce_return_pc = NONE /\ return_buf_frame NONE cenv sa s0 /\
      ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
      s0.vs_gas_readings = vs.vs_gas_readings /\
      s0.vs_code = vs.vs_code /\ s0.vs_labels = vs.vs_labels /\
      (!fuel r. run_from fuel unit.cu_context efn s0 = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_context fuel' unit.cu_context vs = r) /\
      (!D. (!fuel. ptr_safe_run D 0 fuel unit.cu_context efn [] G0 tn0 s0) ==>
        !fuel. ptr_safe_blocks D 0 fuel unit.cu_context efn [] FEMPTY entry_taint
          (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0 |>)) /\
      (!H : (bool # bytes32 # type_value) list # num list.
        stmt_state_rel H unit.cu_context efn cenv
          (initial_evaluation_context am.sources am.layouts tx NONE) es0 s0 /\
        ghost_inv H NONE cenv
          (initial_evaluation_context am.sources am.layouts tx NONE) es0 G0 tn0 s0) /\
      !D explicit.
        gas_origin_ptr_path (D,0,explicit,unit.cu_context,efn,[])
          (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                      vs_inst_idx := 0 |>, FEMPTY, entry_taint) [] (OK s0,G0,tn0)
Proof
  rpt gen_tac >> strip_tac >>
  SUBGOAL_THEN (Term `?types. FIND (\(name,ts). abi_method_id (type_env tops) name ts =
      cd_selector vs.vs_call_ctx.cc_calldata) (abi_external_signatures tops) =
      SOME (tx.function_name,types)`) ASSUME_TAC
  >- (qexists_tac `tys` >> first_assum ACCEPT_TAC) >>
  drule_all dispatched_selected_registration_preparation_nr >>
  disch_then (List.foldr (uncurry qx_choose_then) strip_assume_tac
    [`efn`,`tvs`,`lbl`,`cenv0`,`pos_args`,`min_cds`,`is_payable`,
     `nkey`,`ut'`,`iv`,`rt`,`st`,`cenv`,`sa`,`st'`,`s1`,`G1`,`tn1`]) >>
  `LENGTH args = LENGTH tvs /\ LENGTH args = LENGTH tx.args` by
    fs[LIST_REL_EL_EQN] >>
  `4 + SUM (MAP tv_abi_size tvs) < dimword (:256)` by decide_tac >>
  `fresh_vars_wrt sa s1` by
    (drule compile_register_positional_args_next_var >> strip_tac >>
     irule emitHelperPropsTheory.fresh_vars_wrt_mono >> qexists `st` >> simp[]) >>
  `selected_registration_resources unit.cu_context efn ARB 0 st s1` by
    simp[selected_registration_resources_def] >>
  `alloca_history efn s1` by
    (drule_all externalEntryJointTheory.entry_path_endpoint_facts >> simp[]) >>
  `!ce j. j < LENGTH args /\ ce = cenv0 with ce_vars := ce.ce_vars ==>
    selected_slot_accepts ce (type_env tops) ce.ce_struct_fields (SND (EL j args)) (EL j tvs) /\
    abi_decoder_coherent ce (type_env tops) ce.ce_struct_fields (SND (EL j args)) (EL j tvs)` by
    suspend "slot" >>
  `!j. j < LENGTH args ==> ?loc.
    FLOOKUP cenv0.ce_vars (FST (EL j args)) = SOME loc /\
    var_location_memory_size loc = SOME (type_memory_size (EL j tvs))` by
    (rpt strip_tac >>
     qpat_assum `!i. i < LENGTH args ==> ?off. FLOOKUP _ _ = SOME (MemLoc off _)`
       (qspec_then `j` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (qx_choose_then `off` assume_tac) >>
     qexists `MemLoc off (type_memory_size (EL j tvs))` >>
     simp[moduleLoweringTheory.var_location_memory_size_def]) >>
  `compile_register_positional_args cenv0 (build_positional_args cenv0 args) 4 st = (cenv,sa)` by
    metis_tac[] >>
  drule_at (Pat `calldata_decode_args _ _ _ = _`)
    (selected_registration_fold |> SPEC_ALL |> Q.INST
      [`PG` |-> `[]`]) >>
  disch_then (drule_at (Pat `compile_register_positional_args _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `selected_registration_resources _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `bind_arguments _ _ _ = _`)) >>
  disch_then (qspecl_then [`tn1`,`sa`,`G1`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
  disch_then (List.foldr (uncurry qx_choose_then) strip_assume_tac [`s0`,`G0`,`tn0`]) >>
  qpat_x_assum `selected_registration_resources _ _ _ _ sa s0`
    (strip_assume_tac o REWRITE_RULE [selected_registration_resources_def]) >>
  qpat_x_assum `selected_registration_frame s1 tn1 s0 tn0`
    (strip_assume_tac o REWRITE_RULE [selected_registration_frame_def]) >>
  `!j. j < LENGTH args ==> ?aid q p n.
    FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
    FLOOKUP cenv.ce_vars (FST (EL j args)) = SOME (PtrVar (Var q) n) /\
    lookup_var q s0 = SOME (n2w p) /\ ptr_covers G0 tn0 q s0 n /\
    (!mem. mem_agree_outside tn0.t_mem s0.vs_memory mem ==>
      val_in_memory (EL j tvs) (EL j tx.args) p mem)` by
    suspend "owners" >>
  `tn0.t_stor = {} /\ tn0.t_trans = {} /\ tn0.t_imm = {}` by simp[] >>
  `!H:(bool # 256 word # type_value) list # num list.
    stmt_state_rel H unit.cu_context efn cenv
      (initial_evaluation_context am.sources am.layouts tx NONE) es0 s0 /\
    ghost_inv H NONE cenv
      (initial_evaluation_context am.sources am.layouts tx NONE) es0 G0 tn0 s0` by
    suspend "relations" >>
  suspend "assembly"
QED

Resume dispatched_selected_registration_joint[slot]:
  rpt gen_tac >> strip_tac >>
  `abi_decoder_coherent cenv0 (type_env tops) cenv0.ce_struct_fields
      (SND (EL j args)) (EL j tvs)` by
    (qpat_assum `LIST_REL (abi_decoder_coherent _ _ _) _ _`
       (mp_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >> simp[EL_MAP]) >>
  `abi_decoder_coherent ce (type_env tops) ce.ce_struct_fields
      (SND (EL j args)) (EL j tvs)` by
    (qpat_assum `ce = cenv0 with ce_vars := ce.ce_vars` SUBST1_TAC >>
     simp[ctorRegisterArgsTheory.ctor_decoder_coherent_vars]) >>
  simp[] >> metis_tac[selected_register_one,selected_argument_decoder_accepts]
QED

Resume dispatched_selected_registration_joint[owners]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `selected_registration_owners _ _ _ _ _ _ _ _ _ _`
    (qspec_then `j` mp_tac o REWRITE_RULE [selected_registration_owners_def]) >>
  simp[EL_MAP] >> strip_tac >> rename1 `FLOOKUP s0.vs_allocas aid = SOME (p,n)` >>
  qexistsl [`aid`,`q`,`p`,`n`] >> simp[]
QED

Resume dispatched_selected_registration_joint[relations]:
  `set_external_package_target rpolicy.rpol_target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (mut,nr,lookup_raw_return_or_F (NONE:num option) tx.function_name External tops,
       tx.function_name,args,([]:expr list),ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,nr,nkey,ut',iv,fbody,rt)` by
    (rewrite_tac[Q.INST [`E` |-> `module_consts_env tops []`]
       entryDispatchPropsTheory.external_package_subst_consts,
       constSubstTheory.subst_consts_fn_def, constSubstTheory.subst_consts_expr_def] >>
     first_assum ACCEPT_TAC) >>
  drule_all_then MATCH_ACCEPT_TAC registration_actual_endpoint_relations_from_prefix
QED

Resume dispatched_selected_registration_joint[assembly]:
  `?bb. lookup_block "__entry" efn.fn_blocks = SOME bb` by
    (Cases_on `efn.fn_blocks` >>
     gvs[fn_entry_label_def, entry_block_def, lookup_block_def, FIND_thm]) >>
  `phi_prefix_length bb.bb_instructions = 0` by metis_tac[] >>
  `gas_path_mem unit.cu_context efn
      (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>)
      0 (OK s0)` by
    (drule_all fragGasPathMemTheory.gas_path_mem_then >> simp[]) >>
  `cenv.ce_return_pc = NONE` by
    drule_all_then ACCEPT_TAC registration_external_return_pc >>
  drule_all externalEntryJointTheory.entry_path_endpoint_facts >> strip_tac >>
  mp_tac (Q.SPECL [`unit.cu_context`,`efn`,`vs`,`s0`,`bb`]
    entry_context_continuation) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexistsl_tac [`lbl`,`cenv0`,`pos_args`,`min_cds`,`is_payable`,`nkey`,`ut'`,`iv`,`rt`,
    `st`,`cenv`,`sa`,`st'`,`efn`,`s0`,`G0`,`tn0`] >>
  simp[loweringPostsTheory.return_buf_frame_def] >>
  conj_tac >- metis_tac[] >>
  rpt gen_tac >>
  qpat_assum `!D explicit. gas_origin_ptr_path _ (_,FEMPTY,_) _ _`
    (qspecl_then [`D`,`explicit`] assume_tac) >>
  qpat_assum `!D explicit. gas_origin_ptr_path _ (s1,G1,tn1) _ _`
    (qspecl_then [`D`,`explicit`] assume_tac) >>
  qpat_assum `gas_origin_ptr_path _ (_,FEMPTY,_) _ _`
    (fn prefix => MATCH_MP (SPEC_ALL fragGasOriginPtrTheory.gas_origin_ptr_path_append)
      prefix |> Q.SPECL [`s1`,`G1`,`tn1`,`[]`,`OK s0`,`G0`,`tn0`] |> mp_tac) >>
  simp[]
QED

Finalise dispatched_selected_registration_joint

Theorem dispatched_entry_endpoint_selected:
  !tops rpolicy unit am tx ret vs mut args fbody env es0.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata =
      SOME (tx.function_name, tx.args) /\
    tx.function_name <> "__default__" /\
    initial_venom_state_rel tops am tx vs /\
    vyperInterpreter$lookup_function NONE tx.function_name External tops =
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
  rpt gen_tac >> strip_tac >>
  drule_all dispatchedSelectedFactsTheory.dispatched_selected_source_facts >> strip_tac >>
  SUBGOAL_THEN (Term `?types. FIND (\(name,ts). abi_method_id (type_env tops) name ts =
      cd_selector vs.vs_call_ctx.cc_calldata) (abi_external_signatures tops) =
      SOME (tx.function_name,types)`) ASSUME_TAC
  >- (qexists_tac `MAP SND args` >> first_assum ACCEPT_TAC) >>
  drule_all dispatched_selected_registration_joint >>
  strip_tac >>
  pure_rewrite_tac [runtimeEntryEndpointTheory.runtime_entry_endpoint_def] >>
  qexistsl_tac [`lbl`,`cenv0`,`cenv0`,`pos_args`,`min_cds`,`is_payable`,
    `nkey`,`ut'`,`iv`,`rt`,`st`,`cenv`,`sa`,`st'`,`efn`,`s0`,`G0`,`tn0`] >>
  simp[] >> rpt gen_tac >> strip_tac >>
  qpat_assum `!H. stmt_state_rel H _ _ _ _ _ _ /\ ghost_inv H _ _ _ _ _ _ _`
    (qspec_then `H` strip_assume_tac) >>
  simp[GSYM bodyPtrDefsTheory.ghost_inv_cx_dead] >>
  qpat_assum `!fuel r. run_from _ _ _ _ = r /\ _ ==> _`
    (ACCEPT_TAC o SIMP_RULE (srw_ss()) [])
QED
