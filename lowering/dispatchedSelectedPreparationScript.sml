(* A selector hit hands registration the calldata used to decode the source arguments. *)
Theory dispatchedSelectedPreparation
Ancestors
  dispatchedSelectedFacts dispatchedSelectedPrefix externalEntryJoint
  registrationRejectMetadata entryPtrSeamRegister
  constSubst supportedDecls supportedProgram vyperTypeABI transfer words list
  entryStateRel vyperLoweringCorrect entryRejectCode
  acceptedContextPhi defaultDispatchFacts dispatchedSignatureArgs entryDispatchProps

Theorem selection_type_list_unique[local]:
  OPT_MMAP f tys = SOME tvs /\
  LIST_REL (\ty tv. f ty = SOME tv) tys us ==> us = tvs
Proof
  strip_tac >> drule OPT_MMAP_LIST_REL >> strip_tac >>
  `right_unique (LIST_REL (\ty tv. f ty = SOME tv))` by
    (irule LIST_REL_right_unique >> simp[right_unique_def] >> metis_tac[optionTheory.SOME_11]) >>
  fs[right_unique_def] >> metis_tac[]
QED

Theorem dispatched_selected_registration_preparation_nr:
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
    ?efn tvs lbl cenv0 pos_args min_cds is_payable nkey ut' iv rt st cenv sa st'
      s1 G1 tn1.
      unit.cu_context.ctx_entry = SOME "__entry" /\
      venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn /\
      fn_entry_label efn = SOME "__entry" /\
      set_external_package_target rpolicy.rpol_target
        (package_external_fn tops T (K global_nonreentrant_slot)
          (mut,nr,lookup_raw_return_or_F (NONE:num option)
            tx.function_name External tops,tx.function_name,args,([] : expr list),ret,
             subst_consts_stmts (module_consts_env tops []) fbody)) =
        (lbl,cenv0,pos_args,min_cds,is_payable,nr,nkey,ut',iv,subst_consts_stmts (module_consts_env tops []) fbody,rt) /\
      runtime_selected_body_start tops rpolicy
        (lbl,cenv0,pos_args,min_cds,is_payable,nr,nkey,ut',iv,subst_consts_stmts (module_consts_env tops []) fbody,rt) st /\
      compile_register_positional_args cenv0 pos_args 4 st = (cenv,sa) /\
      compile_guarded_body cenv nr nkey ut' iv (subst_consts_stmts (module_consts_env tops []) fbody) rt sa = ((),st') /\
      fn_has_code st sa efn /\ fn_has_code sa st' efn /\
      fn_inst_ids_distinct efn /\
      local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
      cenv.ce_return_buf = NONE /\
      gas_path_mem unit.cu_context efn
        (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                    vs_inst_idx := 0 |>) 0 (OK s1) /\
      (!D explicit.
         gas_origin_ptr_path (D,0,explicit,unit.cu_context,efn,[])
           (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                       vs_inst_idx := 0 |>,FEMPTY,entry_taint)
           [] (OK s1,G1,tn1)) /\
      vars_pc_only
        (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                    vs_inst_idx := 0 |>) s1 /\
      s1.vs_gas_readings = vs.vs_gas_readings /\
      fresh_vars_wrt st s1 /\ ~s1.vs_halted /\
      s1.vs_current_bb = st.cs_current_bb /\
      s1.vs_inst_idx = LENGTH st.cs_current_insts /\
      tn1.t_mem = {} /\ tn1.t_stor = {} /\ tn1.t_trans = {} /\ tn1.t_imm = {} /\
      (!D. (!fuel. ptr_safe_run D 0 fuel unit.cu_context efn [] G1 tn1 s1) ==>
           !fuel. ptr_safe_blocks D 0 fuel unit.cu_context efn [] FEMPTY entry_taint
             (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                         vs_inst_idx := 0 |>)) /\
      s1.vs_call_ctx = vs.vs_call_ctx /\
      FIND (\(name,tys). abi_method_id (type_env tops) name tys =
        cd_selector s1.vs_call_ctx.cc_calldata) (abi_external_signatures tops) =
        SOME (tx.function_name,MAP SND args) /\
      OPT_MMAP (evaluate_type (type_env tops)) (MAP SND args) = SOME tvs /\
      calldata_decode_args s1.vs_call_ctx.cc_calldata tvs 0 = SOME tx.args /\
      4 <= LENGTH s1.vs_call_ctx.cc_calldata /\
      min_cds = 4 + SUM (MAP tv_abi_size tvs) /\
      min_cds <= LENGTH s1.vs_call_ctx.cc_calldata /\
      LENGTH s1.vs_call_ctx.cc_calldata < dimword (:256) /\
      ALL_DISTINCT (MAP FST args) /\ pos_args = build_positional_args cenv0 args /\
      dec_cenv_agrees cenv0 (type_env tops) /\
      (!k. ~MEM k (MAP FST args) ==> FLOOKUP cenv0.ce_vars k = NONE) /\
      LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv)
        (MAP SND args) tvs /\
      LIST_REL (abi_decoder_coherent cenv0 (type_env tops) cenv0.ce_struct_fields)
        (MAP SND args) tvs /\
      LIST_REL value_has_type tvs tx.args /\
      (!i. i < LENGTH args ==> ?off.
        FLOOKUP cenv0.ce_vars (FST (EL i args)) =
          SOME (MemLoc off (type_memory_size (EL i tvs)))) /\
      (!i. i < LENGTH args ==> type_memory_size (EL i tvs) < dimword (:256)) /\
      s1.vs_allocas = FEMPTY /\ s1.vs_memory = [] /\ s1.vs_alloca_next = 0 /\
      alloca_inv s1 /\ allocas_from 0 s1 /\
      (!site. alloca_frontier_inv unit.cu_context efn site s1) /\
      unit_alloca_budget unit.cu_context < dimword (:256) /\
      (!label bb. lookup_block label efn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0)
Proof
  rpt gen_tac >> strip_tac >>
  drule source_typing_ok_external_names_distinct >> strip_tac >>
  drule lower_vyper_runtime_unit_context_entry >> strip_tac >>
  rename1 `venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn` >>
  `MEM efn unit.cu_context.ctx_functions` by metis_tac[venomInstTheory.lookup_function_MEM] >>
  `fn_entry_label efn = SOME "__entry"` by
    (drule_all_then ACCEPT_TAC lower_vyper_runtime_unit_entry_label) >>
  drule_all default_dispatch_raw_cases >>
  disch_then (DISJ_CASES_THEN2 strip_assume_tac strip_assume_tac) >- gvs[] >>
  `MEM (tx.function_name,tys) (abi_external_signatures tops)` by
    metis_tac[venomInstTheory.FIND_MEM] >>
  `tys = MAP SND args` by metis_tac[dispatched_signature_args] >> gvs[] >>
  `MEM (subst_consts_fn (module_consts_env tops [])
    (mut,nr,lookup_raw_return_or_F (NONE:num option) tx.function_name External tops,
     tx.function_name,args,([]:expr list),ret,fbody)) (FST (classify_functions tops))` by
    (Cases_on `tx.function_name = "__default__"` >-
       (gvs[] >> drule_all default_selected_source_args >> strip_tac >>
        drule_all default_selected_raw_return >> strip_tac >>
        simp[] >> drule_then ACCEPT_TAC public_getter_classified_mem) >>
     drule_all_then ACCEPT_TAC lookup_function_external_raw_member) >>
  `4 <= LENGTH vs.vs_call_ctx.cc_calldata` by decide_tac >>
  `4 + SUM (MAP tv_abi_size tvs) <= LENGTH vs.vs_call_ctx.cc_calldata` by decide_tac >>
  drule_all dispatched_selected_registration_prefix_nr >> strip_tac >>
  rename1 `fn_has_code st sa efn` >>
  rename1 `fn_has_code sa st' efn` >>
  rename1 `vars_pc_only _ s1` >>
  rename1 `gas_origin_ptr_path _ _ [] (OK s1,G1,tn1)` >>
  rename1 `runtime_selected_body_start _ _
    (lbl,cenv0,pos_args,min_cds,is_payable,nr,nkey,ut',iv,pbody,rt) st` >>
  rename1 `compile_register_positional_args cenv0 pos_args 4 st = (cenv,sa)` >>
  qpat_x_assum `pbody = _` SUBST_ALL_TAC >>
  `set_external_package_target rpolicy.rpol_target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (mut,nr,lookup_raw_return_or_F (NONE:num option) tx.function_name External tops,
       tx.function_name,args,([]:expr list),ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,nr,nkey,ut',iv,fbody,rt)` by
    (rewrite_tac[Q.INST [`E` |-> `module_consts_env tops []`]
       external_package_subst_consts] >> first_assum ACCEPT_TAC) >>
  drule_all registration_source_parameter_inputs_nr >> strip_tac >>
  rename1 `LIST_REL value_has_type us tx.args` >>
  `us = tvs` by (drule_all selection_type_list_unique >> simp[]) >>
  qpat_x_assum `us = tvs` SUBST_ALL_TAC >>
  qpat_assum `set_external_package_target _
    (package_external_fn _ _ _ (subst_consts_fn _ _)) = _`
    (assume_tac o SIMP_RULE std_ss
      [constSubstTheory.subst_consts_fn_def, constSubstTheory.subst_consts_expr_def]) >>
  qpat_assum `MEM (subst_consts_fn _ _) _`
    (assume_tac o SIMP_RULE std_ss
      [constSubstTheory.subst_consts_fn_def, constSubstTheory.subst_consts_expr_def]) >>
  drule_all registration_reject_classified_package_inputs >> strip_tac >>
  rename1 `LIST_REL _ args (ZIP (MAP SND args,ts))` >>
  `ts = tvs` by fs[] >>
  qpat_x_assum `ts = tvs` SUBST_ALL_TAC >>
  `!i. i < LENGTH args ==> type_memory_size (EL i tvs) < dimword (:256)` by
    (rpt strip_tac >>
     `LENGTH args = LENGTH tvs` by
       (drule OPT_MMAP_LENGTH >> simp[]) >>
     `EL i (ZIP (MAP SND args,tvs)) = (EL i (MAP SND args),EL i tvs)` by
       (irule EL_ZIP >> simp[]) >>
     qpat_assum `LIST_REL _ args (ZIP _)`
       (qspec_then `i` mp_tac o CONJUNCT2 o REWRITE_RULE [LIST_REL_EL_EQN]) >>
     Cases_on `EL i args` >> simp[]) >>
  drule_all registration_initial_ptr_resources >>
  disch_then (strip_assume_tac o REWRITE_RULE [FORALL_AND_THM]) >>
  drule_all initial_venom_state_calldata_length >> strip_tac >>
  `!label bb. lookup_block label efn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> drule_all lower_vyper_runtime_unit_block_phi >> simp[]) >>
  qexistsl_tac [`lbl`,`cenv0`,`is_payable`,`nkey`,`ut'`,`iv`,`rt`,
    `st`,`cenv`,`sa`,`st'`,`s1`,`G1`,`tn1`] >>
  qpat_x_assum `pos_args = build_positional_args cenv0 args` SUBST_ALL_TAC >>
  qpat_x_assum `min_cds = 4 + SUM (MAP tv_abi_size tvs)` SUBST_ALL_TAC >>
  `SUM (MAP tv_abi_size tvs) + 4 = 4 + SUM (MAP tv_abi_size tvs)` by decide_tac >>
  asm_rewrite_tac [constSubstTheory.subst_consts_fn_def,
    constSubstTheory.subst_consts_expr_def]
QED
