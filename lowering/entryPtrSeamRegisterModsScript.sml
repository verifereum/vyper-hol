Theory entryPtrSeamRegisterMods
Ancestors
  entryModuleLocations entryPtrSeamRegister e2eModsDefs e2eDefs
  compileUnit compileVyper compileEnv constSubstMods
  vyperCompiler vyperLoweringCorrect exprLoweringProps loweringStateRelDefs
  entryStateRel allocaFrontierRoom allocaFrontierBound[qualified]
  moduleLowering moduleLoweringProps bodyPtrDefs bodyInvSplit
  vyperInterpreter vyperContext vyperState vyperAST vyperTypeContract
  vyperTypeContractContext vyperTypeContractGetter supportedProgram supportedDecls
  venomInst venomState venomMemDefs[qualified] fragExec
  list alist pair finite_map words

Theorem linked_runtime_unit_alloca_budget[local]:
  lower_vyper_runtime_unit_mods mods exps rpolicy = SOME unit ==>
  unit_alloca_budget unit.cu_context < dimword (:256)
Proof
  Cases_on `classify_functions_unit mods exps` >>
  rename1 `classify_functions_unit mods exps = classified` >>
  PairCases_on `classified` >>
  rename1 `classify_functions_unit mods exps = (exts,ints,fb,cf,ctors)` >>
  simp[lower_vyper_runtime_unit_mods_def, bool_case_eq] >> strip_tac >>
  irule lowering_context_ok_alloca_budget >>
  Cases_on `EXISTS (external_has_defaults o SND) exts` >> gvs[] >>
  metis_tac[run_grouped_lowering_context, run_lowering_context_ok]
QED

Theorem linked_external_registration_fields[local]:
  set_external_package_target target
    (package_external_fn_unit mods ut nk
      (src,(mut,nr,rr,name,args,dflts,ret,fbody))) =
    (lbl,cenv0,pos,mincd,pay,nr',key,ut',iv,body',rt) /\
  cenv = cenv0 with ce_vars := cenv.ce_vars ==>
  cenv.ce_module = src /\ ~cenv.ce_is_ctor /\
  cenv.ce_imm_alloca = NONE /\ cenv.ce_return_pc = NONE /\
  cenv.ce_module_vars =
    add_immutable_locations_unit
      (get_struct_fields (make_struct_fields_map_mods mods)) mods
      (add_module_var_locations_mods mods FEMPTY)
Proof
  strip_tac >>
  qpat_x_assum `cenv = _` (ONCE_REWRITE_TAC o single) >> simp[] >>
  qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
  simp[package_external_fn_unit_def, set_external_package_target_def,
       update_cenv_nonreentrant_def] >>
  rw[update_cenv_ret_abi_def] >>
  simp[build_compile_env_unit_def, pairTheory.UNCURRY]
QED

Theorem linked_selected_parameter_names[local]:
  source_typing_ok_mods mods exps am tx /\
  src = ALOOKUP exps tx.function_name /\
  ALOOKUP mods src = SOME tops /\
  vyperInterpreter$lookup_function src tx.function_name External tops =
    SOME (mut,nr,args,[],ret,fbody) ==>
  ALL_DISTINCT (MAP FST args)
Proof
  rpt strip_tac >> fs[source_typing_ok_mods_def] >>
  `module_allocated am.layouts tx.target src tops` by
    (Cases_on `src` >> gvs[]
     >- metis_tac[check_contract_main_module_allocated]
     >- (`ALOOKUP exps tx.function_name = SOME x` by
           qpat_x_assum `SOME x = ALOOKUP exps tx.function_name`
             (fn th => ACCEPT_TAC (SYM th)) >>
         `MEM (tx.function_name,x) exps` by metis_tac[ALOOKUP_MEM] >>
         fs[exports_ok_def, EVERY_MEM] >>
         qpat_x_assum `!e. MEM e exps ==>
           (λ(fn,src). case ALOOKUP mods (SOME src) of
              NONE => T
            | SOME tls => module_allocated am.layouts tx.target (SOME src) tls) e`
           (qspec_then `(tx.function_name,x)` mp_tac) >>
         simp[])) >>
  drule lookup_function_External_cases >> strip_tac
  >- (drule check_contract_runtime_function_body_MEM >>
      disch_then (qspecl_then
        [`External`, `tops`, `src`, `ret`, `raw`, `nr`, `mut`,
         `tx.function_name`, `[]`, `fbody`, `args`] mp_tac) >>
      simp[check_function_body_def, params_ok_def])
  >- (drule_all checked_public_getter_params_ok >> simp[params_ok_def])
QED

Theorem linked_section_runtime_relation:
  immutable_section_layout_mods mods ce /\
  immutables_section_rel_mods mods
    (case ALOOKUP es.immutables addr of
       NONE => empty_immutables | SOME imms => imms) ss.vs_data_section ==>
  immutables_rel ce addr src F es ss
Proof
  Cases_on `ALOOKUP es.immutables addr`
  >- simp[immutables_rel_def] >>
  simp[immutables_rel_def, immutable_section_layout_mods_def,
       immutables_section_rel_mods_def] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_assum `!src name off sz. immutable_region_mods _ src name off sz ==> ?tv v. _`
    (drule_then strip_assume_tac) >>
  gvs[] >> metis_tac[]
QED

Theorem linked_registration_endpoint_from_frame:
  immutable_section_layout_mods mods cenv /\
  storage_vars_rel cenv (initial_evaluation_context am.sources am.layouts tx src) /\
  transient_vars_rel cenv (initial_evaluation_context am.sources am.layouts tx src) /\
  ALL_DISTINCT (MAP FST args) /\
  unit_alloca_budget ctx < dimword (:256) /\
  ~cenv.ce_is_ctor /\ cenv.ce_imm_alloca = NONE /\ cenv.ce_return_pc = NONE /\
  vs.vs_accounts = accounts_after_transfer tx am.accounts /\
  vs.vs_transient = am.tStorage /\ am.logs = [] /\ vs.vs_logs = [] /\
  venom_env_rel tx vs /\ vs.vs_requests = [] /\
  vs.vs_pending_deletions = am.pending_deletions /\
  immutables_section_rel_mods mods (account_immutables am tx.target)
    vs.vs_data_section /\
  bind_arguments (type_env_all_modules mods) args vals = SOME env /\
  send_call_value mut (initial_evaluation_context am.sources am.layouts tx src)
    (initial_state am [env] with <|outcomes := SOME vs.vs_outcomes; requests := []|>) =
    (INL (),es0) /\
  vars_pc_only (vs with <|vs_prev_bb := NONE; vs_current_bb := elbl; vs_inst_idx := 0|>) s1 /\
  fmp_room ctx efn s0 /\
  LIST_REL (\ty tv. evaluate_type (type_env_all_modules mods) ty = SOME tv)
    (MAP SND args) tvs /\
  local_ptrs_rel efn cenv [env] s0 /\
  (!j. j < LENGTH args ==> ?aid q p n.
    FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
    FLOOKUP cenv.ce_vars (FST (EL j args)) = SOME (PtrVar (Var q) n) /\
    lookup_var q s0 = SOME (n2w p) /\ ptr_covers G0 tn0 q s0 n /\
    (!mem. mem_agree_outside tn0.t_mem s0.vs_memory mem ==>
      val_in_memory (EL j tvs) (EL j vals) p mem)) /\
  alloca_inv s0 /\ alloca_frontier_inv ctx efn site s0 /\
  tn0.t_stor = {} /\ tn0.t_trans = {} /\ tn0.t_imm = {} /\
  s0.vs_call_ctx = s1.vs_call_ctx /\ s0.vs_accounts = s1.vs_accounts /\
  s0.vs_transient = s1.vs_transient /\ s0.vs_logs = s1.vs_logs /\
  s0.vs_outcomes = s1.vs_outcomes /\ s0.vs_requests = s1.vs_requests /\
  s0.vs_pending_deletions = s1.vs_pending_deletions /\ s0.vs_tx_ctx = s1.vs_tx_ctx /\
  s0.vs_block_ctx = s1.vs_block_ctx /\ s0.vs_data_section = s1.vs_data_section /\
  s0.vs_code = s1.vs_code /\
  (!inst w b n. MEM inst (fn_insts efn) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit w] /\
    FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,n) ==> n = w2n w) ==>
  stmt_state_rel H ctx efn cenv
    (initial_evaluation_context am.sources am.layouts tx src) es0 s0 /\
  ghost_inv H NONE cenv (initial_evaluation_context am.sources am.layouts tx src)
    es0 G0 tn0 s0
Proof
  strip_tac >>
  drule send_call_value_accounts >> strip_tac >>
  `es0.scopes = [env]` by simp[initial_state_def] >>
  conj_tac >- suspend "linked_stmt" >>
  irule registration_indexed_locals_ghost >> simp[] >>
  qexistsl_tac [`args`, `type_env_all_modules mods`, `tvs`, `vals`] >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!j. j < LENGTH args ==> ?aid q p n. _`
    (qspec_then `j` mp_tac) >> simp[] >> strip_tac >>
  qexistsl_tac [`q`, `p`, `n`] >> simp[] >>
  `p + n <= s0.vs_alloca_next` by
    metis_tac[venomMemDefsTheory.alloca_inv_def,
      venomMemDefsTheory.alloca_next_valid_def] >>
  drule_all allocaFrontierBoundTheory.alloca_frontier_inv_bound >>
  decide_tac
QED

Resume linked_registration_endpoint_from_frame[linked_stmt]:
  `alloca_room ctx efn s0` by
    (drule_all registration_frontier_alloca_room >> simp[]) >>
  simp[stmt_state_rel_def, immutable_alloca_sep_def, immutable_decl_sep_def,
       immutable_base_zero_def] >>
  conj_tac >- suspend "linked_state" >> first_assum ACCEPT_TAC
QED

Resume linked_registration_endpoint_from_frame[linked_state]:
  qpat_x_assum `vars_pc_only _ s1` mp_tac >>
  simp[vars_pc_only_def, venom_state_component_equality] >> strip_tac >>
  `immutables_rel cenv tx.target cenv.ce_module F es0 s0` by
    (irule linked_section_runtime_relation >> qexists_tac `mods` >>
     gvs[initial_state_def, account_immutables_def]) >>
  gvs[venom_env_rel_def, state_rel_def, initial_state_def,
      initial_evaluation_context_def] >>
  `s0.vs_call_ctx.cc_address = tx.target` by fs[call_ctx_rel_def] >>
  simp[storage_rel_def, transient_rel_def, contract_storage_def,
       contract_transient_def, logs_rel_def, accounts_rel_def,
       accounts_agree_def, transient_agree_def]
QED

Finalise linked_registration_endpoint_from_frame

Theorem registration_actual_endpoint_relations_from_prefix_mods:
  lower_vyper_runtime_unit_mods mods exps rpolicy = SOME unit /\
  source_typing_ok_mods mods exps am tx /\
  source_deployment_rel_mods mods exps am tx /\
  value_transfer_ok tx am.accounts /\
  vs.vs_accounts = accounts_after_transfer tx am.accounts /\
  vs.vs_transient = am.tStorage /\ am.logs = [] /\ vs.vs_logs = [] /\
  venom_env_rel tx vs /\ vs.vs_requests = [] /\
  vs.vs_pending_deletions = am.pending_deletions /\
  immutables_section_rel_mods mods (account_immutables am tx.target)
    vs.vs_data_section /\
  src = ALOOKUP exps tx.function_name /\ ALOOKUP mods src = SOME tops /\
  vyperInterpreter$lookup_function src tx.function_name External tops =
    SOME (mut,nr,args,[],ret,fbody) /\
  bind_arguments (type_env_all_modules mods) args tx.args = SOME env /\
  send_call_value mut (initial_evaluation_context am.sources am.layouts tx src)
    (initial_state am [env] with <|outcomes := SOME vs.vs_outcomes; requests := []|>) =
    (INL (),es0) /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn /\
  set_external_package_target rpolicy.rpol_target
    (package_external_fn_unit mods T (K global_nonreentrant_slot)
      (src, subst_consts_fn_mods (consts_env_mods mods)
        (mut,nr,lookup_raw_return_or_F src tx.function_name External tops,
         tx.function_name,args,[],ret,fbody))) =
    (lbl,cenv0,pos_args,mincd,pay,nr,key,ut',iv,lowered_body,rt) /\
  compile_register_positional_args cenv0 pos_args 4 st = (cenv,sa) /\
  vars_pc_only (vs with <|vs_prev_bb := NONE; vs_current_bb := elbl; vs_inst_idx := 0|>) s1 /\
  fmp_room unit.cu_context efn s0 /\
  LIST_REL (\ty tv. evaluate_type (type_env_all_modules mods) ty = SOME tv)
    (MAP SND args) tvs /\
  local_ptrs_rel efn cenv [env] s0 /\
  (!j. j < LENGTH args ==> ?aid q p n.
    FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
    FLOOKUP cenv.ce_vars (FST (EL j args)) = SOME (PtrVar (Var q) n) /\
    lookup_var q s0 = SOME (n2w p) /\ ptr_covers G0 tn0 q s0 n /\
    (!mem. mem_agree_outside tn0.t_mem s0.vs_memory mem ==>
      val_in_memory (EL j tvs) (EL j tx.args) p mem)) /\
  cenv = cenv0 with ce_vars := cenv.ce_vars /\
  alloca_inv s0 /\ alloca_frontier_inv unit.cu_context efn site s0 /\
  tn0.t_stor = {} /\ tn0.t_trans = {} /\ tn0.t_imm = {} /\
  s0.vs_call_ctx = s1.vs_call_ctx /\ s0.vs_accounts = s1.vs_accounts /\
  s0.vs_transient = s1.vs_transient /\ s0.vs_logs = s1.vs_logs /\
  s0.vs_outcomes = s1.vs_outcomes /\ s0.vs_requests = s1.vs_requests /\
  s0.vs_pending_deletions = s1.vs_pending_deletions /\ s0.vs_tx_ctx = s1.vs_tx_ctx /\
  s0.vs_block_ctx = s1.vs_block_ctx /\ s0.vs_data_section = s1.vs_data_section /\
  s0.vs_code = s1.vs_code /\
  (!inst w b n. MEM inst (fn_insts efn) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit w] /\
    FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,n) ==> n = w2n w) ==>
  stmt_state_rel H unit.cu_context efn cenv
    (initial_evaluation_context am.sources am.layouts tx src) es0 s0 /\
  ghost_inv H NONE cenv (initial_evaluation_context am.sources am.layouts tx src)
    es0 G0 tn0 s0
Proof
  strip_tac >>
  qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
  pure_rewrite_tac[subst_consts_fn_mods_def] >> strip_tac >>
  drule_all linked_external_registration_fields >> strip_tac >>
  `ALL_DISTINCT (MAP FST mods) /\
   ALL_DISTINCT (contract_keys toplevel_vtype_keys_toplevel mods)` by
    (qpat_assum `source_typing_ok_mods mods exps am tx`
       (strip_assume_tac o REWRITE_RULE [source_typing_ok_mods_def]) >>
     drule check_contract_namespaces_ok >> simp[contract_namespaces_ok_def]) >>
  `immutable_section_layout_mods mods cenv` by
    (irule unit_module_locations_immutable_layout >> simp[] >>
     qexistsl_tac [`am`, `exps`, `tx`] >> fs[source_deployment_rel_mods_def]) >>
  `storage_vars_rel cenv (initial_evaluation_context am.sources am.layouts tx src) /\
   transient_vars_rel cenv (initial_evaluation_context am.sources am.layouts tx src)` by
    (irule unit_module_locations_slot_relations >>
     simp[initial_evaluation_context_def] >> metis_tac[]) >>
  `ALL_DISTINCT (MAP FST args)` by
    (drule_all linked_selected_parameter_names >> simp[]) >>
  drule linked_runtime_unit_alloca_budget >> strip_tac >>
  drule_all linked_registration_endpoint_from_frame >> simp[]
QED
