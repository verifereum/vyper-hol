(* Raw accepted calldata: reconstruct the endpoint relations from the
   registration fold's concrete resources, without canonical call encoding. *)
Theory dispatchedSelectedRelations
Ancestors
  entryPtrSeamRegister entryStateRel bodyPtrDefs moduleLowering
  loweringStateRelDefs supportedProgram vyperInterpreter vyperContext
  compileEnv entryLocals exprLoweringProps vyperCompiler venomState
  venomExecSemantics ptrDiscipline immutableRelation immutableLocationProps
  immutableSectionRel allocaFrontierBound e2eDefs compileVyper
  moduleLoweringProps vyperLoweringCorrect

Theorem dispatched_selected_actual_endpoint_relations:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  source_deployment_rel tops am tx /\
  ALL_DISTINCT (MAP FST args) /\
  unit_alloca_budget unit.cu_context < dimword (:256) /\
  tx.function_name <> "__default__" /\
  initial_venom_state_rel tops am tx vs /\
  lookup_function NONE tx.function_name External tops = SOME (mut,F,args,[],ret,fbody) /\
  bind_arguments (type_env tops) args tx.args = SOME env /\
  send_call_value mut (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [env] with <|outcomes := SOME vs.vs_outcomes; requests := []|>) =
    (INL (),es0) /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn /\
  set_external_package_target rpolicy.rpol_target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (mut,F,lookup_raw_return_or_F (NONE:num option) tx.function_name External tops,
       tx.function_name,args,[],ret,fbody)) =
    (lbl,cenv0,pos_args,mincd,pay,F,key,ut',iv,fbody,rt) /\
  compile_register_positional_args cenv0 pos_args 4 st = (cenv,sa) /\
  vars_pc_only (vs with <|vs_prev_bb := NONE; vs_current_bb := elbl; vs_inst_idx := 0|>) s1 /\
  ~ctx_has_dalloca unit.cu_context /\
  LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) (MAP SND args) tvs /\
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
    (initial_evaluation_context am.sources am.layouts tx NONE) es0 s0 /\
  ghost_inv H NONE cenv (initial_evaluation_context am.sources am.layouts tx NONE)
    es0 G0 tn0 s0
Proof
  strip_tac >>
  drule send_call_value_accounts >> strip_tac >>
  `es0.scopes = [env]` by simp[initial_state_def] >>
  conj_tac >- suspend "stmt" >>
  irule registration_indexed_locals_ghost >>
  conj_tac >- suspend "return_pc" >> simp[] >>
  qexistsl_tac [`args`, `type_env tops`, `tvs`, `tx.args`] >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!j. j < LENGTH args ==> ?aid q p n. _`
    (qspec_then `j` mp_tac) >> simp[] >> strip_tac >>
  qexistsl_tac [`q`, `p`, `n`] >> simp[] >>
  `p + n <= s0.vs_alloca_next` by
    metis_tac[venomMemDefsTheory.alloca_inv_def,
      venomMemDefsTheory.alloca_next_valid_def] >>
  qpat_x_assum `alloca_frontier_inv _ _ _ s0` mp_tac >>
  simp[allocaFrontierBoundTheory.alloca_frontier_inv_def] >> decide_tac
QED

Resume dispatched_selected_actual_endpoint_relations[return_pc]:
  `cenv.ce_return_pc = cenv0.ce_return_pc` by
    (qpat_assum `cenv = cenv0 with ce_vars := cenv.ce_vars`
      (fn th => pure_once_rewrite_tac[th]) >> simp[]) >>
  `cenv0.ce_return_pc = NONE` by
    (qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[package_external_fn_def, set_external_package_target_def] >> strip_tac >>
     gvs[update_cenv_nonreentrant_def] >>
     rw[update_cenv_ret_abi_def, build_compile_env_def] >>
     rpt (pairarg_tac >> gvs[])) >> simp[]
QED

Resume dispatched_selected_actual_endpoint_relations[stmt]:
  `cenv0.ce_module = NONE /\ ~cenv0.ce_is_ctor /\
   cenv0.ce_imm_alloca = NONE /\
   cenv0.ce_module_vars = add_immutable_locations
     (get_struct_fields (make_struct_fields_map tops)) tops 0
     (add_module_var_locations tops FEMPTY)` by
    (qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[package_external_fn_def, set_external_package_target_def] >> strip_tac >>
     gvs[update_cenv_nonreentrant_def] >>
     rw[update_cenv_ret_abi_def, build_compile_env_def] >>
     rpt (pairarg_tac >> gvs[])) >>
  `cenv.ce_module = NONE /\ ~cenv.ce_is_ctor /\
   cenv.ce_imm_alloca = NONE /\ cenv.ce_module_vars = cenv0.ce_module_vars` by
    (qpat_assum `cenv = cenv0 with ce_vars := cenv.ce_vars`
      (fn th => pure_once_rewrite_tac[th]) >> simp[]) >>
  `alloca_room unit.cu_context efn s0` by
    (drule_all registration_frontier_alloca_room >> simp[]) >>
  `fmp_room unit.cu_context efn s0` by
    (irule registration_no_dalloca_fmp_room >> simp[] >>
     drule vyperCompilerTheory.lookup_function_result_name >> simp[]) >>
  simp[stmt_state_rel_def, immutable_alloca_sep_def, immutable_decl_sep_def,
       immutable_base_zero_def] >>
  conj_tac >- suspend "state" >> first_assum ACCEPT_TAC
QED

Resume dispatched_selected_actual_endpoint_relations[state]:
  `storage_vars_rel cenv (initial_evaluation_context am.sources am.layouts tx NONE) /\
   transient_vars_rel cenv (initial_evaluation_context am.sources am.layouts tx NONE)` by
    suspend "module_locations" >>
  `immutable_section_layout cenv tops` by
    (qspecl_then [`tops`, `External`, `mut`, `tx.function_name`, `args`, `ret`,
       `fbody`, `F`] mp_tac
       immutableLocationPropsTheory.immutable_build_compile_env_layout >>
     qpat_x_assum `cenv.ce_module_vars = cenv0.ce_module_vars` mp_tac >>
     qpat_x_assum `cenv0.ce_module_vars = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[immutableRelationTheory.immutable_section_layout_def,
       build_compile_env_def] >> rpt (pairarg_tac >> gvs[])) >>
  `immutables_rel cenv
    (initial_evaluation_context am.sources am.layouts tx NONE).txn.target
    cenv.ce_module cenv.ce_is_ctor es0 s0` by suspend "immutables" >>
  qpat_x_assum `vars_pc_only _ s1` mp_tac >>
  simp[vars_pc_only_def, venom_state_component_equality] >> strip_tac >>
  gvs[initial_venom_state_rel_def, venom_env_rel_def, state_rel_def,
      initial_state_def, initial_evaluation_context_def] >>
  `s0.vs_call_ctx.cc_address = tx.target` by fs[call_ctx_rel_def] >>
  simp[storage_rel_def, transient_rel_def, contract_storage_def,
       contract_transient_def, logs_rel_def, accounts_rel_def]
QED

Resume dispatched_selected_actual_endpoint_relations[immutables]:
  simp[] >> irule immutableSectionRelTheory.immutables_section_rel_runtime_fallback >>
  qexistsl_tac [`vs.vs_data_section`, `tops`] >> simp[] >>
  qpat_x_assum `vars_pc_only _ s1` mp_tac >>
  simp[vars_pc_only_def, venom_state_component_equality] >> strip_tac >>
  gvs[initial_venom_state_rel_def, initial_state_def, e2eDefsTheory.account_immutables_def,
      initial_evaluation_context_def]
QED

Resume dispatched_selected_actual_endpoint_relations[module_locations]:
  `supported_declaration_headers tops` by fs[supported_program_def] >>
  drule source_typing_ok_vtype_keys_distinct >> strip_tac >>
  `storage_vars_rel
     (cenv with ce_module_vars := add_module_var_locations tops FEMPTY)
     (initial_evaluation_context am.sources am.layouts tx NONE) /\
   transient_vars_rel
     (cenv with ce_module_vars := add_module_var_locations tops FEMPTY)
     (initial_evaluation_context am.sources am.layouts tx NONE)` by
    (irule entry_storage_vars_rel >> simp[initial_evaluation_context_def] >>
     qexistsl_tac [`am`, `tops`, `tx`] >> simp[]) >>
  `(!key slot.
     (FLOOKUP (add_immutable_locations
       (get_struct_fields (make_struct_fields_map tops)) tops 0
       (add_module_var_locations tops FEMPTY)) key = SOME (StorageLoc slot) <=>
      FLOOKUP (add_module_var_locations tops FEMPTY) key = SOME (StorageLoc slot))) /\
   (!key slot.
     (FLOOKUP (add_immutable_locations
       (get_struct_fields (make_struct_fields_map tops)) tops 0
       (add_module_var_locations tops FEMPTY)) key = SOME (TransientLoc slot) <=>
      FLOOKUP (add_module_var_locations tops FEMPTY) key = SOME (TransientLoc slot)))` by
    (conj_tac >> rpt gen_tac >> eq_tac
     >- (strip_tac >> drule add_immutable_locations_FLOOKUP >> simp[])
     >- (strip_tac >> suspend "insert")
     >- (strip_tac >> drule add_immutable_locations_FLOOKUP >> simp[]) >>
     strip_tac >> suspend "insert") >>
  mp_tac (module_location_relations_cong |> Q.SPECL
    [`cenv`, `cenv with ce_module_vars := add_module_var_locations tops FEMPTY`,
     `initial_evaluation_context am.sources am.layouts tx NONE`]) >>
  simp[]
QED

Resume dispatched_selected_actual_endpoint_relations[insert]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  rename1 `FLOOKUP (add_module_var_locations tops FEMPTY) ky = SOME _` >>
  `!vis name ty sl.
    MEM (VariableDecl vis Immutable name ty sl) tops ==> (NONE,name) <> ky` by
    (rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
     drule_then (qspecl_then
       [`FEMPTY`, `VariableDecl vis Immutable name ty sl`, `name`] mp_tac)
       add_module_var_locations_mem >>
     simp[vyperTypeContractTheory.toplevel_vtype_keys_toplevel_def] >>
     Cases_on `sl` >> simp[add_module_var_locations_def]) >>
  drule add_immutable_locations_lookup_unchanged >> simp[]
QED

Finalise dispatched_selected_actual_endpoint_relations
