Theory ctorDeployLoweringEntryStateRel
Ancestors
 ctorDeployLoweringEntryBodyResources ctorDeployLoweringEntrySourceFrame
 entryStateRel ctorDeployEntry abiEncoderCorrect o1PassContract
 ctorDeployLoweringDefs ctorDeployLoweringEntryTransport vyperInterpreter vyperState
 e2eDeployDefs e2eDefs compileEnv exprLoweringProps
 ctorDeployDefs abiEncoder moduleLowering e2eEntry venomState
 abiEncoderRegisteredEffect moduleLoweringProps
 supportedProgram supportedNames supportedDecls immutableLocationProps
 vyperTypeContract vyperTypeContractStaticMaps vyperAST vyperContext
 ctorDeployLoweringFrame compileVyper

Theorem deploy_ctor_body_source_frame:
 !tops am tx mut body am_c es0.
 deploy_ctor_start tops am tx (mut,F,body,am_c,es0) ==>
 es0.tStorage = am.tStorage /\ es0.logs = am.logs /\
 es0.requests = [] /\ es0.pending_deletions = am.pending_deletions /\
 es0.accounts = accounts_after_transfer tx am.accounts
Proof
 rpt gen_tac >> strip_tac >>
 qpat_x_assum `deploy_ctor_start _ _ _ _` mp_tac >>
 simp[deploy_ctor_start_def, deploy_ctor_singleton_type_env,
      lock_if_nr_def, ignore_bind_def, bind_def, return_def, AllCaseEqs()] >>
 strip_tac >>
 drule deploy_ctor_send_value_frame >>
 drule deploy_ctor_send_value_accounts >>
 drule deploy_ctor_all_constants_frame >>
 simp[initial_state_def, deploy_evaluation_context_def,
      initial_evaluation_context_def, accounts_after_transfer_def] >>
 rpt strip_tac >>
 fs[evaluation_state_component_equality, abstract_machine_component_equality]
QED

Theorem deploy_ctor_entry_ambient:
 !tops deploy_bc am tx es prog cp vs.
 deploy_state_rel tops deploy_bc am tx es /\
 gas_variant vs (deploy_entry_state prog cp tops es) ==>
 vs.vs_accounts = accounts_after_transfer tx am.accounts /\
 vs.vs_transient = am.tStorage /\ vs.vs_logs = [] /\
 vs.vs_requests = [] /\ vs.vs_pending_deletions = am.pending_deletions /\
 call_ctx_rel tx vs.vs_call_ctx vs.vs_tx_ctx vs.vs_block_ctx /\
 ~vs.vs_call_ctx.cc_static /\ ~tx.is_static /\ am.logs = []
Proof
 rpt gen_tac >>
 simp[deploy_state_rel_def, gas_variant_def, deploy_entry_state_def,
      entry_venom_state_def, init_venom_state_def] >> strip_tac >>
 gvs[venom_state_component_equality, call_ctx_rel_def, tx_block_fields_rel_def] >>
 qpat_x_assum `_ = vs.vs_call_ctx` (assume_tac o GSYM) >>
 qpat_x_assum `_ = vs.vs_tx_ctx` (assume_tac o GSYM) >>
 qpat_x_assum `_ = vs.vs_block_ctx` (assume_tac o GSYM) >> simp[]
QED
(* Deployment analogue of entryStateRel's private immutable-map boundary. *)
Theorem deploy_ctor_module_lookup_immutable_frame[local]:
 !tops sft off key loc.
 ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
 FLOOKUP (add_module_var_locations tops FEMPTY) key = SOME loc ==>
 FLOOKUP (add_immutable_locations sft tops off
   (add_module_var_locations tops FEMPTY)) key = SOME loc
Proof
 rpt gen_tac >> strip_tac >>
 `!vis name ty slot.
   MEM (VariableDecl vis Immutable name ty slot) tops ==> (NONE,name) <> key` by
  (rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
   drule_then (qspecl_then
     [`FEMPTY`, `VariableDecl vis Immutable name ty slot`, `name`] mp_tac)
     add_module_var_locations_mem >>
   simp[toplevel_vtype_keys_toplevel_def] >>
   Cases_on `slot` >> simp[add_module_var_locations_def]) >>
 drule add_immutable_locations_lookup_unchanged >> simp[]
QED

Theorem deploy_ctor_storage_vars_rel:
 !tops am tx cenv.
 deploy_source_ok tops am tx /\ deploy_state_rel tops deploy_bc am tx es /\
 cenv.ce_module = NONE /\
 cenv.ce_module_vars = add_immutable_locations
  (get_struct_fields (make_struct_fields_map tops)) tops 0
  (add_module_var_locations tops FEMPTY) ==>
 storage_vars_rel cenv (deploy_evaluation_context tops am tx) /\
 transient_vars_rel cenv (deploy_evaluation_context tops am tx)
Proof
 rpt gen_tac >> strip_tac >>
 `supported_declaration_headers tops` by fs[deploy_source_ok_def, supported_program_def] >>
 `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))` by
  (fs[deploy_source_ok_def, deploy_typing_ok_def, check_contract_def] >>
   drule contract_namespaces_ok_module_toplevel_vtype_keys >> simp[]) >>
 `layouts_agree tops am tx` by fs[deploy_state_rel_def] >>
 `storage_vars_rel (cenv with ce_module_vars := add_module_var_locations tops FEMPTY)
    (deploy_evaluation_context tops am tx) /\
  transient_vars_rel (cenv with ce_module_vars := add_module_var_locations tops FEMPTY)
    (deploy_evaluation_context tops am tx)` by
  (irule entry_storage_vars_rel >> simp[] >>
   qexistsl_tac [`am with <|sources := (tx.target,[(NONE,tops)])::am.sources;
     exports := []|>`, `tops`, `tx`] >>
   fs[source_deployment_rel_def, deploy_evaluation_context_def,
     initial_evaluation_context_def, layouts_agree_def]) >>
 `!key slot.
  (FLOOKUP cenv.ce_module_vars key = SOME (StorageLoc slot) <=>
   FLOOKUP (add_module_var_locations tops FEMPTY) key = SOME (StorageLoc slot)) /\
  (FLOOKUP cenv.ce_module_vars key = SOME (TransientLoc slot) <=>
   FLOOKUP (add_module_var_locations tops FEMPTY) key = SOME (TransientLoc slot))` by
  (rpt gen_tac >> asm_rewrite_tac[] >> conj_tac >> eq_tac >> strip_tac
   >- (drule add_immutable_locations_FLOOKUP >> simp[])
   >- (irule deploy_ctor_module_lookup_immutable_frame >> simp[])
   >- (drule add_immutable_locations_FLOOKUP >> simp[])
   >- (irule deploy_ctor_module_lookup_immutable_frame >> simp[])) >>
 gvs[storage_vars_rel_def, transient_vars_rel_def] >>
 conj_tac >> rpt gen_tac >> strip_tac >>
 first_x_assum drule >> strip_tac >> gvs[] >>
 first_assum drule_all >> simp[]
QED


Theorem deploy_ctor_entry_body_state_rel:
 !policy tops deploy_bc runtime_bc rp unit dout prog cplan am tx es vs
 body cenv nr key ut imm lbl sa sb sj se sp sf func mut nr' body' am_c es0
 ce1 st1 st2 fargs scope initial actual.
 deploy_phases policy tops (deploy_bc,runtime_bc) (rp,unit,dout,prog,cplan) /\
 deploy_source_ok tops am tx /\ deploy_state_rel tops deploy_bc am tx es /\
 gas_variant vs (deploy_entry_state prog cplan tops es) /\
 deploy_ctor_code tops rp runtime_bc unit
   (body,cenv,nr,key,ut,imm,lbl,sa,sb,sj,se,sp,sf,func) /\
 deploy_ctor_start tops am tx (mut,nr',body',am_c,es0) /\
 nr = F /\ nr' = nr /\ body' = body /\
 cenv = (ce1 with ce_ctor_exit_label := SOME lbl) /\
 fresh_label "ctor_exit" st2 = (lbl,sa) /\
 bind_arguments (type_env tops) fargs tx.args = SOME scope /\
 es0.scopes = [scope] /\ local_ptrs_rel func ce1 [scope] actual /\
 abi_encoder_registered_effect (frag_ids st1 st2) [] initial actual /\
 vars_pc_only vs initial /\ initial.vs_memory = vs.vs_memory /\
 alloca_inv actual /\ alloca_room unit.cu_context func actual /\
 fmp_room unit.cu_context func actual /\
 immutables_rel cenv tx.target NONE T es0 actual /\
 immutable_alloca_sep func cenv (deploy_evaluation_context tops am tx) es0 actual /\
 immutable_base_zero cenv actual /\
 (!inst n b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   inst.inst_operands = [Lit n] /\
   FLOOKUP actual.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) /\
 actual.vs_data_section = vs.vs_data_section /\
 actual.vs_call_ctx = vs.vs_call_ctx /\ actual.vs_labels = vs.vs_labels /\
 ~actual.vs_halted /\ actual.vs_current_bb = st2.cs_current_bb /\
 actual.vs_inst_idx = LENGTH st2.cs_current_insts /\
 actual.vs_gas_readings = vs.vs_gas_readings /\ actual.vs_code = vs.vs_code /\
 actual.vs_outcomes = vs.vs_outcomes /\ actual.vs_tx_ctx = vs.vs_tx_ctx /\
 actual.vs_block_ctx = vs.vs_block_ctx ==>
 state_rel func cenv (deploy_evaluation_context tops am tx)
   (es0 with outcomes := SOME vs.vs_outcomes) actual
Proof
 rpt gen_tac >> strip_tac >>
 drule deploy_ctor_entry_immutable_layout >> strip_tac >>
 drule deploy_ctor_entry_immutable_config >> strip_tac >>
 drule deploy_ctor_module_locations >> strip_tac >>
 drule_all deploy_ctor_storage_vars_rel >> strip_tac >>
 gvs[] >>
 drule deploy_ctor_body_source_frame >> strip_tac >>
 drule_all deploy_ctor_entry_ambient >> strip_tac >>
 `actual.vs_accounts = vs.vs_accounts /\ actual.vs_transient = vs.vs_transient /\
  actual.vs_logs = vs.vs_logs /\ actual.vs_requests = vs.vs_requests /\
  actual.vs_pending_deletions = vs.vs_pending_deletions` by
  (fs[abi_encoder_registered_effect_def, vars_pc_only_def,
      venom_state_component_equality]) >>
 `local_ptrs_rel func (ce1 with ce_ctor_exit_label := SOME lbl) [scope] actual` by
  (qpat_x_assum `local_ptrs_rel _ _ _ _` mp_tac >>
   simp[local_ptrs_rel_def, local_region_def]) >>
 `immutables_rel (ce1 with ce_ctor_exit_label := SOME lbl) tx.target NONE T
   (es0 with outcomes := SOME vs.vs_outcomes) actual` by
  (qpat_x_assum `immutables_rel _ _ _ _ _ _` mp_tac >> simp[immutables_rel_def]) >>
 `vs.vs_call_ctx.cc_address = tx.target` by fs[call_ctx_rel_def] >>
 simp[state_rel_def, deploy_evaluation_context_def, initial_evaluation_context_def,
      storage_rel_def, transient_rel_def,
      accounts_rel_def, logs_rel_def, contract_storage_def, contract_transient_def]
QED
