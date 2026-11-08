Theory ctorDeployMemoryRunMemEntryLanding
Ancestors
  loweringStateRelDefs
  ctorDeployLoweringEntryStateRel
 ctorDeployMemoryRunMemEntryProvenance ctorDeployMemoryRunMemEntryResources
 ctorDeployMemoryRunMemEntrySourceWorld ctorDeployMemoryRunMemEntryZeroImmutables
 ctorDeployMemoryRunMemEntryRegisterEnv ctorDeployLoweringFrame
 ctorDeployLoweringEntryTransport entryStateRel compileEnv compileVyper
 ctorDeployDefs e2eDeployDefs e2eDefs vyperContext vyperTypeContract finite_map list
 supportedProgram vyperTypeContractContext vyperInterpreter immutableLocationProps immutableRelation
 ctorDeployMemoryRunMemEntryTaskInputs ctorDeployLoweringEntrySourceFrame ctorRegisterArgs

Theorem ctor_landing_storage_layout:
 !tops am tx cenv cx.
 supported_declaration_headers tops /\
 ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
 source_deployment_rel tops am tx /\
 cx.sources = am.sources /\ cx.layouts = am.layouts /\
 cx.txn.target = tx.target /\ cenv.ce_module = NONE /\
 cenv.ce_module_vars = add_immutable_locations
   (get_struct_fields (make_struct_fields_map tops)) tops 0
   (add_module_var_locations tops FEMPTY) ==>
 storage_vars_rel cenv cx /\ transient_vars_rel cenv cx
Proof
 rpt gen_tac >> strip_tac >>
 `storage_vars_rel (cenv with ce_module_vars := add_module_var_locations tops FEMPTY) cx /\
  transient_vars_rel (cenv with ce_module_vars := add_module_var_locations tops FEMPTY) cx` by
   (irule entry_storage_vars_rel >> simp[] >>
    qexistsl [`am`, `tops`, `tx`] >> simp[]) >>
 `!key loc vis name ty slot.
   FLOOKUP (add_module_var_locations tops FEMPTY) key = SOME loc /\
   MEM (VariableDecl vis Immutable name ty slot) tops ==> (NONE,name) <> key` by
   (rpt strip_tac >> gvs[] >>
    drule entryStateRelTheory.add_module_var_locations_mem >>
    disch_then (qspecl_then [`FEMPTY`, `VariableDecl vis Immutable name ty slot`, `name`] mp_tac) >>
    simp[toplevel_vtype_keys_toplevel_def] >>
    Cases_on `slot` >> simp[add_module_var_locations_def]) >>
 `!key slot.
   (FLOOKUP (add_immutable_locations
     (get_struct_fields (make_struct_fields_map tops)) tops 0
     (add_module_var_locations tops FEMPTY)) key = SOME (StorageLoc slot) <=>
    FLOOKUP (add_module_var_locations tops FEMPTY) key = SOME (StorageLoc slot)) /\
   (FLOOKUP (add_immutable_locations
     (get_struct_fields (make_struct_fields_map tops)) tops 0
     (add_module_var_locations tops FEMPTY)) key = SOME (TransientLoc slot) <=>
    FLOOKUP (add_module_var_locations tops FEMPTY) key = SOME (TransientLoc slot))` by
   (rpt gen_tac >> conj_tac >> eq_tac >> strip_tac
    >- (drule add_immutable_locations_FLOOKUP >> simp[])
    >- (`!vis name ty sl. MEM (VariableDecl vis Immutable name ty sl) tops ==> (NONE,name) <> key` by metis_tac[] >>
         drule add_immutable_locations_lookup_unchanged >> simp[])
    >- (drule add_immutable_locations_FLOOKUP >> simp[])
    >- (`!vis name ty sl. MEM (VariableDecl vis Immutable name ty sl) tops ==> (NONE,name) <> key` by metis_tac[] >>
         drule add_immutable_locations_lookup_unchanged >> simp[])) >>
 `!src ts. get_module_code cx src = SOME ts ==> src = NONE /\ ts = tops` by
   (gvs[source_deployment_rel_def, get_module_code_def] >> Cases >> simp[]) >>
 gvs[storage_vars_rel_def, transient_vars_rel_def] >>
 conj_tac >> rpt gen_tac >> strip_tac >>
 first_x_assum drule >> strip_tac >> gvs[] >>
 first_assum drule_all >> simp[]
QED

Theorem ctor_task_landing_layout:
 !tops am tx deploy_bc es rpolicy runtime_bc dunit body cenv nr nkey ut imm exit_lbl
  sa sb sj st_exit st_epilogue st_final func.
 deploy_source_ok tops am tx /\
 deploy_state_rel tops deploy_bc am tx es /\
 deploy_ctor_code tops rpolicy runtime_bc dunit
   (body,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,st_epilogue,st_final,func) ==>
 storage_vars_rel cenv (deploy_evaluation_context tops am tx) /\
 transient_vars_rel cenv (deploy_evaluation_context tops am tx)
Proof
 rpt gen_tac >> strip_tac >> drule deploy_ctor_module_locations >> strip_tac >>
 `supported_declaration_headers tops` by
   gvs[deploy_source_ok_def, supported_program_def] >>
 `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))` by
   (gvs[deploy_source_ok_def, deploy_typing_ok_def] >>
    drule check_contract_namespaces_ok >>
    simp[contract_namespaces_ok_def, contract_keys_def]) >>
 irule ctor_landing_storage_layout >>
 simp[] >>
 qexistsl [`am with <|sources := (tx.target,[(NONE,tops)])::am.sources;
                     exports := [] |>`, `tops`, `tx`] >>
 gvs[deploy_evaluation_context_def, initial_evaluation_context_def,
     source_deployment_rel_def, deploy_state_rel_def, layouts_agree_def]
QED

Theorem ctor_landing_immutable_layout:
 !tops cenv.
 cenv.ce_module_vars = add_immutable_locations
   (get_struct_fields (make_struct_fields_map tops)) tops 0
   (add_module_var_locations tops FEMPTY) ==>
 immutable_section_layout cenv tops
Proof
 rpt gen_tac >> strip_tac >>
 mp_tac (Q.SPEC `tops` immutable_build_compile_env_layout) >>
 simp[immutable_section_layout_def, build_compile_env_module_vars]
QED

Theorem ctor_task_landing_state_rel:
 !tops am tx deploy_bc es rpolicy runtime_bc dunit body cenv nr nkey ut imm exit_lbl
  sa sb sj st_exit st_epilogue st_final func mut am_c es0 actual os.
 deploy_source_ok tops am tx /\ deploy_state_rel tops deploy_bc am tx es /\
 deploy_ctor_start tops am tx (mut,nr,body,am_c,es0) /\
 deploy_ctor_code tops rpolicy runtime_bc dunit
   (body,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,st_epilogue,st_final,func) /\
 local_ptrs_rel func cenv es0.scopes actual /\
 (!p. p < imm_len tops ==> mem_bytes_at p 1 actual.vs_memory = mem_bytes_at p 1 []) /\
 actual.vs_accounts = accounts_after_transfer tx am.accounts /\
 actual.vs_transient = am.tStorage /\ actual.vs_call_ctx.cc_address = tx.target /\
 actual.vs_logs = [] /\ actual.vs_requests = [] /\ actual.vs_pending_deletions = [] /\
 call_ctx_rel tx actual.vs_call_ctx actual.vs_tx_ctx actual.vs_block_ctx /\
 ~actual.vs_call_ctx.cc_static /\ ~tx.is_static /\ actual.vs_outcomes = os ==>
 state_rel func cenv (deploy_evaluation_context tops am tx)
   (es0 with outcomes := SOME os) actual
Proof
 rpt gen_tac >> strip_tac >>
 drule_all ctor_task_landing_layout >> strip_tac >>
 drule deploy_ctor_module_locations >> strip_tac >>
 drule deploy_ctor_return_metadata >> strip_tac >>
 drule ctor_landing_immutable_layout >> strip_tac >>
 drule_all ctor_source_zero_memory_immutables >>
 disch_then (qspec_then `os` assume_tac) >>
 drule_all ctor_source_landing_world >>
 disch_then strip_assume_tac >>
 drule_all ctor_source_start_world_fields >> strip_tac >>
 simp[state_rel_def, logs_rel_def] >>
 gvs[deploy_evaluation_context_def, initial_evaluation_context_def]
QED

Theorem ctor_landing_phase_metadata:
 !tops rpolicy runtime_bc dunit body cenv nr nkey ut imm exit_lbl sa sb sj
  st_exit st_epilogue st_final func exts ints fb cf ce_pack pos_args pay ret
  ce0 st_pay st1 ce1 st2.
 deploy_ctor_code tops rpolicy runtime_bc dunit
   (body,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,st_epilogue,st_final,func) /\
 ~nr /\ classify_functions tops = (exts,ints,fb,SOME cf) /\
 package_constructor tops F (assign_nkeys tops 0) cf =
   (ce_pack,pos_args,pay,nr,nkey,ut,body,ret) /\
 ce0 = ((ce_pack with ce_target := rpolicy.rpol_target) with
   ce_imm_alloca := (if imm_len tops > 0 then SOME imm else NONE)) /\
 (if pay then comp_return () else
   comp_bind (emit_op CALLVALUE []) (\cv.
     comp_bind (emit_op ISZERO [cv]) (\nv. emit_void ASSERT [nv])))
   (initial_compile_state "__deploy") = ((),st_pay) /\
 (if imm_len tops > 0 then comp_bind (compile_fixed_region_with_id (imm_len tops))
   (\r. comp_return (SND r).buf_operand) else comp_return (Lit 0w)) st_pay = (imm,st1) /\
 compile_register_constructor_args ce0 pos_args 0 0 st1 = (ce1,st2) ==>
 cenv = ce1 with ce_ctor_exit_label := SOME exit_lbl /\
 sa.cs_current_bb = st2.cs_current_bb /\ sa.cs_current_insts = st2.cs_current_insts
Proof
 rpt gen_tac >> strip_tac >>
 qpat_x_assum `deploy_ctor_code _ _ _ _ _` mp_tac >>
 pure_rewrite_tac[ctorDeployLoweringDefsTheory.deploy_ctor_code_def] >> strip_tac >>
 gvs[set_constructor_package_target_def, comp_return_def, fresh_label_def]
QED

Theorem ctor_landing_source_scopes:
 !tops am tx mut nr stmts am_c es0 rpolicy runtime_bc dunit deploy_bc es
  exts ints fb rr fname fargs dflts ret scope.
 lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
 classify_functions tops = (exts,ints,fb,SOME (mut,nr,rr,fname,fargs,dflts,ret,stmts)) /\
 deploy_source_ok tops am tx /\ deploy_state_rel tops deploy_bc am tx es /\
 deploy_ctor_start tops am tx (mut,nr,stmts,am_c,es0) /\
 bind_arguments (type_env tops) fargs tx.args = SOME scope ==>
 es0.scopes = [scope]
Proof
 rpt gen_tac >> strip_tac >>
 drule_all ctor_task_aligned_inputs >> strip_tac >>
 `tx.function_name = "__init__"` by gvs[deploy_state_rel_def] >>
 `vyperInterpreter$lookup_function NONE tx.function_name Deploy tops =
   SOME (mut,F,fargs,[],NoneT,stmts)` by
   (qspecl_then [`tops`, `NONE`, `fname`] mp_tac deploy_frame_classified_constructor_lookup >> simp[]) >>
 gvs[] >> metis_tac[deploy_ctor_source_start_fields]
QED

Theorem ctor_landing_env_exit_label:
 !func ce lbl scopes s.
 (local_ptrs_rel func (ce with ce_ctor_exit_label := SOME lbl) scopes s <=>
  local_ptrs_rel func ce scopes s) /\
 (!id b sz. local_region (ce with ce_ctor_exit_label := SOME lbl) scopes s id b sz <=>
   local_region ce scopes s id b sz)
Proof
 simp[local_ptrs_rel_def, local_region_def]
QED

Theorem ctor_landing_package_target_invert:
 !target pkg ce args pay nr nk ut stmts ret.
 compileVyper$set_constructor_package_target target pkg = (ce,args,pay,nr,nk,ut,stmts,ret) ==>
 ?raw. pkg = (raw,args,pay,nr,nk,ut,stmts,ret) /\ ce = raw with ce_target := target
Proof
 rpt gen_tac >> PairCases_on `pkg` >>
 simp[compileVyperTheory.set_constructor_package_target_def] >>
 rpt strip_tac >> gvs[]
QED

Theorem ctor_landing_package_payable:
 !tops use_trans keys mut nr rr name args defaults ret stmts ce ps pay nr' nk ut stmts' ret'.
 package_constructor tops use_trans keys (mut,nr,rr,name,args,defaults,ret,stmts) =
   (ce,ps,pay,nr',nk,ut,stmts',ret') ==> pay = (mut = Payable)
Proof
 simp[compileVyperTheory.package_constructor_def] >> metis_tac[]
QED

Theorem ctor_landing_package_result_fields:
 !tops use_trans keys mut nr rr name args defaults ret stmts ce ps pay nr' nk ut stmts' ret'.
 package_constructor tops use_trans keys (mut,nr,rr,name,args,defaults,ret,stmts) =
   (ce,ps,pay,nr',nk,ut,stmts',ret') ==>
 pay = (mut = Payable) /\ nr' = nr /\ ut = use_trans /\ stmts' = stmts /\ ret' = ret
Proof
 simp[compileVyperTheory.package_constructor_def] >> metis_tac[]
QED
