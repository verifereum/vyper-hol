Theory ctorDeployMemoryRunMemEntryTaskActual
Ancestors
  ctorDeployMemoryRunMemEntryTaskInitial ctorDeployMemoryRunMemEntryTaskInputs
  ctorDeployMemoryRunMemEntryShiftedRegistration
  ctorDeployMemoryRunMemEntryTaskRegistration ctorDeployMemoryRunMemEntrySupport
  ctorDeployMemoryRunMemEntryPhaseAdapters
  ctorDeployMemoryRunMemEntryFormalBound
  abiDecoderTypedContract abiDecoderCoherence contextProps fragGasPathMem
  list rich_list words

Theorem ctor_task_actual_phase_contracts:
  !tops rpolicy runtime_bc dunit body cenv nr nkey ut imm exit_lbl sa sb sj
   st_exit st_epilogue st_final func exts ints fb cf ce_pack pos_args pay ret
   ce0 st_pay st1 ce1 st2.
  deploy_ctor_code tops rpolicy runtime_bc dunit
    (body,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,st_epilogue,st_final,func) /\
  classify_functions tops = (exts,ints,fb,SOME cf) /\
  package_constructor tops F (assign_nkeys tops 0) cf =
    (ce_pack,pos_args,pay,nr,nkey,ut,body,ret) /\
  ce0 = ((ce_pack with ce_target := rpolicy.rpol_target) with
    ce_imm_alloca := (if imm_len tops > 0 then SOME imm else NONE)) /\
  (if pay then comp_return () else
    comp_bind (emit_op CALLVALUE []) (\cv.
      comp_bind (emit_op ISZERO [cv]) (\nv. emit_void ASSERT [nv])))
    (initial_compile_state "__deploy") = ((),st_pay) /\
  (if imm_len tops > 0 then comp_bind (compile_fixed_region_with_id (imm_len tops))
    (\r. comp_return (SND r).buf_operand) else comp_return (Lit 0w))
    st_pay = (imm,st1) /\
  compile_register_constructor_args ce0 pos_args 0 0 st1 = (ce1,st2) ==>
  fn_has_code st1 st2 func /\ fn_inst_ids_distinct func /\
  (!bb. lookup_block st2.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `deploy_ctor_code _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[ctorDeployLoweringDefsTheory.deploy_ctor_code_def] >> strip_tac >>
  gvs[compileVyperTheory.set_constructor_package_target_def] >>
  drule_all ctor_phase_extends >> strip_tac >>
  drule_all ctor_phase_code_split >> strip_tac >>
  drule ctorDeployMemoryRunMemEntryEntryPhiTheory.ctor_deploy_prefix_phi >> strip_tac >>
  `phi_prefix_length sa.cs_current_insts = 0` by
    (irule abiDecoderPhiTheory.abi_decoder_phi_safe_head >>
     qexists_tac `initial_compile_state "__deploy"` >>
     fs[abiDecoderPhiTheory.abi_decoder_phi_def,
        vyperCompilerTheory.initial_compile_state_def,
        venomExecSemanticsTheory.phi_prefix_length_def]) >>
  `!bb. lookup_block sa.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[ctorDeployMemoryRunMemEntryEndpointTheory.ctor_deploy_endpoint_phi] >>
  drule_all ctor_phase_code_phi_contracts >> simp[]
QED

Theorem ctor_task_target_layout[local]:
  !ce target ty env tv sf av v args func scopes s.
    type_memory_bytes (ce with ce_target := target) ty = type_memory_bytes ce ty /\
    type_to_abi_dec_info sf (ce with ce_target := target) ty =
      type_to_abi_dec_info sf ce ty /\
    (abi_decoder_coherent (ce with ce_target := target) env sf ty tv <=>
      abi_decoder_coherent ce env sf ty tv) /\
    (abi_decoder_metadata (ce with ce_target := target) env ty tv
       (type_to_abi_dec_info sf (ce with ce_target := target) ty) av v <=>
     abi_decoder_metadata ce env ty tv (type_to_abi_dec_info sf ce ty) av v) /\
    build_positional_args (ce with ce_target := target) args = build_positional_args ce args /\
    (local_ptrs_rel func (ce with ce_target := target) scopes s <=>
      local_ptrs_rel func ce scopes s)
Proof
  rpt gen_tac >>
  `!ty. type_memory_bytes (ce with ce_target := target) ty = type_memory_bytes ce ty` by
    (gen_tac >> AP_THM_TAC >> irule compileEnvTheory.type_memory_bytes_frame >> simp[]) >>
  `!sf ty. type_to_abi_dec_info sf (ce with ce_target := target) ty =
     type_to_abi_dec_info sf ce ty` by
    (rpt gen_tac >> irule exprLoweringTheory.type_to_abi_dec_info_layout_cong >> simp[]) >>
  rpt conj_tac
  >- metis_tac[]
  >- (irule exprLoweringTheory.type_to_abi_dec_info_layout_cong >> simp[])
  >- (irule abi_decoder_coherent_layout_cong >> simp[])
  >- (`type_to_abi_dec_info sf (ce with ce_target := target) ty =
         type_to_abi_dec_info sf ce ty` by
        (irule exprLoweringTheory.type_to_abi_dec_info_layout_cong >> simp[]) >>
      `type_to_abi_dec_info ce.ce_struct_fields (ce with ce_target := target) ty =
         type_to_abi_dec_info ce.ce_struct_fields ce ty` by
        (irule exprLoweringTheory.type_to_abi_dec_info_layout_cong >> simp[]) >>
      fs[abi_decoder_metadata_def])
  >- (irule compileVyperTheory.build_positional_args_layout_cong >> simp[]) >>
  simp[loweringStateRelDefsTheory.local_ptrs_rel_def, loweringStateRelDefsTheory.local_region_def]
QED

Theorem ctor_task_register_actual:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs
   body cenv nr nkey ut imm exit_lbl sa sb sj st_exit st_epilogue st_final func
   mut am_c es0 lbl entry exts ints fb rr fname fargs dflts ret ce_pack pos_args
   ce0 st_pay st1 ce1 st2 site.
  deploy_phases policy tops (deploy_bc,runtime_bc)
    (rpolicy,dunit,dout,prog,cplan) /\
  deploy_source_ok tops am tx /\ deploy_state_rel tops deploy_bc am tx es /\
  gas_variant vs (deploy_entry_state prog cplan tops es) /\
  deploy_ctor_code tops rpolicy runtime_bc dunit
    (body,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,st_epilogue,st_final,func) /\
  deploy_ctor_start tops am tx (mut,nr,body,am_c,es0) /\
  lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME func /\
  fn_entry_label func = SOME lbl /\
  entry = vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|> /\
  classify_functions tops =
    (exts,ints,fb,SOME (mut,nr,rr,fname,fargs,dflts,ret,body)) /\
  package_constructor tops F (assign_nkeys tops 0)
    (mut,nr,rr,fname,fargs,dflts,ret,body) =
    (ce_pack,pos_args,mut = Payable,nr,nkey,ut,body,ret) /\
  ce0 = ((ce_pack with ce_target := rpolicy.rpol_target) with
    ce_imm_alloca := (if imm_len tops > 0 then SOME imm else NONE)) /\
  (if mut = Payable then comp_return () else
    comp_bind (emit_op CALLVALUE []) (\cv.
      comp_bind (emit_op ISZERO [cv]) (\nv. emit_void ASSERT [nv])))
      (initial_compile_state "__deploy") = ((),st_pay) /\
  (if imm_len tops > 0 then comp_bind (compile_fixed_region_with_id (imm_len tops))
    (\r. comp_return (SND r).buf_operand) else comp_return (Lit 0w))
    st_pay = (imm,st1) /\
  compile_register_constructor_args ce0 pos_args 0 0 st1 = (ce1,st2) ==>
  ?fixed actual scope.
    bind_arguments (type_env tops) fargs tx.args = SOME scope /\
    gas_path_mem dunit.cu_context func entry 0 (OK fixed) /\
    eval_operand imm fixed = SOME 0w /\
    fixed.vs_allocas = FEMPTY /\ fixed.vs_alloca_next = imm_len tops /\
    fixed.vs_data_section = vs.vs_data_section /\
    local_ptrs_rel func ce1 [scope] actual /\
    abi_encoder_registered_effect (frag_ids st1 st2) [] fixed actual /\
    alloca_inv actual /\
    alloca_frontier_inv_from (imm_len tops) dunit.cu_context func site actual /\
    fresh_vars_wrt st2 actual /\
    (!aid. st2.cs_next_id <= aid ==> FLOOKUP actual.vs_allocas aid = NONE) /\
    actual.vs_data_section = fixed.vs_data_section /\
    actual.vs_call_ctx = fixed.vs_call_ctx /\ actual.vs_labels = fixed.vs_labels /\
    (!x w. not_fresh_at st1 x /\ lookup_var x fixed = SOME w ==>
      lookup_var x actual = SOME w) /\
    ~actual.vs_halted /\ actual.vs_current_bb = st2.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st2.cs_current_insts /\
    abi_decode_sim dunit.cu_context func fixed actual /\
    gas_path_mem dunit.cu_context func fixed 0 (OK actual) /\
    gas_path_mem dunit.cu_context func entry 0 (OK actual) /\
    actual.vs_gas_readings = vs.vs_gas_readings /\ alloca_history func actual
Proof
  rpt gen_tac >> strip_tac >>
  drule_all ctor_task_actual_phase_contracts >> strip_tac >>
  drule_all ctor_task_registration_initial >> strip_tac >>
  `lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit` by
    metis_tac[ctorDeployLoweringDefsTheory.deploy_ctor_code_def] >>
  `nkey = assign_nkeys tops 0 fname /\ ut = F` by
    (qpat_x_assum `package_constructor _ _ _ _ = _` mp_tac >>
     simp[compileVyperTheory.package_constructor_def] >> metis_tac[]) >>
  drule_all ctor_task_actual_encoded_inputs >> strip_tac >>
  drule ctor_task_checked_namespaces >> strip_tac >>
  gvs[] >>
  drule_all (SRULE [] (Q.INST [
    `ce0` |-> `ce_pack with ce_imm_alloca := (if imm_len tops > 0 then SOME imm else NONE)`,
    `immo` |-> `(if imm_len tops > 0 then SOME imm else NONE)`]
    (Q.INST [`imm` |-> `immo`] ctor_task_registration_metadata))) >>
  disch_then (qspec_then `imm` strip_assume_tac) >>
  gvs[] >>
  qpat_x_assum `!i. i < LENGTH fargs ==> ?entry. _` (fn th =>
    assume_tac th) >>
  `has_types (vyper_to_abi_types (type_env tops) (MAP SND fargs)) avs` by
    (simp[contractABITheory.has_types_LIST_REL, abiDecoderMembersTheory.vyper_to_abi_types_MAP, LIST_REL_EL_EQN] >>
     rpt strip_tac >> first_x_assum drule >> strip_tac >>
     gvs[abi_decoder_metadata_def, EL_MAP]) >>
  `EVERY (\a. type_memory_bytes
      (ce_pack with ce_imm_alloca := (if imm_len tops > 0 then SOME imm else NONE))
      (SND a) < dimword (:256)) fargs` by
    (simp[EVERY_EL] >> qx_gen_tac `i` >> strip_tac >>
     qpat_x_assum `!i. i < LENGTH fargs ==> ?entry. _` drule >> strip_tac >>
     `MEM (FST (EL i fargs),SND (EL i fargs)) fargs` by
       metis_tac[MEM_EL, pairTheory.PAIR] >>
     `evaluate_type (type_env tops) (SND (EL i fargs)) = SOME entry.type` by
       fs[abi_decoder_metadata_def] >>
     drule_all ctor_formal_type_memory_bound >> strip_tac >>
     fs[abi_decoder_metadata_def, wordsTheory.dimword_def] >> decide_tac) >>
  `!aid. st1.cs_next_id <= aid ==> FLOOKUP fixed.vs_allocas aid = NONE` by simp[] >>
  `mem_bytes_at 0 (LENGTH fixed.vs_data_section) fixed.vs_data_section = fixed.vs_data_section` by
    simp[valueEncodingDefsTheory.mem_bytes_at_def, TAKE_APPEND] >>
  `build_positional_args
     (ce_pack with <|ce_target := rpolicy.rpol_target;
       ce_imm_alloca := (if imm_len tops > 0 then SOME imm else NONE)|>) fargs =
   build_positional_args
     (ce_pack with ce_imm_alloca := (if imm_len tops > 0 then SOME imm else NONE)) fargs` by
    (irule compileVyperTheory.build_positional_args_layout_cong >> simp[]) >>
  qpat_assum `compile_register_constructor_args _ (build_positional_args _ fargs) _ _ _ = (ce1,st2)` mp_tac >>
  qpat_x_assum `build_positional_args _ _ = build_positional_args _ _`
    (fn th => once_rewrite_tac[GSYM th]) >>
  disch_tac >>
  mp_tac (BETA_RULE ctor_checked_register_args_from) >>
  disch_then (drule_at (Pat `compile_register_constructor_args _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `fresh_vars_wrt _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `has_types _ _`)) >>
  disch_then (qspec_then `imm_len tops` mp_tac) >>
  disch_then (qspecl_then [`type_env tops`, `fixed.vs_data_section`, `scope`,
    `dunit.cu_context`, `site`] mp_tac) >>
  (impl_tac >- simp[ctor_task_target_layout]) >>
  strip_tac >>
  qexistsl [`fixed`, `actual`] >> simp[] >>
  metis_tac[gas_path_mem_then, arithmeticTheory.ADD]
QED
