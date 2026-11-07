Theory ctorDeployLoweringEntryCoordinatedDeployment
Ancestors
 ctorDeployLoweringEntryCoordinatedRegister
 ctorDeployLoweringEntryInputs ctorDeployLoweringEntryPrefix
 ctorDeployLoweringEntryRegisterRun ctorDeployLoweringEntryTransport
 ctorDeployLoweringDefs ctorDeployDefs compileEnv compileVyper
 abiDecoderLoop ctorDeployMemoryFrontier
 ctorDeployLoweringEntrySelection e2eDeployDefs ctorDeployInitcode
 allocaFrontierBound finite_map venomState venomInst moduleLoweringProps

Theorem deploy_ctor_entry_registered_coordinated_normalized:
 !policy tops deploy_bc runtime_bc rp unit dout prog cplan am tx es vs
 body cenv nr key ut imm lbl sa sb sj se sp sf func mut nr' body' am_c es0
 exts ints fb rr fargs ce_pack pos_args st_pay st1 ce1 st2 st3.
 deploy_phases policy tops (deploy_bc,runtime_bc) (rp,unit,dout,prog,cplan) /\
 deploy_source_ok tops am tx /\ deploy_state_rel tops deploy_bc am tx es /\
 gas_variant vs (deploy_entry_state prog cplan tops es) /\
 deploy_ctor_code tops rp runtime_bc unit
   (body,cenv,nr,key,ut,imm,lbl,sa,sb,sj,se,sp,sf,func) /\
 deploy_ctor_start tops am tx (mut,nr',body',am_c,es0) /\
 classify_functions tops =
   (exts,ints,fb,SOME (mut,nr,rr,"__init__",fargs,[],NoneT,body)) /\
 set_constructor_package_target rp.rpol_target
   (package_constructor tops F (assign_nkeys tops 0)
     (mut,nr,rr,"__init__",fargs,([]:expr list),NoneT,body)) =
   (ce_pack,pos_args,mut = Payable,nr,key,ut,body,NoneT) /\
 (if mut = Payable then comp_return ()
  else comp_bind (emit_op CALLVALUE [])
    (\cv. comp_bind (emit_op ISZERO [cv]) (\nv. emit_void ASSERT [nv])))
     (initial_compile_state "__deploy") = ((),st_pay) /\
 (if imm_len tops > 0 then
    comp_bind (compile_fixed_region_with_id (imm_len tops))
      (\r. comp_return (SND r).buf_operand)
  else comp_return (Lit 0w)) st_pay = (imm,st1) /\
 compile_register_constructor_args
   (ce_pack with ce_imm_alloca := (if imm_len tops > 0 then SOME imm else NONE))
   pos_args 0 0 st1 = (ce1,st2) /\
 (if nr then compile_nonreentrant_lock key ut F else comp_return ()) st2 = ((),st3) /\
 fresh_label "ctor_exit" st3 = (lbl,sa) ==>
 nr = F /\ nr' = nr /\ body' = body /\
 ?scope initial actual.
 bind_arguments (type_env tops) fargs tx.args = SOME scope /\
 local_ptrs_rel func ce1 [scope] actual /\
 abi_encoder_registered_effect (frag_ids st1 st2) [] initial actual /\
 vars_pc_only vs initial /\ initial.vs_memory = vs.vs_memory /\
 eval_operand imm initial = SOME 0w /\
 initial.vs_allocas = FEMPTY /\ initial.vs_alloca_next = imm_len tops /\
 alloca_inv actual /\
 (!site. alloca_frontier_inv_from (imm_len tops) unit.cu_context func site actual) /\
 fresh_vars_wrt st2 actual /\
 (!aid. st2.cs_next_id <= aid ==> FLOOKUP actual.vs_allocas aid = NONE) /\
 actual.vs_data_section = vs.vs_data_section /\
 actual.vs_call_ctx = vs.vs_call_ctx /\ actual.vs_labels = vs.vs_labels /\
 ~actual.vs_halted /\ actual.vs_current_bb = st2.cs_current_bb /\
 actual.vs_inst_idx = LENGTH st2.cs_current_insts /\
 actual.vs_gas_readings = vs.vs_gas_readings /\ actual.vs_code = vs.vs_code /\
 actual.vs_outcomes = vs.vs_outcomes /\ actual.vs_tx_ctx = vs.vs_tx_ctx /\
 actual.vs_block_ctx = vs.vs_block_ctx /\
 initial.vs_alloca_next <= actual.vs_alloca_next /\
 (!p. p < initial.vs_alloca_next ==>
   mem_bytes_at p 1 actual.vs_memory = mem_bytes_at p 1 initial.vs_memory) /\
 (!inst n b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   inst.inst_operands = [Lit n] /\
   FLOOKUP actual.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) /\
 (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   FLOOKUP actual.vs_allocas inst.inst_id = SOME (b,sz) ==> imm_len tops <= b) /\
 (!fuel r. run_from fuel unit.cu_context func actual = r /\ (!err. r <> Error err) ==>
    ?fuel'. run_context fuel' unit.cu_context vs = r)
Proof
 rpt gen_tac >> strip_tac >>
 drule (deploy_ctor_entry_before_register |> SPEC_ALL |>
   Q.INST [`cap` |-> `imm_len tops`, `is_payable` |-> `mut = Payable`] |> GEN_ALL |> SRULE []) >>
 disch_then drule_all >> strip_tac >>
 drule (deploy_ctor_decoder_inputs |> INST_TYPE [``:'a`` |-> ``:expr``] |> SPEC_ALL |>
   Q.INST [`ce0` |-> `ce_pack with ce_imm_alloca := (if imm_len tops > 0 then SOME imm else NONE)`,
           `imm_opt` |-> `if imm_len tops > 0 then SOME imm else NONE`] |>
   GEN_ALL |> SRULE []) >>
 disch_then drule_all >> strip_tac >>
 `fn_has_code (initial_compile_state "__deploy") sa func /\
  fn_inst_ids_distinct func` by fs[deploy_ctor_code_def] >>
 drule_all deploy_ctor_registration_code >> strip_tac >>
 drule deploy_ctor_shifted_budget >> strip_tac >>
 `supported_program tops` by fs[deploy_source_ok_def] >>
 `!bb. lookup_block st2.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0` by
   (rpt strip_tac >> drule_all deploy_ctor_raw_blocks_no_phi >> simp[]) >>
 qpat_assum `pos_args = build_positional_args _ _` (fn th =>
   qpat_assum `compile_register_constructor_args _ _ _ _ _ = _`
     (assume_tac o REWRITE_RULE [th])) >>
 `mem_bytes_at 0 (LENGTH vs.vs_data_section) t.vs_data_section = vs.vs_data_section` by metis_tac[] >>
 suspend "register"
QED

Resume deploy_ctor_entry_registered_coordinated_normalized[register]:
 drule (deploy_ctor_register_args_actual_coordinated |> SPEC_ALL |>
   Q.INST [`q` |-> `imm_len tops`, `k` |-> `imm_len tops`,
           `site` |-> `ARB:instruction`, `data_size` |-> `0`,
           `encoded` |-> `vs.vs_data_section`,
           `atys` |-> `vyper_to_abi_types env (MAP SND fargs)`,
           `ce0` |-> `ce_pack with ce_imm_alloca := (if imm_len tops > 0 then SOME imm else NONE)`] |>
   GEN_ALL |> SRULE []) >>
 disch_then drule >> disch_then drule >> disch_then drule >>
 disch_then drule >> disch_then drule >>
 disch_then drule >> disch_then drule >> disch_then drule >>
 disch_then drule >> disch_then drule >>
 disch_then (qspec_then `unit.cu_context` mp_tac) >>
 (impl_tac >- (asm_rewrite_tac[] >> simp[])) >>
 disch_then (qx_choose_then `actual` (map_every assume_tac o CONJUNCTS)) >>
 suspend "finish"
QED

Resume deploy_ctor_entry_registered_coordinated_normalized[finish]:
 `t.vs_outcomes = vs.vs_outcomes /\ t.vs_tx_ctx = vs.vs_tx_ctx /\
  t.vs_block_ctx = vs.vs_block_ctx` by
   fs[vars_pc_only_def, venom_state_component_equality] >>
 simp[] >> qexistsl [`t`, `actual`] >>
 asm_rewrite_tac[] >> simp[] >>
 reverse conj_tac >- (fs[abi_decode_sim_def] >> metis_tac[]) >>
 fs[alloca_frontier_inv_from_def] >>
 rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise deploy_ctor_entry_registered_coordinated_normalized

Theorem deploy_ctor_entry_registered_coordinated:
 !policy tops deploy_bc runtime_bc rp unit dout prog cplan am tx es vs
 body cenv nr key ut imm lbl sa sb sj se sp sf func mut nr' body' am_c es0.
 deploy_phases policy tops (deploy_bc,runtime_bc) (rp,unit,dout,prog,cplan) /\
 deploy_source_ok tops am tx /\ deploy_state_rel tops deploy_bc am tx es /\
 gas_variant vs (deploy_entry_state prog cplan tops es) /\
 deploy_ctor_code tops rp runtime_bc unit
   (body,cenv,nr,key,ut,imm,lbl,sa,sb,sj,se,sp,sf,func) /\
 deploy_ctor_start tops am tx (mut,nr',body',am_c,es0) ==>
 nr = F /\ nr' = nr /\ body' = body /\
 ?ce1 st1 st2 fargs scope initial actual.
 cenv = (ce1 with ce_ctor_exit_label := SOME lbl) /\
 fresh_label "ctor_exit" st2 = (lbl,sa) /\
 bind_arguments (type_env tops) fargs tx.args = SOME scope /\
 local_ptrs_rel func ce1 [scope] actual /\
 abi_encoder_registered_effect (frag_ids st1 st2) [] initial actual /\
 vars_pc_only vs initial /\ initial.vs_memory = vs.vs_memory /\
 eval_operand imm initial = SOME 0w /\
 initial.vs_allocas = FEMPTY /\ initial.vs_alloca_next = imm_len tops /\
 alloca_inv actual /\
 (!site. alloca_frontier_inv_from (imm_len tops) unit.cu_context func site actual) /\
 fresh_vars_wrt st2 actual /\
 (!aid. st2.cs_next_id <= aid ==> FLOOKUP actual.vs_allocas aid = NONE) /\
 actual.vs_data_section = vs.vs_data_section /\
 actual.vs_call_ctx = vs.vs_call_ctx /\ actual.vs_labels = vs.vs_labels /\
 ~actual.vs_halted /\ actual.vs_current_bb = st2.cs_current_bb /\
 actual.vs_inst_idx = LENGTH st2.cs_current_insts /\
 actual.vs_gas_readings = vs.vs_gas_readings /\ actual.vs_code = vs.vs_code /\
 actual.vs_outcomes = vs.vs_outcomes /\ actual.vs_tx_ctx = vs.vs_tx_ctx /\
 actual.vs_block_ctx = vs.vs_block_ctx /\
 initial.vs_alloca_next <= actual.vs_alloca_next /\
 (!p. p < initial.vs_alloca_next ==>
   mem_bytes_at p 1 actual.vs_memory = mem_bytes_at p 1 initial.vs_memory) /\
 (!inst n b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   inst.inst_operands = [Lit n] /\
   FLOOKUP actual.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) /\
 (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   FLOOKUP actual.vs_allocas inst.inst_id = SOME (b,sz) ==> imm_len tops <= b) /\
 (!fuel r. run_from fuel unit.cu_context func actual = r /\ (!err. r <> Error err) ==>
    ?fuel'. run_context fuel' unit.cu_context vs = r)
Proof
 rpt gen_tac >> strip_tac >>
 qpat_assum `deploy_ctor_code _ _ _ _ _` mp_tac >>
 rewrite_tac[deploy_ctor_code_def] >> strip_tac >>
 drule_all lower_vyper_deploy_unit_ctor_named_init >> strip_tac >>
 PairCases_on `cf` >> gvs[ctor_named_init_def] >>
 drule_all deploy_ctor_entry_selection_agrees >> strip_tac >>
 qpat_assum `deploy_ctor_start _ _ _ _` mp_tac >>
 rewrite_tac[deploy_ctor_start_def] >> strip_tac >>
 `tx.function_name = "__init__"` by fs[deploy_state_rel_def] >>
 qspecl_then [`tops`, `NONE`, `"__init__"`] mp_tac classify_functions_ctor_lookup >>
 simp[] >> strip_tac >>
 `is_payable = (cf0 = Payable) /\ nr = cf1 /\ ret = NoneT` by
   fs[set_constructor_package_target_def, package_constructor_def] >>
 gvs[] >>
 drule_all deploy_ctor_entry_registered_coordinated_normalized >> strip_tac >>
 gvs[comp_return_def] >>
 qexistsl [`cenv1`, `st1`, `st2`, `args`, `scope`, `initial`, `actual`] >>
 asm_rewrite_tac[]
QED
