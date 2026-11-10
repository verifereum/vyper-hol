Theory ctorDeployLoweringEntryBodyResources
Ancestors
 ctorDeployLoweringEntryLocalBounds ctorDeployLoweringEntryCoordinatedDeployment
 ctorDeployLoweringEntryInputs ctorDeployLoweringEntryPrefix
 ctorDeployLoweringEntryRegisterRun ctorDeployLoweringEntryTransport
 ctorDeployLoweringDefs ctorDeployDefs compileEnv compileVyper
 abiDecoderLoop ctorDeployMemoryFrontier
 ctorDeployLoweringEntrySelection e2eDeployDefs ctorDeployInitcode
 allocaFrontierBound finite_map venomState venomInst moduleLoweringProps
 ctorDeployLoweringEntryImmutableMemory ctorDeployLoweringEntryRoom
 ctorDeployLoweringEntryFmp immutableSectionRel immutableRelation exprLoweringProps
 ctorDeployLoweringFrame immutableLocationProps ctorDeployLoweringEntrySourceFrame
 vyperInterpreter vyperState deployEntryLayout e2eEntry asmDataSuffixProps
 fragGasPath bodyStorageMetadata structFieldsProps vyperTypeContractContext vyperTypeContract

Theorem deploy_ctor_entry_operand_frame:
 fresh_vars_wrt st initial /\ actual.vs_labels = initial.vs_labels /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
   lookup_var x actual = SOME w) /\
 eval_operand op initial = SOME w ==>
 eval_operand op actual = SOME w
Proof
 strip_tac >> Cases_on `op` >> gvs[eval_operand_def] >>
 `not_fresh_at st s` by
   (fs[not_fresh_at_def, fresh_vars_wrt_def, lookup_var_def] >>
    rpt strip_tac >> gvs[] >>
    qpat_x_assum `!n. _ >= _ ==> _` (qspec_then `n` mp_tac) >>
    fs[arithmeticTheory.GREATER_EQ, FLOOKUP_DEF]) >>
 metis_tac[]
QED

Theorem deploy_ctor_entry_source_scopes:
 !tops tx am mut nr rr fargs body nr' body' am_c es0 scope exts ints fb.
 classify_functions tops =
   (exts,ints,fb,SOME (mut,nr,rr,"__init__",fargs,[],NoneT,body)) /\
 tx.function_name = "__init__" /\ ~nr /\ nr' = nr /\ body' = body /\
 deploy_ctor_start tops am tx (mut,nr',body',am_c,es0) /\
 bind_arguments (type_env tops) fargs tx.args = SOME scope ==>
 es0.scopes = [scope]
Proof
 rpt gen_tac >> strip_tac >>
 qspecl_then [`tops`, `NONE`, `"__init__"`] mp_tac classify_functions_ctor_lookup >>
 simp[] >> strip_tac >> gvs[] >>
 metis_tac[deploy_ctor_source_start_fields]
QED

Theorem deploy_ctor_entry_registered_map_bounds_normalized_gas_path:
 !policy tops deploy_bc runtime_bc rp unit dout prog cplan am tx es vs
 body cenv nr key ut imm lbl sa sb sj se sp sf func mut nr' body' am_c es0
 exts ints fb rr fargs ce_pack pos_args st_pay st1 ce1 st2 st3 keep_bound.
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
 gas_path unit.cu_context func
   (vs with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>)
   0 (OK actual) /\
 (keep_bound ==> !aid b sz. FLOOKUP actual.vs_allocas aid = SOME (b,sz) ==> imm_len tops <= b) /\
 bind_arguments (type_env tops) fargs tx.args = SOME scope /\
 es0.scopes = [scope] /\
 local_ptrs_rel func ce1 [scope] actual /\
 abi_encoder_registered_effect (frag_ids st1 st2) [] initial actual /\
 vars_pc_only vs initial /\ initial.vs_memory = vs.vs_memory /\
 eval_operand imm initial = SOME 0w /\ eval_operand imm actual = SOME 0w /\
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
 (!id b sz. local_region ce1 [scope] actual id b sz ==> imm_len tops <= b) /\
 (!fuel r. run_from fuel unit.cu_context func actual = r /\ (!err. r <> Error err) ==>
    ?fuel'. run_context fuel' unit.cu_context vs = r)
Proof
 rpt gen_tac >> strip_tac >>
 drule (deploy_ctor_entry_before_register_gas_path |> SPEC_ALL |>
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
 `!id b sz. local_region
   (ce_pack with ce_imm_alloca := (if imm_len tops > 0 then SOME imm else NONE))
   [scope] t id b sz ==> imm_len tops <= b` by
   (rpt strip_tac >> drule deploy_ctor_target_package_no_local_region >>
    disch_then (qspecl_then [`if imm_len tops > 0 then SOME imm else NONE`,
      `[scope]`,`t`,`id`,`b`,`sz`] mp_tac) >> simp[]) >>
 suspend "register"
QED

Resume deploy_ctor_entry_registered_map_bounds_normalized_gas_path[register]:
 qpat_assum `t.vs_allocas = FEMPTY` (fn empty =>
 drule (deploy_ctor_register_args_actual_coordinated_map_bounds_gas_path |> SPEC_ALL |>
   Q.INST [`keep_bound` |-> `T`, `initial` |-> `t`,
           `q` |-> `imm_len tops`, `k` |-> `imm_len tops`,
           `site` |-> `ARB:instruction`, `data_size` |-> `0`,
           `encoded` |-> `vs.vs_data_section`,
           `atys` |-> `vyper_to_abi_types env (MAP SND fargs)`,
           `ce0` |-> `ce_pack with ce_imm_alloca := (if imm_len tops > 0 then SOME imm else NONE)`] |>
   SRULE [empty] |> GEN_ALL)) >>
 disch_then drule >> disch_then drule >> disch_then drule >>
 disch_then drule >> disch_then drule >>
 disch_then drule >> disch_then drule >> disch_then drule >>
 disch_then drule >> disch_then drule >>
 disch_then (qspec_then `unit.cu_context` mp_tac) >>
 (impl_tac >- (asm_rewrite_tac[] >> simp[])) >>
 disch_then (qx_choose_then `actual` (map_every assume_tac o CONJUNCTS)) >>
 suspend "finish"
QED

Resume deploy_ctor_entry_registered_map_bounds_normalized_gas_path[finish]:
 `t.vs_outcomes = vs.vs_outcomes /\ t.vs_tx_ctx = vs.vs_tx_ctx /\
  t.vs_block_ctx = vs.vs_block_ctx` by
   fs[vars_pc_only_def, venom_state_component_equality] >>
 `tx.function_name = "__init__"` by fs[deploy_state_rel_def] >>
 `es0.scopes = [scope]` by
   (drule_all deploy_ctor_entry_source_scopes >> simp[]) >>
 `eval_operand imm actual = SOME 0w` by
   (irule deploy_ctor_entry_operand_frame >>
    qexistsl [`t`, `st1`] >> asm_rewrite_tac[] >>
    fs[vars_pc_only_def, venom_state_component_equality]) >>
 `gas_path unit.cu_context func
   (vs with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>)
   0 (OK actual)` by
   (irule (SIMP_RULE std_ss [arithmeticTheory.ADD_CLAUSES]
     (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_then)) >>
    qexists `t` >> simp[]) >>
 simp[] >> qexistsl [`t`, `actual`] >>
 asm_rewrite_tac[] >> simp[] >>
 reverse conj_tac >- (fs[abi_decode_sim_def] >> metis_tac[]) >>
 fs[alloca_frontier_inv_from_def] >>
 rpt conj_tac >> first_assum ACCEPT_TAC
QED
Finalise deploy_ctor_entry_registered_map_bounds_normalized_gas_path

Theorem deploy_ctor_entry_registered_map_bounds_gas_path:
 !policy tops deploy_bc runtime_bc rp unit dout prog cplan am tx es vs
 body cenv nr key ut imm lbl sa sb sj se sp sf func mut nr' body' am_c es0 keep_bound.
 deploy_phases policy tops (deploy_bc,runtime_bc) (rp,unit,dout,prog,cplan) /\
 deploy_source_ok tops am tx /\ deploy_state_rel tops deploy_bc am tx es /\
 gas_variant vs (deploy_entry_state prog cplan tops es) /\
 deploy_ctor_code tops rp runtime_bc unit
   (body,cenv,nr,key,ut,imm,lbl,sa,sb,sj,se,sp,sf,func) /\
 deploy_ctor_start tops am tx (mut,nr',body',am_c,es0) ==>
 nr = F /\ nr' = nr /\ body' = body /\
 ?ce1 st1 st2 fargs scope initial actual.
 gas_path unit.cu_context func
   (vs with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>)
   0 (OK actual) /\
 (keep_bound ==> !aid b sz. FLOOKUP actual.vs_allocas aid = SOME (b,sz) ==> imm_len tops <= b) /\
 cenv = (ce1 with ce_ctor_exit_label := SOME lbl) /\
 fresh_label "ctor_exit" st2 = (lbl,sa) /\
 bind_arguments (type_env tops) fargs tx.args = SOME scope /\
 es0.scopes = [scope] /\
 local_ptrs_rel func ce1 [scope] actual /\
 abi_encoder_registered_effect (frag_ids st1 st2) [] initial actual /\
 vars_pc_only vs initial /\ initial.vs_memory = vs.vs_memory /\
 eval_operand imm initial = SOME 0w /\ eval_operand imm actual = SOME 0w /\
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
 (!id b sz. local_region ce1 [scope] actual id b sz ==> imm_len tops <= b) /\
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
 drule_all deploy_ctor_entry_registered_map_bounds_normalized_gas_path >>
 disch_then (qspec_then `keep_bound` strip_assume_tac) >>
 gvs[comp_return_def] >>
 qexistsl [`cenv1`, `st1`, `st2`, `args`, `initial`, `actual`] >>
 asm_rewrite_tac[]
QED

Theorem deploy_ctor_entry_registered_local_bounds_normalized_gas_path:
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
 gas_path unit.cu_context func
   (vs with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>)
   0 (OK actual) /\
 bind_arguments (type_env tops) fargs tx.args = SOME scope /\
 es0.scopes = [scope] /\
 local_ptrs_rel func ce1 [scope] actual /\
 abi_encoder_registered_effect (frag_ids st1 st2) [] initial actual /\
 vars_pc_only vs initial /\ initial.vs_memory = vs.vs_memory /\
 eval_operand imm initial = SOME 0w /\ eval_operand imm actual = SOME 0w /\
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
 (!id b sz. local_region ce1 [scope] actual id b sz ==> imm_len tops <= b) /\
 (!fuel r. run_from fuel unit.cu_context func actual = r /\ (!err. r <> Error err) ==>
    ?fuel'. run_context fuel' unit.cu_context vs = r)
Proof
 rpt gen_tac >>
 MATCH_ACCEPT_TAC (deploy_ctor_entry_registered_map_bounds_normalized_gas_path |>
   SPEC_ALL |> Q.INST [`keep_bound` |-> `F`] |>
   PURE_REWRITE_RULE [IMP_CLAUSES, AND_CLAUSES])
QED

Theorem deploy_ctor_entry_registered_local_bounds_gas_path:
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
 gas_path unit.cu_context func
   (vs with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>)
   0 (OK actual) /\
 cenv = (ce1 with ce_ctor_exit_label := SOME lbl) /\
 fresh_label "ctor_exit" st2 = (lbl,sa) /\
 bind_arguments (type_env tops) fargs tx.args = SOME scope /\
 es0.scopes = [scope] /\
 local_ptrs_rel func ce1 [scope] actual /\
 abi_encoder_registered_effect (frag_ids st1 st2) [] initial actual /\
 vars_pc_only vs initial /\ initial.vs_memory = vs.vs_memory /\
 eval_operand imm initial = SOME 0w /\ eval_operand imm actual = SOME 0w /\
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
 (!id b sz. local_region ce1 [scope] actual id b sz ==> imm_len tops <= b) /\
 (!fuel r. run_from fuel unit.cu_context func actual = r /\ (!err. r <> Error err) ==>
    ?fuel'. run_context fuel' unit.cu_context vs = r)
Proof
 rpt gen_tac >>
 MATCH_ACCEPT_TAC (deploy_ctor_entry_registered_map_bounds_gas_path |>
   SPEC_ALL |> Q.INST [`keep_bound` |-> `F`] |>
   PURE_REWRITE_RULE [IMP_CLAUSES, AND_CLAUSES])
QED

Theorem deploy_ctor_section_alloca_sep:
 immutable_decl_sep ce cx es.scopes ss.vs_vars ss.vs_allocas ss.vs_alloca_next /\
 immutable_section_layout ce tops /\ ce.ce_module = NONE /\
 immutables_section_rel tops
   (case ALOOKUP es.immutables cx.txn.target of NONE => [] | SOME imms => imms)
   section /\
 LENGTH section <= q /\ q <= ss.vs_alloca_next /\
 (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   FLOOKUP ss.vs_allocas inst.inst_id = SOME (b,sz) ==> q <= b) /\
 (!id b sz. local_region ce es.scopes ss id b sz ==> q <= b) ==>
 immutable_alloca_sep func ce cx es ss
Proof
 strip_tac >>
 simp[immutable_alloca_sep_def] >>
 Cases_on `ALOOKUP es.immutables cx.txn.target`
 >- simp[immutable_alloca_sep_def] >>
 fs[optionTheory.option_case_def] >>
 simp[immutable_alloca_sep_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
 qpat_assum `immutable_section_layout _ _`
   (mp_tac o REWRITE_RULE [immutable_section_layout_def]) >>
 disch_then drule >> strip_tac >>
 drule_all immutables_section_rel_lookup >> strip_tac >>
 `off + type_memory_size tv <= q` by (gvs[] >> decide_tac) >>
 conj_tac >- decide_tac >>
 conj_tac >> rpt gen_tac >> strip_tac >>
 `q <= b` by metis_tac[] >>
 pure_rewrite_tac[compileEnvTheory.regions_disjoint_def] >> decide_tac
QED

Theorem deploy_ctor_entry_immutable_layout:
 !tops rp runtime_bc unit body cenv nr key ut imm lbl sa sb sj se sp sf func.
 deploy_ctor_code tops rp runtime_bc unit
   (body,cenv,nr,key,ut,imm,lbl,sa,sb,sj,se,sp,sf,func) ==>
 cenv.ce_module = NONE /\ immutable_section_layout cenv tops
Proof
 rpt gen_tac >> strip_tac >> drule deploy_ctor_module_locations >> strip_tac >>
 conj_tac >- asm_rewrite_tac[] >>
 mp_tac (Q.SPEC `tops` immutable_build_compile_env_layout) >>
 simp[immutable_section_layout_def, build_compile_env_module_vars]
QED

Theorem deploy_ctor_start_immutable_field:
 !tops am tx mut body am_c es0.
 deploy_ctor_start tops am tx (mut,F,body,am_c,es0) ==>
 es0.immutables = am_c.immutables
Proof
 simp[deploy_ctor_start_def, lock_if_nr_def, ignore_bind_def,
      bind_def, return_def, AllCaseEqs()] >> rpt strip_tac >>
 drule deploy_ctor_send_value_frame >>
 simp[initial_state_def] >> strip_tac >>
 fs[evaluation_state_component_equality]
QED

Theorem deploy_ctor_entry_declared_extent[local]:
 !tops rp runtime_bc unit body cenv nr key ut imm lbl sa sb sj se sp sf func am tx.
 deploy_ctor_code tops rp runtime_bc unit
   (body,cenv,nr,key,ut,imm,lbl,sa,sb,sj,se,sp,sf,func) /\
 deploy_typing_ok tops am tx ==>
 !name ty tv off.
 FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
 cenv.ce_module_var_type (cenv.ce_module,name) = SOME ty /\
 evaluate_type (get_tenv (deploy_evaluation_context tops am tx)) ty = SOME tv ==>
 off + type_memory_size tv <= imm_len tops
Proof
 rpt gen_tac >> strip_tac >>
 drule deploy_ctor_entry_immutable_layout >> strip_tac >>
 drule deploy_ctor_static_tables >> strip_tac >>
 `contract_namespaces_ok T [(NONE,tops)]` by
   (fs[deploy_typing_ok_def] >>
    qpat_x_assum `check_contract T _ _ _ = _`
      (mp_tac o MATCH_MP check_contract_namespaces_ok) >> simp[]) >>
 `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops))` by
   fs[contract_namespaces_ok_def, contract_keys_def] >>
 rpt gen_tac >> strip_tac >>
 gvs[deploy_evaluation_context_def, initial_evaluation_context_def,
    vyperContextTheory.get_tenv_def, deploy_ctor_singleton_type_env] >>
 drule_all evaluated_type_mem_bytes >> strip_tac >>
 qpat_x_assum `immutable_section_layout _ _` mp_tac >>
 simp[immutable_section_layout_def] >>
 disch_then drule >> strip_tac >>
 `MEM (VariableDecl vis Immutable name ty' slot) tops` by
   (gvs[] >> simp[]) >>
 drule_all build_maps_variable >> strip_tac >>
 gvs[] >>
 pure_rewrite_tac [imm_len_def, GSYM listTheory.APPEND_ASSOC,
   listTheory.APPEND] >>
 irule (PURE_REWRITE_RULE [arithmeticTheory.ADD_CLAUSES]
   (Q.INST [`off` |-> `0`] immutable_declaration_interval_bound))
QED

Theorem deploy_ctor_entry_immutable_resources:
 !tops rp runtime_bc unit body cenv nr key ut imm lbl sa sb sj se sp sf func
 am tx mut am_c es0 ss.
 deploy_ctor_code tops rp runtime_bc unit
   (body,cenv,nr,key,ut,imm,lbl,sa,sb,sj,se,sp,sf,func) /\
 deploy_typing_ok tops am tx /\
 deploy_ctor_start tops am tx (mut,F,body,am_c,es0) /\
 imm_len tops <= ss.vs_alloca_next /\
 (!aid b sz. FLOOKUP ss.vs_allocas aid = SOME (b,sz) ==> imm_len tops <= b) /\
 (!p. p < imm_len tops ==>
   mem_bytes_at p 1 ss.vs_memory = mem_bytes_at p 1 []) /\
 (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   FLOOKUP ss.vs_allocas inst.inst_id = SOME (b,sz) ==> imm_len tops <= b) /\
 (!id b sz. local_region cenv es0.scopes ss id b sz ==> imm_len tops <= b) ==>
 immutables_rel cenv tx.target NONE T es0 ss /\
 immutable_alloca_sep func cenv (deploy_evaluation_context tops am tx) es0 ss
Proof
 rpt gen_tac >> strip_tac >>
 drule deploy_ctor_entry_immutable_layout >> strip_tac >>
 drule deploy_ctor_start_immutable_field >> strip_tac >>
 conj_tac
 >- metis_tac[deploy_ctor_zero_memory_immutables] >>
 drule_all deploy_ctor_start_zero_section >> strip_tac >>
 irule deploy_ctor_section_alloca_sep >>
 conj_tac >- asm_rewrite_tac[] >>
 reverse conj_tac
 >- (rewrite_tac[immutable_decl_sep_alt] >> rpt strip_tac >>
     drule_all deploy_ctor_entry_declared_extent >>
     strip_tac >>
     rpt conj_tac >> rpt strip_tac >>
     fs[regions_disjoint_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
 qexistsl [`imm_len tops`, `REPLICATE (imm_len tops) 0w`, `tops`] >>
 asm_rewrite_tac[] >>
 simp[deploy_evaluation_context_def, initial_evaluation_context_def]
QED

Theorem deploy_ctor_entry_immutable_config:
 !tops rp runtime_bc unit body cenv nr key ut imm lbl sa sb sj se sp sf func.
 deploy_ctor_code tops rp runtime_bc unit
   (body,cenv,nr,key,ut,imm,lbl,sa,sb,sj,se,sp,sf,func) ==>
 cenv.ce_is_ctor /\
 cenv.ce_imm_alloca = (if imm_len tops > 0 then SOME imm else NONE)
Proof
 rpt gen_tac >> simp[deploy_ctor_code_def] >> strip_tac >>
 PairCases_on `cf` >>
 drule_all deploy_ctor_target_reserved_entry >> strip_tac >> gvs[]
QED

Theorem deploy_ctor_entry_runtime_label:
 !policy tops deploy_bc runtime_bc rp unit dout prog cplan am tx es vs.
 deploy_phases policy tops (deploy_bc,runtime_bc) (rp,unit,dout,prog,cplan) /\
 gas_variant vs (deploy_entry_state prog cplan tops es) ==>
 IS_SOME (FLOOKUP vs.vs_labels "runtime_begin")
Proof
 rpt gen_tac >> simp[deploy_phases_def] >> strip_tac >>
 drule_all lower_vyper_deploy_unit_entry_runtime_label >>
 disch_then (qspecl_then [`[]`, `cplan`, `es`] mp_tac) >>
 fs[o1PassContractTheory.gas_variant_def, deploy_entry_state_def,
    entry_venom_state_frame_fields, data_suffix_label_offsets,
    venom_state_component_equality] >>
 qpat_x_assum `(entry_venom_state _ _ _).vs_labels = _`
   (fn th => rewrite_tac[GSYM th]) >>
 simp[entry_venom_state_frame_fields]
QED

Theorem deploy_ctor_entry_base_zero:
 !policy tops deploy_bc runtime_bc rp unit dout prog cplan am tx es vs
 body cenv nr key ut imm lbl sa sb sj se sp sf func actual.
 deploy_phases policy tops (deploy_bc,runtime_bc) (rp,unit,dout,prog,cplan) /\
 gas_variant vs (deploy_entry_state prog cplan tops es) /\
 deploy_ctor_code tops rp runtime_bc unit
   (body,cenv,nr,key,ut,imm,lbl,sa,sb,sj,se,sp,sf,func) /\
 eval_operand imm actual = SOME 0w /\ actual.vs_labels = vs.vs_labels ==>
 immutable_base_zero cenv actual
Proof
 rpt gen_tac >> strip_tac >>
 drule_all deploy_ctor_entry_runtime_label >> strip_tac >>
 drule deploy_ctor_entry_immutable_config >> strip_tac >>
 simp[immutable_base_zero_def] >> rpt strip_tac >>
 gvs[AllCaseEqs()]
QED

Theorem deploy_ctor_entry_body_resources_gas_path:
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
 gas_path unit.cu_context func
   (vs with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>)
   0 (OK actual) /\
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
 actual.vs_block_ctx = vs.vs_block_ctx /\
 (!fuel r. run_from fuel unit.cu_context func actual = r /\ (!err. r <> Error err) ==>
    ?fuel'. run_context fuel' unit.cu_context vs = r)
Proof
 rpt gen_tac >> strip_tac >>
 drule_all deploy_ctor_entry_registered_map_bounds_gas_path >>
 disch_then (qspec_then `T` strip_assume_tac) >> fs[] >>
 `deploy_typing_ok tops am tx /\ supported_program tops` by fs[deploy_source_ok_def] >>
 `vs.vs_memory = []` by
   (fs[o1PassContractTheory.gas_variant_def, deploy_entry_state_def,
       entry_venom_state_def, init_venom_state_def, venom_state_component_equality]) >>
 `!id b sz. local_region cenv es0.scopes actual id b sz ==> imm_len tops <= b` by
   (rpt strip_tac >>
    `local_region ce1 [scope] actual id b sz` by
      (qpat_x_assum `local_region cenv _ _ _ _ _` mp_tac >>
       simp[local_region_def]) >>
    metis_tac[]) >>
 `!p. p < imm_len tops ==>
   mem_bytes_at p 1 actual.vs_memory = mem_bytes_at p 1 []` by metis_tac[] >>
 gvs[] >>
 `!id b sz. local_region (ce1 with ce_ctor_exit_label := SOME lbl)
   es0.scopes actual id b sz ==> imm_len tops <= b` by asm_rewrite_tac[] >>
 drule_all deploy_ctor_entry_immutable_resources >> strip_tac >>
 drule_all deploy_ctor_entry_base_zero >> strip_tac >>
 drule deploy_ctor_shifted_budget >> strip_tac >>
 `alloca_room unit.cu_context func actual` by
   (irule deploy_ctor_frontier_alloca_room >>
    qexistsl [`imm_len tops`, `ARB:instruction`] >> simp[]) >>
 `fmp_room unit.cu_context func actual` by metis_tac[deploy_ctor_entry_fmp_room] >>
 simp[] >> qexistsl [`ce1`, `st1`, `st2`, `fargs`, `initial`, `actual`] >>
 asm_rewrite_tac[]
QED

Theorem deploy_ctor_entry_registered_map_bounds_normalized:
 !policy tops deploy_bc runtime_bc rp unit dout prog cplan am tx es vs
 body cenv nr key ut imm lbl sa sb sj se sp sf func mut nr' body' am_c es0
 exts ints fb rr fargs ce_pack pos_args st_pay st1 ce1 st2 st3 keep_bound.
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
 (keep_bound ==> !aid b sz. FLOOKUP actual.vs_allocas aid = SOME (b,sz) ==> imm_len tops <= b) /\
 bind_arguments (type_env tops) fargs tx.args = SOME scope /\
 es0.scopes = [scope] /\
 local_ptrs_rel func ce1 [scope] actual /\
 abi_encoder_registered_effect (frag_ids st1 st2) [] initial actual /\
 vars_pc_only vs initial /\ initial.vs_memory = vs.vs_memory /\
 eval_operand imm initial = SOME 0w /\ eval_operand imm actual = SOME 0w /\
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
 (!id b sz. local_region ce1 [scope] actual id b sz ==> imm_len tops <= b) /\
 (!fuel r. run_from fuel unit.cu_context func actual = r /\ (!err. r <> Error err) ==>
    ?fuel'. run_context fuel' unit.cu_context vs = r)
Proof
 rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 drule_all deploy_ctor_entry_registered_map_bounds_normalized_gas_path >>
 disch_then (qspec_then `keep_bound` strip_assume_tac) >>
 conj_tac >- first_assum ACCEPT_TAC >>
 conj_tac >- first_assum ACCEPT_TAC >>
 conj_tac >- first_assum ACCEPT_TAC >>
 qexistsl [`scope`, `initial`, `actual`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem deploy_ctor_entry_registered_map_bounds:
 !policy tops deploy_bc runtime_bc rp unit dout prog cplan am tx es vs
 body cenv nr key ut imm lbl sa sb sj se sp sf func mut nr' body' am_c es0 keep_bound.
 deploy_phases policy tops (deploy_bc,runtime_bc) (rp,unit,dout,prog,cplan) /\
 deploy_source_ok tops am tx /\ deploy_state_rel tops deploy_bc am tx es /\
 gas_variant vs (deploy_entry_state prog cplan tops es) /\
 deploy_ctor_code tops rp runtime_bc unit
   (body,cenv,nr,key,ut,imm,lbl,sa,sb,sj,se,sp,sf,func) /\
 deploy_ctor_start tops am tx (mut,nr',body',am_c,es0) ==>
 nr = F /\ nr' = nr /\ body' = body /\
 ?ce1 st1 st2 fargs scope initial actual.
 (keep_bound ==> !aid b sz. FLOOKUP actual.vs_allocas aid = SOME (b,sz) ==> imm_len tops <= b) /\
 cenv = (ce1 with ce_ctor_exit_label := SOME lbl) /\
 fresh_label "ctor_exit" st2 = (lbl,sa) /\
 bind_arguments (type_env tops) fargs tx.args = SOME scope /\
 es0.scopes = [scope] /\
 local_ptrs_rel func ce1 [scope] actual /\
 abi_encoder_registered_effect (frag_ids st1 st2) [] initial actual /\
 vars_pc_only vs initial /\ initial.vs_memory = vs.vs_memory /\
 eval_operand imm initial = SOME 0w /\ eval_operand imm actual = SOME 0w /\
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
 (!id b sz. local_region ce1 [scope] actual id b sz ==> imm_len tops <= b) /\
 (!fuel r. run_from fuel unit.cu_context func actual = r /\ (!err. r <> Error err) ==>
    ?fuel'. run_context fuel' unit.cu_context vs = r)
Proof
 rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 drule_all deploy_ctor_entry_registered_map_bounds_gas_path >>
 disch_then (qspec_then `keep_bound` strip_assume_tac) >>
 conj_tac >- first_assum ACCEPT_TAC >>
 conj_tac >- first_assum ACCEPT_TAC >>
 conj_tac >- first_assum ACCEPT_TAC >>
 qexistsl [`ce1`, `st1`, `st2`, `fargs`, `scope`, `initial`, `actual`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem deploy_ctor_entry_registered_local_bounds_normalized:
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
 es0.scopes = [scope] /\
 local_ptrs_rel func ce1 [scope] actual /\
 abi_encoder_registered_effect (frag_ids st1 st2) [] initial actual /\
 vars_pc_only vs initial /\ initial.vs_memory = vs.vs_memory /\
 eval_operand imm initial = SOME 0w /\ eval_operand imm actual = SOME 0w /\
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
 (!id b sz. local_region ce1 [scope] actual id b sz ==> imm_len tops <= b) /\
 (!fuel r. run_from fuel unit.cu_context func actual = r /\ (!err. r <> Error err) ==>
    ?fuel'. run_context fuel' unit.cu_context vs = r)
Proof
 rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 drule_all deploy_ctor_entry_registered_local_bounds_normalized_gas_path >> strip_tac >>
 conj_tac >- first_assum ACCEPT_TAC >>
 conj_tac >- first_assum ACCEPT_TAC >>
 conj_tac >- first_assum ACCEPT_TAC >>
 qexistsl [`scope`, `initial`, `actual`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem deploy_ctor_entry_registered_local_bounds:
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
 es0.scopes = [scope] /\
 local_ptrs_rel func ce1 [scope] actual /\
 abi_encoder_registered_effect (frag_ids st1 st2) [] initial actual /\
 vars_pc_only vs initial /\ initial.vs_memory = vs.vs_memory /\
 eval_operand imm initial = SOME 0w /\ eval_operand imm actual = SOME 0w /\
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
 (!id b sz. local_region ce1 [scope] actual id b sz ==> imm_len tops <= b) /\
 (!fuel r. run_from fuel unit.cu_context func actual = r /\ (!err. r <> Error err) ==>
    ?fuel'. run_context fuel' unit.cu_context vs = r)
Proof
 rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 drule_all deploy_ctor_entry_registered_local_bounds_gas_path >> strip_tac >>
 conj_tac >- first_assum ACCEPT_TAC >>
 conj_tac >- first_assum ACCEPT_TAC >>
 conj_tac >- first_assum ACCEPT_TAC >>
 qexistsl [`ce1`, `st1`, `st2`, `fargs`, `scope`, `initial`, `actual`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem deploy_ctor_entry_body_resources:
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
 actual.vs_block_ctx = vs.vs_block_ctx /\
 (!fuel r. run_from fuel unit.cu_context func actual = r /\ (!err. r <> Error err) ==>
    ?fuel'. run_context fuel' unit.cu_context vs = r)
Proof
 rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 drule_all deploy_ctor_entry_body_resources_gas_path >> strip_tac >>
 conj_tac >- first_assum ACCEPT_TAC >>
 conj_tac >- first_assum ACCEPT_TAC >>
 conj_tac >- first_assum ACCEPT_TAC >>
 qexistsl [`ce1`, `st1`, `st2`, `fargs`, `scope`, `initial`, `actual`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
