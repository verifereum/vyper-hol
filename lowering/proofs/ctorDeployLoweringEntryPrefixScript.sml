(* The actual original-unit entry state before constructor registration. *)
Theory ctorDeployLoweringEntryPrefix
Ancestors
 ctorDeployDefs context ctorDeployLoweringDefs deployUnitProducers ctorDeployMemoryFrontier
 moduleLoweringProps fragExec venomExecSemantics venomInst venomState
 vyperCompiler compileEnv o1PassContract e2eEntry finite_map list
 ctorDeployLoweringPrefix ctorDeployShape unitShapeDefs compileVyper
 o1ScheduleDecompHelpers ctorDeployInitcode e2eDeployDefs vyperState
 vyperInterpreter vyperContext venomMemDefs allocaBudgetProps
 allocaFrontierBound fcgCorrectnessProof fcgDefs ctorDeployImmBudget
 contextCodegenRel fcgPostorder arithmetic abiDecoderLoop
 actualEntryAllocationFrame immutableWordExecution emitHelperProps rich_list
 emitHelper exprLoweringProps ctorRegisterArgs ctorDeployLoweringCodeShape

Theorem deploy_ctor_enter_context[local]:
 ctx.ctx_entry = SOME name /\
 lookup_function name ctx.ctx_functions = SOME func /\
 fn_entry_label func = SOME lbl /\
 lookup_block lbl func.fn_blocks = SOME bb /\
 phi_prefix_length bb.bb_instructions = 0 ==>
 ?e. e = vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|> /\
 vars_pc_only vs e /\ e.vs_current_bb = lbl /\ e.vs_inst_idx = 0 /\
 (!fuel r. run_from fuel ctx func e = r /\ (!err. r <> Error err) ==>
   ?fuel'. run_context fuel' ctx vs = r)
Proof
 strip_tac >>
 qexists `vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>` >>
 simp[vars_pc_only_def] >> rpt strip_tac >> qexists `SUC fuel` >>
 simp[run_context_def, run_function_def, run_blocks_run_from_no_phi]
QED

Theorem deploy_ctor_entry_initial_fields[local]:
 gas_variant vs (deploy_entry_state prog cplan tops es) ==>
 fresh_vars_wrt (initial_compile_state "__deploy") vs /\
 ~vs.vs_halted /\ vs.vs_allocas = FEMPTY /\
 vs.vs_alloca_next = imm_len tops
Proof
 simp[gas_variant_def, deploy_entry_state_def, entry_venom_state_def,
      init_venom_state_def, venom_state_component_equality] >>
 strip_tac >>
 simp[fresh_vars_wrt_def, initial_compile_state_def, lookup_var_def]
QED

Theorem deploy_ctor_original_entry_shape[local]:
 !tops rp runtime unit body ce nr key ut imm lbl sa sb sj se sp sf func.
 supported_program tops /\
 deploy_ctor_code tops rp runtime unit
   (body,ce,nr,key,ut,imm,lbl,sa,sb,sj,se,sp,sf,func) ==>
 unit.cu_context.ctx_entry = SOME "__deploy" /\
 lookup_function "__deploy" unit.cu_context.ctx_functions = SOME func /\
 fn_entry_label func = SOME "__deploy" /\
 ctx_wf unit.cu_context /\ wf_invoke_targets unit.cu_context /\
 reachable_call_graph_acyclic unit.cu_context /\
 ctx_inst_ids_distinct unit.cu_context /\
 ?bb. lookup_block "__deploy" func.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0
Proof
 rpt gen_tac >> strip_tac >>
 drule_all deploy_prefix_ctor_entry_label >> strip_tac >>
 fs[deploy_ctor_code_def] >>
 drule lower_vyper_deploy_unit_entry >> strip_tac >>
 drule lower_vyper_deploy_unit_context_ok >> strip_tac >>
 `lookup_function "__deploy" unit.cu_context.ctx_functions = SOME func` by
   (fs[lowering_context_ok_def, ctx_fn_names_def] >>
    drule lookup_function_member_iff >>
    disch_then (qspecl_then [`"__deploy"`, `func`] mp_tac) >> simp[]) >>
 drule_all lowered_unit_entry_facts >> strip_tac >>
 simp[] >>
 drule_all lower_vyper_deploy_unit_source_unit_ok >> strip_tac >>
 `EVERY (\inst. raw_opcode_ok inst.inst_opcode) (fn_insts func)` by
   (gvs[o1_source_unit_ok_def, EVERY_MEM] >>
    qpat_x_assum `!fn. MEM fn _ ==> !inst. _`
      (drule_then assume_tac) >> simp[]) >>
 gvs[] >>
 rename1 `fn_entry_label f = SOME "__deploy"` >>
 Cases_on `f.fn_blocks` >- gvs[fn_entry_label_def, entry_block_def] >>
 gvs[fn_entry_label_def, entry_block_def] >>
 qexists `h` >> simp[lookup_block_def, FIND_thm] >>
 Cases_on `h.bb_instructions` >> simp[phi_prefix_length_def] >>
 fs[fn_insts_def, fn_insts_blocks_def, raw_opcode_ok_def]
QED

Theorem deploy_ctor_start_accepts_value[local]:
 !tops am tx mut nr body am_c es0.
 deploy_ctor_start tops am tx (mut,nr,body,am_c,es0) ==>
 mut = Payable \/ tx.value = 0
Proof
 rpt gen_tac >> simp[deploy_ctor_start_def] >> rpt strip_tac >>
 Cases_on `tx.value = 0` >> simp[] >>
 Cases_on `mut = Payable` >> simp[] >>
 gvs[ignore_bind_def, bind_def, send_call_value_def,
     deploy_evaluation_context_def, initial_evaluation_context_def,
     check_def, assert_def, raise_def]
QED

Theorem deploy_ctor_package_accepts_value[local]:
 !tops rp runtime unit exts ints fb cf ce pa pay nr key ut body ret
  am tx mut nr' body' am_c es0 deploy_bc es.
 lower_vyper_deploy_unit tops rp runtime = SOME unit /\
 classify_functions tops = (exts,ints,fb,SOME cf) /\
 set_constructor_package_target rp.rpol_target
   (package_constructor tops F (assign_nkeys tops 0) cf) =
     (ce,pa,pay,nr,key,ut,body,ret) /\
 deploy_state_rel tops deploy_bc am tx es /\
 deploy_ctor_start tops am tx (mut,nr',body',am_c,es0) ==>
 pay \/ tx.value = 0
Proof
 rpt gen_tac >> strip_tac >>
 drule deploy_ctor_start_accepts_value >> strip_tac >> simp[] >>
 `tx.function_name = "__init__"` by fs[deploy_state_rel_def] >>
 drule_all lower_vyper_deploy_unit_ctor_named_init >> strip_tac >>
 PairCases_on `cf` >> gvs[ctor_named_init_def] >>
 qspecl_then [`tops`, `NONE`, `"__init__"`] mp_tac
   classify_functions_ctor_lookup >> simp[] >> strip_tac >>
 fs[deploy_ctor_start_def] >>
 gvs[package_constructor_def, set_constructor_package_target_def]
QED

Theorem deploy_ctor_prefix_entry:
 !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs
  body cenv nr nkey ut imm exit_lbl sa sb sj st_exit st_epilogue st_final func
  mut nr' body' am_c es0 exts ints fb cf cenv0 pos_args is_payable ret.
 deploy_phases policy tops (deploy_bc,runtime_bc)
   (rpolicy,dunit,dout,prog,cplan) /\
 deploy_source_ok tops am tx /\
 deploy_state_rel tops deploy_bc am tx es /\
 gas_variant vs (deploy_entry_state prog cplan tops es) /\
 deploy_ctor_code tops rpolicy runtime_bc dunit
   (body,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,st_epilogue,st_final,func) /\
 deploy_ctor_start tops am tx (mut,nr',body',am_c,es0) /\
 classify_functions tops = (exts,ints,fb,SOME cf) /\
 set_constructor_package_target rpolicy.rpol_target
   (package_constructor tops F (assign_nkeys tops 0) cf) =
     (cenv0,pos_args,is_payable,nr,nkey,ut,body,ret) ==>
 lookup_function func.fn_name dunit.cu_context.ctx_functions = SOME func /\
 ctx_wf dunit.cu_context /\ wf_invoke_targets dunit.cu_context /\
 reachable_call_graph_acyclic dunit.cu_context /\
 ctx_inst_ids_distinct dunit.cu_context /\
 ?e. fresh_vars_wrt (initial_compile_state "__deploy") e /\
     ~e.vs_halted /\
     e.vs_current_bb = (initial_compile_state "__deploy").cs_current_bb /\
     e.vs_inst_idx = LENGTH (initial_compile_state "__deploy").cs_current_insts /\
     e.vs_allocas = FEMPTY /\ e.vs_alloca_next = imm_len tops /\
     vars_pc_only vs e /\
     (is_payable \/ e.vs_call_ctx.cc_callvalue = 0w) /\
     (!fuel r. run_from fuel dunit.cu_context func e = r /\
        (!err. r <> Error err) ==>
        ?fuel'. run_context fuel' dunit.cu_context vs = r)
Proof
 rpt gen_tac >> strip_tac >>
 `supported_program tops` by fs[deploy_source_ok_def] >>
 drule_all deploy_ctor_original_entry_shape >> strip_tac >>
 `lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
  func.fn_name = "__deploy"` by fs[deploy_ctor_code_def] >>
 drule_all deploy_ctor_package_accepts_value >> disch_tac >>
 `is_payable \/ vs.vs_call_ctx.cc_callvalue = 0w` by
   (Cases_on `is_payable` >> simp[] >>
    gvs[gas_variant_def, deploy_entry_state_def, entry_venom_state_def,
        deploy_state_rel_def, venom_state_component_equality,
        call_context_component_equality]) >>
 drule_all deploy_ctor_enter_context >>
 disch_then (qspec_then `vs` strip_assume_tac) >>
 drule deploy_ctor_entry_initial_fields >> strip_tac >>
 simp[] >>
 qexists `vs with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>` >>
 gvs[fresh_vars_wrt_def, initial_compile_state_def, lookup_var_def]
QED

Theorem deploy_ctor_vars_pc_frame:
 vars_pc_only e t ==>
 t.vs_allocas = e.vs_allocas /\ t.vs_alloca_next = e.vs_alloca_next /\
 t.vs_memory = e.vs_memory /\ t.vs_data_section = e.vs_data_section /\
 t.vs_call_ctx = e.vs_call_ctx /\ t.vs_gas_readings = e.vs_gas_readings /\
 t.vs_code = e.vs_code /\ t.vs_labels = e.vs_labels /\
 t.vs_accounts = e.vs_accounts /\ t.vs_transient = e.vs_transient /\
 t.vs_logs = e.vs_logs /\ t.vs_requests = e.vs_requests /\
 t.vs_pending_deletions = e.vs_pending_deletions /\
 t.vs_halted = e.vs_halted
Proof
 simp[vars_pc_only_def, venom_state_component_equality]
QED

Theorem deploy_ctor_vars_pc_resources:
 !e t k ctx func site.
 vars_pc_only e t ==>
 (alloca_inv t <=> alloca_inv e) /\
 (alloca_frontier_inv_from k ctx func site t <=>
  alloca_frontier_inv_from k ctx func site e)
Proof
 rpt gen_tac >> strip_tac >> drule deploy_ctor_vars_pc_frame >> strip_tac >>
 `remaining_alloca_budget (fn_insts func) t =
  remaining_alloca_budget (fn_insts func) e` by
   (irule remaining_alloca_budget_domain_cong >> simp[]) >>
 simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
      alloca_frontier_inv_from_def]
QED

Theorem deploy_ctor_empty_alloca_frontier:
 !ctx name func e k.
 ctx_wf ctx /\ wf_invoke_targets ctx /\ reachable_call_graph_acyclic ctx /\
 ctx.ctx_entry = SOME name /\ lookup_function name ctx.ctx_functions = SOME func /\
 e.vs_allocas = FEMPTY /\ e.vs_alloca_next = k ==>
 alloca_inv e /\ !site. alloca_frontier_inv_from k ctx func site e
Proof
 rpt gen_tac >> strip_tac >>
 conj_tac >- simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
 `func.fn_name = name` by metis_tac[lookup_function_result_name] >>
 `MEM func ctx.ctx_functions` by metis_tac[lookup_function_MEM] >>
 `fcg_is_reachable (fcg_analyze ctx) name` by
   (irule fcg_analyze_reachable_complete_proof >>
    simp[fcg_path_def, ctx_fn_names_def] >> metis_tac[lookup_function_mem]) >>
 simp[alloca_frontier_inv_from_def] >> conj_tac
 >- (rpt strip_tac >>
     `fcg_is_reachable (fcg_analyze ctx) g` by
       metis_tac[reachable_fcg_acyclic_tc_rank, reachable_call_graph_acyclic_def] >>
     metis_tac[reachable_fcg_acyclic_no_reachable_cycle,
               reachable_call_graph_acyclic_def]) >>
 simp_tac bool_ss [unit_alloca_budget_def, LET_THM] >>
 qmatch_goalsub_abbrev_tac `CARD below * frame` >>
 qabbrev_tac `n = LENGTH (FILTER (\i. i.inst_opcode = INVOKE)
                   (FLAT (MAP fn_insts ctx.ctx_functions)))` >>
 `remaining_alloca_budget (fn_insts func) e <= frame /\ CARD below <= n` by
   simp[Abbr `below`, Abbr `frame`, Abbr `n`, call_targets_card,
        remaining_alloca_budget_frame] >>
 `CARD below * frame <= n * frame` by (irule LESS_MONO_MULT >> simp[]) >>
 full_simp_tac bool_ss [RIGHT_ADD_DISTRIB, MULT_LEFT_1] >> decide_tac
QED

Theorem deploy_ctor_shifted_budget:
 !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan.
 deploy_phases policy tops (deploy_bc,runtime_bc)
   (rpolicy,dunit,dout,prog,cplan) ==>
 imm_len tops + unit_alloca_budget dunit.cu_context < dimword (:256)
Proof
 rpt strip_tac >> drule deploy_imm_budget_ok >> decide_tac
QED

Theorem deploy_ctor_initial_local_ptrs:
 !target tops use_trans nkeys cf cenv args pay nr key ut body ret cap imm
  func scope s.
 set_constructor_package_target target (package_constructor tops use_trans nkeys cf) =
   (cenv,args,pay,nr,key,ut,body,ret) ==>
 local_ptrs_rel func
   (cenv with ce_imm_alloca := (if cap > 0 then SOME imm else NONE)) [scope] s
Proof
 rpt gen_tac >> strip_tac >> PairCases_on `cf` >>
 gvs[set_constructor_package_target_def, package_constructor_def,
     update_cenv_nonreentrant_def] >>
 simp[local_ptrs_rel_def, local_region_def, cj 3 build_compile_env_vars]
QED

Theorem deploy_ctor_payable_actual[local]:
 !pay st st' ctx func e.
 (if pay then comp_return ()
  else comp_bind (emit_op CALLVALUE [])
    (\cv. comp_bind (emit_op ISZERO [cv]) (\nv. emit_void ASSERT [nv]))) st = ((),st') /\
 fn_has_code st st' func /\ fresh_vars_wrt st e /\ ~e.vs_halted /\
 e.vs_current_bb = st.cs_current_bb /\
 e.vs_inst_idx = LENGTH st.cs_current_insts /\
 (pay \/ e.vs_call_ctx.cc_callvalue = 0w) ==>
 ?t. vars_pc_only e t /\ fresh_vars_wrt st' t /\ ~t.vs_halted /\
     t.vs_current_bb = st'.cs_current_bb /\
     t.vs_inst_idx = LENGTH st'.cs_current_insts /\ abi_decode_sim ctx func e t
Proof
 rpt gen_tac >> Cases_on `pay`
 >- (simp[comp_return_def] >> rpt strip_tac >> gvs[] >>
     qexists `e` >> simp[vars_pc_only_refl, abi_decode_sim_refl]) >>
 simp[comp_bind_def] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >>
 drule_all payable_check_frag_allocas >>
 disch_then (qspec_then `ctx` assume_tac) >>
 `frag_exec ctx st st' (\s. s = e)
    (\t. vars_pc_only e t /\ fresh_vars_wrt st' t /\
         (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x e) /\
         e.vs_call_ctx.cc_callvalue = 0w /\ t.vs_allocas = e.vs_allocas) (K F)` by
   (irule frag_exec_conseq >> goal_assum $ drule_at Any >> simp[]) >>
 drule abi_decode_sim_from_fragment >>
 disch_then (qspecl_then [`e`, `func`] mp_tac) >> simp[] >> strip_tac >>
 goal_assum $ drule_at Any >> simp[]
QED

Theorem deploy_ctor_fixed_region_actual[local]:
 !cap st st' id buf ctx func e.
 compile_fixed_region_with_id cap st = ((id,buf),st') /\
 fn_has_code st st' func /\ fresh_vars_wrt st e /\ ~e.vs_halted /\
 e.vs_current_bb = st.cs_current_bb /\
 e.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?t. vars_pc_only e t /\ fresh_vars_wrt st' t /\ ~t.vs_halted /\
     t.vs_current_bb = st'.cs_current_bb /\
     t.vs_inst_idx = LENGTH st'.cs_current_insts /\
     eval_operand buf.buf_operand t = SOME 0w /\ abi_decode_sim ctx func e t
Proof
 rpt gen_tac >> strip_tac >>
 drule compile_fixed_region_with_id_result >> strip_tac >>
 `st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb` by
   (qpat_x_assum `compile_fixed_region_with_id _ _ = _` mp_tac >>
    simp[compile_fixed_region_with_id_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
    strip_tac >> gvs[]) >>
 `frag_exec ctx st st' (\s. s = e)
   (\t. vars_pc_only e t /\ fresh_vars_wrt st' t /\
        eval_operand buf.buf_operand t = SOME 0w) (K F)` by
   (irule frag_exec_run_inst_seq >>
    simp[emitted_insts_def, DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def] >>
    drule compile_fixed_region_execution >>
    disch_then (qspec_then `e` strip_assume_tac) >>
    gvs[emitted_insts_def, DROP_LENGTH_APPEND, mk_inst_def] >>
    simp[vars_pc_only_def, update_var_def, eval_operand_def, lookup_var_def,
         FLOOKUP_UPDATE, venom_state_component_equality, fresh_vars_wrt_def] >>
    fs[fresh_vars_wrt_def]) >>
 drule abi_decode_sim_from_fragment >>
 disch_then (qspecl_then [`e`, `func`] mp_tac) >> simp[] >> strip_tac >>
 goal_assum $ drule_at Any >> simp[]
QED

Theorem deploy_ctor_payable_extends[local]:
 (if pay then comp_return ()
  else comp_bind (emit_op CALLVALUE [])
    (\cv. comp_bind (emit_op ISZERO [cv]) (\nv. emit_void ASSERT [nv]))) st = ((),st') ==>
 cs_extends st st'
Proof
 Cases_on `pay` >- simp[comp_return_def, cs_extends_refl] >>
 simp[comp_bind_def] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >>
 imp_res_tac emit_op_extends >> drule emit_void_extends >> strip_tac >>
 irule cs_extends_same_block >>
 gvs[same_blocks_def, APPEND_ASSOC, IS_PREFIX_APPEND]
QED

Theorem deploy_ctor_fixed_extends[local]:
 (if cap > 0 then
    comp_bind (compile_fixed_region_with_id cap) (\r. comp_return (SND r).buf_operand)
  else comp_return (Lit 0w)) st = (imm,st') ==>
 cs_extends st st'
Proof
 Cases_on `cap > 0` >- (
   simp[comp_bind_def] >> pairarg_tac >> simp[comp_return_def] >> strip_tac >>
   PairCases_on `r''` >> gvs[] >>
   drule compile_fixed_region_with_id_result >> strip_tac >>
   irule cs_extends_same_block >>
   gvs[compile_fixed_region_with_id_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def]) >>
 simp[comp_return_def, cs_extends_refl]
QED

Theorem deploy_ctor_pre_register_actual:
 !pay cap st st_pay st1 imm ctx func e.
 (if pay then comp_return ()
  else comp_bind (emit_op CALLVALUE [])
    (\cv. comp_bind (emit_op ISZERO [cv]) (\nv. emit_void ASSERT [nv]))) st = ((),st_pay) /\
 (if cap > 0 then
    comp_bind (compile_fixed_region_with_id cap) (\r. comp_return (SND r).buf_operand)
  else comp_return (Lit 0w)) st_pay = (imm,st1) /\
 fn_has_code st st1 func /\ fresh_vars_wrt st e /\ ~e.vs_halted /\
 e.vs_current_bb = st.cs_current_bb /\
 e.vs_inst_idx = LENGTH st.cs_current_insts /\
 (pay \/ e.vs_call_ctx.cc_callvalue = 0w) ==>
 ?t. vars_pc_only e t /\ fresh_vars_wrt st1 t /\ ~t.vs_halted /\
     t.vs_current_bb = st1.cs_current_bb /\
     t.vs_inst_idx = LENGTH st1.cs_current_insts /\
     eval_operand imm t = SOME 0w /\ abi_decode_sim ctx func e t
Proof
 rpt gen_tac >> strip_tac >>
 drule deploy_ctor_payable_extends >> strip_tac >>
 drule deploy_ctor_fixed_extends >> strip_tac >>
 drule_all fn_has_code_split >> strip_tac >>
 drule deploy_ctor_payable_actual >>
 disch_then (qspecl_then [`ctx`, `func`, `e`] mp_tac) >>
 simp[] >> strip_tac >>
 (Cases_on `cap > 0`
 >- (gvs[comp_bind_def, comp_return_def] >>
     pairarg_tac >> gvs[] >> PairCases_on `r''` >>
     drule_all deploy_ctor_fixed_region_actual >>
     disch_then (qspec_then `ctx` strip_assume_tac) >>
     goal_assum $ drule_at Any >>
     simp[] >> conj_tac
     >- (irule vars_pc_only_trans >> goal_assum $ drule_at Any >> simp[]) >>
     irule abi_decode_sim_trans >> goal_assum $ drule_at Any >> simp[]) >>
 gvs[comp_return_def] >> goal_assum $ drule_at Any >>
 simp[eval_operand_def])
QED

Theorem deploy_ctor_registration_code:
 !pay cap ce args nr key ut st st_pay imm st1 ce1 st2 st3 lbl sa func.
 (if pay then comp_return ()
  else comp_bind (emit_op CALLVALUE [])
    (\cv. comp_bind (emit_op ISZERO [cv]) (\nv. emit_void ASSERT [nv]))) st = ((),st_pay) /\
 (if cap > 0 then
    comp_bind (compile_fixed_region_with_id cap) (\r. comp_return (SND r).buf_operand)
  else comp_return (Lit 0w)) st_pay = (imm,st1) /\
 compile_register_constructor_args
   (ce with ce_imm_alloca := (if cap > 0 then SOME imm else NONE))
   args 0 0 st1 = (ce1,st2) /\
 (if nr then compile_nonreentrant_lock key ut F else comp_return ()) st2 = ((),st3) /\
 fresh_label "ctor_exit" st3 = (lbl,sa) /\ fn_has_code st sa func ==>
 fn_has_code st st1 func /\ fn_has_code st1 st2 func
Proof
 rpt gen_tac >> strip_tac >>
 drule deploy_ctor_payable_extends >> strip_tac >>
 drule deploy_ctor_fixed_extends >> strip_tac >>
 drule ctor_registration_extends >> strip_tac >>
 `cs_extends st2 st3` by
   (Cases_on `nr` >> gvs[comp_return_def, cs_extends_refl] >>
    mp_tac (cj 2 ctor_code_primitives_append) >>
    simp[cs_appends_def] >> disch_then drule >> simp[]) >>
 drule cs_extends_fresh_label >> strip_tac >>
 `cs_extends st st1` by metis_tac[cs_extends_trans] >>
 `cs_extends st2 sa` by metis_tac[cs_extends_trans] >>
 `cs_extends st1 sa` by metis_tac[cs_extends_trans] >>
 drule_all fn_has_code_split >> strip_tac >>
 qpat_x_assum `fn_has_code st1 sa func` mp_tac >>
 qspecl_then [`st1`, `st2`, `sa`, `func`] mp_tac fn_has_code_split >>
 simp[]
QED

Theorem deploy_ctor_entry_before_register:
 !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs
  body cenv nr nkey ut imm exit_lbl sa sb sj se sp sf func mut nr' body' am_c es0
  exts ints fb cf cenv0 pos_args is_payable ret cap st_pay st1 cenv1 st2 st3.
 deploy_phases policy tops (deploy_bc,runtime_bc) (rpolicy,dunit,dout,prog,cplan) /\
 deploy_source_ok tops am tx /\ deploy_state_rel tops deploy_bc am tx es /\
 gas_variant vs (deploy_entry_state prog cplan tops es) /\
 deploy_ctor_code tops rpolicy runtime_bc dunit
   (body,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,se,sp,sf,func) /\
 deploy_ctor_start tops am tx (mut,nr',body',am_c,es0) /\
 classify_functions tops = (exts,ints,fb,SOME cf) /\
 set_constructor_package_target rpolicy.rpol_target
   (package_constructor tops F (assign_nkeys tops 0) cf) =
     (cenv0,pos_args,is_payable,nr,nkey,ut,body,ret) /\
 cap = imm_len tops /\
 (if is_payable then comp_return ()
  else comp_bind (emit_op CALLVALUE [])
    (\cv. comp_bind (emit_op ISZERO [cv]) (\nv. emit_void ASSERT [nv])))
     (initial_compile_state "__deploy") = ((),st_pay) /\
 (if cap > 0 then
    comp_bind (compile_fixed_region_with_id cap) (\r. comp_return (SND r).buf_operand)
  else comp_return (Lit 0w)) st_pay = (imm,st1) /\
 compile_register_constructor_args
   (cenv0 with ce_imm_alloca := (if cap > 0 then SOME imm else NONE))
   pos_args 0 0 st1 = (cenv1,st2) /\
 (if nr then compile_nonreentrant_lock nkey ut F else comp_return ()) st2 = ((),st3) /\
 fresh_label "ctor_exit" st3 = (exit_lbl,sa) ==>
 ?t. fresh_vars_wrt st1 t /\ ~t.vs_halted /\
     t.vs_current_bb = st1.cs_current_bb /\
     t.vs_inst_idx = LENGTH st1.cs_current_insts /\ eval_operand imm t = SOME 0w /\
     vars_pc_only vs t /\ t.vs_allocas = FEMPTY /\ t.vs_alloca_next = imm_len tops /\
     alloca_inv t /\
     (!site. alloca_frontier_inv_from (imm_len tops) dunit.cu_context func site t) /\
     (!aid. st1.cs_next_id <= aid ==> FLOOKUP t.vs_allocas aid = NONE) /\
     (!scope. local_ptrs_rel func
        (cenv0 with ce_imm_alloca := (if cap > 0 then SOME imm else NONE)) [scope] t) /\
     t.vs_memory = vs.vs_memory /\ t.vs_data_section = vs.vs_data_section /\
     t.vs_call_ctx = vs.vs_call_ctx /\ t.vs_gas_readings = vs.vs_gas_readings /\
     t.vs_code = vs.vs_code /\ t.vs_labels = vs.vs_labels /\
     t.vs_accounts = vs.vs_accounts /\ t.vs_transient = vs.vs_transient /\
     t.vs_logs = vs.vs_logs /\ t.vs_requests = vs.vs_requests /\
     t.vs_pending_deletions = vs.vs_pending_deletions /\
     (!fuel r. run_from fuel dunit.cu_context func t = r /\ (!err. r <> Error err) ==>
        ?fuel'. run_context fuel' dunit.cu_context vs = r)
Proof
 rpt gen_tac >> strip_tac >>
 drule_all deploy_ctor_prefix_entry >>
 disch_then (map_every assume_tac o CONJUNCTS) >>
 qpat_x_assum `?e. _` (qx_choose_then `e` (map_every assume_tac o CONJUNCTS)) >>
 `fn_has_code (initial_compile_state "__deploy") sa func` by fs[deploy_ctor_code_def] >>
 drule_all deploy_ctor_registration_code >> strip_tac >>
 drule_all deploy_ctor_pre_register_actual >>
 disch_then (qspec_then `dunit.cu_context` strip_assume_tac) >>
 `vars_pc_only vs t` by
   (irule vars_pc_only_trans >> goal_assum $ drule_at Any >> simp[]) >>
 `t.vs_allocas = FEMPTY /\ t.vs_alloca_next = imm_len tops` by
   (drule deploy_ctor_vars_pc_frame >> strip_tac >>
    qpat_x_assum `vars_pc_only e t` (strip_assume_tac o MATCH_MP deploy_ctor_vars_pc_frame) >>
    simp[]) >>
 `dunit.cu_context.ctx_entry = SOME func.fn_name` by
   (fs[deploy_ctor_code_def] >> drule lower_vyper_deploy_unit_entry >> simp[]) >>
 drule_all deploy_ctor_empty_alloca_frontier >> strip_tac >>
 `!scope. local_ptrs_rel func
   (cenv0 with ce_imm_alloca := (if cap > 0 then SOME imm else NONE)) [scope] t` by
   (gen_tac >> drule deploy_ctor_initial_local_ptrs >> disch_then irule) >>
 qpat_assum `vars_pc_only vs t` (strip_assume_tac o MATCH_MP deploy_ctor_vars_pc_frame) >>
 qexists `t` >> simp[] >>
 fs[abi_decode_sim_def] >> metis_tac[]
QED

Theorem deploy_ctor_pre_register_unterminated:
 (if pay then comp_return ()
  else comp_bind (emit_op CALLVALUE [])
    (\cv. comp_bind (emit_op ISZERO [cv]) (\nv. emit_void ASSERT [nv])))
     (initial_compile_state "__deploy") = ((),st_pay) /\
 (if cap > 0 then
    comp_bind (compile_fixed_region_with_id cap) (\r. comp_return (SND r).buf_operand)
  else comp_return (Lit 0w)) st_pay = (imm,st1) ==>
 ~block_is_terminated st1
Proof
 Cases_on `pay` >> Cases_on `cap > 0` >>
 simp[compile_fixed_region_with_id_def, comp_bind_def, comp_ignore_bind_def,
     comp_return_def, fresh_id_def, fresh_var_def, emit_op_def, emit_void_def,
     emit_def, initial_compile_state_def, block_is_terminated_def,
     mk_inst_def, is_terminator_def, LAST_APPEND] >>
 strip_tac >> gvs[is_terminator_def, LAST_APPEND]
QED
