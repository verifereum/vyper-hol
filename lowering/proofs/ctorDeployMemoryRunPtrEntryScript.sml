(* The constructor prefix with the pointer ghost: the run from the unit's
 * entry, after the payable check, the immutables region's base, the
 * constructor arguments' decode (DLOAD from the data section) and the lock,
 * reaches the body start sa in a state s0 related to the source's body
 * start, with the GAS readings still unread and deploy_ptr_inv holding of
 * the ghost there; and a pointer-safe run from s0 makes the run from the
 * entry pointer-safe.
 * TOP-LEVEL: deploy_ctor_entry_run_ptr.
 *)
Theory ctorDeployMemoryRunPtrEntry
Ancestors
  ctorDeployMemoryRunPtrDefs ctorDeployLoweringDefs gasSummary ptrSafeRun
  stmtSimDefs venomInst
  ctorDeployMemoryRunPtrPrefixInit ctorDeployMemoryRunPtrPrefixPrepare
  ctorDeployMemoryRunPtrPrefixRegisterList
  ctorDeployMemoryRunPtrPrefixCompleteCoherent
  ctorDeployMemoryRunPtrPrefixEntryInputs ctorDeployImmBudget
  ctorDeployLoweringEntryTransport ctorDeployLoweringPrefix
  o1PassContract e2eEntry venomState compileEnv
  ctorDeployDefs e2eDeployDefs context vyperCompiler
  emitHelperProps ctorRegisterArgs exprLoweringProps fragExec
  ctorDeployMemoryFrontier deployUnitProducers allocaFrontierBound
  allocaBudgetProps fcgCorrectnessProof fcgDefs fcgPostorder
  contextCodegenRel arithmetic finite_map venomMemDefs
  vyperInterpreter vyperState vyperContext ctorDeployInitcode compileVyper
  ctorDeployMemoryRunPtrPrefixEntryPrepare
  ctorDeployMemoryRunPtrPrefixEntryRegisterList
  ctorDeployMemoryRunPtrPrefixEntryPrepared
  ctorDeployMemoryRunPtrPrefixEntryPreparedSizes abiEncoderRegisteredEffect
  ctorDeployLoweringEntrySourceFrame
  ctorDeployMemoryRunPtrPrefixEntryPreparedOrigins
  ctorDeployMemoryRunPtrPrefixEntrySeparation
  ctorDeployMemoryRunPtrPrefixEntryBase ctorDeployMemoryRunPtrPrefixEntryAmbient
  ctorDeployLoweringEntryRoom ctorDeployLoweringEntryFmp
  ctorDeployLoweringEntryBodyResources
  ctorDeployMemoryRunPtrPrefixEntrySemantic ctorDeployMemoryRunPtrPrefixEntryImmutable
  valueEncoding codegenRel

val _ = Parse.hide "body";

(* The concrete entry used by the ghost prefix is the compiler entry,
   not an independently chosen witness of semantic execution. *)
Theorem deploy_ptr_entry_normalized:
  deploy_phases policy tops (deploy_bc,runtime_bc)
    (rp,unit,dout,prog,cplan) /\
  deploy_source_ok tops am tx /\
  gas_variant vs (deploy_entry_state prog cplan tops es) /\
  deploy_ctor_code tops rp runtime_bc unit
    (body,ce,nr,key,ut,imm,exit,sa,sb,sj,se,sp,sf,func) /\
  lookup_function "__deploy" unit.cu_context.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl ==>
  let initial = vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>
  in fn = func /\ lbl = "__deploy" /\
     fresh_vars_wrt (initial_compile_state "__deploy") initial /\
     ~initial.vs_halted /\
     initial.vs_current_bb = (initial_compile_state "__deploy").cs_current_bb /\
     initial.vs_inst_idx = LENGTH (initial_compile_state "__deploy").cs_current_insts /\
     initial.vs_allocas = FEMPTY /\ initial.vs_alloca_next = imm_len tops /\
     allocas_from (imm_len tops) initial /\
     ~ctx_has_dalloca unit.cu_context /\
     imm_len tops + unit_alloca_budget unit.cu_context < dimword (:256) /\
     (!bb label. lookup_block label func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0)
Proof
  strip_tac >>
  `supported_program tops` by fs[deploy_source_ok_def] >>
  drule_all deploy_ctor_lookup_unique >> strip_tac >> gvs[] >>
  drule_all deploy_prefix_ctor_entry_label >> strip_tac >> gvs[] >>
  drule_all deploy_prefix_no_dalloca >> strip_tac >>
  `imm_len tops + unit_alloca_budget unit.cu_context < dimword (:256)` by
    (drule deploy_imm_budget_ok >> decide_tac) >>
  `vs.vs_vars = FEMPTY /\ ~vs.vs_halted` by
    (qpat_assum `gas_variant _ _` mp_tac >>
     rewrite_tac[gas_variant_def] >> strip_tac >>
     pop_assum (mp_tac o Q.AP_TERM `\s. (s.vs_vars,s.vs_halted)`) >>
     simp[deploy_entry_state_def, entry_venom_state_fresh]) >>
  drule deploy_prefix_normalized_allocations >> simp[] >> strip_tac >>
  simp[fresh_vars_wrt_def, initial_compile_state_def, lookup_var_def] >>
  rpt strip_tac >> drule_all deploy_ctor_raw_blocks_no_phi >> simp[]
QED

(* A successfully started deployment cannot enable the constructor lock.
   Neither the lock nor label generation emits an instruction, so its
   paired execution is exactly the identity on both machine and ghost. *)
Theorem deploy_ptr_entry_lock_identity:
  deploy_state_rel tops deploy_bc am tx es /\
  deploy_ctor_start tops am tx (mut,nr,body,am_c,es0) /\
  (if nr then compile_nonreentrant_lock key ut F else comp_return ()) st = ((),locked) /\
  fresh_label "ctor_exit" locked = (exit,sa) ==>
  nr = F /\ locked = st /\
  sa.cs_current_bb = st.cs_current_bb /\
  sa.cs_current_insts = st.cs_current_insts /\
  sa.cs_next_var = st.cs_next_var /\ sa.cs_next_id = st.cs_next_id /\
  sa.cs_blocks = st.cs_blocks /\
  (!initial. fresh_vars_wrt sa initial <=> fresh_vars_wrt st initial)
Proof
  strip_tac >>
  `nr = F` by
    (qpat_x_assum `deploy_state_rel _ _ _ _ _` mp_tac >>
     qpat_x_assum `deploy_ctor_start _ _ _ _` mp_tac >>
     pure_rewrite_tac[deploy_state_rel_def, deploy_ctor_start_def,
                     constructor_args_encode_def] >>
     rpt strip_tac >>
     qpat_x_assum `tx.function_name = _` (fn th =>
       qpat_x_assum `lookup_function NONE tx.function_name _ _ = _`
         (mp_tac o PURE_REWRITE_RULE [th])) >>
     qpat_x_assum `lookup_function NONE "__init__" _ _ = _`
       (fn th => pure_rewrite_tac[th]) >>
     simp_tac bool_ss [optionTheory.SOME_11, pairTheory.PAIR_EQ]) >>
  gvs[comp_return_def] >> drule fresh_label_props >> strip_tac >>
  simp[fresh_vars_wrt_def]
QED

(* Code splitting without the unrelated semantic EntryPrefix dependency. *)
Theorem deploy_ptr_entry_registration_code[local]:
  (if pay then comp_return ()
   else comp_bind (emit_op CALLVALUE [])
     (\cv. comp_bind (emit_op ISZERO [cv]) (\nv. emit_void ASSERT [nv]))) st = ((),st_pay) /\
  (if cap > 0 then
     comp_bind (compile_fixed_region_with_id cap) (\r. comp_return (SND r).buf_operand)
   else comp_return (Lit 0w)) st_pay = (imm,st1) /\
  compile_register_constructor_args ce args 0 0 st1 = (ce1,st2) /\
  fresh_label "ctor_exit" st2 = (lbl,sa) /\ fn_has_code st sa func ==>
  fn_has_code st st1 func /\ fn_has_code st1 st2 func
Proof
  strip_tac >>
  drule prefix_prepare_payable_layout >> strip_tac >>
  drule prefix_prepare_region_layout >> strip_tac >>
  drule ctor_registration_extends >> strip_tac >>
  drule cs_extends_fresh_label >> strip_tac >>
  `cs_extends st st1` by metis_tac[cs_extends_trans] >>
  `cs_extends st1 sa` by metis_tac[cs_extends_trans] >>
  drule_all fn_has_code_split >> strip_tac >>
  metis_tac[fn_has_code_split]
QED

Theorem deploy_ptr_entry_empty_frontier[local]:
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

Theorem deploy_ptr_entry_initial_resources[local]:
  deploy_ctor_code tops rp runtime unit
    (body,ce,nr,key,ut,imm,exit,sa,sb,sj,se,sp,sf,func) /\
  lookup_function "__deploy" unit.cu_context.ctx_functions = SOME func /\
  initial.vs_allocas = FEMPTY /\ initial.vs_alloca_next = imm_len tops ==>
  alloca_inv initial /\
  !site. alloca_frontier_inv_from (imm_len tops) unit.cu_context func site initial
Proof
  strip_tac >>
  `lower_vyper_deploy_unit tops rp runtime = SOME unit` by fs[deploy_ctor_code_def] >>
  drule lower_vyper_deploy_unit_context_ok >> strip_tac >>
  drule lower_vyper_deploy_unit_entry >> strip_tac >>
  drule_all lowered_unit_entry_facts >> strip_tac >>
  irule deploy_ptr_entry_empty_frontier >> simp[] >> gvs[]
QED

Theorem deploy_ptr_entry_start_accepts_value[local]:
  deploy_ctor_start tops am tx (mut,nr,body,am_c,es0) ==>
  mut = Payable \/ tx.value = 0
Proof
  simp[deploy_ctor_start_def] >> rpt strip_tac >>
  Cases_on `tx.value = 0` >> simp[] >>
  Cases_on `mut = Payable` >> simp[] >>
  gvs[ignore_bind_def, bind_def, send_call_value_def,
      deploy_evaluation_context_def, initial_evaluation_context_def,
      check_def, assert_def, raise_def]
QED

Theorem deploy_ptr_entry_package_accepts_value[local]:
  lower_vyper_deploy_unit tops rp runtime = SOME unit /\
  classify_functions tops = (exts,ints,fb,SOME cf) /\
  set_constructor_package_target rp.rpol_target
    (package_constructor tops F (assign_nkeys tops 0) cf) =
      (ce,pa,pay,nr,key,ut,body,ret) /\
  deploy_state_rel tops deploy_bc am tx es /\
  deploy_ctor_start tops am tx (mut,nr',body',am_c,es0) ==>
  pay \/ tx.value = 0
Proof
  strip_tac >> drule deploy_ptr_entry_start_accepts_value >> strip_tac >> simp[] >>
  `tx.function_name = "__init__"` by fs[deploy_state_rel_def] >>
  drule_all lower_vyper_deploy_unit_ctor_named_init >> strip_tac >>
  PairCases_on `cf` >> gvs[ctor_named_init_def] >>
  qspecl_then [`tops`, `NONE`, `"__init__"`] mp_tac
    classify_functions_ctor_lookup >> simp[] >> strip_tac >>
  fs[deploy_ctor_start_def] >>
  gvs[package_constructor_def, set_constructor_package_target_def]
QED

(* One concrete endpoint for both semantic reconstruction and the ghost. *)
Theorem deploy_ptr_entry_prefix:
  deploy_phases policy tops (deploy_bc,runtime_bc) (rp,unit,dout,prog,cplan) /\
  deploy_source_ok tops am tx /\ deploy_state_rel tops deploy_bc am tx es /\
  gas_variant vs (deploy_entry_state prog cplan tops es) /\
  deploy_ctor_code tops rp runtime_bc unit
    (body,ce,nr,key,ut,imm,exit,sa,sb,sj,se,sp,sf,func) /\
  deploy_ctor_start tops am tx (mut,nr,body,am_c,es0) /\
  lookup_function "__deploy" unit.cu_context.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl ==>
  ?actual H qt scope fargs ce0.
    (!inst n base sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_operands = [Lit n] /\
      FLOOKUP actual.vs_allocas inst.inst_id = SOME (base,sz) ==> sz = w2n n) /\
    actual.vs_accounts = vs.vs_accounts /\ actual.vs_transient = vs.vs_transient /\
    actual.vs_logs = vs.vs_logs /\ actual.vs_requests = vs.vs_requests /\
    actual.vs_pending_deletions = vs.vs_pending_deletions /\
    allocas_from (imm_len tops) actual /\
    (!a. a < imm_len tops ==> read_byte a actual.vs_memory = 0w) /\
    bind_arguments (type_env tops) fargs tx.args = SOME scope /\
    local_ptrs_rel func ce [scope] actual /\
    alloca_inv actual /\
    (!site. alloca_frontier_inv_from (imm_len tops) unit.cu_context func site actual) /\
    fresh_vars_wrt sa actual /\
    (!aid. sa.cs_next_id <= aid ==> FLOOKUP actual.vs_allocas aid = NONE) /\
    ~actual.vs_halted /\ actual.vs_current_bb = sa.cs_current_bb /\
    actual.vs_inst_idx = LENGTH sa.cs_current_insts /\
    actual.vs_data_section = vs.vs_data_section /\
    actual.vs_call_ctx = vs.vs_call_ctx /\ actual.vs_labels = vs.vs_labels /\
    actual.vs_code = vs.vs_code /\ actual.vs_outcomes = vs.vs_outcomes /\
    actual.vs_tx_ctx = vs.vs_tx_ctx /\ actual.vs_block_ctx = vs.vs_block_ctx /\
    actual.vs_gas_readings = vs.vs_gas_readings /\
    abi_decode_sim unit.cu_context func
      (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) actual /\
    eval_operand imm actual = SOME 0w /\ op_taint qt imm = {} /\ op_prov H imm = NONE /\
    deploy_ptr_inv tops runtime_bc am tx imm H qt actual /\
    ((!fuel. ptr_safe_run (deploy_dead tops runtime_bc am tx) (imm_len tops)
        fuel unit.cu_context func [] H qt actual) ==>
      !fuel. ptr_safe_run (deploy_dead tops runtime_bc am tx) (imm_len tops)
        fuel unit.cu_context func [] FEMPTY entry_taint
        (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)) /\
    (!j. j < LENGTH fargs ==>
      ?entry d B.
        lookup_scopes (FST (EL j fargs)) [scope] = SOME entry /\
        local_region ce [scope] actual (FST (EL j fargs)) d
          (type_memory_bytes ce0 (SND (EL j fargs))) /\
        FINITE B /\ B SUBSET range_bytes [(d,type_memory_bytes ce0 (SND (EL j fargs)))] /\
        DISJOINT B qt.t_mem /\ (!a. a IN B ==> a < actual.vs_alloca_next) /\
        (!mem. (!a. a IN B ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 actual.vs_memory) ==>
          val_in_memory entry.type entry.value d mem))
Proof
  strip_tac >>
  drule_all deploy_ptr_entry_normalized >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `fresh_vars_wrt _ initial` >> gvs[] >>
  drule_all deploy_ptr_entry_initial_resources >> strip_tac >>
  VALID (qpat_assum `deploy_ctor_code _ _ _ _ _` (strip_assume_tac o REWRITE_RULE [deploy_ctor_code_def])) >>
  drule_all deploy_ptr_entry_lock_identity >> strip_tac >> gvs[] >>
  drule_all deploy_ptr_entry_registration_code >> strip_tac >>
  drule_all deploy_ptr_entry_package_accepts_value >> disch_tac >>
  Q.SUBGOAL_THEN `is_payable \/ initial.vs_call_ctx.cc_callvalue = 0w` assume_tac
  >- (Cases_on `is_payable` >> simp[] >>
      gvs[Abbr `initial`, gas_variant_def, deploy_entry_state_def, entry_venom_state_def,
          deploy_state_rel_def, venom_state_component_equality, call_context_component_equality]) >>
  drule_all prefix_entry_prepare_actual >>
  disch_then (qspecl_then [`entry_taint`, `[]`, `FEMPTY`,
    `deploy_dead tops runtime_bc am tx`] strip_assume_tac) >>
  qpat_x_assum `is_payable \/ tx.value = 0` kall_tac >>
  qpat_x_assum `is_payable \/ initial.vs_call_ctx.cc_callvalue = 0w` kall_tac >>
  drule_all deploy_ctor_entry_data_section >> strip_tac >>
  `constructor_args_encode tops tx initial.vs_data_section` by simp[Abbr `initial`] >>
  drule_all deploy_ctor_common_source_witness >> strip_tac >>
  qspecl_then [`tops`, `NONE`, `"__init__"`] mp_tac classify_functions_ctor_lookup >>
  simp[] >> strip_tac >> gvs[] >>
  drule_all lower_vyper_deploy_unit_ctor_named_init >> strip_tac >>
  PairCases_on `cf` >> gvs[ctor_named_init_def] >>
  `is_payable = (cf0 = Payable) /\ ret = NoneT` by
    fs[set_constructor_package_target_def, package_constructor_def] >>
  gvs[] >>
  `t.vs_data_section = vs.vs_data_section` by fs[Abbr `initial`] >>
  drule (deploy_ctor_decoder_inputs |> INST_TYPE [``:'a`` |-> ``:expr``] |> SPEC_ALL |>
    Q.INST [`ce0` |-> `ce_pack with ce_imm_alloca := (if imm_len tops > 0 then SOME imm else NONE)`,
            `imm_opt` |-> `if imm_len tops > 0 then SOME imm else NONE`] |> GEN_ALL |> SRULE []) >>
  disch_then drule_all >> strip_tac >>
  `alloca_inv t /\ !site. alloca_frontier_inv_from (imm_len tops) unit.cu_context fn site t` by
    (irule deploy_ptr_entry_initial_resources >> simp[] >> goal_assum (drule_at Any)) >>
  `allocas_from (imm_len tops) t` by simp[ptrDisciplineTheory.allocas_from_def] >>
  `!aid. st1.cs_next_id <= aid ==> FLOOKUP t.vs_allocas aid = NONE` by simp[] >>
  Q.SUBGOAL_THEN `st1.cs_blocks = st2.cs_blocks \/
    !bb. lookup_block st2.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0` assume_tac >- metis_tac[] >>
  qpat_assum `pos_args = _` (fn th =>
    qpat_assum `compile_register_constructor_args _ _ _ _ _ = _`
      (assume_tac o REWRITE_RULE [th])) >>
  `mem_bytes_at 0 (LENGTH t.vs_data_section) t.vs_data_section = t.vs_data_section` by metis_tac[] >>
  `LENGTH t.vs_data_section < dimword (:256)` by metis_tac[] >>
  `t.vs_data_section = enc (Tuple (vyper_to_abi_types (type_env tops) (MAP SND args))) (ListV avs')` by fs[] >>
  qpat_assum `t.vs_data_section = enc _ _` (assume_tac o SRULE []) >>
  `!inst b sz n. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n` by simp[] >>
  drule (deploy_ptr_entry_register_prepared_sizes |> INST_TYPE [``:'a`` |-> ``:word8``] |> SPEC_ALL |>
    Q.INST [`ce0` |-> `cenv0 with ce_imm_alloca := (if imm_len tops > 0 then SOME imm else NONE)`] |>
    GEN_ALL |> SRULE []) >>
  disch_then drule_all >>
  disch_then (qspec_then `tx` mp_tac) >>
  disch_then (qspec_then `qt` mp_tac) >>
  disch_then (qspec_then `runtime_bc` mp_tac) >>
  disch_then (qspec_then `am` mp_tac) >>
  disch_then (qspec_then `H`
    (qx_choose_then `end_state` (qx_choose_then `end_G`
      (qx_choose_then `end_taint` strip_assume_tac)))) >>
  `end_state.vs_accounts = vs.vs_accounts /\ end_state.vs_transient = vs.vs_transient /\
   end_state.vs_logs = vs.vs_logs /\ end_state.vs_requests = vs.vs_requests /\
   end_state.vs_pending_deletions = vs.vs_pending_deletions` by
    (qpat_assum `abi_encoder_registered_effect _ _ t end_state` mp_tac >>
     simp_tac bool_ss [abi_encoder_registered_effect_def] >> strip_tac >>
     fs[Abbr `initial`]) >>
  `!a. a < imm_len tops ==> read_byte a end_state.vs_memory = 0w` by
    (rpt strip_tac >>
     `read_byte a end_state.vs_memory = read_byte a t.vs_memory` by metis_tac[] >>
     simp[Abbr `initial`] >>
     qpat_assum `gas_variant _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     rewrite_tac[gas_variant_def] >> strip_tac >>
     pop_assum (mp_tac o Q.AP_TERM `\s. s.vs_memory`) >>
     simp[deploy_entry_state_def, entry_venom_state_def, init_venom_state_def,
       codegenRelTheory.read_byte_def]) >>
  qexistsl [`end_state`, `end_G`, `end_taint`, `scope'`, `args`,
    `cenv0 with ce_imm_alloca := (if imm_len tops > 0 then SOME imm else NONE)`] >>
  `local_ptrs_rel fn (cenv1 with ce_ctor_exit_label := SOME exit) [scope'] end_state` by
    (qpat_x_assum `local_ptrs_rel fn cenv1 _ end_state` mp_tac >>
     simp[local_ptrs_rel_def, local_region_def]) >>
  (conj_tac >- (rpt gen_tac >> strip_tac >>
    qpat_assum `!inst b sz n. _` irule >> goal_assum (drule_at Any) >> simp[])) >>
  simp[Abbr `initial`] >>
  conj_tac >- metis_tac[abiDecoderLoopTheory.abi_decode_sim_trans] >>
  `!x. imm = Var x ==> not_fresh_at st1 x` by
    (rpt strip_tac >> gvs[eval_operand_def] >>
     fs[fresh_vars_wrt_def, not_fresh_at_def, lookup_var_def, FLOOKUP_DEF] >>
     metis_tac[arithmeticTheory.GREATER_EQ]) >>
  `eval_operand imm end_state = SOME 0w /\ op_taint end_taint imm = {} /\ op_prov end_G imm = NONE` by
    (qpat_assum `end_state.vs_labels = t.vs_labels` mp_tac >>
     qpat_assum `!x. imm = Var x ==> not_fresh_at st1 x` mp_tac >>
     qpat_assum `!x. not_fresh_at st1 x ==> FLOOKUP end_G x = _ /\ _` mp_tac >>
     qpat_assum `!x w. not_fresh_at st1 x /\ _ ==> _` mp_tac >>
     qpat_assum `eval_operand imm t = SOME 0w` mp_tac >>
     qpat_assum `op_taint qt imm = {}` mp_tac >>
     qpat_assum `op_prov H imm = NONE` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `imm` >>
     simp[eval_operand_def, ptrDisciplineTheory.op_taint_def, ptrDisciplineTheory.op_prov_def] >>
     metis_tac[]) >>
  simp[] >>
  reverse conj_tac
  >- (qpat_x_assum `!j. j < LENGTH args ==> _` mp_tac >>
      simp[local_region_def]) >>
  simp[deploy_ptr_inv_def] >>
  conj_tac
  >- (qpat_assum `!j. j < imm_len tops /\ j IN end_taint.t_mem ==> _` mp_tac >>
      qpat_assum `qt.t_mem = {}` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> simp[] >> metis_tac[]) >>
  rpt strip_tac >> qpat_x_assum `imm = Var _` (fn th => rewrite_tac[GSYM th]) >>
  first_assum ACCEPT_TAC
QED

(* Source-linked companion: retain the source selection before hiding args. *)
Theorem deploy_ptr_entry_prefix_source:
  deploy_phases policy tops (deploy_bc,runtime_bc) (rp,unit,dout,prog,cplan) /\
  deploy_source_ok tops am tx /\ deploy_state_rel tops deploy_bc am tx es /\
  gas_variant vs (deploy_entry_state prog cplan tops es) /\
  deploy_ctor_code tops rp runtime_bc unit
    (body,ce,nr,key,ut,imm,exit,sa,sb,sj,se,sp,sf,func) /\
  deploy_ctor_start tops am tx (mut,nr,body,am_c,es0) /\
  lookup_function "__deploy" unit.cu_context.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl ==>
  ?actual H qt scope fargs ce0.
    nr = F /\
    lookup_function NONE tx.function_name Deploy tops = SOME (mut,F,fargs,[],NoneT,body) /\
    es0.scopes = [scope] /\
    (!id b sz. local_region ce es0.scopes actual id b sz ==> imm_len tops <= b) /\
    es0.tStorage = am.tStorage /\ es0.logs = am.logs /\
    es0.requests = [] /\ es0.pending_deletions = am.pending_deletions /\
    imm_len tops <= actual.vs_alloca_next /\
    es0.immutables = am_c.immutables /\ es0.outcomes = NONE /\
    send_call_value mut (deploy_evaluation_context tops am tx)
      (initial_state am_c [scope]) = (INL (),es0) /\
    am_c.accounts = am.accounts /\
    (!inst n base sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_operands = [Lit n] /\
      FLOOKUP actual.vs_allocas inst.inst_id = SOME (base,sz) ==> sz = w2n n) /\
    actual.vs_accounts = vs.vs_accounts /\ actual.vs_transient = vs.vs_transient /\
    actual.vs_logs = vs.vs_logs /\ actual.vs_requests = vs.vs_requests /\
    actual.vs_pending_deletions = vs.vs_pending_deletions /\
    allocas_from (imm_len tops) actual /\
    (!a. a < imm_len tops ==> read_byte a actual.vs_memory = 0w) /\
    bind_arguments (type_env tops) fargs tx.args = SOME scope /\
    local_ptrs_rel func ce [scope] actual /\
    alloca_inv actual /\
    (!site. alloca_frontier_inv_from (imm_len tops) unit.cu_context func site actual) /\
    fresh_vars_wrt sa actual /\
    (!aid. sa.cs_next_id <= aid ==> FLOOKUP actual.vs_allocas aid = NONE) /\
    ~actual.vs_halted /\ actual.vs_current_bb = sa.cs_current_bb /\
    actual.vs_inst_idx = LENGTH sa.cs_current_insts /\
    actual.vs_data_section = vs.vs_data_section /\
    actual.vs_call_ctx = vs.vs_call_ctx /\ actual.vs_labels = vs.vs_labels /\
    actual.vs_code = vs.vs_code /\ actual.vs_outcomes = vs.vs_outcomes /\
    actual.vs_tx_ctx = vs.vs_tx_ctx /\ actual.vs_block_ctx = vs.vs_block_ctx /\
    actual.vs_gas_readings = vs.vs_gas_readings /\
    abi_decode_sim unit.cu_context func
      (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) actual /\
    eval_operand imm actual = SOME 0w /\ op_taint qt imm = {} /\ op_prov H imm = NONE /\
    deploy_ptr_inv tops runtime_bc am tx imm H qt actual /\
    ((!fuel. ptr_safe_run (deploy_dead tops runtime_bc am tx) (imm_len tops)
        fuel unit.cu_context func [] H qt actual) ==>
      !fuel. ptr_safe_run (deploy_dead tops runtime_bc am tx) (imm_len tops)
        fuel unit.cu_context func [] FEMPTY entry_taint
        (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)) /\
    (!j. j < LENGTH fargs ==>
      ?entry d B.
        lookup_scopes (FST (EL j fargs)) [scope] = SOME entry /\
        local_region ce [scope] actual (FST (EL j fargs)) d
          (type_memory_bytes ce0 (SND (EL j fargs))) /\
        FINITE B /\ B SUBSET range_bytes [(d,type_memory_bytes ce0 (SND (EL j fargs)))] /\
        DISJOINT B qt.t_mem /\ (!a. a IN B ==> a < actual.vs_alloca_next) /\
        (!mem. (!a. a IN B ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 actual.vs_memory) ==>
          val_in_memory entry.type entry.value d mem))
Proof
  strip_tac >>
  drule_all deploy_ptr_entry_normalized >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `fresh_vars_wrt _ initial` >> gvs[] >>
  drule_all deploy_ptr_entry_initial_resources >> strip_tac >>
  VALID (qpat_assum `deploy_ctor_code _ _ _ _ _` (strip_assume_tac o REWRITE_RULE [deploy_ctor_code_def])) >>
  drule_all deploy_ptr_entry_lock_identity >> strip_tac >> gvs[] >>
  drule_all deploy_ptr_entry_registration_code >> strip_tac >>
  drule_all deploy_ptr_entry_package_accepts_value >> disch_tac >>
  Q.SUBGOAL_THEN `is_payable \/ initial.vs_call_ctx.cc_callvalue = 0w` assume_tac
  >- (Cases_on `is_payable` >> simp[] >>
      gvs[Abbr `initial`, gas_variant_def, deploy_entry_state_def, entry_venom_state_def,
          deploy_state_rel_def, venom_state_component_equality, call_context_component_equality]) >>
  drule_all prefix_entry_prepare_actual >>
  disch_then (qspecl_then [`entry_taint`, `[]`, `FEMPTY`,
    `deploy_dead tops runtime_bc am tx`] strip_assume_tac) >>
  qpat_x_assum `is_payable \/ tx.value = 0` kall_tac >>
  qpat_x_assum `is_payable \/ initial.vs_call_ctx.cc_callvalue = 0w` kall_tac >>
  drule_all deploy_ctor_entry_data_section >> strip_tac >>
  `constructor_args_encode tops tx initial.vs_data_section` by simp[Abbr `initial`] >>
  drule_all deploy_ctor_common_source_witness >> strip_tac >>
  qspecl_then [`tops`, `NONE`, `"__init__"`] mp_tac classify_functions_ctor_lookup >>
  simp[] >> strip_tac >> gvs[] >>
  drule_all lower_vyper_deploy_unit_ctor_named_init >> strip_tac >>
  PairCases_on `cf` >> gvs[ctor_named_init_def] >>
  `is_payable = (cf0 = Payable) /\ ret = NoneT` by
    fs[set_constructor_package_target_def, package_constructor_def] >>
  gvs[] >>
  `t.vs_data_section = vs.vs_data_section` by fs[Abbr `initial`] >>
  drule (deploy_ctor_decoder_inputs |> INST_TYPE [``:'a`` |-> ``:expr``] |> SPEC_ALL |>
    Q.INST [`ce0` |-> `ce_pack with ce_imm_alloca := (if imm_len tops > 0 then SOME imm else NONE)`,
            `imm_opt` |-> `if imm_len tops > 0 then SOME imm else NONE`] |> GEN_ALL |> SRULE []) >>
  disch_then drule_all >> strip_tac >>
  `alloca_inv t /\ !site. alloca_frontier_inv_from (imm_len tops) unit.cu_context fn site t` by
    (irule deploy_ptr_entry_initial_resources >> simp[] >> goal_assum (drule_at Any)) >>
  `allocas_from (imm_len tops) t` by simp[ptrDisciplineTheory.allocas_from_def] >>
  `!aid. st1.cs_next_id <= aid ==> FLOOKUP t.vs_allocas aid = NONE` by simp[] >>
  Q.SUBGOAL_THEN `st1.cs_blocks = st2.cs_blocks \/
    !bb. lookup_block st2.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0` assume_tac >- metis_tac[] >>
  qpat_assum `pos_args = _` (fn th =>
    qpat_assum `compile_register_constructor_args _ _ _ _ _ = _`
      (assume_tac o REWRITE_RULE [th])) >>
  `mem_bytes_at 0 (LENGTH t.vs_data_section) t.vs_data_section = t.vs_data_section` by metis_tac[] >>
  `LENGTH t.vs_data_section < dimword (:256)` by metis_tac[] >>
  `t.vs_data_section = enc (Tuple (vyper_to_abi_types (type_env tops) (MAP SND args))) (ListV avs')` by fs[] >>
  qpat_assum `t.vs_data_section = enc _ _` (assume_tac o SRULE []) >>
  `!inst b sz n. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n` by simp[] >>
  drule (deploy_ptr_entry_register_prepared_origins |> INST_TYPE [``:'a`` |-> ``:word8``] |> SPEC_ALL |>
    Q.INST [`ce0` |-> `cenv0 with ce_imm_alloca := (if imm_len tops > 0 then SOME imm else NONE)`] |>
    GEN_ALL |> SRULE []) >>
  disch_then drule_all >>
  disch_then (qspec_then `tx` mp_tac) >>
  disch_then (qspec_then `qt` mp_tac) >>
  disch_then (qspec_then `runtime_bc` mp_tac) >>
  disch_then (qspec_then `am` mp_tac) >>
  disch_then (qspec_then `H`
    (qx_choose_then `end_state` (qx_choose_then `end_G`
      (qx_choose_then `end_taint` strip_assume_tac)))) >>
  `tx.function_name = "__init__"` by fs[deploy_state_rel_def] >>
  `lookup_function NONE tx.function_name Deploy tops =
    SOME (cf0,F,args,[],NoneT,body)` by simp[] >>
  drule_all deploy_ctor_source_start_fields >> strip_tac >>
  `end_state.vs_accounts = vs.vs_accounts /\ end_state.vs_transient = vs.vs_transient /\
   end_state.vs_logs = vs.vs_logs /\ end_state.vs_requests = vs.vs_requests /\
   end_state.vs_pending_deletions = vs.vs_pending_deletions` by
    (qpat_assum `abi_encoder_registered_effect _ _ t end_state` mp_tac >>
     simp_tac bool_ss [abi_encoder_registered_effect_def] >> strip_tac >>
     fs[Abbr `initial`]) >>
  `!a. a < imm_len tops ==> read_byte a end_state.vs_memory = 0w` by
    (rpt strip_tac >>
     `read_byte a end_state.vs_memory = read_byte a t.vs_memory` by metis_tac[] >>
     simp[Abbr `initial`] >>
     qpat_assum `gas_variant _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     rewrite_tac[gas_variant_def] >> strip_tac >>
     pop_assum (mp_tac o Q.AP_TERM `\s. s.vs_memory`) >>
     simp[deploy_entry_state_def, entry_venom_state_def, init_venom_state_def,
       codegenRelTheory.read_byte_def]) >>
  `!id b sz. local_region (cenv1 with ce_ctor_exit_label := SOME exit)
       [scope'] end_state id b sz ==> imm_len tops <= b` by
    (rpt gen_tac >> strip_tac >> irule prefix_entry_bound_argument_regions >>
     goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
     qexistsl [`type_env tops`,`args`,`tx.args`] >>
     asm_rewrite_tac[] >> rpt strip_tac >>
     qpat_assum `!j. j < LENGTH args ==> _` drule >> strip_tac >>
     qexistsl [`d`,`type_memory_bytes
       (cenv0 with ce_imm_alloca := (if imm_len tops > 0 then SOME imm else NONE))
       (SND (EL j args))`] >>
     fs[local_region_def]) >>
  qexistsl [`end_state`, `end_G`, `end_taint`, `scope'`, `args`,
    `cenv0 with ce_imm_alloca := (if imm_len tops > 0 then SOME imm else NONE)`] >>
  `local_ptrs_rel fn (cenv1 with ce_ctor_exit_label := SOME exit) [scope'] end_state` by
    (qpat_x_assum `local_ptrs_rel fn cenv1 _ end_state` mp_tac >>
     simp[local_ptrs_rel_def, local_region_def]) >>
  asm_simp_tac bool_ss [] >>
  (conj_tac >- (rpt gen_tac >> strip_tac >>
    qpat_assum `!id b sz. local_region _ _ _ _ _ _ ==> _` irule >>
    goal_assum (drule_at Any))) >>
  (conj_tac >- (rpt gen_tac >> strip_tac >>
    qpat_assum `!inst b sz n. _` irule >> goal_assum (drule_at Any) >> simp[])) >>
  simp[Abbr `initial`] >>
  conj_tac >- metis_tac[abiDecoderLoopTheory.abi_decode_sim_trans] >>
  `!x. imm = Var x ==> not_fresh_at st1 x` by
    (rpt strip_tac >> gvs[eval_operand_def] >>
     fs[fresh_vars_wrt_def, not_fresh_at_def, lookup_var_def, FLOOKUP_DEF] >>
     metis_tac[arithmeticTheory.GREATER_EQ]) >>
  `eval_operand imm end_state = SOME 0w /\ op_taint end_taint imm = {} /\ op_prov end_G imm = NONE` by
    (qpat_assum `end_state.vs_labels = t.vs_labels` mp_tac >>
     qpat_assum `!x. imm = Var x ==> not_fresh_at st1 x` mp_tac >>
     qpat_assum `!x. not_fresh_at st1 x ==> FLOOKUP end_G x = _ /\ _` mp_tac >>
     qpat_assum `!x w. not_fresh_at st1 x /\ _ ==> _` mp_tac >>
     qpat_assum `eval_operand imm t = SOME 0w` mp_tac >>
     qpat_assum `op_taint qt imm = {}` mp_tac >>
     qpat_assum `op_prov H imm = NONE` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `imm` >>
     simp[eval_operand_def, ptrDisciplineTheory.op_taint_def, ptrDisciplineTheory.op_prov_def] >>
     metis_tac[]) >>
  simp[] >>
  reverse conj_tac
  >- (qpat_x_assum `!j. j < LENGTH args ==> _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> disch_tac >>
      qx_gen_tac `j` >> strip_tac >> first_x_assum drule >>
      disch_then (qx_choose_then `entry` (qx_choose_then `d`
        (qx_choose_then `B` strip_assume_tac))) >>
      qexistsl [`entry`,`d`,`B`] >>
      gvs[local_region_def] >> metis_tac[]) >>
  simp[deploy_ptr_inv_def] >>
  conj_tac
  >- (qpat_assum `!j. j < imm_len tops /\ j IN end_taint.t_mem ==> _` mp_tac >>
      qpat_assum `qt.t_mem = {}` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> simp[] >> metis_tac[]) >>
  rpt strip_tac >> qpat_x_assum `imm = Var _` (fn th => rewrite_tac[GSYM th]) >>
  first_assum ACCEPT_TAC
QED

Theorem deploy_ptr_entry_prefix_related:
  deploy_phases policy tops (deploy_bc,runtime_bc) (rp,unit,dout,prog,cplan) /\
  deploy_source_ok tops am tx /\ deploy_state_rel tops deploy_bc am tx es /\
  gas_variant vs (deploy_entry_state prog cplan tops es) /\
  deploy_ctor_code tops rp runtime_bc unit
    (body,ce,nr,key,ut,imm,exit,sa,sb,sj,se,sp,sf,func) /\
  deploy_ctor_start tops am tx (mut,nr,body,am_c,es0) /\
  lookup_function "__deploy" unit.cu_context.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl ==>
  ?actual H qt.
    stmt_state_rel unit.cu_context func ce (deploy_evaluation_context tops am tx)
      (es0 with outcomes := SOME vs.vs_outcomes) actual /\
    ~actual.vs_halted /\ actual.vs_current_bb = sa.cs_current_bb /\
    actual.vs_inst_idx = LENGTH sa.cs_current_insts /\
    actual.vs_gas_readings = vs.vs_gas_readings /\
    deploy_ptr_inv tops runtime_bc am tx imm H qt actual /\
    ((!fuel. ptr_safe_run (deploy_dead tops runtime_bc am tx) (imm_len tops)
        fuel unit.cu_context func [] H qt actual) ==>
      !fuel. ptr_safe_run (deploy_dead tops runtime_bc am tx) (imm_len tops)
        fuel unit.cu_context func [] FEMPTY entry_taint
        (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>))
Proof
  strip_tac >> drule_all deploy_ptr_entry_prefix_source >> strip_tac >> gvs[] >>
  drule deploy_ptr_ctor_environment >> strip_tac >>
  `deploy_typing_ok tops am tx /\ supported_program tops` by fs[deploy_source_ok_def] >>
  `immutables_rel ce (deploy_evaluation_context tops am tx).txn.target
     ce.ce_module ce.ce_is_ctor (es0 with outcomes := SOME vs.vs_outcomes) actual` by
    (simp[] >> irule prefix_entry_zero_memory_immutables >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >>
     simp[deploy_evaluation_context_def, initial_evaluation_context_def] >>
     rpt strip_tac >>
     qpat_x_assum `!a. a < imm_len tops ==> read_byte _ _ = _` drule >>
     disch_tac >> irule listTheory.LIST_EQ >>
     simp[valueEncodingProofsTheory.LENGTH_mem_bytes_at_proof] >>
     rpt strip_tac >>
     rewrite_tac[GSYM listTheory.EL] >>
     simp[valueEncodingProofsTheory.EL_mem_bytes_at] >> fs[read_byte_def]) >>
  `state_rel func ce (deploy_evaluation_context tops am tx)
     (es0 with outcomes := SOME vs.vs_outcomes) actual` by
    (`local_ptrs_rel func ce es0.scopes actual` by simp[] >>
     drule_all deploy_ptr_entry_actual_state_rel >> simp[]) >>

  `!p. p < imm_len tops ==>
     mem_bytes_at p 1 actual.vs_memory = mem_bytes_at p 1 []` by
    (rpt strip_tac >>
     qpat_x_assum `!a. a < imm_len tops ==> read_byte _ _ = _` drule >>
     disch_tac >> irule listTheory.LIST_EQ >>
     simp[valueEncodingProofsTheory.LENGTH_mem_bytes_at_proof] >>
     rpt strip_tac >>
     rewrite_tac[GSYM listTheory.EL] >>
     simp[valueEncodingProofsTheory.EL_mem_bytes_at] >> fs[read_byte_def]) >>
  `immutable_alloca_sep func ce (deploy_evaluation_context tops am tx)
     es0 actual` by
    (drule (cj 2 deploy_ctor_entry_immutable_resources) >>
     disch_then irule >> fs[ptrDisciplineTheory.allocas_from_def] >> metis_tac[]) >>
  `immutable_alloca_sep func ce (deploy_evaluation_context tops am tx)
     (es0 with outcomes := SOME vs.vs_outcomes) actual` by
    (qpat_x_assum `immutable_alloca_sep func ce _ es0 actual` mp_tac >>
     simp[immutable_alloca_sep_def] >> tautLib.TAUT_TAC) >>
  `immutable_base_zero ce actual` by
    (drule_all prefix_entry_immutable_base >> simp[]) >>
  `alloca_room unit.cu_context func actual` by
    (irule deploy_ctor_frontier_alloca_room >>
     qexistsl [`imm_len tops`,`mk_inst 0 STOP [] []`] >> simp[] >>
     drule deploy_imm_budget_ok >> simp[]) >>
  `fmp_room unit.cu_context func actual` by
    (drule_all deploy_ctor_entry_fmp_room >> simp[]) >>
  qexistsl [`actual`,`H`,`qt`] >> simp[stmt_state_rel_def] >> first_assum ACCEPT_TAC
QED

Theorem deploy_ctor_entry_run_ptr:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs
   body cenv nr nkey ut imm exit_lbl sa sb sj st_exit st_epilogue st_final func
   mut am_c es0 fn lbl.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs (deploy_entry_state prog cplan tops es) /\
    (!marks. ~deploy_source_exempt tops
               (load_contract NONE (gas_explicit marks vs.vs_gas_readings) am tx
                  [(NONE, tops)] [])) /\
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (body, cenv, nr, nkey, ut, imm, exit_lbl, sa, sb, sj, st_exit,
       st_epilogue, st_final, func) /\
    deploy_ctor_start tops am tx (mut, nr, body, am_c, es0) /\
    lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl
    ==>
    ?s0 G0 tn0.
      stmt_state_rel dunit.cu_context func cenv
        (deploy_evaluation_context tops am tx)
        (es0 with outcomes := SOME vs.vs_outcomes) s0 /\
      ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
      s0.vs_gas_readings = vs.vs_gas_readings /\
      deploy_ptr_inv tops runtime_bc am tx imm G0 tn0 s0 /\
      ((!fuel. ptr_safe_run (deploy_dead tops runtime_bc am tx) (imm_len tops)
                 fuel dunit.cu_context func [] G0 tn0 s0) ==>
       !fuel. ptr_safe_blocks (deploy_dead tops runtime_bc am tx) (imm_len tops)
                fuel dunit.cu_context fn [] FEMPTY entry_taint
                (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                            vs_inst_idx := 0 |>))
Proof
  rpt strip_tac >>
  drule_all deploy_ptr_entry_prefix_related >> strip_tac >>
  drule_all deploy_ptr_entry_normalized >> simp_tac bool_ss [LET_THM] >> strip_tac >> gvs[] >>
  qexistsl [`actual`,`H`,`qt`] >> simp[] >> strip_tac >>
  qpat_x_assum `(!fuel. ptr_safe_run _ _ _ _ _ _ H qt actual) ==> _` drule >>
  disch_tac >> Cases_on `fuel` >> simp[Once ptr_safe_blocks_def] >>
  Cases_on `lookup_block "__deploy" fn.fn_blocks` >> simp[] >>
  rename1 `lookup_block "__deploy" fn.fn_blocks = SOME bb` >>
  `phi_prefix_length bb.bb_instructions = 0` by metis_tac[] >>
  simp[eval_phis_no_phi] >>
  qpat_x_assum `!fuel. ptr_safe_run _ _ _ _ _ _ FEMPTY entry_taint _`
    (qspec_then `n` mp_tac) >>
  simp[ptr_safe_run_def]
QED
