(* Counted operand/suffix composition for len. *)
Theory bodyMemBiLenCompose
Ancestors
  bodyMemBiLenPath exprSimLen exprSimSource exprSimProps exprSimHypsDefs
  exprSimDefs loweringPosts list fragExec exprSimHyps exprSimWordBuiltins
  exprBopLowering exprLowering exprLoweringProps builtinSimple emitHelper
  compileEnv accountsRelProps valueEncoding venomExecSemantics venomInst
  venomState vyperAST vyperInterpreter vyperState vyperContext vyperTypeSystem
  vyperTypeBuiltins vyperValue vyperTyping vyperStorage builtinProps
  vyperTypeInvariants context freshWrites loweringSlice emitHelperProps
  exprSimUnwrap exprSimCopy vyperTypeExprResult vyperTypeExprSoundness
  vyperExprNoControl gasContext gasOutcome gasSummary gasSummaryCompose
  gasExemptCert fragGasMode fragGasPath exprSimMemDefs exprSimMemUnwrap
  fragGasPathMem gasStorage vyperStorageTrace vyperStorageFootprint

Theorem len_vv_post_transport[local]:
  !(H0:(bool # bytes32 # type_value) list # num list)
   (H:(bool # bytes32 # type_value) list # num list)
   ctx func cenv cx e es sa sb s0 es' tv vt op u s.
  vv_post H0 ctx func cenv cx e es sa sb s0 es' tv (StackValue vt op) u /\
  stmt_state_rel H ctx func cenv cx es' s /\ storage_well_formed_on cx es' (FST H) /\
  u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
  u.vs_requests = s.vs_requests /\ u.vs_call_ctx = s.vs_call_ctx ==>
  vv_post H ctx func cenv cx e es sa sb s0 es' tv (StackValue vt op) u
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `vv_post H0 _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vv_post_def]) >>
  `stmt_state_rel H ctx func cenv cx es' u` by
    metis_tac[INST_TYPE [alpha |-> ``:256``]
      exprLoweringPropsTheory.stmt_state_rel_fields_transport] >>
  rewrite_tac[vv_post_def] >> rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  strip_tac >> gvs[vv_storage_live_def]
QED

Theorem compile_len_singleton_sim_mem:
  !ctx func cenv cx env ty e es.
    expr_body_pre cenv cx env (Builtin (BaseT (UintT 256)) Len [e]) es /\
    expr_vv_sim_mem ctx func cenv cx ty e es ==>
    expr_vv_sim_mem ctx func cenv cx ty (Builtin (BaseT (UintT 256)) Len [e]) es
Proof
  rpt gen_tac >> strip_tac >>
  `is_sized_type (expr_type e)` by (drule len_pre_args >> simp[]) >>
  `expr_body_pre cenv cx env e es` by
    (drule expr_body_pre_builtin_arg >>
     disch_then (qspecl_then [`e`, `es`] mp_tac) >> fs[expr_body_pre_def]) >>
  drule post_type_evaluates >> disch_then (qx_choose_then `ptv` assume_tac) >>
  `type_widens_to env.type_defs (post_value_type cenv e) (expr_type e)` by
    (irule post_value_type_widens >>
     fs[expr_body_pre_def] >> metis_tac[]) >>
  simp[expr_vv_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  gvs[compile_expr_len] >> pairarg_tac >> gvs[] >>
  rename1 `compile_expr cenv ty e sa = (evv, sm)` >>
  Cases_on `compile_builtin_len cenv.ce_is_ctor cenv.ce_imm_alloca (vv_operand evv)
    (case vv_location evv of SOME l => l | NONE => LocMemory) sm` >>
  gvs[as_stack_val_def] >>
  drule_all len_load_extends >> strip_tac >>
  drule compile_expr_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  rename1 `compile_builtin_len _ _ _ _ _ = (lop, lsb)` >>
  `env.type_defs = get_tenv cx` by
    fs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
       env_context_consistent_def] >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[len_operand_admissible] >>
  qpat_x_assum `expr_vv_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_mem_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`evv`,`s0`] mp_tac) >>
  (impl_tac >- (asm_simp_tac (srw_ss()) [] >> metis_tac[])) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      rewrite_tac[len_source] >>
      irule gasStorageTheory.gas_bad_storage_at_bind_left >>
      simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
           vyperStorageTraceTheory.storage_trace_frame_array_length,
           vyperStorageTraceTheory.storage_trace_frame_return])
  >- (qexists_tac `marks` >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [gas_summary_at_def]) >>
      strip_tac
      >- (gvs[] >> rename1 `gas_marked_exec _ _ _ _ _ _ fe _` >>
          reverse (Cases_on `storage_trace_domain cx st0 fe.storage_trace`)
          >- (disj1_tac >> rewrite_tac[len_source] >>
              irule gasStorageTheory.gas_bad_storage_at_bind_left >>
              simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
                   vyperStorageTraceTheory.storage_trace_frame_array_length,
                   vyperStorageTraceTheory.storage_trace_frame_return] >>
              metis_tac[gasStorageTheory.gas_bad_storage_at_counted_prefix]) >>
          `?H0. valid_horizon cx st0 H0 fe.storage_trace` by
            metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
          `?tv. res = INL tv` by
            (qpat_x_assum `!H. valid_horizon _ _ H fe.storage_trace ==> _`
               (qspec_then `H0` mp_tac) >> impl_tac >- first_assum ACCEPT_TAC >>
             simp[] >> metis_tac[]) >>
          qpat_x_assum `res = _` SUBST_ALL_TAC >>
          qpat_x_assum `!H. valid_horizon _ _ H fe.storage_trace ==> _`
            (assume_tac o SIMP_RULE (srw_ss()) []) >>
          `!H. valid_horizon cx st0 H fe.storage_trace ==>
             vv_post H ctx func cenv cx e es sa sm s0 (fe with gas_obs := []) tv evv t /\
             vv_store_bound cx (expr_type e) (lowered_value_type cenv e)
               (fe with gas_obs := []) tv evv t /\
             t.vs_current_bb = sm.cs_current_bb /\
             t.vs_inst_idx = LENGTH sm.cs_current_insts /\
             alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next` by
            (rpt strip_tac >> first_x_assum drule >> simp[]) >>
          first_assum (qspec_then `H0` mp_tac) >>
          impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
          disj2_tac >> disj1_tac >>
          `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
             (INL tv, fe with gas_obs := [])` by
            (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
               (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
             strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
          `~t.vs_halted` by
            metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
          mp_tac (Q.SPECL [`cenv`,`cx`,`env`,`e`,
                    `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
                    `tv`,`fe with gas_obs := []`] expr_body_pre_runtime_typed) >>
          simp[] >> strip_tac >>
          mp_tac (Q.SPECL [`H0`,`env`,`ctx`,`func`,`cenv`,`cx`,`e`,`es`,`sa`,`sm`,`lsb`,`s0`,
                    `fe with gas_obs := []`,`tv`,`evv`,`lop`,`tvt`,`t`,`ptv`] len_vv_path_mem) >>
          (impl_tac >- (asm_simp_tac (srw_ss()) [] >> metis_tac[])) >> strip_tac >>
          `!tail. result_array_length cx tv (fe with gas_obs := tail) =
                  (INL n, fe with gas_obs := tail)` by
            (gen_tac >> drule len_ral_gas_obs >>
             disch_then (qspec_then `tail` mp_tac) >> simp[]) >>
          simp[gas_summary_at_def] >>
          qexistsl_tac [`INL (Value (IntV (&n)))`, `fe`, `OK t'`] >>
          conj_tac
          >- (rewrite_tac[len_source] >>
              irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
                       |> REWRITE_RULE [APPEND_NIL]) >>
              qexistsl_tac [`fe`,`t`,`tv`] >> simp[] >>
              simp[gas_marked_exec_def, gas_marked_path_def, bind_def, return_def,
                   gas_explicit_def]) >>
          disj1_tac >> qexists_tac `t'` >> simp[] >>
          qx_gen_tac `H2` >> strip_tac >>
          first_x_assum (qspec_then `H2` mp_tac) >>
          impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
          rpt conj_tac
          >- (irule len_vv_post_transport >>
              qexistsl_tac [`H0`, `t`] >>
              fs[vv_post_def])
          >- simp[vv_store_bound_stack_word, expr_type_def, is_word_type_def]
          >> simp[expr_type_def] >> gvs[]) >>
      rename1 `gas_marked_exec _ _ _ _ _ _ fe _` >>
      reverse (Cases_on `storage_trace_domain cx st0 fe.storage_trace`)
      >- (disj1_tac >> rewrite_tac[len_source] >>
          irule gasStorageTheory.gas_bad_storage_at_bind_left >>
          simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
               vyperStorageTraceTheory.storage_trace_frame_array_length,
               vyperStorageTraceTheory.storage_trace_frame_return] >>
          metis_tac[gasStorageTheory.gas_bad_storage_at_counted_prefix]) >>
      disj2_tac >> disj1_tac >>
      Cases_on `res`
      >- (gvs[] >>
          metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def]) >>
      simp[gas_summary_at_def] >>
      rename1 `gas_marked_exec _ _ _ _ marks (INR exn) fe fr` >>
      qexistsl_tac [`INR exn`,`fe`,`fr`] >>
      simp[] >> conj_tac
      >- (rewrite_tac[len_source] >> irule gas_marked_exec_bind_exception >> simp[]) >>
      gvs[] >> disj2_tac >> first_assum ACCEPT_TAC) >>
  qexists_tac `marks` >> disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`finish'`] >>
  irule len_exempt_cert >> simp[]
QED

Theorem compile_len_singleton_forced_sim_mem:
  !ctx func cenv cx env ty e es.
    expr_body_pre cenv cx env (Builtin (BaseT (UintT 256)) Len [e]) es /\
    expr_vv_sim_mem ctx func cenv cx ty e es ==>
    expr_sim_mem ctx func cenv cx ty (Builtin (BaseT (UintT 256)) Len [e]) es
Proof
  rpt strip_tac >> irule expr_sim_mem_of_vv_sim_mem >>
  simp[expr_type_def, is_word_type_def, evaluate_type_def] >>
  irule compile_len_singleton_sim_mem >> metis_tac[]
QED
