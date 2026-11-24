(* Len evaluates its child as a VV. Only the successful child edge starts
   the selected length-load suffix, with the same state and ghosts. *)
Theory entryCreateBuiltinLenCompose
Ancestors
  entryCreateScopedBind entryCreateFocusSpec entryCreateWordArgsGeometry
  entryCreateIntervalLayout createSizeOperandCode createSizeCutCode
  exprSimLen exprSimSource exprSimHyps
  bodyFullGhostFrame exprSimFullBundleProps gasShadowCompileStmtHelpers
  fragGasSeqPtr fragGasOriginPtr gasExemptCert builtinSimple
  vyperTypeInvariants vyperStorageTrace vyperStorageFootprint
  context compileEnv pair s1PrefixDefs exprSimDefs vyperContext exprSimHypsDefs
  exprLowering exprBopLowering gasShadowState exprSimUnwrap fragExec vyperState
  vyperInterpreter vyperAST loweringPosts exprSimMemDefs bodyPtrDefs
  entryCreateCompletedCut exprLoweringProps gasSummary

Theorem len_cut_code[local]:
  create_cut_code {} m (SND (compile_builtin_len ctor imm p loc m))
Proof
  Cases_on `loc` >> simp[compile_builtin_len_def, compile_ptr_load_def,
                        compile_imm_load_word_def] >>
  rpt CASE_TAC >> simp[create_cut_code_emit_op, create_cut_targets_def] >>
  irule create_cut_code_bind >> simp[create_cut_code_emit_op, create_cut_targets_def]
QED

Theorem len_exception_post[local]:
  (\H (res : 'a + exception) ee gt r. ?exc. res = INR exc /\
    create_operand_exit_post ctx cx H (INR exc : value + exception) ee gt r) =
  create_operand_exit_post ctx cx
Proof
  simp[FUN_EQ_THM] >> rpt gen_tac >>
  Cases_on `res` >- simp[create_operand_exit_post_def] >>
  rename1 `INR ex` >> Cases_on `ex` >> Cases_on `r` >>
  simp[create_operand_exit_post_def, halt_exit_def, expr_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >> simp[expr_exit_def]
QED

Theorem len_child_gas_obs[local]:
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 a m source start Q R ==>
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 a m source start
    (\H res ee G tn t. Q H res ee G tn t /\ ee.gas_obs = []) R
Proof
  PairCases_on `start` >> simp[scoped_operand_outcome_def]
QED

Theorem len_value_post[local]:
  expr_sim_full_post (DF,lo,d,ctx,func) cenv cx (Builtin (BaseT (UintT 256)) Len [e])
    (es,sa,sb,s0,op,G0,tn0) H (INL (IntV (&n)) : value + exception) ee G tn z <=>
  expr_post H ctx func cenv cx (Builtin (BaseT (UintT 256)) Len [e])
    es sa sb s0 ee (IntV (&n)) op z /\
  expr_store_bound cx (BaseT (UintT 256)) (IntV (&n)) op z /\
  z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
  s0.vs_alloca_next <= z.vs_alloca_next /\
  ghost_inv_at (DF H) lo d cenv cx ee G tn z /\
  ptr_val_ok cx (BaseT (UintT 256)) (IntV (&n)) op G tn z /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn
Proof
  simp[expr_sim_full_post_def, expr_sim_full_endpoint_def,
       vyperASTTheory.expr_type_def, compileEnvTheory.is_word_type_def] >>
  metis_tac[]
QED

Theorem len_value_scoped_from_suffix:
  (!DF lo d explicit ctx func PG cenv cx env e es st0 sa sm sb s0
     G0 tn0 ee tv vv t G tn op pvt tvt.
    expr_body_pre cenv cx env (Builtin (BaseT (UintT 256)) Len [e]) es /\
    expr_body_pre cenv cx env e es /\ is_sized_type (expr_type e) /\
    compile_builtin_len cenv.ce_is_ctor cenv.ce_imm_alloca (vv_operand vv)
      (case vv_location vv of NONE => LocMemory | SOME l => l) sm = (op,sb) /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    type_widens_to (get_tenv cx) (post_value_type cenv e) (expr_type e) /\
    evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME pvt /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
    env.type_defs = get_tenv cx /\
    eval_result_typed (env,cx,ee) tv (Type (expr_type e)) /\
    (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type tvt v) /\
    storage_trace_domain cx st0 ee.storage_trace /\ ~t.vs_halted /\
    t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      vv_post H ctx func cenv cx e es sa sm s0 ee tv vv t /\
      vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv t /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn t /\
      (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
       ?val. read_result cx tv ee = (INL val,ee) /\
         !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
           eval_operand (vv_operand vv) t = SOME w ==>
           w2n w + type_memory_size rt <= lo /\
           !mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
             val_in_memory rt val (w2n w) mem) /\
      (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type cenv e) ==>
         ptr_buf_ok cenv e op G t) /\
      (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
         ptr_buf_ok cenv e p.ptr_operand G t) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn) ==>
    ?n z G2 tn2.
      result_array_length cx tv ee = (INL n,ee) /\
      create_operand_full_scope sm sb explicit ctx func t [] (OK z) /\
      !H. valid_horizon cx st0 H ee.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
          (t,G,tn) [] (OK z,G2,tn2) /\
        expr_post H ctx func cenv cx (Builtin (BaseT (UintT 256)) Len [e])
          es sa sb s0 ee (IntV (&n)) op z /\
        expr_store_bound cx (BaseT (UintT 256)) (IntV (&n)) op z /\
        z.vs_current_bb = sb.cs_current_bb /\
        z.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
        s0.vs_alloca_next <= z.vs_alloca_next /\
        ghost_inv_at (DF H) lo d cenv cx ee G2 tn2 z /\
        ptr_val_ok cx (BaseT (UintT 256)) (IntV (&n)) op G2 tn2 z /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2) ==>
  !DF lo d ctx shctx PG tops func shfunc cenv env cx ty ann args es
     st0 sa sb sha shb op s0 G0 tn0.
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin ann Len args) es /\
    (builtin_args_length_ok Len (LENGTH args) ==>
     expr_vv_sim_scoped (DF,lo,d,ctx,shctx,PG,func,shfunc) cenv cx ty (HD args) es) /\
    create_layout sa sb /\
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
      cenv cx ty (Builtin ann Len args) es (st0,sa,sb,sha,shb,op,s0,G0,tn0) ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
      (cx_tops cx) cx st0 sa sb
      (bind (eval_expr cx (Builtin ann Len args)) (read_result cx))
      (es,s0,G0,tn0)
      (expr_sim_full_post (DF,lo,d,ctx,func) cenv cx (Builtin ann Len args)
        (es,sa,sb,s0,op,G0,tn0))
      (create_operand_exit_post ctx cx)
Proof
  disch_tac >> rpt gen_tac >> strip_tac >>
  drule len_pre_args >> strip_tac >> gvs[builtin_args_length_ok_def] >>
  `expr_body_pre cenv cx env e es` by
    (drule expr_body_pre_builtin_arg >> disch_then irule >> gvs[expr_body_pre_def]) >>
  qpat_x_assum `expr_sim_full_pre _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[expr_sim_full_pre_def]) >>
  gvs[lower_value_def, compile_expr_len, comp_bind_def,
      gasShadowTheory.gas_shadow_expr_def, gasShadowTheory.gas_shadow_builtin_def] >>
  rpt (pairarg_tac >> gvs[as_stack_val_pair, unwrap_value_def, comp_return_def]) >>
  rename1 `compile_expr cenv ty e sa = (evv,sm)` >>
  rename1 `compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) sha = (shvv,shm)` >>
  `gas_shadow_compiles (compile_expr cenv ty e)
      (compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e))` by
    irule gas_shadow_stmt_compile_expr_env >>
  qpat_x_assum `gas_shadow_compiles _ _`
    (qspecl_then [`sa`,`sha`] mp_tac o REWRITE_RULE[gas_shadow_compiles_def]) >>
  simp[] >> strip_tac >> gvs[] >>
  `create_cut_code {} sa sm /\ create_cut_code {} sm sb` by
    metis_tac[cj 1 create_operand_cut_code, len_cut_code, SND] >>
  `cs_extends sa sm /\ cs_extends sm sb /\
   sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id <= sb.cs_next_id` by
    fs[create_cut_code_def] >>
  `cs_extends sha shm /\ cs_extends shm shb` by
    metis_tac[compile_expr_extends, len_load_extends] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func /\ fn_has_code sha shm shfunc` by
    metis_tac[fn_has_code_split] >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by metis_tac[len_operand_admissible] >>
  `create_operand_at sa s0` by simp[create_operand_at_def] >>
  `scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
     (cx_tops cx) cx st0 sa sm (eval_expr cx e) (es,s0,G0,tn0)
     (\H res ee G tn t. create_operand_vv_post (DF,lo,d,ctx,func) cenv cx e
          (es,sa,sm,s0,evv,G0,tn0) H res ee G tn t /\
       t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts)
     (create_operand_exit_post ctx cx)` by
    (qpat_assum `expr_vv_sim_scoped _ _ _ _ _ _`
       (qspecl_then [`st0`,`sa`,`sm`,`sha`,`shm`,`evv`,`s0`,`G0`,`tn0`] mp_tac o
        REWRITE_RULE[expr_vv_sim_scoped_def]) >>
     (impl_tac >- (simp[expr_vv_sim_full_pre_def] >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  `bind (eval_expr cx (Builtin (BaseT (UintT 256)) Len [e])) (read_result cx) =
   bind (eval_expr cx e) (\tv. bind (result_array_length cx tv) (\n. return (IntV (&n))))` by
    simp[len_source, bind_assoc, read_result_def, bind_return] >>
  pop_assum SUBST1_TAC >>
  drule_all create_word_args_scope_embeddings >>
  disch_then (qspec_then `gas_explicit_sites ctx shctx` strip_assume_tac) >>
  suspend "bind"
QED

Resume len_value_scoped_from_suffix[bind]:
  irule scoped_operand_bind_all_mixed >> conj_tac
  >- simp[evaluate_storage_trace_frame, storage_trace_frame_bind_all,
          storage_trace_frame_array_length, storage_trace_frame_return,
          cj 5 evaluate_storage_trace_frame] >>
  rpt conj_tac
  >~ [`storage_trace_frame (eval_expr _ _)`] >- simp[cj 5 evaluate_storage_trace_frame]
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`] >-
    (rpt strip_tac >> pure_rewrite_tac[ignore_bind_def] >>
     pure_once_rewrite_tac[bind_assoc] >> irule gas_exempt_cert_bind_result >>
     qexistsl_tac [`mid`,`t`,`v`] >> fs[ignore_bind_def])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`] >-
    (rpt strip_tac >> pure_rewrite_tac[ignore_bind_def] >>
     pure_once_rewrite_tac[bind_assoc] >> irule gas_exempt_cert_error_result >>
     simp[ignore_bind_def]) >>
  qmatch_asmsub_abbrev_tac `scoped_operand_outcome _ _ _ _ _ sm _ _ Qchild _` >>
  drule len_child_gas_obs >> strip_tac >>
  qexistsl_tac [`\H res ee G tn t. Qchild H res ee G tn t /\ ee.gas_obs = []`,`sm`] >>
  pure_rewrite_tac[len_exception_post] >> BETA_TAC >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC) >>
  suspend "continuation"
QED

Resume len_value_scoped_from_suffix[continuation]:
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_x_assum `Abbrev (Qchild = _)` (SUBST_ALL_TAC o REWRITE_RULE[markerTheory.Abbrev_def]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then (strip_assume_tac o SIMP_RULE bool_ss [create_operand_vv_post_def])) >>
  `~t.vs_halted` by
    metis_tac[gas_origin_ptr_path_projections, gas_path_ptr_ok_not_halted] >>
  qpat_x_assum `res = INL tv` SUBST_ALL_TAC >>
  qexists_tac `tv` >> simp_tac bool_ss [] >>
  `env.type_defs = get_tenv cx` by
    fs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `type_widens_to (get_tenv cx) (post_value_type cenv e) (expr_type e)` by
    (`type_widens_to env.type_defs (post_value_type cenv e) (expr_type e)` suffices_by simp[] >>
     irule post_value_type_widens >> fs[expr_body_pre_def] >> metis_tac[]) >>
  qpat_assum `expr_body_pre cenv cx env e es`
    (strip_assume_tac o MATCH_MP post_type_evaluates) >>
  qpat_assum `!tail. eval_expr _ _ _ = _`
    (qspec_then `mid.gas_obs` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  drule_at (Pos last) expr_body_pre_runtime_typed >>
  disch_then (qspecl_then [`cenv`,`env`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (qpat_assum `compile_expr cenv ty e sa = _`
       (strip_assume_tac o MATCH_MP compile_expr_extends) >> first_assum ACCEPT_TAC) >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  qabbrev_tac `E = gas_explicit_sites ctx shctx` >>
  `?n z G2 tn2.
    result_array_length cx tv mid = (INL n,mid) /\
    create_operand_full_scope sm sb E ctx func t [] (OK z) /\
    !H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,E,ctx,func,PG) (t,G1,tn1) [] (OK z,G2,tn2) /\
      expr_sim_full_post (DF,lo,d,ctx,func) cenv cx (Builtin (BaseT (UintT 256)) Len [e])
        (es,sa,sb,s0,op,G0,tn0) H (INL (IntV (&n)) : value + exception) mid G2 tn2 z` by
    suspend "selected" >>
  rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`INL (IntV (&n))`,`mid`,`OK z`,`G2`,`tn2`] >>
  simp[gas_explicit_def] >> conj_tac
  >- (drule len_ral_gas_obs >> simp[bind_def, return_def]) >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >> simp[] >>
  qx_gen_tac `horizon` >> disch_tac >> disj1_tac >>
  qpat_x_assum `!H. _ ==> _ /\ expr_sim_full_post _ _ _ _ _ H _ _ _ _ _`
    (qspec_then `horizon` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  strip_tac >> first_assum ACCEPT_TAC
QED

Resume len_value_scoped_from_suffix[selected]:
  pure_rewrite_tac[len_value_post] >>
  qpat_assum `!DF lo d explicit. _` irule >>
  simp[create_operand_at_def] >> conj_tac
  >- (qexists_tac `evv` >> simp[] >> qx_gen_tac `h` >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
        (qspec_then `h` mp_tac) >>
      simp_tac bool_ss [create_operand_vv_post_def] >>
      (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
      gvs[arithmeticTheory.ADD_COMM]) >>
  qexists_tac `env` >> simp[]
QED

Finalise len_value_scoped_from_suffix
