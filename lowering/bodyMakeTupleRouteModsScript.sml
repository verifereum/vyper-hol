(* Linked tuple allocation, heterogeneous element loop, and result read. *)
Theory bodyMakeTupleRouteMods
Ancestors
  bodyMakeElementsContractMods bodyMakeBufferInitMods bodyMakeArrayCompletedMods
  bodyAggregateReadMods bodyAssignNameLinkedSetup bodyFullIfExpReach
  exprSimAggregateLayout exprSimAggregateSource exprOperandVar exprSimCopy
  exprBodyPreProps exprBodyPreTypingProps exprBodyPreCallSafetyProps
  gasOutcomeFullPostMods gasOutcomeFullZeroPrefixMods gasShadowCompileStmtHelpers
  gasShadowCompileContext vyperStorageTrace vyperTypeABI vyperTypeArgFits
  allocLimits supportedExprTraverse vyperTypeSystem vyperValue
  vyperTypeInvariants exprSimHypsDefs vyperAST compileEnv valueEncoding list words
  exprSimDefs gasOutcomeFull vyperContext vyperInterpreter vyperState
  vyperTypeCallGraph loweringPosts exprLowering context
  vyperTypeEvalCaseProofs exprSimSource gasContext
  exprLoweringProps fragExec gasShadow gasShadowState
  bodyFullPostsMods bodyFullPredsMods exprSimFullBundleProps
  venomExecSemantics loweringStateRelDefs bodyPtrDefs finite_map
  gasOutcomeFullMods gasStorage fragGasOriginPtr valueEncodingDefs stmtSimProps haltExitProj
  vyperStorageFootprint stateRelProj exprSimProps exprSimMemDefs exprSimUnwrapProps

val _ = Parse.hide "base";

Theorem tuple_route_type_mods[local]:
  expr_body_pre_mods mods ce cx env (Builtin ann (MakeArray NONE n) args) es ==>
  ?tys tvs. ann = TupleT tys /\ compatible_bound n (LENGTH args) /\
    LIST_REL (\t e. arg_type_fits (expr_type e) t) tys args /\
    OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
    evaluate_type (get_tenv cx) ann = SOME (TupleTV tvs) /\
    LIST_REL (\ty tv. type_memory_bytes ce ty = type_memory_size tv) tys tvs /\
    type_memory_bytes ce ann = type_memory_size_list tvs /\
    type_memory_size_list tvs < dimword (:256)
Proof
  strip_tac >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule expr_sim_inv_mods_env >>
  disch_then (strip_assume_tac o MATCH_MP (SPEC_ALL env_consistent_type_defs_get_tenv)) >>
  qpat_x_assum `well_typed_expr _ _` mp_tac >>
  simp[Once well_typed_expr_def, well_typed_builtin_app_def,
       well_formed_type_def, arg_types_fit_LIST_REL] >> strip_tac >> gvs[] >>
  `?tvs. OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs` by
    (qpat_assum `IS_SOME (evaluate_type _ _)` mp_tac >>
     Cases_on `OPT_MMAP (evaluate_type (get_tenv cx)) tys` >>
     pure_rewrite_tac [evaluate_type_def, evaluate_types_OPT_MMAP] >> simp[]) >>
  rename1 `OPT_MMAP _ tys = SOME tvs` >>
  `evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs)` by
    (qpat_assum `IS_SOME (evaluate_type _ _)` mp_tac >>
     pure_rewrite_tac [evaluate_type_def, evaluate_types_OPT_MMAP] >> simp[]) >>
  `LIST_REL (\ty tv. type_memory_bytes ce ty = type_memory_size tv) tys tvs` by
    (drule OPT_MMAP_LIST_REL >> match_mp_tac LIST_REL_mono >>
     BETA_TAC >> rpt strip_tac >> drule_all_then ACCEPT_TAC assign_name_memory_bytes_mods) >>
  `type_memory_bytes ce (TupleT tys) = type_memory_size_list tvs` by
    (drule_all_then assume_tac assign_name_memory_bytes_mods >> simp[type_memory_size_def]) >>
  `type_memory_size_list tvs < 2 ** 64` by
    (qpat_assum `expr_body_pre_mods _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac [expr_body_pre_mods_def, alloc_limits_expr_def, type_alloc_ok_def,
          expr_type_def, is_word_type_def] >> simp[] >> decide_tac) >>
  qexists_tac `tvs` >> simp[compatible_bound_def] >>
  conj_tac
  >- (fs[LIST_REL_EL_EQN, EL_MAP] >> metis_tac[]) >>
  fs[dimword_def] >> decide_tac
QED

Theorem tuple_route_children_mods[local]:
  expr_body_pre_mods mods ce cx env (Builtin ann (MakeArray NONE n) args) es /\
  MEM e args /\ expr_sim_inv_mods mods ce cx env mid ==>
  expr_body_pre_mods mods ce cx env e mid
Proof
  simp[expr_body_pre_mods_def, Once well_typed_expr_def, int_calls_expr_def,
       byte_widths_expr_def, alloc_limits_expr_def, supported_expr_exists_def,
       supported_exprs_exists_every, expr_has_evm_run_thm, EXISTS_MEM] >>
  strip_tac >>
  drule_all_then assume_tac well_typed_exprs_member >>
  drule_all_then assume_tac byte_widths_exprs_mem >>
  drule_all_then assume_tac alloc_limits_exprs_mem >>
  drule_all_then assume_tac call_evaluation_safe_exprs_mem >>
  drule_all_then assume_tac int_calls_exprs_every_mem >>
  simp[] >> metis_tac[]
QED

Theorem tuple_route_source[local]:
  compatible_bound n (LENGTH args) ==>
  !st. eval_expr cx (Builtin ann (MakeArray NONE n) args) st =
       ((case FST (eval_exprs cx args st) of
          INL vs => INL (Value (ArrayV (TupleV vs))) | INR exc => INR exc),
        SND (eval_exprs cx args st))
Proof
  strip_tac >> gen_tac >> Cases_on `eval_exprs cx args st` >>
  drule_all_then assume_tac aggregate_eval_make_tuple >> simp[]
QED

Theorem tuple_route_admissible_mods[local]:
  compatible_bound n (LENGTH args) /\
  gas_admissible (eval_expr cx (Builtin ann (MakeArray NONE n) args)) expr_vv_res_ok es ==>
  make_elements_admissible_mods cx args es
Proof
  strip_tac >> drule_then assume_tac tuple_route_source >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >>
  simp[make_elements_admissible_mods_def, gas_admissible_def] >>
  strip_tac >> qx_genl_tac [`gs`,`rr`,`ee`] >> strip_tac >>
  Cases_on `rr` >> simp[] >> first_x_assum (qspec_then `gs` mp_tac) >>
  simp[expr_vv_res_ok_def, expr_res_ok_def]
QED

Theorem tuple_route_compile[local]:
  type_memory_bytes ce (TupleT tys) = cap /\
  compile_expr ce ty (Builtin (TupleT tys) (MakeArray NONE n) args) sa = (vv,sb) /\
  fn_has_code sa sb func ==>
  ?ba sm. compile_alloc_buffer cap sa = (ba,sm) /\
    compile_make_tuple compile_expr ce args tys ba.buf_operand 0 sm = (ba.buf_operand,sb) /\
    vv = LocatedValue (TupleT tys) (mk_ptr ba.buf_operand LocMemory) /\
    ci_mono sa sm /\ ci_mono sm sb /\ fn_has_code sa sm func /\ fn_has_code sm sb func
Proof
  strip_tac >> drule_then strip_assume_tac compile_tuple_literal_inv >>
  gvs[tuple_literal_types_def, type_memory_bytes_def] >>
  drule_then assume_tac compiler_make_tuple_result >> gvs[] >>
  `ci_mono sa sm` by metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND] >>
  `ci_mono sm sb` by metis_tac[ci_mono_compile_make_tuple_cfn, compile_expr_ci_mono, pairTheory.SND] >>
  `cs_extends sa sm /\ cs_extends sm sb` by fs[ci_mono_def] >>
  drule_all_then strip_assume_tac fn_has_code_split >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem tuple_route_paired[local]:
  type_memory_bytes ce (TupleT tys) = cap /\
  compile_expr ce ty (Builtin (TupleT tys) (MakeArray NONE n) args) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T ce) ty
    (gas_shadow_expr (Builtin (TupleT tys) (MakeArray NONE n) args)) sha = (vv,shb) /\
  gas_shadow_state sa sha /\ gas_shadow_state sb shb /\
  fn_has_code sa sb func /\ fn_has_code sha shb shfn ==>
  ?ba sm shm. compile_alloc_buffer cap sa = (ba,sm) /\
    compile_alloc_buffer cap sha = (ba,shm) /\
    compile_make_tuple compile_expr ce args tys ba.buf_operand 0 sm = (ba.buf_operand,sb) /\
    compile_make_tuple compile_expr (gas_shadow_env T ce) (MAP gas_shadow_expr args) tys
      ba.buf_operand 0 shm = (ba.buf_operand,shb) /\
    vv = LocatedValue (TupleT tys) (mk_ptr ba.buf_operand LocMemory) /\
    ci_mono sa sm /\ ci_mono sm sb /\ fn_has_code sa sm func /\
    make_elements_code_mods func shfn sm sb shm shb
Proof
  strip_tac >> drule_all_then strip_assume_tac tuple_route_compile >>
  `type_memory_bytes (gas_shadow_env T ce) (TupleT tys) = cap` by simp[] >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _`
    (assume_tac o SIMP_RULE (srw_ss()) [gas_shadow_expr_def, gas_shadow_builtin_def]) >>
  drule_all_then strip_assume_tac tuple_route_compile >>
  `!sa sha. gas_shadow_state sa sha ==>
     FST (compile_alloc_buffer cap sa) = FST (compile_alloc_buffer cap sha) /\
     gas_shadow_state (SND (compile_alloc_buffer cap sa)) (SND (compile_alloc_buffer cap sha))` by
    (qspec_then `cap` mp_tac (GEN_ALL gas_shadow_compiles_alloc_buffer) >>
     rewrite_tac[gas_shadow_compiles_def]) >>
  first_x_assum (qspecl_then [`sa`,`sha`] mp_tac) >> simp[] >>
  strip_tac >> gvs[make_elements_code_mods_def]
QED

Theorem tuple_route_map[local]:
  compatible_bound n (LENGTH args) /\
  make_elements_run_mods (DF,lo,ctx,shadow_ctx,PG,func) ce cx st0
    (eval_exprs cx args) (es,s,G,tn) Q /\
  (!H vs ee G' tn' t gs.
     eval_exprs cx args (es with gas_obs := gs) = (INL vs,ee) /\
     ee.gas_obs = [] /\ valid_horizon cx st0 H ee.storage_trace /\
     Q H (INL vs) ee G' tn' t ==>
     P H (INL (Value (ArrayV (TupleV vs)))) ee G' tn' t) /\
  (!H rr ee G' tn' t. Q H rr ee G' tn' t ==> ISL rr) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    ce.ce_modules cx st0 (eval_expr cx (Builtin ann (MakeArray NONE n) args)) (es,s,G,tn) P
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
          (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  strip_tac >> drule_then assume_tac tuple_route_source >>
  `ignore_bind (eval_expr cx (Builtin ann (MakeArray NONE n) args)) (return ()) =
   ignore_bind (eval_exprs cx args) (return ())` by
    (simp[FUN_EQ_THM, ignore_bind_def, bind_def] >>
     gen_tac >> Cases_on `eval_exprs cx args x` >> Cases_on `q` >> simp[]) >>
  qpat_x_assum `make_elements_run_mods _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [make_elements_run_mods_def, gas_outcome_full_mods_def]) >>
  rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks`
  >- (disj1_tac >> conj_tac >- fs[gas_bad_storage_at_def] >>
      qexistsl [`H`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >> simp[])
  >- (disj2_tac >> disj1_tac >> Cases_on `res`
      >- (qexistsl [`INL (Value (ArrayV (TupleV x)))`,`ee`,`r`,`G'`,`tn'`] >> simp[] >>
          qx_gen_tac `H` >> strip_tac >> first_x_assum drule >> strip_tac >> simp[]
          >- (first_x_assum irule >> simp[] >>
              qexists_tac `gas_explicit marks s.vs_gas_readings` >>
              qpat_assum `!tail. eval_exprs _ _ (_ with gas_obs := _ ++ tail) = _`
                (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [APPEND_NIL])))
          >> gvs[expr_exit_def]) >>
      qexistsl [`INR y`,`ee`,`r`,`G'`,`tn'`] >> simp[] >>
      qx_gen_tac `H` >> strip_tac >> first_x_assum drule >> strip_tac >> simp[]
      >- (first_x_assum drule >> simp[]) >>
      disj2_tac >>
      qpat_x_assum `(\h rr e g r. _) H (INR y) _ _ _` mp_tac >> BETA_TAC >>
      ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:eval_result``] expr_exit_INR_type,
                        INST_TYPE [beta |-> ``:eval_result``] halt_exit_INR_type] >>
      fs[createSizeExitTheory.create_size_exit_ok_inr]) >>
  disj2_tac >> disj2_tac >> qexistsl [`err`,`ee`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >>
  simp[] >> qexists_tac `H` >> simp[]
QED

val tuple_init_contract = concl (GEN_ALL make_buffer_init_mods);
val tuple_complete_contract =
  concl (GEN_ALL (INST_TYPE [alpha |-> ``:256``] make_array_completed_mods));

Theorem tuple_route_vv_mods[local]:
  make_elements_contract_mods /\ ^tuple_init_contract /\ ^tuple_complete_contract /\
  (builtin_args_length_ok (MakeArray NONE n) (LENGTH args) ==>
    body_exprs_full_ok_mods mods exps cx args) /\
  contract_inv mods exps ctx ce cx /\ module_body_inv mods src tops ce cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\ body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods ce cx env (Builtin ann (MakeArray NONE n) args) es ==>
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx ty (Builtin ann (MakeArray NONE n) args) es
Proof
  strip_tac >> drule_then (qx_choosel_then [`tys`,`tvs`] strip_assume_tac) tuple_route_type_mods >>
  `body_exprs_full_ok_mods mods exps cx args` by
    (first_x_assum irule >> simp[builtin_args_length_ok_def]) >>
  qpat_x_assum `ann = TupleT tys` SUBST_ALL_TAC >>
  qpat_assum `expr_body_pre_mods _ _ _ _ _ _` (assume_tac o MATCH_MP expr_body_pre_mods_inv) >>
  rewrite_tac[expr_vv_sim_full_mods_def] >> rpt gen_tac >> strip_tac >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (irule gas_outcome_full_mods_bad_nil >> simp[] >> qx_gen_tac `tail` >>
      Cases_on `eval_expr cx (Builtin (TupleT tys) (MakeArray NONE n) args)
        (es with gas_obs := tail)` >> simp[] >>
      irule (INST_TYPE [alpha |-> ``:eval_result``] storage_trace_frame_preserves_bad_domain) >>
      qexistsl [`eval_expr cx (Builtin (TupleT tys) (MakeArray NONE n) args)`,
                `q`,`es with gas_obs := tail`] >> simp[evaluate_storage_trace_frame]) >>
  drule_all_then (qx_choosel_then [`ba`,`sm`,`shm`] strip_assume_tac) tuple_route_paired >>
  `gas_shadow_state sm shm` by fs[make_elements_code_mods_def] >>
  `make_elements_admissible_mods cx args es` by
    drule_all_then ACCEPT_TAC tuple_route_admissible_mods >>
  qpat_x_assum `^tuple_init_contract`
    (qspecl_then [`tn0`,`st0`,`sm`,`shm`,`ba`,`shadow_sa`,`sa`,`s0`,`lo`,`func`,
      `gas_explicit_sites ctx shadow_ctx`,`es`,`d`,`cx`,`ctx`,`ce`,
      `type_memory_size_list tvs`,`ba`,`PG`,`G0`,`DF`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`q`,`addr`,`si`,`Gi`,`tni`] strip_assume_tac) >>
  suspend "elements"
QED

Resume tuple_route_vv_mods[elements]:
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC body_inv_no_phi_mods) >>
  `!fn i z. frag_reachable ctx func si fn i z ==> dalloca_fmp_headroom i z` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s0,G0,tn0) [] (OK si,Gi,tni)`
       (qspec_then `DF (storage_trace_horizon es.storage_trace)` assume_tac) >>
     rpt strip_tac >> drule_all_then ACCEPT_TAC gas_origin_ptr_path_dalloca_fmp_headroom) >>
  `make_elements_entry_mods mods exps src tops ce cx env
      (DF,lo,d,ctx,shadow_ctx,func,shadow_func) st0 (sa,es,s0,G0,tn0)
      (sa.cs_next_id,addr,type_memory_size_list tvs,q) args [] 0 sm (es,si,Gi,tni)` by
    (qpat_x_assum `^tuple_complete_contract` kall_tac >>
     `!e ee. MEM e args /\ expr_sim_inv_mods mods ce cx env ee ==>
             expr_body_pre_mods mods ce cx env e ee` by
       (rpt strip_tac >> drule_all_then ACCEPT_TAC tuple_route_children_mods) >>
     fs[expr_sim_full_endpoint_def,ci_mono_def] >>
     simp[make_elements_entry_mods_def,make_elements_cut_mods_def,
          make_elements_static_mods_def,make_elements_prefix_mods_def,
          make_elements_save_mods_def] >>
     rpt conj_tac >> rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `make_elements_run_mods (DF,lo,ctx,shadow_ctx,PG,func) ce cx st0
      (eval_exprs cx args) (es,si,Gi,tni)
      (make_elements_post_mods mods ce cx env DF lo d ctx func st0
        (sa,es,s0,G0,tn0) (sa.cs_next_id,addr,type_memory_size_list tvs,q)
        args tvs [] 0 sm sb es si)` by
    (qpat_x_assum `make_elements_contract_mods`
       (irule o REWRITE_RULE [make_elements_contract_mods_def]) >>
     conj_tac >- simp[] >>
     qexistsl [`exps`,`shm`,`shadow_func`,`shadow_sb`,`src`,`tops`,`tys`] >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
       (qpat_assum `ba.buf_operand = Var q` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC))) >>
  irule gas_outcome_full_mods_zero_prefix >> qexistsl [`Gi`,`si`,`tni`] >>
  conj_tac >- (rpt gen_tac >> first_assum irule) >>
  irule tuple_route_map >> goal_assum (drule_at Any) >>
  qexists_tac `make_elements_post_mods mods ce cx env DF lo d ctx func st0
        (sa,es,s0,G0,tn0) (sa.cs_next_id,addr,type_memory_size_list tvs,q)
        args tvs [] 0 sm sb es si` >>
  reverse conj_tac
  >- (conj_tac >- (rewrite_tac[make_elements_post_mods_def] >>
                   rpt strip_tac >> ASM_REWRITE_TAC [sumTheory.ISL]) >>
      first_assum ACCEPT_TAC) >>
  suspend "completed"
QED

Resume tuple_route_vv_mods[completed]:
  BETA_TAC >> map_every qx_gen_tac [`H`,`vs`,`ee`,`Gfin`,`tnt`,`t`,`gs`] >> strip_tac >>
  qhdtm_x_assum `make_elements_post_mods`
    (strip_assume_tac o REWRITE_RULE [make_elements_post_mods_def,sumTheory.INL_11]) >>
  qpat_x_assum `vs = _` (SUBST_ALL_TAC o SYM) >>
  qhdtm_x_assum `make_elements_cut_mods`
    (strip_assume_tac o REWRITE_RULE [make_elements_cut_mods_def]) >>
  `eval_expr cx (Builtin (TupleT tys) (MakeArray NONE n) args) (es with gas_obs := gs) =
    (INL (Value (ArrayV (TupleV vs))),ee)` by
    (irule (SIMP_RULE (srw_ss()) [] (Q.INST [`rr` |-> `INL vs`] aggregate_eval_make_tuple)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `^tuple_complete_contract`
    (qspecl_then [`ArrayV (TupleV vs)`,`TupleTV tvs`,`tn0`,`tnt`,`t`,`sm`,`si`,`sb`,`sa`,
      `s0`,`q`,`mods`,`lo`,`gs`,`func`,`es`,`env`,`ee`,`Builtin (TupleT tys) (MakeArray NONE n) args`,
      `d`,`cx`,`ctx`,`ce`,`type_memory_size_list tvs`,`addr`,
      `H:(bool # 256 word # type_value) list # num list`,`G0`,`Gfin`,
      `DF (H:(bool # 256 word # type_value) list # num list)`] mp_tac) >>
  (impl_tac >-
    (`!n b k. local_region ce es.scopes si n b k <=> local_region ce es.scopes s0 n b k` by
       (`local_ptrs_rel func ce es.scopes s0` by
          (`valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
             (rewrite_tac[GSYM storage_trace_domain_def] >> first_assum ACCEPT_TAC) >>
           qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel _ _ _ _ _ _ s0 /\ _`
             (qspec_then `storage_trace_horizon es.storage_trace` (fn th => drule_then strip_assume_tac th)) >>
           drule_all_then ACCEPT_TAC (cj 1 stmt_state_rel_local_ptrs_alloca)) >>
        qpat_assum `wb_frame ce es es sa s0 si`
          (assume_tac o CONJUNCT1 o REWRITE_RULE [wb_frame_def]) >>
        rpt gen_tac >> eq_tac >> strip_tac
        >- (irule local_region_frame >> conj_tac
            >- (qexists_tac `func` >> first_assum ACCEPT_TAC) >>
            qexistsl [`sa`,`es.scopes`,`si`] >> simp[])
        >> irule local_region_frame_fwd >> qexistsl [`s0`,`sa`,`es.scopes`] >> simp[]) >>
     qpat_assum `!h. valid_horizon cx st0 h ee.storage_trace ==> _`
       (qspec_then `H:(bool # 256 word # type_value) list # num list` (fn th => drule_then strip_assume_tac th)) >>
     simp[expr_type_def,lowered_value_type_def,is_word_type_def,type_memory_size_def,
          val_in_memory_def,expr_has_effect_def,supported_expr_exists_def,
          supported_exprs_exists_every] >>
     conj_tac >- (qpat_assum `!m. _ ==> tuple_in_memory _ _ _ m`
                    (ACCEPT_TAC o REWRITE_RULE [arithmeticTheory.ADD_CLAUSES])) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_x_assum `~EXISTS _ _ ==> make_elements_frame_mods _ _ _ _ _ _ _ _` mp_tac >>
     simp[make_elements_frame_mods_def,expr_has_effect_def,arithmeticTheory.ADD_COMM])) >>
  disch_then (strip_assume_tac o REWRITE_RULE
    [expr_type_def,mk_ptr_def,post_value_type_def,lowered_value_type_def]) >>
  qpat_x_assum `vv = _` SUBST_ALL_TAC >>
  simp[expr_type_def,mk_ptr_def,vv_location_def,post_value_type_def,lowered_value_type_def]
QED

Finalise tuple_route_vv_mods

Theorem tuple_route_compiled_read[local]:
  lower_value compile_expr ce ty (Builtin (TupleT tys) (MakeArray NONE n) args) sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T ce) ty
    (gas_shadow_expr (Builtin (TupleT tys) (MakeArray NONE n) args)) shadow_sa = (op,shadow_sb) /\
  gas_shadow_state sa shadow_sa ==>
  compile_expr ce ty (Builtin (TupleT tys) (MakeArray NONE n) args) sa =
      (LocatedValue (TupleT tys) (mk_ptr op LocMemory),sb) /\
  compile_expr (gas_shadow_env T ce) ty
    (gas_shadow_expr (Builtin (TupleT tys) (MakeArray NONE n) args)) shadow_sa =
      (LocatedValue (TupleT tys) (mk_ptr op LocMemory),shadow_sb)
Proof
  strip_tac >>
  Cases_on `compile_expr ce ty (Builtin (TupleT tys) (MakeArray NONE n) args) sa` >>
  drule_then strip_assume_tac compile_tuple_literal_inv >> gvs[] >>
  `gas_shadow_compiles (compile_expr ce ty (Builtin (TupleT tys) (MakeArray NONE n) args))
    (compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr (Builtin (TupleT tys) (MakeArray NONE n) args)))` by
    MATCH_ACCEPT_TAC gas_shadow_stmt_compile_expr_env >>
  qpat_x_assum `gas_shadow_compiles _ _`
    (qspecl_then [`sa`,`shadow_sa`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
  Cases_on `compile_expr (gas_shadow_env T ce) ty
    (gas_shadow_expr (Builtin (TupleT tys) (MakeArray NONE n) args)) shadow_sa` >>
  simp[] >> strip_tac >> gvs[] >>
  qpat_assum `compile_expr _ _ (Builtin _ _ _) _ = _`
    (fn th => mp_tac (MATCH_MP (ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO]
      lower_value_nonword_memory) th)) >>
  simp[mk_ptr_def,is_word_type_def] >> strip_tac >> gvs[] >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _`
    (fn th => mp_tac (MATCH_MP (ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO]
      lower_value_nonword_memory) th)) >>
  simp[mk_ptr_def,is_word_type_def]
QED

Theorem tuple_route_read_mods[local]:
  compatible_bound n (LENGTH args) /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx ty (Builtin (TupleT tys) (MakeArray NONE n) args) es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx ty (Builtin (TupleT tys) (MakeArray NONE n) args) es
Proof
  strip_tac >> irule materialized_value_from_vv_mods >>
  reverse (rpt conj_tac >> TRY (first_assum ACCEPT_TAC))
  >- (map_every qx_gen_tac [`gs`,`raw`,`ee`] >>
      simp[tuple_route_source] >>
      Cases_on `eval_exprs cx args (es with gas_obs := gs)` >>
      Cases_on `q` >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> drule_all_then strip_assume_tac tuple_route_compiled_read >>
  qexists_tac `LocatedValue (TupleT tys) (mk_ptr op LocMemory)` >>
  simp[] >> rpt gen_tac >> strip_tac >>
  reverse conj_tac
  >- fs[ptr_val_ok_def,ptr_vv_ok_def,vv_store_bound_def,expr_store_bound_def,
        expr_type_def,lowered_value_type_def,is_word_type_def,read_result_def,return_def,mk_ptr_def] >>
  qhdtm_x_assum `vv_post_mods`
    (strip_assume_tac o PURE_REWRITE_RULE [vv_post_mods_def]) >>
  simp[expr_post_mods_def] >>
  irule (SIMP_RULE (srw_ss()) [mk_ptr_def,is_word_type_def]
    (Q.INST [`p` |-> `mk_ptr op LocMemory`, `t` |-> `TupleT tys`]
      (SPEC_ALL expr_post_of_vv_post_memory))) >>
  fs[vv_post_def,vv_place_ptr_mods_def,vv_place_ptr_def,vv_holds_mods_def,mk_ptr_def] >>
  qexists_tac `tys` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem make_tuple_route_from_elements_mods:
  make_elements_contract_mods /\ ^tuple_init_contract /\ ^tuple_complete_contract /\
  (builtin_args_length_ok (MakeArray NONE n) (LENGTH args) ==>
    body_exprs_full_ok_mods mods exps cx args) /\
  contract_inv mods exps ctx ce cx /\ module_body_inv mods src tops ce cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\ body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods ce cx env (Builtin ann (MakeArray NONE n) args) es ==>
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx ty (Builtin ann (MakeArray NONE n) args) es /\
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx ty (Builtin ann (MakeArray NONE n) args) es
Proof
  strip_tac >> conj_asm1_tac
  >- (irule tuple_route_vv_mods >> rpt conj_tac >>
      (first_assum ACCEPT_TAC ORELSE
       (qexistsl [`env`,`exps`,`mods`,`src`,`tops`] >> rpt conj_tac >> first_assum ACCEPT_TAC))) >>
  drule_then (qx_choosel_then [`tys`,`tvs`] strip_assume_tac) tuple_route_type_mods >>
  qpat_x_assum `ann = TupleT tys` SUBST_ALL_TAC >>
  drule_all_then ACCEPT_TAC tuple_route_read_mods
QED
