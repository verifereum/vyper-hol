(* Run the Array iterator's base once, ending at the paired expression cut. *)
Theory bodyForArrayExprRunMods
Ancestors
  bodyForEntryInputsMods bodyForArrayHeaderMods bodyActiveStmtCallsMods bodyFullForFacts bodySim
  vyperEvalOutcomeSuffix vyperTypeEvalCaseProofs vyperTypeEnv bodyInvExecutionProps
  exprSimSource exprSimHypsDefs exprSimDefs vyperTypeExprSoundness vyperInterpreter vyperState
  bodyInvCodeProps bodyInvMetadataProps bodyFullIfExpReach
  bodyExprPreFacts exprBodyPreProps exprBodyPreTypingProps exprBodyPreCallSafetyProps
  bodyWriteSubscriptSourceMods bodyNormalHeadTailMods bodyBranchCellFrameMods
  bodyFullPredsMods bodyFullPostsMods bodyFullShared
  gasOutcomeFullMods gasOutcomeFull gasOutcomeFullPostMods gasOutcomeFullPostPathMods gasShadowCompile
  gasShadowState loweringPosts compileEnv fragExec context venomState bodyFullShadowBodyInv
  bodyForRangeHeaderMods
  reasonEndpointResourcesPtr exprSimCopy exprLoweringProps
  vyperTypeSystem vyperTypeCallStackSoundness vyperTypeCallGraph
  vyperTypeInvariants vyperTypeExprResult vyperTypeEvalSoundness vyperExprNoControl
  vyperEvalExprPreservesScopesDom vyperStorageTrace vyperStorageFootprint
  supportedStmtTraverse supportedExprTraverse allocLimits allocLimitsProps
  stmtSimDefs stmtSimProps haltExitProj bodyMemoryDefs bodyPtrDefs
  fragGasOriginPtr gasContext finite_map list option
Libs monadsyntax

val _ = Parse.hide "body";

Theorem for_array_source_pre_mods:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  supported_stmt tops bindings (For id typ (Array e) n body) /\
  type_stmt env ret_ty (For id typ (Array e) n body) = SOME env' /\
  expr_sim_inv_mods mods cenv cx env es /\ body_const_cells_agree_mods mods cx env es /\
  stmt_exprs_ok cenv (For id typ (Array e) n body) /\
  ~supported_stmt_expr_exists (unallocated_bare_global_root cenv env)
    (For id typ (Array e) n body) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (For id typ (Array e) n body) ==>
    EXISTS (occurs_abi_decode_target target o SND) mods) /\
  call_evaluation_safe cx (int_calls_stmt (For id typ (Array e) n body)) ==>
  expr_body_pre_mods mods cenv cx env e es
Proof
  strip_tac >>
  `EVERY (source_body_call_supported cx) (int_calls_stmt (For id typ (Array e) n body))` by
    (drule_all_then strip_assume_tac active_stmt_calls_resolve_mods >>
     first_x_assum irule >> conj_tac
     >- (qexistsl_tac [`env'`,`ret_ty`] >> first_assum ACCEPT_TAC) >>
     qexists_tac `bindings` >> first_assum ACCEPT_TAC) >>
  drule_then assume_tac supported_stmt_body_safe >>
  drule_then strip_assume_tac type_stmt_for_projection >>
  drule_then assume_tac contract_inv_cenv_modules >>
  drule_then assume_tac contract_inv_type_env >>
  qpat_x_assum `stmt_exprs_ok _ _` (strip_assume_tac o SIMP_RULE std_ss
    [stmt_exprs_ok_def, alloc_limits_stmt_def, alloc_limits_iterator_def,
     supported_stmt_expr_exists_def, supported_iterator_exists_def, DE_MORGAN_THM]) >>
  qpat_x_assum `body_stmt_safe _ _` (strip_assume_tac o SIMP_RULE std_ss
    [body_stmt_safe_def, supported_stmt_expr_exists_def,
     supported_iterator_exists_def, DE_MORGAN_THM]) >>
  qpat_x_assum `~supported_stmt_expr_exists _ _` (strip_assume_tac o SIMP_RULE std_ss
    [supported_stmt_expr_exists_def, supported_iterator_exists_def, DE_MORGAN_THM]) >>
  qpat_x_assum `!target. supported_stmt_expr_exists _ _ ==> _`
    (strip_assume_tac o SIMP_RULE std_ss
      [supported_stmt_expr_exists_def, supported_iterator_exists_def,
       DISJ_IMP_THM, FORALL_AND_THM]) >>
  fs[well_typed_iterator_def, int_calls_stmt_def, int_calls_iterator_def, EVERY_APPEND] >>
  irule stmt_expr_body_pre_mods >>
  qpat_assum `call_evaluation_safe _ _` (irule_at Any) >>
  simp[expr_has_evm_run_def, DE_MORGAN_THM, LEFT_AND_OVER_OR, supported_expr_exists_disj] >>
  conj_tac >- (irule alloc_limits_expr_not_extcode >> goal_assum (drule_at Any)) >>
  conj_tac >-
    (qpat_assum `cenv.ce_modules = mods` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  irule (cj 1 alloc_limits_expr_exists) >> simp[]
QED

Theorem for_array_eval_type_mods[local]:
  expr_sim_inv_mods mods cenv cx env es /\
  type_stmt env ret_ty (For id typ (Array e) n body) = SOME env' ==>
  ?tyv. evaluate_type (get_tenv cx) typ = SOME tyv
Proof
  strip_tac >> drule_then strip_assume_tac type_stmt_for_projection >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  drule assignable_type_well_formed >>
  simp[well_formed_type_def, IS_SOME_EXISTS]
QED

Theorem for_array_eval_sound_mods[local]:
  expr_body_pre_mods mods cenv cx env e es /\ eval_expr cx e es = (res,ee) ==>
  expr_sim_inv_mods mods cenv cx env ee /\ no_type_error_result res /\
  (case res of INL raw => eval_result_typed (env,cx,ee) raw (Type (expr_type e))
             | INR _ => T)
Proof
  strip_tac >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then assume_tac expr_body_pre_mods_call_evaluation_safe >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  `IS_SOME ee.outcomes` by
    (drule_at (Pat `eval_expr _ _ _ = _`) eval_expr_outcomes_some >>
     fs[expr_sim_inv_mods_def]) >>
  qpat_x_assum `expr_sim_inv_mods _ _ _ _ es` mp_tac >>
  simp[expr_sim_inv_mods_def] >> strip_tac >>
  drule_all_then assume_tac eval_expr_popped_keys_indexed >>
  qspecl_then [`cx`, `e`] (mp_tac o cj 1) (cj 5 eval_scc_type_sound_mutual) >>
  disch_then (qspecl_then [`env`, `es`, `res`, `ee`] mp_tac) >>
  simp[] >> strip_tac >>
  `outcomes_accounts_typed ee.outcomes` by
    (rw[outcomes_accounts_typed_def] >>
     drule (cj 5 eval_outcome_suffix_mutual) >> strip_tac >>
     drule_then irule outcome_suffix_EVERY >> fs[outcomes_accounts_typed_def]) >>
  simp[] >> conj_tac >> first_assum ACCEPT_TAC
QED

Theorem for_array_raw_admissible_mods[local]:
  expr_body_pre_mods mods cenv cx env e es ==>
  gas_admissible (eval_expr cx e) expr_vv_res_ok es
Proof
  rw[gas_admissible_def] >>
  `expr_body_pre_mods mods cenv cx env e (es with gas_obs := gs)` by simp[] >>
  drule_all_then strip_assume_tac for_array_eval_sound_mods >>
  Cases_on `res` >> gvs[expr_vv_res_ok_def]
  >- (rename1 `eval_result_typed _ raw _` >> Cases_on `raw` >>
      gvs[eval_result_typed_def]) >>
  drule (cj 1 eval_expr_no_control) >> rename1 `INR exc` >> Cases_on `exc` >>
  gvs[no_control_exc_def, no_type_error_result_def] >>
  rename1 `Error err` >> Cases_on `err` >> gvs[]
QED

Theorem for_array_raw_cells_mods[local]:
  well_typed_expr env e /\ body_const_cells_agree_mods mods cx env es /\
  eval_expr cx e es = (INL raw,ee) ==>
  body_const_cells_agree_mods mods cx env ee
Proof
  strip_tac >>
  `?res. eval_stmt cx (Expr e) es = (res,ee)` by
    (simp[Once evaluate_def, bind_def, type_check_def, assert_def, return_def, raise_def] >>
     Cases_on `is_HashMapRef raw` >> simp[]) >>
  `type_stmt env NoneT (Expr e) = SOME env` by
    simp[type_stmt_def, well_typed_expr_not_hashmap_place] >>
  irule body_const_cells_agree_mods_stmt >>
  goal_assum (drule_at (Pat `eval_stmt _ _ _ = _`)) >>
  qexistsl_tac [`env`,`NoneT`] >> simp[]
QED

(* Re-index the entry observations at the horizon of this same successful
   evaluation, while keeping the source scopes and constant cells. *)
Theorem for_array_raw_source_frame_mods[local]:
  expr_body_pre_mods mods cenv cx env e es /\ body_const_cells_agree_mods mods cx env es /\
  eval_expr cx e (es with gas_obs := obs) = (INL raw,ee) /\
  valid_horizon cx st0 H ee.storage_trace ==>
  valid_horizon cx st0 H es.storage_trace /\
  expr_sim_inv_mods mods cenv cx env ee /\ body_const_cells_agree_mods mods cx env ee /\
  MAP FDOM ee.scopes = MAP FDOM es.scopes
Proof
  strip_tac >>
  `expr_body_pre_mods mods cenv cx env e (es with gas_obs := obs) /\
   body_const_cells_agree_mods mods cx env (es with gas_obs := obs)` by simp[] >>
  drule_all_then strip_assume_tac for_array_eval_sound_mods >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_all_then assume_tac for_array_raw_cells_mods >>
  drule_then (assume_tac o GSYM o SRULE []) eval_expr_preserves_scopes_dom >>
  simp[] >> irule valid_horizon_append >>
  drule_at (Pat `f _ = _`) storage_trace_frame_prefix >>
  simp[evaluate_storage_trace_frame] >> strip_tac >>
  qexists_tac `observations` >> fs[]
QED

Theorem for_array_raw_abi_frame_mods[local]:
  vv_post_mods H ctx func cenv cx e es sa sb s0 ee raw vv t /\
  MAP FDOM ee.scopes = MAP FDOM es.scopes /\ stmt_state_rel H ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sb.cs_next_var /\
  s0.vs_alloca_next <= t.vs_alloca_next /\ ret_pc_ok cenv sa s0 /\
  return_buf_frame d cenv sa s0 /\ return_buf_sep d cenv es s0 /\
  (!bw capacity. d = SOME (bw,capacity) ==> allocas_from (w2n bw + capacity) t) ==>
  ret_pc_ok cenv sa t /\ ret_pc_ok cenv sb t /\ return_buf_frame d cenv sb t /\
  return_buf_sep d cenv ee t /\ alloca_frame cenv es sa s0 cenv ee t
Proof
  simp[vv_post_mods_def] >> strip_tac >>
  conj_tac >-
    (irule ret_pc_ok_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[]) >>
  conj_tac >-
    (irule ret_pc_ok_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[]) >>
  conj_tac >-
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[]) >>
  conj_tac >-
    (irule return_buf_sep_locals_kept >>
     conj_tac >- fs[arithmeticTheory.ADD_COMM] >>
     qpat_assum `stmt_state_rel _ _ _ _ _ es s0` (irule_at Any) >>
     qexists_tac `sa` >> simp[]) >>
  irule alloca_frame_of_mem_frame >>
  qpat_assum `stmt_state_rel _ _ _ _ _ es s0` (irule_at Any) >> simp[] >>
  first_assum ACCEPT_TAC
QED

Theorem for_array_raw_terminal_mods[local]:
  expr_exit (res:eval_result + exception) r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s) ==>
  ?ex. res = INR ex /\
    (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex : unit + exception) gt r) /\
    halt_exit H cx ee (INR ex : unit + exception) r /\
    (ctx_has_dalloca ctx ==> !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s)
Proof
  strip_tac >> Cases_on `res` >- fs[expr_exit_INL] >> gvs[] >>
  conj_tac >-
    (simp[stmt_exit_ptr_def] >> gen_tac >> disj1_tac >>
     irule (iffLR (INST_TYPE [alpha |-> ``:eval_result``, beta |-> ``:unit``] expr_exit_INR_type)) >>
     first_assum ACCEPT_TAC) >>
  conj_tac >-
    (irule (iffLR (INST_TYPE [alpha |-> ``:eval_result``, beta |-> ``:unit``] halt_exit_INR_type)) >>
     first_assum ACCEPT_TAC) >>
  rpt strip_tac >- simp[] >>
  gvs[] >> rename1 `expr_exit (INR ex) (IntRet ir s)` >>
  Cases_on `ex` >> gvs[expr_exit_def] >>
  rename1 `expr_exit (INR (Error err)) _` >> Cases_on `err` >> gvs[expr_exit_def]
QED

Theorem for_array_raw_clean_mods[local]:
  ptr_vv_ok cx vt raw vv ee G tn t ==> op_taint tn (vv_operand vv) = {}
Proof
  Cases_on `vv` >> simp[ptr_vv_ok_def, vv_operand_def, ptr_val_ok_def, PULL_EXISTS]
QED

(* The Cut describes an ordinary landing only. Unsupported storage domains
   and exceptional exits stay in the linked gas outcome. *)
Definition for_array_expr_landed_mods_def[nocompute]:
  for_array_expr_landed_mods (DF,lo,d,ctx,func) mods cx cenv env e vv se
      (es,sa,s0,G0,tn0) H raw ee G tn t <=>
    vv_post_mods H ctx func cenv cx e es sa se s0 ee raw vv t /\
    vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee raw vv t /\
    ptr_vv_ok cx (post_value_type cenv e) raw vv ee G tn t /\
    (!v. raw = Value v /\ ~is_word_type (post_value_type cenv e) /\
      ~is_bytestring_type (post_value_type cenv e) ==>
      vv_own cenv cx (post_value_type cenv e) sa se ee raw vv t /\
      (!ann p. vv = LocatedValue ann p ==> p.ptr_location = LocMemory)) /\
    (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
      ?v. read_result cx raw ee = (INL v,ee) /\
        !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
          eval_operand (vv_operand vv) t = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
            val_in_memory rt v (w2n w) mem)) /\
    (!ann op. vv = StackValue ann op /\ ~is_word_type (post_value_type cenv e) ==>
      ptr_buf_ok cenv e op G t) /\
    (!ann p. vv = LocatedValue ann p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok cenv e p.ptr_operand G t) /\
    copy_old_operand se (vv_operand vv) /\ op_taint tn (vv_operand vv) = {} /\
    ~t.vs_halted /\ t.vs_current_bb = se.cs_current_bb /\
    t.vs_inst_idx = LENGTH se.cs_current_insts /\
    storage_well_formed_on cx es (FST H) /\
    expr_sim_inv_mods mods cenv cx env ee /\ body_const_cells_agree_mods mods cx env ee /\
    MAP FDOM ee.scopes = MAP FDOM es.scopes /\ ee.gas_obs = [] /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
    ret_pc_ok cenv sa t /\ ret_pc_ok cenv se t /\
    return_buf_frame d cenv se t /\ return_buf_sep d cenv ee t /\
    (!bw capacity. d = SOME (bw,capacity) ==> allocas_from (w2n bw + capacity) t) /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\
    (!fn inst q. frag_reachable ctx func t fn inst q ==> dalloca_fmp_headroom inst q) /\
    for_array_outer_frame_mods ctx func cenv sa es s0 G0 tn0 ee G tn t
End

(* This is the first input to for_array_outcome_from_capture_mods. The
   source replay (including the observation split) remains under that bind. *)
Theorem for_array_raw_run_mods:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  supported_stmt tops bindings (For id typ (Array e) n body) /\
  type_stmt env ret_ty (For id typ (Array e) n body) = SOME env' /\
  expr_sim_inv_mods mods cenv cx env es /\ body_const_cells_agree_mods mods cx env es /\
  stmt_exprs_ok cenv (For id typ (Array e) n body) /\
  ~supported_stmt_expr_exists (unallocated_bare_global_root cenv env)
    (For id typ (Array e) n body) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (For id typ (Array e) n body) ==>
    EXISTS (occurs_abi_decode_target target o SND) mods) /\
  call_evaluation_safe cx (int_calls_stmt (For id typ (Array e) n body)) /\
  (!tenv s tv t. tenv = get_tenv cx /\
    lift_option_type (evaluate_type tenv typ) "For evaluate_type" s = (INL tv,t) ==>
    body_iterator_full_ok_mods mods exps cx (Array e)) /\
  compile_expr cenv (expr_type e) e sa = (vv,se) /\
  compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) sha = (vv,she) /\
  gas_shadow_state sa sha /\ gas_shadow_context ctx shadow_ctx /\
  ctx_inst_ids_distinct ctx /\ gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa se func /\ fn_has_code sha she shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ret_pc_ok cenv sa s0 /\ return_buf_frame d cenv sa s0 /\ return_buf_sep d cenv es s0 /\
  alloca_history func s0 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst q. frag_reachable ctx func s0 fn inst q ==> dalloca_fmp_headroom inst q) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    mods cx st0 (eval_expr cx e) (es,s0,G0,tn0)
    (\H res ee G tn t. (?raw. res = INL raw) /\
      for_array_expr_landed_mods (DF,lo,d,ctx,func) mods cx cenv env e vv se
        (es,sa,s0,G0,tn0) H (OUTL res) ee G tn t)
    (\H res ee gt r. ?ex. res = INR ex /\
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex : unit + exception) gt r) /\
      halt_exit H cx ee (INR ex : unit + exception) r /\
      (ctx_has_dalloca ctx ==> !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
Proof
  strip_tac >>
  drule_all_then assume_tac for_array_source_pre_mods >>
  drule_all_then strip_assume_tac for_array_eval_type_mods >>
  drule_all_then (assume_tac o REWRITE_RULE [body_iterator_full_ok_mods_def])
    for_iterator_callback_mods >>
  `expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (expr_type e) e es` by
    (qhdtm_x_assum `body_expr_full_ok_mods`
       (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
     qpat_assum `!df lo d pg src tops ctx sh fn shfn ce env ty es. _ ==>
       expr_sim_full_mods _ _ _ _ _ _ /\ expr_vv_sim_full_mods _ _ _ _ _ _`
       (drule_all_then mp_tac) >>
     simp[IMP_CONJ_THM,FORALL_AND_THM] >> strip_tac >> first_assum (irule o SPEC_ALL)) >>
  `gas_shadow_state se she` by
    (`gas_shadow_compiles (compile_expr cenv (expr_type e) e)
       (compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e))` by
       irule (cj 1 gas_shadow_compile_expr_env |> SPEC_ALL |>
         Q.INST [`shadow` |-> `T`] |> REWRITE_RULE [COND_CLAUSES]) >>
     drule_all gas_shadow_step >> simp[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by fs[ret_pc_ok_def] >>
  drule_then assume_tac for_array_raw_admissible_mods >>
  qhdtm_x_assum `expr_vv_sim_full_mods` (mp_tac o REWRITE_RULE [expr_vv_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`se`,`sha`,`she`,`vv`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  drule_then (fn eq => disch_then (assume_tac o REWRITE_RULE [eq])) contract_inv_cenv_modules >>
  suspend "posts"
QED

Resume for_array_raw_run_mods[posts]:
  drule_all_then assume_tac gas_outcome_full_mods_return_buf_allocas >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ (\H res ee G tn t. ?tv. _) _` kall_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ rawQ rawR` >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (match_mp_tac (GEN_ALL body_inv_no_phi_mods) >>
     qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >> simp[]) >>
  irule gas_outcome_full_mods_post_source >>
  qexistsl_tac [`\H res ee G tn t. rawQ H res ee G tn t /\
     (!fn inst q. frag_reachable ctx func t fn inst q ==> dalloca_fmp_headroom inst q)`, `rawR`] >>
  rpt conj_tac
  >- suspend "normal"
  >- (simp[Abbr `rawR`] >> rpt strip_tac >> irule for_array_raw_terminal_mods >> simp[]) >>
  irule gas_outcome_full_mods_post_path >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ rawQ rawR` (irule_at Any) >>
  simp[] >> rpt strip_tac >> drule_all gas_origin_ptr_path_dalloca_fmp_headroom >> simp[]
QED

Resume for_array_raw_run_mods[normal]:
  simp[Abbr `rawQ`] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  qpat_assum `ee with gas_obs := [] = ee` (fn eq =>
    qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` (assume_tac o SRULE [eq]))) >>
  drule_all_then strip_assume_tac for_array_raw_source_frame_mods >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `sa.cs_next_var <= se.cs_next_var` by
    (qpat_assum `compile_expr cenv (expr_type e) e sa = _`
       (mp_tac o MATCH_MP compileExprAllocaFreshTheory.compile_expr_alloca_fresh) >>
     simp[ci_mono_def]) >>
  drule_all_then strip_assume_tac (SRULE [arithmeticTheory.ADD_COMM] for_array_raw_abi_frame_mods) >>
  drule_all_then assume_tac compile_expr_old_operand >>
  drule_then assume_tac for_array_raw_clean_mods >>
  simp[for_array_expr_landed_mods_def] >>
  simp[for_array_outer_frame_mods_def,range_outer_frame_mods_def] >>
  fs[vv_post_mods_def, ghost_inv_at_mods_def, ghost_kept_at_def, arithmeticTheory.ADD_COMM] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Finalise for_array_raw_run_mods
