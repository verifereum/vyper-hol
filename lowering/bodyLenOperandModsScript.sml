(* Len evaluates its single operand without forcing its value first. *)
Theory bodyLenOperandMods
Ancestors
  bodyFullPredsMods bodyFullShared bodyFullPostsMods bodyScalarStackVVMods
  exprBodyPreProps exprBodyPreTypingProps exprBodyPreCallSafetyProps
  exprSimLen exprSimHyps exprSimHypsDefs exprSimUnwrap gasShadowCompile gasShadowState
  vyperTypeCallGraph gasContext vyperExprNoControl gasShadow exprBopLowering fragExec
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasExemptCertMods
  bodySimStmtFacts vyperTypeEvalSoundness vyperTypeEvalCaseProofs
  vyperTypeExprSoundness vyperStorageTrace vyperStorageFootprint
  supportedExprTraverse allocLimits exprSimDefs fragGasOriginPtr
  vyperTypeSystem vyperTypeBuiltins vyperTypeInvariants vyperInterpreter
  vyperState vyperAST compileEnv exprLowering exprLoweringProps
  loweringPosts bodyPtrDefs context list exprSafeOperand vyperContext
  vyperTypeValues finite_map exprSimSource haltExitProj stmtSimProps vyperTypeInitialState
Libs monadsyntax

Theorem len_linked_child_pre[local]:
  expr_body_pre_mods mods ce cx env (Builtin ann Len args) es ==>
  ?e. args = [e] /\ ann = BaseT (UintT 256) /\ is_sized_type (expr_type e) /\
      expr_body_pre_mods mods ce cx env e es
Proof
  strip_tac >> drule_then assume_tac expr_body_pre_mods_well_typed >>
  `?e. args = [e] /\ ann = BaseT (UintT 256) /\ is_sized_type (expr_type e)` by
    (qpat_x_assum `well_typed_expr _ _` mp_tac >>
     simp[Once well_typed_expr_def, well_typed_builtin_app_def] >> strip_tac >>
     Cases_on `args` >> gvs[] >> rename1 `LENGTH rest = 0` >>
     Cases_on `rest` >> gvs[]) >>
  gvs[] >> fs[Once well_typed_expr_def] >> fs[Once well_typed_expr_def] >>
  qpat_x_assum `expr_body_pre_mods _ _ _ _ (Builtin _ Len _) _` mp_tac >>
  simp[expr_body_pre_mods_def, Once well_typed_expr_def,
       byte_widths_expr_def, alloc_limits_expr_def, int_calls_expr_def,
       expr_has_evm_run_thm, supported_expr_exists_def, DISJ_IMP_THM,
       FORALL_AND_THM]
QED

Theorem len_forced_source[local]:
  bind (eval_expr cx (Builtin ann Len [e])) (read_result cx) =
  bind (eval_expr cx e) (\tv. bind (result_array_length cx tv)
    (\n. return (IntV (&n))))
Proof
  simp[len_source, bind_assoc, read_result_def, bind_return]
QED

Theorem len_child_eval_sound[local]:
  expr_body_pre_mods mods ce cx env e es /\ eval_expr cx e es = (res,ee) ==>
  no_type_error_result res /\
  (case res of INL raw => eval_result_typed (env,cx,ee) raw (Type (expr_type e))
             | INR _ => T)
Proof
  strip_tac >> drule_then strip_assume_tac expr_body_pre_mods_runtime_typing >>
  drule_then assume_tac expr_body_pre_mods_call_evaluation_safe >>
  qspecl_then [`cx`,`e`] (mp_tac o cj 1) (cj 5 eval_scc_type_sound_mutual) >>
  disch_then (qspecl_then [`env`,`es`,`res`,`ee`] mp_tac) >>
  fs[runtime_consistent_def]
QED

Theorem len_pre_gas_obs[local]:
  expr_body_pre_mods mods ce cx env e (es with gas_obs := gs) <=>
  expr_body_pre_mods mods ce cx env e es
Proof
  simp[expr_body_pre_mods_def, expr_sim_inv_mods_def]
QED

Theorem len_child_admissible[local]:
  expr_body_pre_mods mods ce cx env e es ==>
  gas_admissible (eval_expr cx e) expr_vv_res_ok es
Proof
  rw[gas_admissible_def] >>
  `expr_body_pre_mods mods ce cx env e (es with gas_obs := gs)` by
    (PURE_REWRITE_TAC[len_pre_gas_obs] >> first_assum ACCEPT_TAC) >>
  drule_all_then strip_assume_tac len_child_eval_sound >>
  Cases_on `res` >> gvs[expr_vv_res_ok_def]
  >- (rename1 `eval_result_typed _ raw _` >> Cases_on `raw` >>
      gvs[eval_result_typed_def]) >>
  drule (cj 1 eval_expr_no_control) >> rename1 `INR exc` >> Cases_on `exc` >>
  gvs[no_control_exc_def, no_type_error_result_def] >>
  rename1 `Error err` >> Cases_on `err` >> gvs[]
QED

Theorem len_cut[local]:
  lower_value compile_expr ce ty (Builtin ann Len [e]) sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T ce) ty
    (gas_shadow_expr (Builtin ann Len [e])) sha = (op,shb) /\
  gas_shadow_state sa sha /\ fn_has_code sa sb func /\
  fn_has_code sha shb shadow_func ==>
  ?vv sm shm.
    compile_expr ce ty e sa = (vv,sm) /\
    compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) sha = (vv,shm) /\
    compile_builtin_len ce.ce_is_ctor ce.ce_imm_alloca (vv_operand vv)
      (case vv_location vv of NONE => LocMemory | SOME l => l) sm = (op,sb) /\
    gas_shadow_state sm shm /\ cs_extends sa sm /\ cs_extends sm sb /\
    fn_has_code sa sm func /\ fn_has_code sm sb func /\
    fn_has_code sha shm shadow_func
Proof
  strip_tac >>
  Cases_on `compile_expr ce ty e sa` >>
  Cases_on `compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) sha` >>
  `gas_shadow_compiles (compile_expr ce ty e)
    (compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e))` by
    irule (cj 1 gas_shadow_compile_expr_env |> SPEC_ALL |>
      Q.INST [`shadow` |-> `T`] |> REWRITE_RULE [COND_CLAUSES]) >>
  drule_all_then strip_assume_tac gas_shadow_step >> gvs[] >>
  qpat_x_assum `lower_value _ _ _ (Builtin _ Len _) _ = _` mp_tac >>
  qpat_x_assum `lower_value _ _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[lower_value_def, compile_expr_len, gas_shadow_expr_def,
       gas_shadow_builtin_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[as_stack_val_pair, unwrap_value_def, comp_return_def]) >>
  rpt strip_tac >> gvs[] >>
  qpat_assum `compile_builtin_len _ _ _ _ _ = (_,sb)`
    (assume_tac o MATCH_MP len_load_extends) >>
  qpat_assum `compile_builtin_len _ _ _ _ _ = (_,shb)`
    (assume_tac o MATCH_MP len_load_extends) >>
  qpat_assum `compile_expr ce ty e sa = _`
    (strip_assume_tac o MATCH_MP compile_expr_extends) >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _`
    (strip_assume_tac o MATCH_MP compile_expr_extends) >>
  `fn_has_code sa r func /\ fn_has_code r sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code sha r' shadow_func /\ fn_has_code r' shb shadow_func` by
    (irule fn_has_code_split >> simp[]) >> simp[]
QED

Theorem len_child_vv[local]:
  (builtin_args_length_ok Len (LENGTH [e]) ==>
    body_expr_full_ok_mods mods exps cx (HD [e])) /\
  contract_inv mods exps ctx ce cx /\ module_body_inv mods src tops ce cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods ce cx env e es ==>
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty e es
Proof
  simp[builtin_args_length_ok_def] >> strip_tac >>
  qpat_x_assum `body_expr_full_ok_mods _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  qpat_assum `!a b c d e f g h i j k l m n. _ ==> expr_sim_full_mods _ _ _ _ _ _ /\ _`
    (drule_all_then (mp_tac o SPEC_ALL)) >> simp[]
QED

Theorem len_child_env[local]:
  expr_body_pre_mods mods ce cx env e es ==>
  env_consistent env cx es /\ env.type_defs = get_tenv cx
Proof
  strip_tac >> drule expr_body_pre_mods_inv >>
  disch_then (assume_tac o MATCH_MP expr_sim_inv_mods_env) >>
  drule env_consistent_type_defs_get_tenv >> simp[]
QED

Theorem len_annotation_evaluates[local]:
  expr_body_pre_mods mods ce cx env e es ==>
  ?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt
Proof
  strip_tac >> drule_then strip_assume_tac len_child_env >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  `!id t. FLOOKUP env.var_types id = SOME t ==>
          well_formed_type env.type_defs t` by
    metis_tac[well_formed_type_def, env_consistent_var_type_evaluates] >>
  drule_all well_typed_expr_type_well_formed >>
  simp[well_formed_type_def, optionTheory.IS_SOME_EXISTS]
QED

Theorem len_reached_types[local]:
  expr_body_pre_mods mods ce cx env e es /\
  eval_expr cx e es = (INL raw,ee) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tvt ==>
  eval_result_typed (env,cx,ee) raw (Type (expr_type e)) /\
  !v. read_result cx raw ee = (INL v,ee) ==> value_has_type tvt v
Proof
  strip_tac >> conj_tac
  >- (drule_all len_child_eval_sound >> simp[]) >>
  rpt strip_tac >>
  `bind (eval_expr cx e) (read_result cx) es = (INL v,ee)` by simp[bind_def] >>
  drule_all_then strip_assume_tac (REWRITE_RULE [ETA_THM] expr_body_pre_eval_mods) >>
  drule_then strip_assume_tac len_child_env >> gvs[value_runtime_typed_def]
QED

(* At the successful unforced landing, the remainder is just the length
   load. Keep the source result paired with the same suffix path. *)
Theorem len_pure_tail[local]:
  result_array_length cx tv ee = (INL n,ee) /\ ~t.vs_halted /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK z,G2,tn2) /\
    Q H (INL (IntV (&n))) (ee with gas_obs := []) G2 tn2 z) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (bind (result_array_length cx tv) (\n. return (IntV (&n)))) (ee,t,G,tn) Q R
Proof
  strip_tac >> irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl_tac [`G2`,`ee`,`INL (IntV (&n))`,`z`,`tn2`] >> simp[] >>
  drule len_ral_gas_obs >> simp[bind_def,return_def]
QED

Theorem len_child_terminal[local]:
  expr_exit (res : eval_result + exception) r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s) ==>
  ?exc. res = INR exc /\
    expr_exit (INR exc : value + exception) r /\
    halt_exit H cx ee (INR exc : value + exception) r /\
    (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)
Proof
  Cases_on `res` >> simp[expr_exit_def] >>
  metis_tac[expr_exit_INR_type, halt_exit_INR_type]
QED

val len_suffix = ``
  !DF lo d explicit ctx func PG cenv cx env e es st0 sa sm sb s0
   G0 tn0 ee tv vv t G tn op pvt tvt.
    expr_body_pre_mods mods cenv cx env (Builtin (BaseT (UintT 256)) Len [e]) es /\
    expr_body_pre_mods mods cenv cx env e es /\ is_sized_type (expr_type e) /\
    compile_builtin_len cenv.ce_is_ctor cenv.ce_imm_alloca (vv_operand vv)
      (case vv_location vv of NONE => LocMemory | SOME l => l) sm = (op,sb) /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
    type_widens_to (get_tenv cx) (post_value_type cenv e) (expr_type e) /\
    evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME pvt /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
    env.type_defs = get_tenv cx /\
    eval_result_typed (env,cx,ee) tv (Type (expr_type e)) /\
    (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type tvt v) /\
    storage_trace_domain cx st0 ee.storage_trace /\ ~t.vs_halted /\
    t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      vv_post_mods H ctx func cenv cx e es sa sm s0 ee tv vv t /\
      vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv t /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
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
      !H. valid_horizon cx st0 H ee.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK z,G2,tn2) /\
        expr_post_mods H ctx func cenv cx (Builtin (BaseT (UintT 256)) Len [e])
          es sa sb s0 ee (IntV (&n)) op z /\
        expr_store_bound cx (BaseT (UintT 256)) (IntV (&n)) op z /\
        z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
        s0.vs_alloca_next <= z.vs_alloca_next /\
        ghost_inv_at_mods (DF H) lo d cenv cx ee G2 tn2 z /\
        ptr_val_ok cx (BaseT (UintT 256)) (IntV (&n)) op G2 tn2 z /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2``;

Theorem len_bind_tail[local]:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (eval_expr cx e) (es,s0,G0,tn0) Qchild
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)) /\
  (!marks res mid G tn t.
    (!tail. eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (res,mid with gas_obs := tail)) /\ storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      Qchild H res mid G tn t /\ mid.gas_obs = [] /\ ~t.vs_halted) ==>
    ?tv. res = INL tv /\
      gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
        (bind (result_array_length cx tv) (\n. return (IntV (&n))))
        (mid,t,G,tn) Qend
        (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
          (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (bind (eval_expr cx (Builtin ann Len [e])) (read_result cx))
    (es,s0,G0,tn0) Qend
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  strip_tac >> PURE_REWRITE_TAC[len_forced_source] >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_result >>
      goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_result >> simp[])
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`!v. storage_trace_frame (bind (result_array_length _ v) _)`]
  >- simp[storage_trace_frame_bind_all, storage_trace_frame_array_length,
          storage_trace_frame_return] >>
  qexists_tac `\H res ee G tn t. Qchild H res ee G tn t /\ ee.gas_obs = [] /\ ~t.vs_halted` >>
  BETA_TAC >> conj_tac
  >- (rpt strip_tac >> disj1_tac >> first_x_assum irule >>
      conj_tac >- (qexists_tac `marks` >> first_assum ACCEPT_TAC) >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> rpt strip_tac >> drule_all len_child_terminal >> simp[]
QED

Theorem len_signature_evaluates[local]:
  functions_well_typed cx /\ env_context_consistent env cx /\
  FLOOKUP env.fn_sigs fid = SOME sg ==>
  ?tv. evaluate_type (get_tenv cx) sg.ret_ty = SOME tv
Proof
  strip_tac >> PairCases_on `fid` >>
  `fn_sigs_consistent env.fn_sigs cx /\ fn_sigs_live env.fn_sigs cx` by
    fs[env_context_consistent_def] >>
  qpat_x_assum `fn_sigs_consistent _ _`
    (strip_assume_tac o REWRITE_RULE [fn_sigs_consistent_def]) >>
  qpat_x_assum `fn_sigs_live _ _`
    (strip_assume_tac o REWRITE_RULE [fn_sigs_live_def]) >>
  first_x_assum (drule_then assume_tac) >> first_x_assum (drule_then strip_assume_tac) >>
  qpat_x_assum `functions_well_typed cx` mp_tac >>
  simp[functions_well_typed_def] >>
  disch_then (qspecl_then [`env.fn_sigs`, `env.bare_globals`,
     `env.bare_global_assignable`,`env.toplevel_vtypes`,`env.flag_members`] mp_tac) >>
  impl_tac
  >- (drule env_context_consistent_static_maps_function_side_condition >>
      strip_tac >> gvs[env_context_consistent_def] >>
      rw[] >> first_x_assum drule_all >> simp[]) >>
  rename1 `lookup_callable_function _ _ _ = SOME (mut,nr,args,ds,ret,ss)` >>
  rename1 `get_module_code cx src = SOME ts` >>
  rename1 `lookup_callable_function _ fn ts = _` >>
  disch_then (qspecl_then [`src`,`fn`,`ts`,`mut`,`nr`,`args`,`ds`,`ret`,`ss`] mp_tac) >>
  simp[] >> strip_tac >> goal_assum (drule_at Any)
QED

Theorem len_post_typing[local]:
  expr_body_pre_mods mods cenv cx env e es ==>
  type_widens_to (get_tenv cx) (post_value_type cenv e) (expr_type e) /\
  ?pvt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME pvt
Proof
  strip_tac >> drule_then strip_assume_tac len_child_env >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then strip_assume_tac expr_body_pre_mods_runtime_typing >>
  drule_then strip_assume_tac len_annotation_evaluates >>
  Cases_on `?a fid args drv. e = Call a (IntCall fid) args drv`
  >- (gvs[] >> PairCases_on `fid` >>
      fs[Once well_typed_expr_def, expr_type_def] >>
      rename1 `FLOOKUP env.fn_sigs (src,fn) = SOME sg` >>
      drule_all_then assume_tac expr_sim_inv_mods_return_type >>
      `env_context_consistent env cx` by fs[env_consistent_def] >>
      drule_all_then strip_assume_tac len_signature_evaluates >>
      simp[post_value_type_def, lowered_value_type_def, expr_type_def,
           type_widens_to_def] >>
      Cases_on `is_word_type a \/ is_bytestring_type a` >> gvs[type_widens_to_def]) >>
  `post_value_type cenv e = expr_type e` by metis_tac[post_value_type_not_int_call] >>
  simp[type_widens_to_def]
QED

Theorem len_sim_from_load_mods:
  ^len_suffix ==>
  !exps src tops DF lo d ctx shadow_ctx PG func shadow_func cenv env cx ty ann args es.
    (builtin_args_length_ok Len (LENGTH args) ==>
      body_expr_full_ok_mods mods exps cx (HD args)) /\
    contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    body_const_cells_agree_mods mods cx env es /\
    expr_body_pre_mods mods cenv cx env (Builtin ann Len args) es ==>
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin ann Len args) es /\
    expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin ann Len args) es
Proof
  disch_tac >> rpt gen_tac >> strip_tac >> drule_then strip_assume_tac len_linked_child_pre >> gvs[] >>
  `expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es` by
    (irule len_child_vv >> qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >> simp[]) >>
  conj_asm1_tac >- suspend "value" >>
  irule scalar_stack_vv_sim_full_mods >>
  simp[expr_type_def,is_word_type_def] >> conj_tac
  >- (gen_tac >> simp[compile_expr_len] >>
      Cases_on `compile_expr cenv ty e sa` >> simp[as_stack_val_pair]) >>
  simp[len_source, bind_def, AllCaseEqs(), return_def] >> metis_tac[]
QED

Resume len_sim_from_load_mods[value]:
  rewrite_tac[expr_sim_full_mods_def] >> rpt gen_tac >> strip_tac >>
  drule_all_then strip_assume_tac len_cut >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (qpat_assum `compile_expr cenv ty e sa = _`
      (strip_assume_tac o MATCH_MP compile_expr_extends) >> simp[]) >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    (irule len_child_admissible >> goal_assum (drule_at Any)) >>
  qhdtm_x_assum `expr_vv_sim_full_mods` (mp_tac o REWRITE_RULE [expr_vv_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shm`,`vv`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  irule len_bind_tail >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >>
  BETA_TAC >> suspend "continuation"
QED

Resume len_sim_from_load_mods[continuation]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then strip_assume_tac) >>
  qexists_tac `tv` >> simp[] >>
  qpat_x_assum `res = INL tv` SUBST_ALL_TAC >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  qpat_assum `!tail. eval_expr _ _ _ = _`
    (qspec_then `[]` (mp_tac o SIMP_RULE (srw_ss()) [])) >>
  asm_rewrite_tac[] >> strip_tac >>
  drule_then strip_assume_tac len_post_typing >>
  drule_then strip_assume_tac len_annotation_evaluates >>
  drule_then strip_assume_tac len_child_env >>
  `expr_body_pre_mods mods cenv cx env e
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    simp[len_pre_gas_obs] >>
  drule_all_then strip_assume_tac len_reached_types >>
  qabbrev_tac `explicit = gas_explicit_sites ctx shadow_ctx` >>
  `?n z G2 tn2.
      result_array_length cx tv mid = (INL n,mid) /\
      !H. valid_horizon cx st0 H mid.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G1,tn1) [] (OK z,G2,tn2) /\
        expr_post_mods H ctx func cenv cx (Builtin (BaseT (UintT 256)) Len [e])
          es sa sb s0 mid (IntV (&n)) op z /\
        expr_store_bound cx (BaseT (UintT 256)) (IntV (&n)) op z /\
        z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
        s0.vs_alloca_next <= z.vs_alloca_next /\
        ghost_inv_at_mods (DF H) lo d cenv cx mid G2 tn2 z /\
        ptr_val_ok cx (BaseT (UintT 256)) (IntV (&n)) op G2 tn2 z /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2` by
    (qpat_assum `!DF lo d explicit ctx f PG ce cx env e es st0 sa sm sb s0 G0 tn0 ee tv vv t G tn op pvt tvt. _`
       irule >> simp[] >> conj_tac
     >- (qexistsl_tac [`sm`,`vv`] >> simp[] >> rpt strip_tac >>
         qpat_assum `!H. valid_horizon _ _ H _ ==> _`
           (drule_then strip_assume_tac) >> gvs[]) >>
     qexists_tac `env` >> simp[]) >>
  irule len_pure_tail >> simp[] >>
  qexistsl_tac [`G2`,`tn2`,`z`] >> gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  simp[expr_type_def,is_word_type_def]
QED

Finalise len_sim_from_load_mods
