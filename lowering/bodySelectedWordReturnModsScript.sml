(* A selected internal callee returning one stack word. *)
Theory bodySelectedWordReturnMods
Ancestors
  stmtSimReturn bodyFullPostsMods gasOutcomeFullPostMods stateRelProj
  exprSimWordArgs gasShadowStmtEnv stmtLowering exprLowering compileEnv
  emitHelper emitHelperProps exprLoweringProps loweringStateRelDefs
  stmtSimDefs gasShadowCompileStmtHelpers gasShadowState vyperTypeSystem
  loweringPosts bodyInvSplit fragGasOriginPtr ptrDiscipline venomState
  venomExecSemantics vyperState list rich_list pair fragExec bodyFullShadowBodyInv
  vyperInterpreter vyperStorageFootprint bodyPtrDefs gasOutcome gasContext gasExplicitSites
  gasOutcomeFullMods gasOutcomeFull exprSimDefs gasShadow gasShadowCompileBase
  bodySelectedForcedReturnMods
Libs
  monadsyntax

Theorem word_return_unlock_cut[local]:
  is_word_type ty /\ cenv.ce_return_buf = NONE /\ cenv.ce_returns_count = 1 /\
  compile_internal_return_from_env cenv ty src_ty op rpc sm = ((),sb) ==>
  ?su. compile_return_unlock cenv sm = ((),su) /\
       emit_inst RET [op; rpc] [] su = ((),sb)
Proof
  rpt strip_tac >>
  qpat_x_assum `compile_internal_return_from_env _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_internal_return_from_env_def, compile_internal_return_def,
       word_type_elem_types, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  Cases_on `compile_return_unlock cenv sm` >> rename1 `_ = (u, su)` >>
  Cases_on `u` >> simp[]
QED

Theorem word_return_code_cut[local]:
  cenv.ce_return_pc = SOME (PtrVar (Var rpc) slot_size) /\
  cenv.ce_returns_count = 1 /\ cenv.ce_return_buf = NONE /\
  is_word_type ty /\
  stmt_env cenv lctx ty (Return (SOME e)) sa = (cenv', sb) /\
  fn_has_code sa sb func ==>
  cenv' = cenv /\
  ?op sm su. lower_value compile_expr cenv ty e sa = (op, sm) /\
    compile_return_unlock cenv sm = ((),su) /\
    emit_inst RET [op; Var rpc] [] su = ((),sb) /\
    fn_has_code sa sm func /\ fn_has_code sm su func /\
    fn_has_code su sb func
Proof
  strip_tac >>
  gvs[stmt_env_def, declare_stmt_local_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def, Once compile_stmt_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `lower_value compile_expr cenv ty e sa = (_, sm)` >>
  rename1 `fn_has_code sa sb func` >>
  drule_all word_return_unlock_cut >> strip_tac >>
  qexists_tac `su` >> simp[] >>
  drule compile_return_unlock_shape >> strip_tac >>
  `cs_extends sm su` by
    (irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
  `cs_extends su sb` by metis_tac[cs_extends_emit_inst] >>
  `cs_extends sa sm` by metis_tac[compile_expr_grows] >>
  `cs_extends sm sb` by metis_tac[cs_extends_trans] >>
  qspecl_then [`sa`,`sm`,`sb`,`func`] mp_tac fn_has_code_split >>
  simp[] >> strip_tac >>
  qspecl_then [`sm`,`su`,`sb`,`func`] mp_tac fn_has_code_split >> simp[]
QED

Theorem word_return_operand[local]:
  IS_SOME (type_stmt env ty (Return (SOME e))) /\ is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  expr_post H ctx func cenv cx e es sa sb s0 ee v op s ==>
  eval_operand op s = SOME (typed_val_to_w256 tv v)
Proof
  strip_tac >>
  `expr_type e = ty` by
    (gvs[type_stmt_def, AllCaseEqs()] >>
     metis_tac[type_widens_to_word]) >>
  `post_value_type cenv e = expr_type e` by
    metis_tac[post_value_type_word] >>
  gvs[expr_post_def, expr_val_rel_def]
QED

(* This suffix has one endpoint (including its taint) for all masks. *)
Theorem word_return_suffix_path[local]:
  compile_return_unlock cenv sm = ((),su) /\
  emit_inst RET [op; Var rpc] [] su = ((),sb) /\
  fn_has_code sm su func /\ fn_has_code su sb func /\
  eval_operand op s = SOME w /\ lookup_var rpc s = SOME pc /\
  op_taint tn op = {} /\ op_taint tn (Var rpc) = {} /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ((FST cenv.ce_nonreentrant /\ ~SND (SND (SND cenv.ce_nonreentrant))) ==>
    ~s.vs_call_ctx.cc_static) /\ allocas_from lo s /\
  ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?tf. tf.t_mem = tn.t_mem /\
    (((FST cenv.ce_nonreentrant /\ ~SND (SND (SND cenv.ce_nonreentrant))) ==>
       FST (SND (SND cenv.ce_nonreentrant))) ==>
      tf.t_stor = tn.t_stor /\ tf.t_trans SUBSET tn.t_trans /\
      tf.t_imm = tn.t_imm) /\
    !D. gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (s, G, tn) []
      (IntRet <| iret_values := [w]; iret_adopt_fmp := NONE |>
         (return_unlock_state cenv s), G, tf)
Proof
  strip_tac >>
  mp_tac (Q.INST [`sa` |-> `sm`] (SPEC_ALL return_unlock_origin_ptr_taint)) >>
  impl_tac >- simp[] >> strip_tac >>
  qexists_tac `tn'` >> simp[] >> gen_tac >>
  drule compile_return_unlock_shape >> strip_tac >>
  qabbrev_tac `s1 = return_unlock_state cenv s` >>
  `lookup_var rpc s1 = SOME pc /\ eval_operand op s1 = SOME w /\
   allocas_from lo s1 /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp s1) /\ ~s1.vs_halted /\
   s1.vs_current_bb = su.cs_current_bb /\
   s1.vs_inst_idx = LENGTH su.cs_current_insts` by
    (fs[Abbr `s1`, lookup_var_def, eval_operand_return_unlock] >>
     qspecl_then [`cenv`, `s`, `sm.cs_next_id`] strip_assume_tac
       return_unlock_state_frames >>
     simp[allocas_from_def] >> metis_tac[allocas_from_def]) >>
  `op_taint tn' op = {} /\ op_taint tn' (Var rpc) = {}` by
    (Cases_on `op` >> fs[op_taint_def]) >>
  `gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (s1, G, tn') []
     (IntRet <| iret_values := [w]; iret_adopt_fmp := NONE |> s1, G, tn')` by
    (irule (Q.INST [`ops` |-> `[op]`] emitted_ret_origin_ptr) >>
     simp[eval_operands_def] >>
     qexistsl_tac [`op`, `pc`, `rpc`, `su`, `sb`] >> simp[]) >>
  metis_tac[gas_origin_ptr_path_append, APPEND_NIL]
QED

Theorem word_return_immutable_frame[local]:
  immutable_frame_mods func cenv cx ee s ==>
  immutable_frame_mods func cenv cx (ee with <|scopes := []; gas_obs := tail|>)
    (return_unlock_state cenv s)
Proof
  `(return_unlock_state cenv s).vs_memory = s.vs_memory /\
   (return_unlock_state cenv s).vs_data_section = s.vs_data_section /\
   (return_unlock_state cenv s).vs_allocas = s.vs_allocas /\
   (return_unlock_state cenv s).vs_alloca_next = s.vs_alloca_next` by
    (qabbrev_tac `info = cenv.ce_nonreentrant` >> PairCases_on `info` >>
     Cases_on `info0` >> Cases_on `info2` >> Cases_on `info3` >>
     gvs[return_unlock_state_def, tstore_def, sstore_def]) >>
  simp[immutable_frame_mods_def, immutables_rel_mods_def,
       immutable_alloca_sep_mods_def, immutables_rel_def,
       immutable_alloca_sep_def, immutable_decl_sep_def, local_region_def,
       lookup_scopes_def] >>
  strip_tac >> conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!src tops. ALOOKUP _ src = SOME tops ==> _ /\ _`
    (drule_then strip_assume_tac) >>
  Cases_on `cenv.ce_is_ctor` >> fs[] >> metis_tac[]
QED

val selected_unlock_taint =
  ``!(H : (bool # bytes32 # type_value) list # num list) D lo ce cx tf tn d ee G s.
      dead_lo_ok_mods H D lo ce cx /\
      ((FST ce.ce_nonreentrant /\ ~SND (SND (SND ce.ce_nonreentrant))) ==>
       FST (SND (SND ce.ce_nonreentrant))) /\
      tf.t_stor = tn.t_stor /\ tf.t_trans SUBSET tn.t_trans /\
      tf.t_imm = tn.t_imm /\ tf.t_mem = tn.t_mem /\
      ghost_inv_at_mods D lo d ce cx ee G tn s ==>
      stor_taint_ok_at D tf (return_unlock_state ce s) /\
      (!i. i < lo /\ i IN tf.t_mem ==>
         imm_section_dead_mods ce (mem_bytes_at 0 lo (return_unlock_state ce s).vs_memory) i)``;

Theorem word_return_reached_suffix[local]:
  ^selected_unlock_taint /\
  cenv.ce_return_pc = SOME (PtrVar (Var rpc) slot_size) /\
  cenv.ce_returns_count = 1 /\
  ((FST cenv.ce_nonreentrant /\ ~SND (SND (SND cenv.ce_nonreentrant))) ==>
    ~cx.txn.is_static /\ FST (SND (SND cenv.ce_nonreentrant))) /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  IS_SOME (type_stmt env ty (Return (SOME e))) /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  compile_return_unlock cenv sm = ((),su) /\
  emit_inst RET [op; Var rpc] [] su = ((),sb) /\
  fn_has_code sm su func /\ fn_has_code su sb func /\
  ret_pc_ok cenv sa s0 /\
  storage_trace_domain cx st0 mid.storage_trace /\ ~t.vs_halted /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post_mods H ctx func cenv cx e es sa sm s0 mid v op t /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid G1 tn1 t /\
    ptr_val_ok cx (post_value_type cenv e) v op G1 tn1 t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts) ==>
  gas_outcome_full_mods (DF, lo, explicit, ctx, func, PG)
    cenv.ce_modules cx st0 (raise (ReturnException v)) (mid,t,G1,tn1) Q
    (\H res ee gt r.
      (!tail. stmt_exit_ptr
        (\v ee gt r. intret_q H func cenv cx tv v ee r /\
          !ir u. r = IntRet ir u ==>
            immutable_frame_mods func cenv cx (ee with scopes := []) u /\
            stor_taint_ok_at (DF H) (SND gt) u /\
            (!i. i < lo /\ i IN (SND gt).t_mem ==>
              imm_section_dead_mods cenv (mem_bytes_at 0 lo u.vs_memory) i))
        (ee with gas_obs := tail) res gt r) /\
      halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==>
       !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
Proof
  strip_tac >>
  qpat_assum `storage_trace_domain _ _ _` (assume_tac o REWRITE_RULE [storage_trace_domain_def]) >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qhdtm_assum `expr_post_mods`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  `eval_operand op t = SOME (typed_val_to_w256 tv v)` by
    (drule_all word_return_operand >> simp[]) >>
  `?pc. lookup_var rpc t = SOME pc` by
    (fs[ret_pc_ok_def, expr_post_def] >> metis_tac[]) >>
  `op_taint tn1 op = {} /\ op_taint tn1 (Var rpc) = {} /\ allocas_from lo t` by
    fs[ptr_val_ok_def, ghost_inv_at_mods_def] >>
  `((FST cenv.ce_nonreentrant /\ ~SND (SND (SND cenv.ce_nonreentrant))) ==>
    ~t.vs_call_ctx.cc_static)` by
    (fs[expr_post_def] >>
     drule stmt_state_rel_state_rel >> disch_then (mp_tac o MATCH_MP state_rel_call_ctx_rel) >>
     simp[call_ctx_rel_def]) >>
  drule_all word_return_suffix_path >>
  disch_then (strip_assume_tac o Q.INST [`tn` |-> `tn1`, `G` |-> `G1`] o SPEC_ALL) >>
  irule gas_outcome_full_mods_exit >> simp[] >>
  qexistsl_tac [`G1`, `mid`,
    `IntRet <|iret_values := [typed_val_to_w256 tv v]; iret_adopt_fmp := NONE|>
      (return_unlock_state cenv t)`, `INR (ReturnException v)`, `tf`] >>
  simp[raise_def, exit_result_def, halt_exit_def] >>
  rpt strip_tac >>
  simp[stmt_exit_ptr_def] >> disj2_tac >>
  conj_tac
  >- (irule intret_q_intro >> simp[result_rel_def] >>
      qexists_tac `t` >> simp[] >>
      conj_tac
      >- (`mid with <|scopes := []; gas_obs := tail|> =
           (mid with scopes := []) with gas_obs := tail` by simp[] >>
          pop_assum SUBST1_TAC >> REWRITE_TAC [state_rel_gas_obs] >>
          irule state_rel_scopes_nil >>
          qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
            (drule_then strip_assume_tac) >>
          fs[expr_post_mods_def, expr_post_def] >>
          drule_then ACCEPT_TAC stmt_state_rel_state_rel) >>
      drule_all intret_vals_match_word >> simp[]) >>
  conj_tac
  >- (simp[] >> drule_then (qspec_then `tail` mp_tac) word_return_immutable_frame >> simp[]) >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `tf.t_stor = tn1.t_stor /\ tf.t_trans SUBSET tn1.t_trans /\ tf.t_imm = tn1.t_imm` by metis_tac[] >>
  conj_tac
  >- (qpat_assum `!H D lo ce cx tf tn d ee G s. _`
        (irule o cj 1) >>
      conj_tac >- metis_tac[] >>
      qpat_assum `ghost_inv_at_mods (DF H) _ _ _ _ _ _ _ _` (irule_at Any) >>
      qexists_tac `H` >> simp[]) >>
  fs[ghost_inv_at_mods_def]
QED

Theorem word_return_paired_cut[local]:
  cenv.ce_return_pc = SOME (PtrVar (Var rpc) slot_size) /\
  cenv.ce_returns_count = 1 /\ cenv.ce_return_buf = NONE /\
  is_word_type ty /\
  stmt_env cenv lctx ty (Return (SOME e)) sa = (ce',sb) /\
  stmt_env (gas_shadow_env T cenv) lctx ty (gas_shadow_stmt (Return (SOME e))) sha =
    (gas_shadow_env T ce',shb) /\
  gas_shadow_state sa sha /\ fn_has_code sa sb func /\ fn_has_code sha shb shadow_func ==>
  ?op sm shm.
    lower_value compile_expr cenv ty e sa = (op,sm) /\
    lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) sha = (op,shm) /\
    gas_shadow_state sm shm /\ fn_has_code sa sm func /\ fn_has_code sha shm shadow_func /\
    ?su. compile_return_unlock cenv sm = ((),su) /\
      emit_inst RET [op; Var rpc] [] su = ((),sb) /\
      fn_has_code sm su func /\ fn_has_code su sb func
Proof
  strip_tac >> drule_all word_return_code_cut >> strip_tac >>
  `?shadow_op shm.
     lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) sha =
       (shadow_op,shm) /\ fn_has_code sha shm shadow_func` by
    (qpat_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _`
       (assume_tac o REWRITE_RULE [gas_shadow_stmt_def, optionTheory.OPTION_MAP_DEF]) >>
     `(gas_shadow_env T cenv).ce_return_pc = SOME (PtrVar (Var rpc) slot_size) /\
      (gas_shadow_env T cenv).ce_returns_count = 1 /\
      (gas_shadow_env T cenv).ce_return_buf = NONE` by simp[gas_shadow_env_def] >>
     drule_all (Q.INST [`cenv` |-> `gas_shadow_env T cenv`] word_return_code_cut) >>
     metis_tac[]) >>
  `op = shadow_op /\ gas_shadow_state sm shm` by
    (mp_tac (Q.INST [`sd` |-> `T`] gas_shadow_stmt_lower_value_env) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`sha`] mp_tac) >> simp[]) >>
  qpat_x_assum `op = shadow_op` SUBST_ALL_TAC >>
  qexistsl_tac [`shadow_op`,`sm`,`shm`] >> simp[]
QED

Theorem selected_word_return_frag_mods:
  ^selected_unlock_taint /\
  cenv.ce_return_pc = SOME (PtrVar (Var rpc) slot_size) /\
  cenv.ce_returns_count = 1 /\ cenv.ce_return_buf = NONE /\
  ((FST cenv.ce_nonreentrant /\ ~SND (SND (SND cenv.ce_nonreentrant))) ==>
    ~cx.txn.is_static /\ FST (SND (SND cenv.ce_nonreentrant))) /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  IS_SOME (type_stmt env ty (Return (SOME e))) /\
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es ==>
  stmt_frag_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx lctx
    (\H v ee gt r. intret_q H func cenv cx tv v ee r /\
      !ir u. r = IntRet ir u ==>
        immutable_frame_mods func cenv cx (ee with scopes := []) u /\
        stor_taint_ok_at (DF H) (SND gt) u /\
        (!i. i < lo /\ i IN (SND gt).t_mem ==>
          imm_section_dead_mods cenv (mem_bytes_at 0 lo u.vs_memory) i))
    cenv (stmt_env cenv lctx ty (Return (SOME e)))
    (stmt_env (gas_shadow_env T cenv) lctx ty (Return (SOME (gas_shadow_expr e))))
    (eval_stmt cx (Return (SOME e))) es
Proof
  strip_tac >>
  irule (SIMP_RULE bool_ss [LET_THM] selected_forced_return_frag_mods) >>
  reverse conj_tac >- simp[] >>
  qexists `\sa sb sha shb op sm shm.
    ?su. compile_return_unlock cenv sm = ((),su) /\
         emit_inst RET [op; Var rpc] [] su = ((),sb) /\
         fn_has_code sm su func /\ fn_has_code su sb func` >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> drule_all word_return_paired_cut >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  irule word_return_reached_suffix >>
  qpat_assum `emit_inst RET _ [] _ = _` (irule_at Any) >>
  qpat_assum `ret_pc_ok cenv sa s0` (irule_at Any) >>
  qpat_assum `IS_SOME (type_stmt env ty (Return (SOME e)))` (irule_at Any) >>
  qpat_assum `compile_return_unlock cenv sm = _` (irule_at Any) >>
  qpat_assum `cenv.ce_return_pc = SOME (PtrVar (Var rpc) _)` (irule_at Any) >>
  qexistsl_tac [`es`,`d`] >> asm_rewrite_tac[] >>
  rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >> simp[]
QED
