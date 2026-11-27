(* A present proxy salt executes at the already framed buffer endpoint. *)
Theory bodyCreateProxySaltCutMods
Ancestors
  bodyCreateOperandCutMods bodyCreateOperandPreMods
  bodyFullPredsMods bodyFullPostsMods exprBodyPreProps
  exprSimWordArgs exprSimPrecompiles exprLoweringProps loweringShapeDefs
  wordArgsPtr abiValueEncoding vyperCreate vyperValue vyperTypeExprResult
  vyperTypeExprSoundness vyperTypeInvariants vyperStorageTrace
  vyperStorageFootprint loweringPosts bodyPtrDefs gasOutcomeFullMods
  vyperAST vyperState vyperTypeSystem vyperTyping compileEnv list

Theorem proxy_salt_singleton_bind[local]:
  bind (eval_exprs cx [salt]) k =
    bind (bind (eval_expr cx salt) (read_result cx)) (\v. k [v])
Proof
  `eval_exprs cx [] = return []` by simp[FUN_EQ_THM,eval_exprs_nil,return_def] >>
  once_rewrite_tac[eval_exprs_cons_action] >> simp[bind_assoc,bind_return]
QED

Theorem proxy_salt_word[local]:
  value_has_type (BaseTV (BytesT (Fixed 32))) v ==>
  dest_create_salt v = SOME (typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) v)
Proof
  Cases_on `v` >>
  simp[value_has_type_def,dest_create_salt_def,dest_BytesV_def,
       valueEncodingTheory.typed_val_to_w256_def,PAD_RIGHT]
QED

val exit = ``\(H:(bool # 256 word # type_value) list # num list)
  (res:value + exception) ee (gt:(string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z)``;

Theorem create_proxy_salt_cut_mods:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  expr_body_pre_mods mods cenv cx env
    (Call ann (CreateTarget CreateMinimalProxy T rof ks) args dflt) es /\
  MEM salt args /\ expr_type salt = BaseT (BytesT (Fixed 32)) /\
  body_exprs_full_ok_mods mods exps cx [salt] /\
  body_const_cells_agree_mods mods cx env ea /\ expr_sim_inv_mods mods cenv cx env ea /\
  lower_value compile_expr cenv (expr_type salt) salt c = (q,sd) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type salt)
    (gas_shadow_expr salt) ch = (q,sdh) /\
  gas_shadow_state c ch /\ gas_shadow_state sd sdh /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code c sd func /\ fn_has_code ch sdh shadow_func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= c.cs_next_var /\ sa.cs_next_id <= c.cs_next_id /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at c x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at c x) /\
  return_buf_frame d cenv c u /\ alloca_history func u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  (!fn i z. frag_reachable ctx func u fn i z ==> dalloca_fmp_headroom i z) /\
  ~u.vs_halted /\ u.vs_current_bb = c.cs_current_bb /\ u.vs_inst_idx = LENGTH c.cs_current_insts /\
  storage_trace_domain cx st0 ea.storage_trace /\
  (!H. valid_horizon cx st0 H ea.storage_trace ==> valid_horizon cx st0 H es.storage_trace) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
  (!H. valid_horizon cx st0 H ea.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ea u /\ immutable_frame_mods func cenv cx ea u /\
    storage_well_formed_on cx ea (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ea Gu tu u) /\
  wb_frame cenv es ea sa s0 u /\ ghost_kept_at lo cenv es sa G0 tn0 s0 Gu tu /\
  s0.vs_alloca_next <= u.vs_alloca_next /\ (!vs. storage_trace_frame (k vs)) /\
  (!sv sw ew Gend tt t.
    dest_create_salt sv = SOME sw /\ eval_operand q t = SOME sw /\ op_taint tt q = {} /\
    wb_frame cenv ea ew c u t /\ ghost_kept_at lo cenv ea c Gu tu u Gend tt /\
    wb_frame cenv es ew sa s0 t /\ ghost_kept_at lo cenv es sa G0 tn0 s0 Gend tt /\
    u.vs_alloca_next <= t.vs_alloca_next /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    body_const_cells_agree_mods mods cx env ew /\ expr_sim_inv_mods mods cenv cx env ew /\
    storage_trace_domain cx st0 ew.storage_trace /\
    (!H. valid_horizon cx st0 H ew.storage_trace ==>
      valid_horizon cx st0 H es.storage_trace /\ stmt_state_rel H ctx func cenv cx ew t /\
      immutable_frame_mods func cenv cx ew t /\ storage_well_formed_on cx ew (FST H) /\
      ghost_inv_at_mods (DF H) lo d cenv cx ew Gend tt t) /\
    local_ptrs_reserved cenv sd /\ sa.cs_next_var <= sd.cs_next_var /\
    (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sd x) /\
    (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sd x) /\
    return_buf_frame d cenv sd t /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!fn i z. frag_reachable ctx func t fn i z ==> dalloca_fmp_headroom i z) /\
    ~t.vs_halted /\ t.vs_current_bb = sd.cs_current_bb /\
    t.vs_inst_idx = LENGTH sd.cs_current_insts ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 (k [sv]) (ew,t,Gend,tt) Q ^exit) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (eval_exprs cx [salt]) k) (ea,u,Gu,tu) Q ^exit
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre_mods mods cenv cx env salt ea` by
    (irule create_operand_pre_mods >>
     qpat_assum `expr_body_pre_mods _ _ _ _ (Call _ _ _ _) _` (irule_at Any) >> simp[]) >>
  qpat_x_assum `body_exprs_full_ok_mods _ _ _ [salt]`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_exprs_full_ok_mods_def]) >>
  `local_ptrs_reserved cenv c` by drule_all_then ACCEPT_TAC local_ptrs_reserved_next_var >>
  rewrite_tac[proxy_salt_singleton_bind] >>
  irule create_body_operand_cut_replay_mods >> BETA_TAC >>
  asm_rewrite_tac[] >>
  qexistsl_tac [`d`,`env`,`exps`,`mods`,`q`,`c`,`sd`,`ch`,`shadow_func`,`sdh`,`src`,`tops`] >>
  asm_rewrite_tac[] >>
  reverse conj_tac
  >- (qpat_assum `expr_type salt = _` (fn th => once_rewrite_tac [GSYM th]) >>
      asm_rewrite_tac[]) >>
  qx_genl_tac [`sv`,`ew`,`Gend`,`tt`,`t`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "word_and_frame"
QED

Resume create_proxy_salt_cut_mods[word_and_frame]:
  `valid_horizon cx st0 (storage_trace_horizon ew.storage_trace) ew.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. _ ==> expr_post_mods H _ _ _ _ salt _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `expr_post_mods _ _ _ _ _ salt _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  drule_then assume_tac expr_post_frame >>
  `evaluate_type (get_tenv cx) (expr_type salt) = SOME (BaseTV (BytesT (Fixed 32))) /\
   is_word_type (expr_type salt)` by simp[evaluate_type_def,is_word_type_def] >>
  `value_has_type (BaseTV (BytesT (Fixed 32))) sv` by
    (qpat_assum `expr_result_typed _ _ _` (mp_tac o REWRITE_RULE
       [expr_result_typed_def,expr_runtime_typed_def,value_result_typed_def]) >>
     simp[evaluate_type_def]) >>
  drule_all_then assume_tac expr_post_typed_stack_operand >>
  `op_taint tt q = {}` by fs[ptr_val_ok_def,post_value_type_def,is_word_type_def] >>
  suspend "join"
QED

Resume create_proxy_salt_cut_mods[join]:
  `valid_horizon cx st0 (storage_trace_horizon ea.storage_trace) ea.storage_trace` by
    fs[storage_trace_domain_def] >>
  `stmt_state_rel (storage_trace_horizon ea.storage_trace) ctx func cenv cx es s0` by
    (qpat_assum `!H. _ ==> stmt_state_rel H _ _ _ _ es s0` irule >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM ea.scopes` by fs[wb_frame_def,locals_kept_def] >>
  `wb_frame cenv es ew sa s0 t` by
    (irule (INST_TYPE [alpha |-> ``:256``] wb_frame_trans) >> asm_rewrite_tac[] >>
     conj_tac >- (qexistsl_tac [`ea`,`c`,`u`] >> asm_rewrite_tac[]) >>
     qexistsl_tac [`storage_trace_horizon ea.storage_trace`,`ctx`,`cx`,`func`] >> first_assum ACCEPT_TAC) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gend tt` by
    (irule (INST_TYPE [beta |-> ``:256``] ghost_kept_at_wb_trans) >>
     qpat_assum `stmt_state_rel _ _ _ _ _ es s0` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 Gu tu` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo cenv ea c Gu tu u Gend tt` (irule_at Any) >>
     qexists_tac `ea` >> simp[]) >>
  suspend "finish"
QED

Resume create_proxy_salt_cut_mods[finish]:
  `ci_mono c sd` by
    (qspecl_then [`cenv`,`expr_type salt`,`salt`,`c`] mp_tac ci_mono_lower_value_compile_expr >> simp[]) >>
  `c.cs_next_var <= sd.cs_next_var` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv sd` by drule_all_then ACCEPT_TAC local_ptrs_reserved_next_var >>
  `sa.cs_next_var <= sd.cs_next_var /\ s0.vs_alloca_next <= t.vs_alloca_next` by decide_tac >>
  `!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sd x` by
    metis_tac[not_fresh_at_mono] >>
  `!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sd x` by
    metis_tac[not_fresh_at_mono] >>
  qpat_assum `!sv sw ew Gend tt t. _ ==> gas_outcome_full_mods _ _ _ _ (k [sv]) _ _ _` irule >>
  simp[proxy_salt_word] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. _ ==> expr_post_mods H _ _ _ _ salt _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  fs[expr_post_mods_def,expr_post_def]
QED

Finalise create_proxy_salt_cut_mods
