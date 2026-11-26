(* Reached target and amount of a minimal proxy, before any buffer writes. *)
Theory bodyCreateProxyOperandsMods
Ancestors
  bodyCreateOperandCutMods bodyCreateOperandPreMods bodyFullPredsMods
  bodyFullPostsMods exprBodyPreProps exprSimWordArgs exprSimPrecompiles
  abiValueEncoding exprWordOperand exprSimSend exprLoweringProps abiEncodeArgsSim
  emittedSeqComposePtr wordArgsPtr builtinCreate vyperCreate
  vyperTypeEvalCaseProofs vyperTypeExprResult vyperTypeExprSoundness
  vyperTypeInvariants vyperStorageTrace loweringPosts list
  vyperStorageFootprint vyperTypeSystem exprSimSource bodyPtrDefs vyperTyping
  vyperState compileEnv exprLowering loweringShapeDefs gasShadow

Triviality proxy_operand_word:
  expr_body_pre_mods mods cenv cx env e es /\ expr_result_typed env e (Value v) /\
  expr_type e = BaseT bt /\ is_word_type (BaseT bt) /\
  lower_value compile_expr cenv (expr_type e) e sa = (op,sb) /\
  ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post_mods H ctx func cenv cx e es sa sb s ee v op t) ==>
  value_has_type (BaseTV bt) v /\
  eval_operand op t = SOME (typed_val_to_w256 (BaseTV bt) v) /\
  op_taint tn op = {} /\ (!x. op = Var x ==> not_fresh_at sb x) /\ (!l. op <> Label l) /\
  wb_frame cenv es ee sa s t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v` by
    fs[expr_result_typed_def,expr_runtime_typed_def,value_result_typed_def] >>
  `tv = BaseTV bt` by metis_tac[evaluate_type_base_result] >>
  `is_word_type (expr_type e)` by simp[] >>
  `!id ty. FLOOKUP env.var_types id = SOME ty ==> well_formed_type (get_tenv cx) ty` by
    (simp[well_formed_type_def] >> rpt strip_tac >>
     drule_all env_consistent_var_type_evaluates >> simp[]) >>
  drule lower_value_word_shape >> disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. _ ==> expr_post_mods H _ _ _ _ e _ _ _ _ _ _ _ _`
    (drule_then assume_tac) >>
  fs[expr_post_mods_def,ptr_val_ok_def] >>
  drule_then assume_tac expr_post_frame >>
  drule_all_then assume_tac expr_post_typed_stack_operand >> simp[]
QED

Triviality proxy_operand_frames:
  stmt_state_rel (H:(bool # 256 word # type_value) list # num list) ctx func cenv cx es s /\
  local_ptrs_reserved cenv sa /\ ci_mono sa sm /\
  wb_frame cenv es em sa s m /\ wb_frame cenv em ee sm m t /\
  ghost_kept_at lo cenv es sa G tn s Gm tm /\ ghost_kept_at lo cenv em sm Gm tm m G1 tn1 /\
  (!x. op = Var x ==> not_fresh_at sm x) /\ (!l. op <> Label l) /\
  eval_operand op m = SOME w /\ op_taint tm op = {} ==>
  wb_frame cenv es ee sa s t /\ ghost_kept_at lo cenv es sa G tn s G1 tn1 /\
  eval_operand op t = SOME w /\ op_taint tn1 op = {}
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `MAP FDOM es.scopes = MAP FDOM em.scopes` by fs[wb_frame_def,locals_kept_def] >>
  fs[ci_mono_def] >> conj_asm1_tac
  >- (irule (INST_TYPE [alpha |-> ``:256``] wb_frame_trans) >>
      asm_rewrite_tac[] >> conj_tac
      >- (qexistsl_tac [`em`,`sm`,`m`] >> asm_rewrite_tac[]) >>
      qexistsl_tac [`H`,`ctx`,`cx`,`func`] >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (irule (INST_TYPE [beta |-> ``:256``] ghost_kept_at_wb_trans) >>
      qpat_assum `stmt_state_rel _ _ _ _ _ es s` (irule_at Any) >>
      qpat_assum `ghost_kept_at lo cenv es sa G tn s Gm tm` (irule_at Any) >>
      qpat_assum `ghost_kept_at lo cenv em sm Gm tm m G1 tn1` (irule_at Any) >>
      qexists_tac `em` >> simp[]) >>
  drule_all_then assume_tac abi_args_operand_kept >> simp[] >>
  `op_taint tn1 op = op_taint tm op` suffices_by simp[] >>
  irule old_operand_taint_frame >> qexists_tac `sm` >> fs[ghost_kept_at_def]
QED

val exit = ``\(H:(bool # 256 word # type_value) list # num list)
  (res:value + exception) ee (gt:(string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)``;

Theorem create_proxy_target_amount_cut_mods:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\ body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env
    (Call ann (CreateTarget CreateMinimalProxy salted rof ks) (target::amount::salts) dflt) es /\
  body_exprs_full_ok_mods mods exps cx (target::amount::salts) /\
  expr_type target = BaseT AddressT /\ expr_type amount = BaseT (UintT 256) /\
  lower_value compile_expr cenv (expr_type target) target sa = (x,a) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type target)
    (gas_shadow_expr target) sha = (x,ah) /\
  lower_value compile_expr cenv (expr_type amount) amount a = (y,b) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type amount)
    (gas_shadow_expr amount) ah = (y,bh) /\
  gas_shadow_state sa sha /\ gas_shadow_state a ah /\ gas_shadow_state b bh /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  fn_has_code sa a func /\ fn_has_code a b func /\
  fn_has_code sha ah shadow_func /\ fn_has_code ah bh shadow_func /\
  ci_mono sa a /\ ci_mono a b /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn i z. frag_reachable ctx func s0 fn i z ==> dalloca_fmp_headroom i z) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!vs. storage_trace_frame (next vs)) /\
  (!tv av tw aw ea Gm tm m.
    body_exprs_full_ok_mods mods exps cx salts /\
    dest_AddressV tv = SOME (w2w tw) /\ dest_NumV av = SOME (w2n aw) /\
    eval_operand x m = SOME tw /\ op_taint tm x = {} /\
    eval_operand y m = SOME aw /\ op_taint tm y = {} /\
    (!z. x = Var z ==> not_fresh_at b z) /\ (!l. x <> Label l) /\
    (!z. y = Var z ==> not_fresh_at b z) /\ (!l. y <> Label l) /\
    wb_frame cenv es ea sa s0 m /\ ghost_kept_at lo cenv es sa G0 tn0 s0 Gm tm /\
    expr_sim_inv_mods mods cenv cx env ea /\ body_const_cells_agree_mods mods cx env ea /\
    s0.vs_alloca_next <= m.vs_alloca_next /\ alloca_history func m /\
    return_buf_frame d cenv b m /\ (ctx_has_dalloca ctx ==> allocas_below_fmp m) /\
    (!fn i z. frag_reachable ctx func m fn i z ==> dalloca_fmp_headroom i z) /\
    ~m.vs_halted /\ m.vs_current_bb = b.cs_current_bb /\ m.vs_inst_idx = LENGTH b.cs_current_insts /\
    storage_trace_domain cx st0 ea.storage_trace /\
    (!H. valid_horizon cx st0 H ea.storage_trace ==>
      valid_horizon cx st0 H es.storage_trace /\ stmt_state_rel H ctx func cenv cx ea m /\
      immutable_frame_mods func cenv cx ea m /\ storage_well_formed_on cx ea (FST H) /\
      ghost_inv_at_mods (DF H) lo d cenv cx ea Gm tm m) ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 (bind (eval_exprs cx salts) (\vs. next (tv::av::vs)))
      (ea,m,Gm,tm) Q ^exit) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (eval_exprs cx (target::amount::salts)) next)
    (es,s0,G0,tn0) Q ^exit
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre_mods mods cenv cx env target es` by
    (irule create_operand_pre_mods >>
     qpat_assum `expr_body_pre_mods _ _ _ _ (Call _ _ _ _) _` (irule_at Any) >>
     simp[] >> drule_then ACCEPT_TAC expr_body_pre_mods_inv) >>
  qpat_x_assum `body_exprs_full_ok_mods _ _ _ (target::_)`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_exprs_full_ok_mods_def]) >>
  once_rewrite_tac[eval_exprs_cons_action] >>
  simp[NoAsms,bind_assoc,bind_return] >> once_rewrite_tac[GSYM bind_assoc] >>
  irule create_body_operand_cut_replay_mods >> BETA_TAC >>
  asm_rewrite_tac[] >> conj_tac
  >- simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame] >>
  qexistsl_tac [`d`,`env`,`exps`,`mods`,`x`,`sa`,`a`,`sha`,`shadow_func`,`ah`,`src`,`tops`] >>
  asm_rewrite_tac[] >> reverse conj_tac
  >- (qpat_assum `expr_type target = _` (fn th => once_rewrite_tac [GSYM th]) >>
      asm_rewrite_tac[]) >>
  suspend "target_landing"
QED

Resume create_proxy_target_amount_cut_mods[target_landing]:
  map_every qx_gen_tac [`tv`,`et`,`Gaddr`,`tt`,`t`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `body_exprs_full_ok_mods mods exps cx (amount::salts)` by
    (qpat_assum `_ ==> body_exprs_full_ok_mods _ _ _ (amount::salts)` drule >> simp[]) >>
  qpat_x_assum `body_exprs_full_ok_mods _ _ _ (amount::_)`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_exprs_full_ok_mods_def]) >>
  `expr_body_pre_mods mods cenv cx env amount et` by
    (irule create_operand_pre_mods >>
     qpat_assum `expr_body_pre_mods _ _ _ _ (Call _ _ _ _) _` (irule_at Any) >> simp[]) >>
  `sa.cs_next_var <= a.cs_next_var` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv a` by drule_all_then ACCEPT_TAC local_ptrs_reserved_next_var >>
  `!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at a z` by
    metis_tac[not_fresh_at_mono] >>
  `!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at a z` by
    metis_tac[not_fresh_at_mono] >>
  `!H. valid_horizon cx st0 H et.storage_trace ==>
    stmt_state_rel H ctx func cenv cx et t /\ immutable_frame_mods func cenv cx et t /\
    storage_well_formed_on cx et (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx et Gaddr tt t` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H et.storage_trace ==> expr_post_mods _ _ _ _ _ target _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> fs[expr_post_mods_def,expr_post_def]) >>
  once_rewrite_tac[eval_exprs_cons_action] >>
  simp[NoAsms,bind_assoc,bind_return] >> once_rewrite_tac[GSYM bind_assoc] >>
  irule create_body_operand_cut_replay_mods >> BETA_TAC >>
  asm_rewrite_tac[] >> conj_tac
  >- simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame] >>
  qexistsl_tac [`d`,`env`,`exps`,`mods`,`y`,`a`,`b`,`ah`,`shadow_func`,`bh`,`src`,`tops`] >>
  asm_rewrite_tac[] >> reverse conj_tac
  >- (qpat_assum `expr_type amount = _` (fn th => once_rewrite_tac [GSYM th]) >>
      asm_rewrite_tac[]) >>
  suspend "amount_landing"
QED

Resume create_proxy_target_amount_cut_mods[amount_landing]:
  map_every qx_gen_tac [`av`,`ea`,`Gm`,`tm`,`m`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `body_exprs_full_ok_mods mods exps cx salts` by
    (qpat_assum `_ ==> body_exprs_full_ok_mods _ _ _ salts` drule >> simp[]) >>
  `is_word_type (BaseT AddressT) /\ is_word_type (BaseT (UintT 256))` by simp[is_word_type_def] >>
  `!H. valid_horizon cx st0 H et.storage_trace ==>
      expr_post_mods H ctx func cenv cx target es sa a s0 et tv x t` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H et.storage_trace ==> expr_post_mods _ _ _ _ _ target _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H ea.storage_trace ==>
      expr_post_mods H ctx func cenv cx amount et a b t ea av y m` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H ea.storage_trace ==> expr_post_mods _ _ _ _ _ amount _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  qpat_assum `lower_value compile_expr cenv (expr_type target) target sa = _`
    (mp_then Any (drule_all_then strip_assume_tac) proxy_operand_word) >>
  qpat_assum `lower_value compile_expr cenv (expr_type amount) amount a = _`
    (mp_then Any (drule_all_then strip_assume_tac) proxy_operand_word) >>
  qabbrev_tac `tw = typed_val_to_w256 (BaseTV AddressT) tv` >>
  qabbrev_tac `aw = typed_val_to_w256 (BaseTV (UintT 256)) av` >>
  `dest_AddressV tv = SOME (w2w tw)` by simp[Abbr `tw`,address_typed_dest] >>
  `dest_NumV av = SOME (w2n aw)` by simp[Abbr `aw`,uint256_typed_dest] >>
  `valid_horizon cx st0 (storage_trace_horizon et.storage_trace) et.storage_trace`
    by fs[storage_trace_domain_def] >>
  `valid_horizon cx st0 (storage_trace_horizon et.storage_trace) es.storage_trace` by simp[] >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `eval_operand x t = SOME tw`
    (mp_then Any (drule_all_then strip_assume_tac) proxy_operand_frames) >>
  `!z. x = Var z ==> not_fresh_at b z` by metis_tac[ci_mono_def,not_fresh_at_mono] >>
  `s0.vs_alloca_next <= m.vs_alloca_next` by decide_tac >>
  suspend "amount_next"
QED

Resume create_proxy_target_amount_cut_mods[amount_next]:
  qpat_assum `!tv av tw aw ea Gm tm m. _ ==> gas_outcome_full_mods _ _ _ _ _ _ _ _` irule >>
  asm_rewrite_tac[] >>
  conj_tac >- (gen_tac >> disch_tac >>
    qpat_assum `!H. valid_horizon _ _ H ea.storage_trace ==> expr_post_mods _ _ _ _ _ amount _ _ _ _ _ _ _ _ /\ _`
      (drule_then strip_assume_tac) >>
    `valid_horizon cx st0 H et.storage_trace` by simp[] >>
    fs[expr_post_mods_def,expr_post_def]) >>
  conj_tac >- (qexists_tac `tw` >> asm_rewrite_tac[]) >>
  qexists_tac `aw` >> asm_rewrite_tac[]
QED

Finalise create_proxy_target_amount_cut_mods
