(* The copy suffix starts at the target's landing. Its continuation receives
   the actual source values and the one reached copy-entry machine state. *)
Theory bodyCreateCopyScalarSuffixMods
Ancestors
  bodyCreateOperandCutMods bodyFullPredsMods bodyFullPostsMods
  exprBodyPreProps exprSimWordArgs exprSimPrecompiles exprWordOperand
  exprSimSend exprLoweringProps abiValueEncoding abiEncodeArgsSim emittedSeqComposePtr
  wordArgsPtr fragGasOriginPtr builtinCreate vyperCreate vyperTypeEvalCaseProofs
  vyperTypeExprResult vyperTypeExprSoundness vyperTypeInvariants vyperStorageTrace
  loweringPosts list vyperStorageFootprint vyperTypeSystem exprSimSource
  bodyPtrDefs vyperTyping vyperState compileEnv exprLowering loweringShapeDefs gasShadow

Triviality copy_scalar_word:
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

Triviality copy_scalar_frames:
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

Triviality copy_compile_salt_some:
  compile_create_salt f cenv (SOME e) st = (sop,sb) <=>
  ?p. sop = SOME p /\ lower_value f cenv (expr_type e) e st = (p,sb)
Proof
  Cases_on `lower_value f cenv (expr_type e) e st` >>
  simp[compile_create_salt_def,comp_bind_def,comp_return_def,EQ_SYM_EQ]
QED

Triviality copy_scalar_salt_word:
  value_has_type (BaseTV (BytesT (Fixed 32))) v ==>
  dest_create_salt v = SOME (typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) v)
Proof
  Cases_on `v` >>
  simp[value_has_type_def,dest_create_salt_def,vyperValueTheory.dest_BytesV_def,
       valueEncodingTheory.typed_val_to_w256_def,PAD_RIGHT]
QED

Triviality copy_scalar_nil:
  eval_exprs cx [] = return []
Proof
  simp[FUN_EQ_THM,eval_exprs_nil,return_def]
QED

val exit = ``\(H:(bool # 256 word # type_value) list # num list)
  (res:value + exception) ee (gt:(string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z)``;

Theorem create_copy_scalar_suffix_cut_mods:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\ body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env amount es /\
  (!ee z. MEM z salts /\ expr_sim_inv_mods mods cenv cx env ee ==>
    expr_body_pre_mods mods cenv cx env z ee) /\
  body_exprs_full_ok_mods mods exps cx (amount::salts) /\
  expr_type amount = BaseT (UintT 256) /\
  (if salted then ?salt. salts = [salt] /\ expr_type salt = BaseT (BytesT (Fixed 32))
   else salts = []) /\
  lower_value compile_expr cenv (expr_type amount) amount sa = (y,sm) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type amount)
    (gas_shadow_expr amount) sh = (y,shm) /\
  compile_create_salt compile_expr cenv (if salted then SOME (HD salts) else NONE) sm = (sop,sb) /\
  compile_create_salt compile_expr (gas_shadow_env T cenv)
    (OPTION_MAP gas_shadow_expr (if salted then SOME (HD salts) else NONE)) shm = (sop,shb) /\
  gas_shadow_state sa sh /\ gas_shadow_state sm shm /\ gas_shadow_state sb shb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  fn_has_code sh shm shadow_func /\ fn_has_code shm shb shadow_func /\ ci_mono sa sm /\
  local_ptrs_reserved cenv sa /\ (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!fn i z. frag_reachable ctx func s fn i z ==> dalloca_fmp_headroom i z) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\ immutable_frame_mods func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!vs. storage_trace_frame (next vs)) /\
  (!av sv aw sw ee G1 tn1 t marks.
    dest_NumV av = SOME (w2n aw) /\ dest_optional_salt sv = SOME sw /\ IS_SOME sv = salted /\
    eval_operand y t = SOME aw /\ op_taint tn1 y = {} /\
    OPTREL (\op w. eval_operand op t = SOME w /\ op_taint tn1 op = {}) sop sw /\
    (!x. y = Var x \/ sop = SOME (Var x) ==> not_fresh_at sb x) /\
    wb_frame cenv es ee sa s t /\ ghost_kept_at lo cenv es sa G tn s G1 tn1 /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\ expr_sim_inv_mods mods cenv cx env ee /\
    body_const_cells_agree_mods mods cx env ee /\
    s.vs_alloca_next <= t.vs_alloca_next /\ alloca_history func t /\
    return_buf_frame d cenv sb t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!fn i z. frag_reachable ctx func t fn i z ==> dalloca_fmp_headroom i z) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      valid_horizon cx st0 H es.storage_trace /\ stmt_state_rel H ctx func cenv cx ee t /\
      immutable_frame_mods func cenv cx ee t /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G1 tn1 t /\
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G,tn) marks (OK t,G1,tn1)) ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 (next (av::(case sv of NONE => [] | SOME v => [v])))
      (ee,t,G1,tn1) Q ^exit) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (eval_exprs cx (amount::salts)) next) (es,s,G,tn) Q ^exit
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `body_exprs_full_ok_mods _ _ _ (amount::_)`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_exprs_full_ok_mods_def]) >>
  once_rewrite_tac[eval_exprs_cons_action] >>
  simp[NoAsms,bind_assoc,bind_return] >> once_rewrite_tac[GSYM bind_assoc] >>
  irule create_body_operand_cut_replay_mods >> BETA_TAC >>
  suspend "amount_entry"
QED

Resume create_copy_scalar_suffix_cut_mods[amount_entry]:
  asm_rewrite_tac[] >> conj_tac
  >- simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame] >>
  qexistsl_tac [`d`,`env`,`exps`,`mods`,`y`,`sa`,`sm`,`sh`,`shadow_func`,`shm`,`src`,`tops`] >>
  asm_rewrite_tac[] >> reverse conj_tac
  >- (qpat_assum `expr_type amount = _` (fn th => once_rewrite_tac [GSYM th]) >>
      asm_rewrite_tac[]) >>
  map_every qx_gen_tac [`av`,`em`,`Gm`,`tm`,`m`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?ms. _ /\ (!H. _ ==> gas_origin_ptr_path _ _ ms _)`
    (qx_choose_then `ma` strip_assume_tac) >>
  `!H. valid_horizon cx st0 H em.storage_trace ==>
      expr_post_mods H ctx func cenv cx amount es sa sm s em av y m` by
    (gen_tac >> disch_tac >> first_assum (drule_then strip_assume_tac) >> simp[]) >>
  `is_word_type (BaseT (UintT 256))` by simp[is_word_type_def] >>
  drule_all_then strip_assume_tac copy_scalar_word >>
  qabbrev_tac `aw = typed_val_to_w256 (BaseTV (UintT 256)) av` >>
  `dest_NumV av = SOME (w2n aw)` by simp[Abbr `aw`,uint256_typed_dest] >>
  Cases_on `salted` >>
  gvs[copy_compile_salt_some,CONJUNCT1 compile_create_salt_def,comp_return_def,gas_shadow_expr_type]
  >- suspend "salt_some" >>
  simp[copy_scalar_nil,bind_return] >>
  suspend "salt_none"
QED

Resume create_copy_scalar_suffix_cut_mods[salt_some]:
  rename1 `lower_value _ _ _ salt sm = (sop1,sb)` >>
  `expr_body_pre_mods mods cenv cx env salt em` by simp[] >>
  `sa.cs_next_var <= sm.cs_next_var` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv sm` by drule_all_then ACCEPT_TAC local_ptrs_reserved_next_var >>
  `!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z` by
    metis_tac[not_fresh_at_mono] >>
  `!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z` by
    metis_tac[not_fresh_at_mono] >>
  `!H. valid_horizon cx st0 H em.storage_trace ==>
    stmt_state_rel H ctx func cenv cx em m /\ immutable_frame_mods func cenv cx em m /\
    storage_well_formed_on cx em (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx em Gm tm m` by
    (rpt strip_tac >> first_assum (drule_then strip_assume_tac) >>
     fs[expr_post_mods_def,expr_post_def] >> first_assum drule >> simp[]) >>
  fs[Once body_exprs_full_ok_mods_def] >>
  once_rewrite_tac[eval_exprs_cons_action] >>
  simp[copy_scalar_nil,bind_assoc,bind_return] >> once_rewrite_tac[GSYM bind_assoc] >>
  irule create_body_operand_cut_replay_mods >> BETA_TAC >>
  simp[NoAsms] >> asm_rewrite_tac[] >>
  qexistsl_tac [`d`,`env`,`exps`,`mods`,`sop1`,`sm`,`sb`,`shm`,`shadow_func`,`shb`,`src`,`tops`] >>
  asm_rewrite_tac[] >>
  suspend "salt_landing"
QED

Resume create_copy_scalar_suffix_cut_mods[salt_landing]:
  map_every qx_gen_tac [`sv`,`en`,`Gn`,`tnn`,`n`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?ms. _ /\ (!H. _ ==> gas_origin_ptr_path _ _ ms _)`
    (qx_choose_then `ms` strip_assume_tac) >>
  `!H. valid_horizon cx st0 H en.storage_trace ==>
      expr_post_mods H ctx func cenv cx salt em sm sb m en sv sop1 n` by
    (gen_tac >> disch_tac >> first_assum (drule_then strip_assume_tac) >> simp[]) >>
  `is_word_type (BaseT (BytesT (Fixed 32)))` by simp[is_word_type_def] >>
  `lower_value compile_expr cenv (expr_type salt) salt sm = (sop1,sb)` by simp[] >>
  drule_all_then strip_assume_tac copy_scalar_word >>
  `valid_horizon cx st0 (storage_trace_horizon en.storage_trace) en.storage_trace`
    by fs[storage_trace_domain_def] >>
  `valid_horizon cx st0 (storage_trace_horizon en.storage_trace) es.storage_trace`
    by (qpat_assum `!H. valid_horizon _ _ H em.storage_trace ==> valid_horizon _ _ H es.storage_trace` irule >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `eval_operand y m = SOME _`
    (mp_then Any (drule_all_then strip_assume_tac) copy_scalar_frames) >>
  qabbrev_tac `sw = typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) sv` >>
  `dest_create_salt sv = SOME sw` by simp[Abbr `sw`,copy_scalar_salt_word] >>
  suspend "salt_finish"
QED

Resume create_copy_scalar_suffix_cut_mods[salt_finish]:
  `ci_mono sm sb` by
    (qspecl_then [`cenv`,`expr_type salt`,`salt`,`sm`] mp_tac ci_mono_lower_value_compile_expr >> simp[]) >>
  `!x. y = Var x ==> not_fresh_at sb x` by
    metis_tac[ci_mono_def,not_fresh_at_mono] >>
  `MAP FDOM es.scopes = MAP FDOM en.scopes` by fs[wb_frame_def,locals_kept_def] >>
  `s.vs_alloca_next <= n.vs_alloca_next` by decide_tac >>
  qpat_assum `!av sv aw sw ee G1 tn1 t marks. _ ==> gas_outcome_full_mods _ _ _ _ (next _) _ _ _`
    (qspecl_then [`av`,`SOME sv`,`aw`,`SOME sw`] mp_tac) >> simp[] >>
  disch_then irule >> simp[dest_optional_salt_def,optionTheory.OPTREL_def] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!fn i z. frag_reachable ctx func n fn i z ==> _` (drule_then ACCEPT_TAC)) >>
  conj_tac >- (rpt strip_tac >> simp[]) >>
  qexists_tac `ma ++ ms` >> gen_tac >> disch_tac >>
  `valid_horizon cx st0 H em.storage_trace` by simp[] >>
  qpat_assum `!H. _ ==> expr_post_mods H _ _ _ _ salt _ _ _ _ _ _ _ _`
    (drule_then assume_tac) >>
  fs[expr_post_mods_def,expr_post_def] >>
  irule gas_origin_ptr_path_append >>
  qexistsl_tac [`Gm`,`m`,`(OK m,Gm,tm)`,`tm`] >> simp[]
QED

Resume create_copy_scalar_suffix_cut_mods[salt_none]:
  `MAP FDOM es.scopes = MAP FDOM em.scopes` by fs[wb_frame_def,locals_kept_def] >>
  qpat_assum `!av aw ee G1 tn1 t marks. _ ==> gas_outcome_full_mods _ _ _ _ (next _) _ _ _`
    irule >>
  simp[dest_optional_salt_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `ma` >> gen_tac >> disch_tac >>
  qpat_assum `!H. _ ==> expr_post_mods H _ _ _ _ amount _ _ _ _ _ _ _ _`
    (drule_then assume_tac) >>
  fs[expr_post_mods_def,expr_post_def]
QED

Finalise create_copy_scalar_suffix_cut_mods
