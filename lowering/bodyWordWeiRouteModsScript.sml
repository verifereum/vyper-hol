(* AsWeiValue: one linked forced operand followed by unsigned scaling. *)
Theory bodyWordWeiRouteMods
Ancestors
  bodyFullBuiltinWordWeiPrefix bodyFullBuiltinWordWeiSuffix
  bodyFullPredsMods bodyScalarStackVVMods bodyForRangeScalarFrameMods
  bodySimStmtFacts exprBodyPreProps exprBodyPreTypingProps exprSimWordArgs
  exprSimHypsDefs supportedExprTraverse allocLimits vyperTypeCallGraph
  bodyFullPostsMods bodyFullShadowBodyInv exprSimDefs gasStorage gasContext
  valueEncoding loweringPosts bodyPtrDefs loweringStateRelDefs ptrDiscipline
  exprSimMemDefs fragGasOriginPtr gasOutcomeFull fragExecMem vyperTyping
  exprSimStack exprSimWordBuiltins exprSimUnopProps exprSimProps
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasExemptCertMods
  entryDecoderHistoryFrame vyperStorageTrace vyperStorageFootprint
  vyperTypeExprSoundness vyperTypeInvariants vyperValueOperation
  bodyPtrWordBuiltinsScaling exprLoweringProps compileEnv fragExec
  venomState vyperInterpreter vyperState vyperContext vyperTypeSystem vyperAST list
Libs monadsyntax

Theorem wei_operand_pre[local]:
  (builtin_args_length_ok (AsWeiValue dn) (LENGTH args) ==>
     body_exprs_full_ok_mods mods exps cx args) /\
  expr_body_pre_mods mods cenv cx env (Builtin ann (AsWeiValue dn) args) es ==>
  ?e k. args = [e] /\ ann = BaseT (UintT 256) /\
    expr_type e = BaseT (UintT k) /\
    expr_body_pre_mods mods cenv cx env e es /\ body_expr_full_ok_mods mods exps cx e
Proof
  strip_tac >> drule expr_body_pre_mods_well_typed >>
  simp[Once well_typed_expr_def, well_typed_builtin_app_def,
       LENGTH_EQ_NUM_compute, is_uint_type_def] >> strip_tac >> gvs[] >>
  fs[constSubstCorrectTheory.frame_well_typed_exprs_cons] >>
  conj_tac
  >- (qpat_x_assum `expr_body_pre_mods _ _ _ _ (Builtin _ _ _) _` mp_tac >>
      simp[expr_body_pre_mods_def, Once well_typed_expr_def,
           byte_widths_expr_def, alloc_limits_expr_def, int_calls_expr_def,
           expr_has_evm_run_thm, supported_expr_exists_def, DISJ_IMP_THM,
           FORALL_AND_THM, constSubstCorrectTheory.frame_well_typed_exprs_cons]) >>
  fs[builtin_args_length_ok_def, Once body_expr_full_ok_mods_def]
QED

Theorem wei_operand_typed[local]:
  expr_body_pre_mods mods cenv cx env e es /\ expr_type e = BaseT (UintT k) /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := readings) = (INL v,mid) ==>
  evaluate_type (get_tenv cx) (BaseT (UintT k)) = SOME (BaseTV (UintT k)) /\
  value_has_type (BaseTV (UintT k)) v
Proof
  strip_tac >>
  `expr_body_pre_mods mods cenv cx env e (es with gas_obs := readings)` by
    simp[bodyWriteSubscriptSourceModsTheory.write_subscript_source_gas_obs_mods] >>
  drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_eval_mods) >> strip_tac >>
  drule expr_body_pre_mods_inv >> drule expr_sim_inv_mods_env >> strip_tac >>
  gvs[value_runtime_typed_def, env_consistent_def, env_context_consistent_def,
      vyperValueTheory.evaluate_type_def]
QED

Theorem wei_operand_admissible[local]:
  gas_admissible (bind (eval_expr cx (Builtin ann (AsWeiValue dn) [e]))
    (read_result cx)) expr_res_ok es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  simp[as_wei_value_source_bind, gas_admissible_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >> Cases_on `res` >- simp[expr_res_ok_def] >>
  first_x_assum irule >> qexistsl_tac [`ee`,`gs`] >> simp[bind_def]
QED

Theorem wei_suffix_layout[local]:
  compile_as_wei_value_int x (denomination_multiplier dn) F s1 = (op,sb) ==>
  sb.cs_current_bb = s1.cs_current_bb /\ isPREFIX s1.cs_current_insts sb.cs_current_insts /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts s1 sb)
Proof
  strip_tac >> drule word_scale_current_block >> strip_tac >> simp[] >>
  Cases_on `denomination_multiplier dn = 1`
  >- (gvs[] >> drule word_scale_identity >> simp[]) >>
  drule_all word_scale_emitted_shape >> simp[EVERY_MEM] >> metis_tac[]
QED

Theorem wei_encoded_operand[local]:
  expr_type e = BaseT (UintT k) /\
  evaluate_type (get_tenv cx) (BaseT (UintT k)) = SOME (BaseTV (UintT k)) /\
  value_has_type (BaseTV (UintT k)) v /\
  expr_post_mods H ctx func cenv cx e es sa s1 s0 mid v x t ==>
  v = IntV (&w2n (val_to_w256 v)) /\ eval_operand x t = SOME (val_to_w256 v)
Proof
  strip_tac >> conj_tac
  >- (irule uint_value_word_rep >> qexists_tac `k` >>
      fs[vyperValueTheory.evaluate_type_def, AllCaseEqs()]) >>
  `post_value_type cenv e = expr_type e` by simp[loweringPostsTheory.post_value_type_word, is_word_type_def] >>
  fs[expr_post_mods_def, expr_post_def] >>
  `expr_val_rel cx (BaseT (UintT k)) v x t` by metis_tac[] >>
  `is_word_type (BaseT (UintT k))` by simp[is_word_type_def] >>
  drule_all exprBopSimPropsTheory.expr_val_rel_typed >>
  Cases_on `v` >> fs[value_has_type_def, typed_val_to_w256_def]
QED

Theorem wei_builtin_result[local]:
  v = IntV (&w2n (val_to_w256 v)) ==>
  builtin_result cx ac (BaseT (UintT 256)) (AsWeiValue dn) [BaseT (UintT k)] [v] =
    if w2n (val_to_w256 v) * denomination_multiplier dn < dimword (:256)
    then INL (IntV (&(w2n (val_to_w256 v) * denomination_multiplier dn)))
    else INR (Error (RuntimeError "ewv bound"))
Proof
  strip_tac >> qpat_assum `v = IntV _` (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
  simp[builtin_result_def, evaluate_builtin_def, evaluate_as_wei_value_uint, wordsTheory.dimword_def] >>
  IF_CASES_TAC >> simp[]
QED

Theorem wei_post_frame[local]:
  expr_post_mods H ctx func cenv cx e es sa s1 s0 mid v x t /\
  u = (t with vs_vars := V) with vs_inst_idx := idx /\
  local_ptrs_reserved cenv s1 /\
  (!y. not_fresh_at s1 y ==> lookup_var y u = lookup_var y t) /\
  expr_val_rel cx (BaseT (UintT 256)) w op u /\ sa.cs_next_var <= s1.cs_next_var ==>
  expr_post_mods H ctx func cenv cx (Builtin (BaseT (UintT 256)) (AsWeiValue dn) [e])
    es sa sb s0 mid w op u
Proof
  strip_tac >> fs[expr_post_mods_def] >>
  `stmt_state_rel H ctx func cenv cx mid u` by
    (`stmt_state_rel H ctx func cenv cx mid (t with vs_vars := V)` by
       (irule stmt_state_rel_vars_frame >>
        drule expr_post_state >> strip_tac >>
        qpat_x_assum `!y. not_fresh_at _ y ==> _` mp_tac >>
        simp[lookup_var_def] >> strip_tac >>
        fs[local_ptrs_reserved_def] >> metis_tac[]) >>
     mp_tac (stmt_state_rel_inst_idx |> Q.SPECL
       [`H`,`func`,`cenv`,`cx`,`mid`,`t with vs_vars := V`,`idx`,`ctx`]) >> simp[]) >>
  qpat_x_assum `u = _` SUBST_ALL_TAC >>
  conj_tac
  >- (irule expr_post_unop >>
      qpat_assum `expr_post H _ _ _ _ e _ _ _ _ mid _ x t` (irule_at Any) >>
      simp[is_word_type_def] >> metis_tac[]) >>
  irule immutable_frame_mods_exterior_frame >> qexistsl_tac [`mid`,`t`,`s1`] >> simp[]
QED

Theorem wei_success_landing[local]:
  compile_as_wei_value_int x (denomination_multiplier dn) F s1 = (op,sb) /\
  run_inst_seq (emitted_insts s1 sb) t = OK ss /\
  eval_operand op ss = SOME (val_to_w256 v * n2w (denomination_multiplier dn)) /\
  fn_has_code s1 sb func /\ fn_inst_ids_distinct func /\
  t.vs_current_bb = s1.cs_current_bb /\ t.vs_inst_idx = LENGTH s1.cs_current_insts /\
  ~t.vs_halted /\ local_ptrs_reserved cenv s1 /\ sa.cs_next_var <= s1.cs_next_var /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s1 z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s1 z) /\
  op_prov G1 x = NONE /\ op_taint tn1 x = {} /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ allocas_from lo t /\ lo <= t.vs_alloca_next /\
  mid.gas_obs = [] /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
     expr_post_mods H ctx func cenv cx e es sa s1 s0 mid v x t /\
     alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
     ghost_inv_at_mods (DF H) lo d cenv cx mid G1 tn1 t /\
     ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (\ee. (INL (IntV (&(denomination_multiplier dn * w2n (val_to_w256 v)))),ee))
    (mid,t,G1,tn1)
    (\H res ee G tn u. ?w. res = INL w /\
      expr_post_mods H ctx func cenv cx (Builtin (BaseT (UintT 256)) (AsWeiValue dn) [e])
        es sa sb s0 ee w op u /\
      expr_store_bound cx (BaseT (UintT 256)) w op u /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
      s0.vs_alloca_next <= u.vs_alloca_next /\ ghost_inv_at_mods (DF H) lo d cenv cx ee G tn u /\
      ptr_val_ok cx (BaseT (UintT 256)) w op G tn u /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn) R
Proof
  strip_tac >> drule_all as_wei_value_success_origin >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  drule_all (Q.INST [`sc` |-> `sa`] as_wei_value_runtime_frame |> SIMP_RULE (srw_ss()) []) >> strip_tac >>
  drule wei_suffix_layout >> strip_tac >>
  qabbrev_tac `u = ss with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  irule gas_outcome_full_mods_pure >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G'`,`mid`,`INL (IntV (&(w2n (val_to_w256 v) * denomination_multiplier dn)))`,`u`,`tn'`] >>
  simp[] >> qx_gen_tac `H` >> strip_tac >> first_x_assum drule >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "post"
QED

Resume wei_success_landing[post]:
  `u.vs_alloca_next = t.vs_alloca_next /\ u.vs_current_bb = sb.cs_current_bb /\
     u.vs_inst_idx = LENGTH sb.cs_current_insts /\
     (ctx_has_dalloca ctx ==> allocas_below_fmp u)` by
    (simp[Abbr `u`] >> qpat_assum `ss = t with vs_vars := _` SUBST1_TAC >>
     simp[allocas_below_fmp_def] >> fs[allocas_below_fmp_def] >> metis_tac[]) >>
  `alloca_history func u` by
    (simp[Abbr `u`] >> irule entry_straight_line_alloca_history >>
     qpat_assum `run_inst_seq _ _ = OK ss` (irule_at Any) >> simp[] >>
     fs[expr_post_mods_def] >> drule expr_post_state >>
     disch_then (strip_assume_tac o MATCH_MP stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >>
     first_assum ACCEPT_TAC) >>
  `expr_val_rel cx (BaseT (UintT 256))
      (IntV (&(w2n (val_to_w256 v) * denomination_multiplier dn))) op u` by
    (simp[expr_val_rel_def, is_word_type_def, vyperValueTheory.evaluate_type_def,
          typed_val_to_w256_def, val_to_w256_def, integer_wordTheory.i2w_pos,
          GSYM wordsTheory.word_mul_n2w, Abbr `u`, eval_operand_def, lookup_var_def] >>
     Cases_on `op` >> fs[eval_operand_def, lookup_var_def, wordsTheory.WORD_MULT_COMM]) >>
  `expr_post_mods H ctx func cenv cx (Builtin (BaseT (UintT 256)) (AsWeiValue dn) [e])
       es sa sb s0 mid (IntV (&(w2n (val_to_w256 v) * denomination_multiplier dn))) op u` by
    (irule wei_post_frame >>
     qpat_assum `expr_post_mods H _ _ _ _ e _ _ _ _ _ _ _ _` (irule_at Any) >>
     qexistsl_tac [`LENGTH sb.cs_current_insts`,`ss.vs_vars`] >>
     fs[Abbr `u`, lookup_var_def] >>
     qpat_assum `ss = t with vs_vars := _` (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
     simp[]) >>
  `ghost_inv_at_mods (DF H) lo d cenv cx mid G' tn' u` by
    (irule ghost_inv_at_mods_exterior_frame >> qexistsl_tac [`G1`,`mid`,`t`,`s1`,`tn1`] >>
     simp[Abbr `u`] >> qpat_assum `ss = t with vs_vars := _` SUBST1_TAC >>
     fs[lookup_var_def]) >>
  fs[expr_store_bound_word, ptr_val_ok_word, is_word_type_def, arithmeticTheory.MULT_COMM] >>
  qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[ghost_kept_at_def] >> strip_tac >>
  `!y. not_fresh_at sa y ==> not_fresh_at s1 y` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >> metis_tac[]
QED

Finalise wei_success_landing

Theorem wei_abort_landing[local]:
  compile_as_wei_value_int x (denomination_multiplier dn) F s1 = (op,sb) /\
  run_inst_seq (emitted_insts s1 sb) t = Abort Revert_abort ss /\
  fn_has_code s1 sb func /\
  t.vs_current_bb = s1.cs_current_bb /\ t.vs_inst_idx = LENGTH s1.cs_current_insts /\
  ~t.vs_halted /\ op_prov G1 x = NONE /\ op_taint tn1 x = {} /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ allocas_from lo t /\ lo <= t.vs_alloca_next ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (\ee. (INR (Error (RuntimeError "ewv bound")),ee)) (mid,t,G1,tn1) Q
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  strip_tac >> drule_all as_wei_value_abort_origin >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  irule gas_outcome_full_mods_exit_revert >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G'`, `mid`, `INR (Error (RuntimeError "ewv bound"))`, `tn'`,
                `ss with vs_inst_idx := t.vs_inst_idx + 5`] >>
  simp[expr_exit_def, halt_exit_def, exit_result_def]
QED

Theorem wei_child_value_sim[local]:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\ body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env e es /\ body_expr_full_ok_mods mods exps cx e ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (expr_type e) e es
Proof
  strip_tac >> qpat_x_assum `body_expr_full_ok_mods _ _ _ _`
    (strip_assume_tac o PURE_ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  qpat_x_assum `!DF lo d PG src tops ctx sh f sf ce en ty st. _ ==> expr_sim_full_mods _ _ _ _ _ _ /\ _`
    (mp_tac o REWRITE_RULE [IMP_CONJ_THM, FORALL_AND_THM]) >> metis_tac[]
QED

Theorem wei_operand_code[local]:
  expr_type e = BaseT (UintT k) /\ local_ptrs_reserved cenv sa /\
  gas_shadow_state sa shadow_sa /\
  lower_value compile_expr cenv ty (Builtin ann (AsWeiValue dn) [e]) sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Builtin ann (AsWeiValue dn) [e])) shadow_sa = (op,shadow_sb) /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func ==>
  ?x s1 sh1.
    lower_value compile_expr cenv (expr_type e) e sa = (x,s1) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) shadow_sa = (x,sh1) /\
    gas_shadow_state s1 sh1 /\ fn_has_code sa s1 func /\ fn_has_code s1 sb func /\
    fn_has_code shadow_sa sh1 shadow_func /\
    compile_as_wei_value_int x (denomination_multiplier dn) F s1 = (op,sb) /\
    sa.cs_next_var <= s1.cs_next_var /\ (!y. x = Var y ==> not_fresh_at s1 y)
Proof
  strip_tac >> drule_all as_wei_value_lower_pair >> strip_tac >>
  `cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var /\ cs_extends shadow_sa sh1` by
    metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends s1 sb /\ cs_extends sh1 shadow_sb` by
    metis_tac[straight_fresh_cs_extends, straight_fresh_as_wei_value_int] >>
  qexistsl_tac [`x`,`s1`,`sh1`] >> simp[] >>
  metis_tac[fn_has_code_split, exprOperandVarTheory.compile_lower_value_var]
QED

Theorem wei_value_sim[local]:
  expr_type e = BaseT (UintT k) /\ expr_body_pre_mods mods cenv cx env e es /\
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (expr_type e) e es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin (BaseT (UintT 256)) (AsWeiValue dn) [e]) es
Proof
  strip_tac >> rewrite_tac[expr_sim_full_mods_def] >> rpt gen_tac >> strip_tac >>
  drule_all wei_operand_code >> strip_tac >>
  drule wei_operand_admissible >> strip_tac >>
  qpat_x_assum `expr_sim_full_mods _ _ _ _ e es`
    (qspecl_then [`st0`,`sa`,`s1`,`shadow_sa`,`sh1`,`x`,`s0`,`G0`,`tn0`] mp_tac o
      REWRITE_RULE [expr_sim_full_mods_def]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` >>
  PURE_REWRITE_TAC [as_wei_value_source_bind] >>
  irule gas_outcome_full_mods_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      qexistsl_tac [`mid`,`t`,`v`] >> gvs[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame (bind _ _)`]
  >- simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame, storage_trace_frame_read_result]
  >~ [`storage_trace_frame _`] >- simp[storage_trace_frame_def] >>
  qexists_tac `\H res ee G tn t. childQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` (irule_at Any) >>
      simp[Abbr `childR`] >> gen_tac >> Cases >> simp[expr_exit_def]) >>
  suspend "continuation"
QED

Resume wei_value_sim[continuation]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qunabbrev_tac `childQ` >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?v. res = INL v /\ _` (qx_choose_then `v` (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >> disj1_tac >> qexists_tac `v` >> simp[] >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,mid)` by
    (qpat_assum `mid with gas_obs := [] = mid` (fn frame =>
       qpat_assum `!tail. bind _ _ _ = _`
         (qspec_then `[]` (ACCEPT_TAC o PURE_REWRITE_RULE [APPEND_NIL,frame])))) >>
  drule_all wei_operand_typed >> strip_tac >>
  drule_all wei_encoded_operand >> strip_tac >>
  `post_value_type cenv e = BaseT (UintT k)` by
    (`post_value_type cenv e = expr_type e` by simp[loweringPostsTheory.post_value_type_word, is_word_type_def] >> simp[]) >>
  `op_prov G1 x = NONE /\ op_taint tn1 x = {}` by
    (qpat_assum `post_value_type cenv e = BaseT (UintT k)` (fn ty_th =>
       qpat_assum `ptr_val_ok _ _ _ _ _ _ _` (mp_tac o PURE_REWRITE_RULE [ty_th, ptr_val_ok_def])) >>
     simp[is_word_type_def]) >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `0 < denomination_multiplier dn /\ denomination_multiplier dn < dimword (:256)` by
    (qspec_then `dn` mp_tac denomination_multiplier_bounds >> simp[wordsTheory.dimword_def]) >>
  drule_all compile_as_wei_value_int_run >> strip_tac >>
  drule wei_builtin_result >> strip_tac >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!y. not_fresh_at sa y ==> not_fresh_at s1 y` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  suspend "scaling"
QED

Resume wei_value_sim[scaling]:
  Cases_on `w2n (val_to_w256 v) * denomination_multiplier dn < dimword (:256)`
  >- (qpat_x_assum `_ ==> ?ss. run_inst_seq _ _ = OK ss /\ _` drule >> strip_tac >>
      simp[loweringPostsTheory.post_value_type_word, expr_type_def, is_word_type_def, Abbr `childR`] >>
      irule wei_success_landing >>
      qpat_assum `compile_as_wei_value_int _ _ _ _ = _` (irule_at Any) >>
      qpat_assum `run_inst_seq _ _ = OK _` (irule_at Any) >> simp[] >>
      qx_gen_tac `H` >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
        (qspec_then `H` mp_tac) >>
      BETA_TAC >> simp[] >> strip_tac >> gvs[]) >>
  qpat_x_assum `_ ==> ?ss. run_inst_seq _ _ = Abort _ ss` drule >> strip_tac >>
  simp[Abbr `childR`] >> irule wei_abort_landing >>
  qpat_assum `run_inst_seq _ _ = Abort _ _` (irule_at Any) >> simp[] >> metis_tac[]
QED

Finalise wei_value_sim

Theorem word_wei_sim_mods:
  (?dn. bt = AsWeiValue dn) /\
  (builtin_args_length_ok bt (LENGTH args) ==> body_exprs_full_ok_mods mods exps cx args) /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\ body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env (Builtin ann bt args) es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty (Builtin ann bt args) es /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty (Builtin ann bt args) es
Proof
  strip_tac >> gvs[] >> drule_all wei_operand_pre >> strip_tac >> gvs[] >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (expr_type e) e es` by
    (irule wei_child_value_sim >> metis_tac[]) >>
  conj_asm1_tac
  >- (irule wei_value_sim >> metis_tac[]) >>
  irule scalar_stack_vv_sim_full_mods >>
  simp[loweringPostsTheory.post_value_type_word, expr_type_def, is_word_type_def] >>
  conj_tac
  >- (gen_tac >> Cases_on `compile_expr cenv ty
        (Builtin (BaseT (UintT 256)) (AsWeiValue dn) [e]) sa` >>
      drule_at Any compile_word_builtin_stack >> simp[] >> metis_tac[]) >>
  metis_tac[eval_expr_builtin_value]
QED
