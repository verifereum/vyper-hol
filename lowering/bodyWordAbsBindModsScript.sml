(* Compose the forced Abs operand with the linked scalar suffix. *)
Theory bodyWordAbsBindMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyFullShadowBodyInv bodyForRangeScalarFrameMods
  bodyWriteSubscriptSourceMods bodyBranchCellFrameMods bodyFullBuiltinWordAbs
  bodyPtrWordBuiltinsAbsSuffix exprSimAbsSource exprSimUnopComposeProps
  exprSimUnopProps exprBopSimProps exprBodyPreProps stateRelProj exprSimProps
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasExemptCertMods
  allocaHistoryFragment freshWrites loweringPosts loweringStateRelDefs
  vyperStorageTrace vyperStorageFootprint vyperTypeExprSoundness vyperTypeInvariants
  exprSimMemDefs exprSimDefs vyperValue vyperTyping exprLoweringProps
  fragExec bodyPtrDefs ptrDiscipline vyperAST list rich_list
  compileEnv venomInst venomState exprSimMemUnwrap exprSimWordArgs words
  gasContext emitHelperProps vyperState

Theorem abs_signed_operand[local]:
  expr_body_pre_mods mods cenv cx env e es /\ body_const_cells_agree_mods mods cx env es /\
  expr_type e = BaseT (IntT 256) /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := readings) = (INL v,mid) ==>
  value_has_type (BaseTV (IntT 256)) v
Proof
  strip_tac >>
  `expr_body_pre_mods mods cenv cx env e (es with gas_obs := readings) /\
   body_const_cells_agree_mods mods cx env (es with gas_obs := readings)` by
    simp[body_const_cells_agree_mods_branch_updates] >>
  drule_all_then strip_assume_tac write_index_read_source_mods >>
  `env.type_defs = get_tenv cx` by
    (drule expr_sim_inv_mods_env >>
     simp[env_consistent_def, env_context_consistent_def]) >>
  gvs[value_runtime_typed_def, vyperValueTheory.evaluate_type_def]
QED

Theorem abs_eval_operand[local]:
  expr_post_mods H ctx func cenv cx e es sa sm s0 mid v x t /\
  expr_type e = BaseT (IntT 256) ==>
  eval_operand x t = SOME (typed_val_to_w256 (BaseTV (IntT 256)) v)
Proof
  strip_tac >>
  `is_word_type (expr_type e)` by simp[is_word_type_def] >>
  irule expr_val_rel_typed >> qexistsl_tac [`cx`,`expr_type e`] >>
  simp[vyperValueTheory.evaluate_type_def] >>
  fs[expr_post_mods_def, expr_post_def]
QED

Theorem abs_code_cursor[local]:
  compile_builtin_abs x sm = (op,sb) ==>
  sb.cs_current_bb = sm.cs_current_bb /\
  sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb
Proof
  strip_tac >> qspec_then `x` mp_tac straight_fresh_abs >>
  simp[straight_fresh_def] >> disch_then drule >> simp[]
QED

Theorem abs_suffix_history[local]:
  compile_builtin_abs x sm = (op,sb) /\
  run_inst_seq (emitted_insts sm sb) t = OK u /\
  fn_inst_ids_distinct func /\ alloca_history func t /\ alloca_inv t /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sm sb) (DROP t.vs_inst_idx bb.bb_instructions) ==>
  alloca_history func (u with vs_inst_idx := t.vs_inst_idx + LENGTH (emitted_insts sm sb))
Proof
  strip_tac >>
  qpat_x_assum `isPREFIX _ _` (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
  irule alloca_history_run_inst_seq >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
  drule abs_suffix_opcodes >> strip_tac >>
  `EVERY (\opc. ~is_terminator opc)
    (MAP (\i. i.inst_opcode) (emitted_insts sm sb))` by simp[is_terminator_def] >>
  fs[EVERY_MAP]
QED

Theorem abs_frame_state_rel[local]:
  stmt_state_rel H ctx func cenv cx mid t /\ local_ptrs_reserved cenv sm /\
  u = t with vs_vars := u.vs_vars /\
  (!y. not_fresh_at sm y ==> lookup_var y u = lookup_var y t) ==>
  stmt_state_rel H ctx func cenv cx mid (u with vs_inst_idx := idx)
Proof
  strip_tac >> simp[stmt_state_rel_inst_idx] >>
  qpat_assum `u = _` (fn th => once_rewrite_tac[th]) >>
  irule stmt_state_rel_vars_frame >> simp[] >>
  gvs[local_ptrs_reserved_def, lookup_var_def] >> metis_tac[]
QED

Theorem abs_parent_post[local]:
  expr_post_mods H ctx func cenv cx e es sa sm s0 mid v x t /\
  u = t with vs_vars := u.vs_vars /\ z = u with vs_inst_idx := idx /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!y. not_fresh_at sm y ==> lookup_var y z = lookup_var y t) /\
  eval_operand op u = SOME (typed_val_to_w256 (BaseTV (IntT 256)) v') ==>
  expr_post_mods H ctx func cenv cx (Builtin (BaseT (IntT 256)) Abs [e]) es sa sb s0
    mid v' op z
Proof
  strip_tac >> fs[expr_post_mods_def] >>
  `z.vs_memory = t.vs_memory /\ z.vs_data_section = t.vs_data_section /\
   z.vs_allocas = t.vs_allocas /\ z.vs_alloca_next = t.vs_alloca_next` by
    (qpat_assum `z = _` (fn th => once_rewrite_tac[th]) >>
     qpat_assum `u = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  conj_tac
  >- (`stmt_state_rel H ctx func cenv cx mid z` by
       (qpat_assum `z = _` (fn th => once_rewrite_tac[th]) >> irule abs_frame_state_rel >>
        qexistsl_tac [`sm`,`t`] >> drule_then assume_tac expr_post_state >> simp[] >>
        rpt strip_tac >> first_x_assum drule >> simp[lookup_var_def]) >>
      `stmt_state_rel H ctx func cenv cx mid u` by
       (qpat_assum `z = _` (fn th =>
          qpat_assum `stmt_state_rel _ _ _ _ _ _ z` (mp_tac o REWRITE_RULE [th])) >>
        simp[stmt_state_rel_inst_idx]) >>
      `expr_val_rel cx (BaseT (IntT 256)) v' op u` by
        simp[expr_val_rel_def, is_word_type_def, vyperValueTheory.evaluate_type_def] >>
      irule expr_post_unop >> simp[is_word_type_def] >>
      qexistsl_tac [`sm`,`t`,`v`,`x`] >> simp[] >>
      conj_tac
      >- (rpt strip_tac >>
          qpat_assum `z = _` (fn th =>
            qpat_assum `!y. not_fresh_at sm y ==> _` (drule o REWRITE_RULE [th])) >>
          simp[lookup_var_def] >> fs[lookup_var_def]) >>
      qpat_assum `u = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  irule immutable_frame_mods_exterior_frame >>
  qexistsl_tac [`mid`,`t`,`sm`] >> simp[] >>
  conj_tac
  >- (qpat_assum `z = _` (fn th =>
       qpat_assum `!y. not_fresh_at sm y ==> _` (mp_tac o REWRITE_RULE [th])) >> simp[]) >>
  qpat_assum `u = _` (fn th => once_rewrite_tac[th]) >> simp[]
QED

Theorem abs_source_signed_suffix[local]:
  expr_type e = BaseT (IntT 256) /\
  value_has_type (BaseTV (IntT 256)) v /\
  compile_builtin_abs x sm = (op,sb) /\
  eval_operand x t = SOME (typed_val_to_w256 (BaseTV (IntT 256)) v) /\
  (!z. x = Var z ==> not_fresh_at sm z) ==>
  (typed_val_to_w256 (BaseTV (IntT 256)) v <> INT_MINw ==>
   ?v' u. unop_result cx (BaseT (IntT 256)) Abs [expr_type e] v mid = INL v' /\
          run_inst_seq (emitted_insts sm sb) t = OK u /\
          eval_operand op u = SOME (typed_val_to_w256 (BaseTV (IntT 256)) v')) /\
  (typed_val_to_w256 (BaseTV (IntT 256)) v = INT_MINw ==>
   ?m. unop_result cx (BaseT (IntT 256)) Abs [expr_type e] v mid =
       INR (Error (RuntimeError m)) /\ eval_operand x t = SOME INT_MINw)
Proof
  strip_tac >>
  drule_all word_abs_actual_run >> strip_tac >>
  drule word_abs_typed_source >> disch_then (qspecl_then [`[expr_type e]`,`mid`,`cx`] mp_tac) >>
  Cases_on `typed_val_to_w256 (BaseTV (IntT 256)) v = INT_MINw` >> simp[] >>
  strip_tac >> rpt (first_assum (irule_at Any)) >> simp[]
QED

Theorem abs_ghost_kept[local]:
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  (!y. not_fresh_at sa y ==> FLOOKUP G' y = FLOOKUP G y /\
                           op_taint tn' (Var y) = op_taint tn (Var y)) /\
  tn'.t_mem = tn.t_mem ==>
  ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'
Proof
  simp[ghost_kept_at_def] >> metis_tac[]
QED

Theorem word_abs_bind_mods:
  expr_body_pre_mods mods cenv cx env e es /\ body_const_cells_agree_mods mods cx env es /\
  expr_type e = BaseT (IntT 256) /\
  compile_builtin_abs x s1 = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l) /\
  cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var /\
  fn_has_code s1 sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!t u bb G tn.
    run_inst_seq (emitted_insts s1 sb) t = OK u /\
    op_prov G x = NONE /\ op_taint tn x = {} /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    ~t.vs_halted /\ lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts s1 sb) (DROP t.vs_inst_idx bb.bb_instructions) ==>
    ?z G' tn'.
      z = (u with vs_inst_idx := t.vs_inst_idx + LENGTH (emitted_insts s1 sb)) /\
      u = (t with vs_vars := u.vs_vars) /\
      (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (t,G,tn) [] (OK z,G',tn')) /\
      (!v. not_fresh_at s1 v ==> lookup_var v z = lookup_var v t /\
        FLOOKUP G' v = FLOOKUP G v /\ op_taint tn' (Var v) = op_taint tn (Var v)) /\
      op_prov G' op = NONE /\ op_taint tn' op = {} /\
      tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
      tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm) /\
  gas_outcome_full_mods
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cenv.ce_modules cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?v. res = INL v /\
      expr_post_mods H ctx func cenv cx e es sa s1 s0 ee v x t /\
      expr_store_bound cx (post_value_type cenv e) v x t /\
      t.vs_current_bb = s1.cs_current_bb /\ t.vs_inst_idx = LENGTH s1.cs_current_insts /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
      ptr_val_ok cx (post_value_type cenv e) v x G tn t /\
      (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e x G t) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)) ==>
  gas_outcome_full_mods
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cenv.ce_modules cx st0
    (bind (eval_expr cx (Builtin (BaseT (IntT 256)) Abs [e])) (read_result cx))
    (es,s0,G0,tn0)
    (\H res ee G tn t. ?v. res = INL v /\
      expr_post_mods H ctx func cenv cx (Builtin (BaseT (IntT 256)) Abs [e])
        es sa sb s0 ee v op t /\
      expr_store_bound cx (post_value_type cenv (Builtin (BaseT (IntT 256)) Abs [e])) v op t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
      ptr_val_ok cx (post_value_type cenv (Builtin (BaseT (IntT 256)) Abs [e])) v op G tn t /\
      (~is_word_type (post_value_type cenv (Builtin (BaseT (IntT 256)) Abs [e])) ==>
       ptr_buf_ok cenv (Builtin (BaseT (IntT 256)) Abs [e]) op G t) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[eval_expr_unop_action] >>
  qmatch_assum_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` >>
  irule gas_outcome_full_mods_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      goal_assum (drule_at Any) >> fs[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame (bind _ _)`]
  >- simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame, storage_trace_frame_read_result]
  >~ [`storage_trace_frame _`] >- simp[storage_trace_frame_def, unop_result_def] >>
  qexists_tac `\H res ee G tn t. childQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` (irule_at Any) >>
      simp[Abbr `childR`] >> gen_tac >> Cases >> simp[expr_exit_def]) >>
  suspend "continue"
QED

Resume word_abs_bind_mods[continue]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qunabbrev_tac `childQ` >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> BETA_TAC >> strip_tac >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >> disj1_tac >> qexists_tac `v` >> simp[] >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  `bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,mid)` by
    (qpat_assum `mid with gas_obs := [] = mid` (fn frame =>
       qpat_assum `!tail. bind _ _ _ = _`
         (qspec_then `[]` (ACCEPT_TAC o PURE_REWRITE_RULE [APPEND_NIL,frame])))) >>
  drule_all_then assume_tac abs_signed_operand >>
  drule_all_then assume_tac abs_eval_operand >>
  drule_all_then strip_assume_tac word_abs_code_prefix >>
  `is_word_type (expr_type e)` by simp[is_word_type_def] >>
  `op_prov G1 x = NONE /\ op_taint tn1 x = {}` by
    (qhdtm_assum `ptr_val_ok` mp_tac >> simp[ptr_val_ok_def, is_word_type_def] >>
     (gvs[ptr_val_ok_def])) >>
  `allocas_from lo t` by
    (qhdtm_assum `ghost_inv_at_mods` (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
     first_assum ACCEPT_TAC) >>
  drule_all abs_source_signed_suffix >>
  disch_then (qspecl_then [`mid`,`cx`] strip_assume_tac) >>
  Cases_on `typed_val_to_w256 (BaseTV (IntT 256)) v = INT_MINw`
  >- suspend "abort" >>
  suspend "success"
QED

Resume word_abs_bind_mods[abort]:
  fs[] >> drule_all abs_suffix_abort_nonfresh_full >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (qx_choosel_then [`u`,`G'`,`tn'`] strip_assume_tac)) >>
  irule gas_outcome_full_mods_exit_revert >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`G'`,`mid`,`INR (Error (RuntimeError m))`,`tn'`,
    `u with vs_inst_idx := t.vs_inst_idx + 5`] >>
  simp[Abbr `childR`, unop_result_gas_obs, exit_result_def, expr_exit_def, halt_exit_def] >>
  qpat_assum `expr_type e = _` (fn th =>
    qpat_assum `unop_result _ _ _ _ _ _ = _` (ACCEPT_TAC o PURE_REWRITE_RULE [th]))
QED

Resume word_abs_bind_mods[success]:
  qpat_x_assum `_ ==> ?v' u. _` (drule_then (qx_choosel_then [`v'`,`u`] strip_assume_tac)) >>
  qpat_x_assum `!t u bb G tn. _ ==> _` (drule_all_then (qx_choosel_then [`z`,`G'`,`tn'`] strip_assume_tac)) >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!y. not_fresh_at sa y ==> not_fresh_at s1 y` by
    (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `alloca_inv t` by
    (fs[expr_post_mods_def] >> drule_then assume_tac expr_post_state >>
     drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `alloca_history func z` by
    (drule_all_then assume_tac abs_suffix_history >>
     qpat_assum `z = _` (fn th => once_rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
  drule_then strip_assume_tac abs_code_cursor >>
  irule gas_outcome_full_mods_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`G'`,`mid`,`INL v'`,`z`,`tn'`] >>
  conj_tac
  >- (simp[unop_result_gas_obs] >>
      qpat_assum `expr_type e = _` (fn th =>
        qpat_assum `unop_result _ _ _ _ _ _ = _` (ACCEPT_TAC o PURE_REWRITE_RULE [th]))) >>
  qx_gen_tac `H` >> strip_tac >> BETA_TAC >>
  conj_tac >- (first_x_assum irule ORELSE first_assum ACCEPT_TAC) >>
  qpat_assum `mid with gas_obs := [] = mid` (fn th => PURE_REWRITE_TAC [th]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> BETA_TAC >> strip_tac >>
  suspend "post"
QED

Resume word_abs_bind_mods[post]:
  `z.vs_current_bb = t.vs_current_bb /\ z.vs_alloca_next = t.vs_alloca_next /\
   z.vs_allocas = t.vs_allocas /\ z.vs_memory = t.vs_memory /\ z.vs_fmp = t.vs_fmp /\
   z.vs_initial_fmp = t.vs_initial_fmp /\ z.vs_call_ctx = t.vs_call_ctx /\
   z.vs_accounts = t.vs_accounts /\ z.vs_transient = t.vs_transient /\
   z.vs_immutables = t.vs_immutables` by
    (qpat_assum `z = _` (fn th => once_rewrite_tac[th]) >>
     qpat_assum `u = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `z.vs_inst_idx = LENGTH sb.cs_current_insts` by simp[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp z` by
    (strip_tac >> `allocas_below_fmp t` by metis_tac[] >>
     qpat_assum `allocas_below_fmp t` mp_tac >>
     pure_rewrite_tac[allocas_below_fmp_def] >>
     qpat_assum `z.vs_initial_fmp = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `z.vs_fmp = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `z.vs_allocas = _` (fn th => rewrite_tac[th])) >>
  `expr_post_mods H ctx func cenv cx (Builtin (BaseT (IntT 256)) Abs [e])
      es sa sb s0 mid v' op z` by
    (irule abs_parent_post >>
     qpat_assum `expr_post_mods H _ _ _ _ e _ _ _ _ _ _ _ _` (irule_at Any) >>
     goal_assum (drule_at Any) >> qexistsl_tac [`u`,`t.vs_inst_idx + LENGTH (emitted_insts s1 sb)`] >>
     simp[] >> first_assum ACCEPT_TAC) >>
  `ghost_inv_at_mods (DF H) lo d cenv cx mid G' tn' z` by
    (irule ghost_inv_at_mods_exterior_frame >> qexistsl_tac [`G1`,`mid`,`t`,`s1`,`tn1`] >>
     simp[] >> metis_tac[]) >>
  qpat_x_assum `z = u with vs_inst_idx := _` kall_tac >>
  simp[expr_type_def, is_word_type_def, expr_store_bound_word, ptr_val_ok_def] >>
  irule abs_ghost_kept >> qexistsl_tac [`G1`,`tn1`] >> simp[] >>
  rpt strip_tac >>
  `not_fresh_at s1 y` by simp[] >>
  qpat_assum `!v. not_fresh_at s1 v ==> _` (drule_then strip_assume_tac) >> simp[]
QED

Finalise word_abs_bind_mods
