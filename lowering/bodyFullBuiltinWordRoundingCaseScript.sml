(* Ceil and Floor in the joint expression induction. *)
Theory bodyFullBuiltinWordRoundingCase
Ancestors
  bodyFullBuiltinWordRounding bodyFullShared bodyFullPreds bodySimFull
  gasOutcomeFullCompose gasOutcomeFullStmts exprSimWordBuiltins
  exprSimUnopProps exprSimUnopComposeProps exprSimSource
  gasShadowCompileStmtHelpers allocaHistoryFragment
  fragExecMem fragGasSeqPtr instIdxIndep freshWrites
  valueEncoding vyperValueOperation vyperInterpreter
  exprSimHypsDefs vyperTypeSystem vyperTyping vyperValue vyperContext
  vyperValueOperation valueEncoding
  exprLowering exprLoweringProps compileEnv venomExecSemantics venomState
  venomInst list rich_list finite_map

Theorem rounding_typed_source[local]:
  (bt = Ceil \/ bt = Floor) /\ value_has_type (BaseTV DecimalT) v ==>
  ?v'. unop_result cx (BaseT (IntT 256)) bt tys v es = INL v' /\
    typed_val_to_w256 (BaseTV (IntT 256)) v' =
    safe_sdiv
      (if bt = Ceil then
         (if word_lt (typed_val_to_w256 (BaseTV DecimalT) v) 0w then
            typed_val_to_w256 (BaseTV DecimalT) v
          else typed_val_to_w256 (BaseTV DecimalT) v + n2w (10000000000 - 1))
       else (if word_lt (typed_val_to_w256 (BaseTV DecimalT) v) 0w then
            typed_val_to_w256 (BaseTV DecimalT) v - n2w (10000000000 - 1)
          else typed_val_to_w256 (BaseTV DecimalT) v))
      (n2w 10000000000)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  Cases_on `bt = Ceil` >> gvs[] >>
  simp[unop_result_def, vyperContextTheory.evaluate_builtin_def,
    typed_val_to_w256_def, val_to_w256_def, vyperValueTheory.decimal_scale_def] >>
  drule decimal_ceil_word >>
  disch_then (assume_tac o SIMP_RULE (srw_ss())
    [integer_wordTheory.WORD_LTi, integer_wordTheory.word_0_w2i]) >>
  drule decimal_floor_word >>
  simp[integer_wordTheory.WORD_LTi, integer_wordTheory.word_0_w2i]
QED

Theorem rounding_continuation_full:
  (bt = Ceil \/ bt = Floor) /\
  expr_type e = BaseT DecimalT /\
  expr_body_pre cenv cx env e es /\
  (if bt = Ceil then compile_ceil x 10000000000 else compile_floor x 10000000000)
    s1 = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\
  cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var /\
  fn_has_code s1 sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!tail. bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
     (res,mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    ?v. res = INL v /\ expr_post H ctx func cenv cx e es sa s1 s0 mid v x t /\
      expr_store_bound cx (expr_type e) v x t /\
      t.vs_current_bb = s1.cs_current_bb /\
      t.vs_inst_idx = LENGTH s1.cs_current_insts /\ alloca_history func t /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t /\
      ptr_val_ok cx (expr_type e) v x G1 tn1 t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\ ~t.vs_halted) ==>
  ?v. res = INL v /\
    gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
      (\es. (unop_result cx (BaseT (IntT 256)) bt [expr_type e] v es,es))
      (mid,t,G1,tn1)
      (\H res ee G tn t.
        ?v. res = INL v /\
          expr_post H ctx func cenv cx (Builtin (BaseT (IntT 256)) bt [e])
            es sa sb s0 ee v op t /\
          expr_store_bound cx (BaseT (IntT 256)) v op t /\
          t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
          ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
          ptr_val_ok cx (BaseT (IntT 256)) v op G tn t /\
          ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
      (\H res ee gt r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
    mid.storage_trace` by
    gvs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  impl_tac >- asm_rewrite_tac[] >> strip_tac >>
  qexists_tac `v` >> asm_rewrite_tac[] >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >>
  `value_has_type (BaseTV DecimalT) v` by
    (`?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
      value_has_type tv v` by
      (irule expr_body_pre_word_value >> conj_tac >- simp[is_word_type_def] >>
       qexistsl_tac [`cenv`, `env`,
         `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
         `mid with gas_obs := []`] >> simp[] >> metis_tac[APPEND_NIL]) >>
     gvs[vyperValueTheory.evaluate_type_def]) >>
  `eval_operand x t = SOME (typed_val_to_w256 (BaseTV DecimalT) v) /\
   ~t.vs_halted /\ alloca_inv t` by
    gvs[loweringPostsTheory.expr_post_def, loweringPostsTheory.expr_val_rel_def,
      loweringPostsTheory.post_value_type_def, vyperValueTheory.evaluate_type_def,
      is_word_type_def,
      exprLoweringPropsTheory.stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def] >>
  `op_taint tn1 x = {} /\ op_prov G1 x = NONE /\ allocas_from lo t` by
    gvs[bodyPtrDefsTheory.ptr_val_ok_def, bodyPtrDefsTheory.ghost_inv_at_def,
      is_word_type_def] >>
  `sb.cs_current_bb = s1.cs_current_bb /\
   sb.cs_current_insts = s1.cs_current_insts ++ emitted_insts s1 sb /\
   writes_fresh s1 (emitted_insts s1 sb)` by
    (Cases_on `bt = Ceil` >> gvs[] >>
     metis_tac[straight_fresh_ceil, straight_fresh_floor, straight_fresh_def]) >>
  `?bb. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts s1 sb) (DROP t.vs_inst_idx bb.bb_instructions)` by
    (gvs[fragExecTheory.fn_has_code_def] >>
     qpat_x_assum `isPREFIX (_ ++ _) _` mp_tac >>
     rewrite_tac[IS_PREFIX_APPEND] >> strip_tac >>
     qpat_x_assum `bb.bb_instructions = _` SUBST1_TAC >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, exprLoweringPropsTheory.DROP_PREFIX] >>
     qexists_tac `l` >> rewrite_tac[]) >>
  `local_ptrs_reserved cenv s1 /\
   (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s1 z) /\
   (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s1 z)` by
    (conj_tac >- metis_tac[local_ptrs_reserved_next_var] >>
     conj_tac >> rpt gen_tac >> strip_tac >>
     `not_fresh_at sa z` by metis_tac[] >>
     gvs[loweringStateRelDefsTheory.not_fresh_at_def]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` by
    (rpt strip_tac >> first_x_assum (drule_then strip_assume_tac) >> gvs[]) >>
  mp_tac (Q.INST [`cx` |-> `cx`, `tys` |-> `[expr_type e]`,
      `es` |-> `mid`, `v` |-> `v`, `bt` |-> `bt`] rounding_typed_source) >>
  asm_rewrite_tac[] >> strip_tac >>
  drule_all word_rounding_run_nonfresh >> strip_tac >>
  `?u. run_inst_seq (emitted_insts s1 sb) t = OK u /\
    eval_operand op u = SOME (typed_val_to_w256 (BaseTV (IntT 256)) v')` by
    metis_tac[] >>
  `mid.scopes = mid.scopes` by simp[] >>
  drule_all rounding_suffix_success_full >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  drule_all run_inst_seq_writes_fresh >> strip_tac >>
  `alloca_history func z` by
    (qpat_x_assum `isPREFIX _ _` mp_tac >>
     rewrite_tac[IS_PREFIX_APPEND] >> strip_tac >>
     `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts s1 sb)` by
       (drule_all rounding_suffix_opcodes >> strip_tac >>
        `EVERY (\opc. ~is_terminator opc)
          (MAP (\i. i.inst_opcode) (emitted_insts s1 sb))` by
          (Cases_on `bt = Ceil` >> simp[is_terminator_def]) >> gvs[EVERY_MAP]) >>
     drule_all alloca_history_run_inst_seq >> simp[]) >>
  irule gas_outcome_full_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`G'`, `mid`, `INL v'`, `z`, `tn'`] >>
  simp[unop_result_gas_obs] >> qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> ?v. _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  qpat_x_assum `INL v = INL _` (SUBST_ALL_TAC o SYM o SRULE [sumTheory.INL_11]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >> simp[] >>
  `stmt_state_rel H ctx func cenv cx mid t` by gvs[loweringPostsTheory.expr_post_def] >>
  `stmt_state_rel H ctx func cenv cx mid (t with vs_vars := u.vs_vars)` by
    (irule exprSimPropsTheory.stmt_state_rel_vars_frame >> simp[] >>
     gvs[loweringStateRelDefsTheory.local_ptrs_reserved_def, lookup_var_def] >>
     metis_tac[lookup_var_def]) >>
  `stmt_state_rel H ctx func cenv cx mid z` by
    (qpat_assum `z = _` (fn th => once_rewrite_tac[th]) >>
     simp[exprLoweringPropsTheory.stmt_state_rel_inst_idx] >> metis_tac[]) >>
  `stmt_state_rel H ctx func cenv cx mid u` by
    (qpat_assum `z = _` (fn th =>
       qpat_assum `stmt_state_rel _ _ _ _ _ _ z` (mp_tac o REWRITE_RULE [th])) >>
     simp[exprLoweringPropsTheory.stmt_state_rel_inst_idx]) >>
  `u.vs_allocas = t.vs_allocas /\ u.vs_memory = t.vs_memory` by
    (qpat_assum `u = t with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  conj_tac
  >- (irule expr_post_unop >>
      simp[exprLoweringPropsTheory.stmt_state_rel_inst_idx,
        exprSimWordArgsTheory.stmt_state_rel_gas_obs,
        loweringPostsTheory.expr_val_rel_def, vyperValueTheory.evaluate_type_def,
        is_word_type_def, eval_operand_def, lookup_var_def] >>
      qexistsl_tac [`s1`, `t`, `v`, `x`] >> simp[] >>
      `expr_post H ctx func cenv cx e es sa s1 s0 (mid with gas_obs := []) v x t =
       expr_post H ctx func cenv cx e es sa s1 s0 mid v x t` by
        (`storage_well_formed_on cx (mid with gas_obs := []) (FST H) <=>
          storage_well_formed_on cx mid (FST H)` by
          (irule vyperStorageFootprintTheory.storage_well_formed_on_backends >> simp[]) >>
         qpat_x_assum `storage_well_formed_on _ (_ with gas_obs := _) _ <=> _`
           (fn th => POP_ASSUM_LIST (K all_tac) >> assume_tac th) >>
         simp[loweringPostsTheory.expr_post_def, loweringPostsTheory.expr_val_at_def,
           loweringPostsTheory.expr_val_own_def, exprLoweringPropsTheory.stmt_state_rel_def,
           loweringStateRelDefsTheory.state_rel_gas_obs, loweringPostsTheory.locals_kept_def,
           loweringPostsTheory.popped_kept_def]) >> simp[]) >>
  `ghost_inv_at (DF H) lo d cenv cx (mid with gas_obs := []) G' tn' z` by
    (qpat_assum `ghost_inv_at _ _ _ _ _ mid G' tn' z`
       (fn th => POP_ASSUM_LIST (K all_tac) >> mp_tac th) >>
     simp[bodyPtrDefsTheory.ghost_inv_at_def] >> strip_tac >> simp[]) >>
  `u.vs_current_bb = t.vs_current_bb /\ u.vs_alloca_next = t.vs_alloca_next` by
    (qpat_assum `u = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  qpat_x_assum `z = _` SUBST_ALL_TAC >>
  simp[is_word_type_def, exprSimMemDefsTheory.expr_store_bound_word,
    bodyPtrDefsTheory.ptr_val_ok_def] >>
  `!n. not_fresh_at sa n ==> not_fresh_at s1 n` by
    metis_tac[not_fresh_at_mono] >>
  qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ G1 tn1` mp_tac >>
  simp[bodyPtrDefsTheory.ghost_kept_at_def] >> metis_tac[]
QED


Theorem lower_value_rounding[local]:
  (bt = Ceil \/ bt = Floor) /\
  lower_value compile_expr cenv ty (Builtin ann bt [e]) sa = (op,sb) ==>
  ?x s1. lower_value compile_expr cenv ty e sa = (x,s1) /\
    (if bt = Ceil then compile_ceil x 10000000000 else compile_floor x 10000000000)
      s1 = (op,sb)
Proof
  Cases_on `bt = Ceil` >> simp[] >>
  metis_tac[lower_value_ceil, lower_value_floor]
QED

Theorem straight_fresh_rounding[local]:
  (bt = Ceil \/ bt = Floor) ==>
  straight_fresh
    (if bt = Ceil then compile_ceil x 10000000000 else compile_floor x 10000000000)
Proof
  Cases_on `bt = Ceil` >> simp[straight_fresh_ceil, straight_fresh_floor]
QED

Theorem compile_rounding_stack[local]:
  (bt = Ceil \/ bt = Floor) /\
  compile_expr cenv ty (Builtin ann bt [e]) sa = (vv,sb) ==>
  ?op. vv = StackValue ann op
Proof
  rpt strip_tac >> Cases_on `bt = Ceil` >> gvs[]
  >- (drule compile_ceil_stack >> simp[]) >>
  mp_tac (Q.SPECL [`cenv`, `ann`, `ty`, `Floor`, `[e]`, `sa`, `vv`, `sb`]
    compile_word_builtin_stack) >> simp[]
QED

Theorem word_rounding_sim_full:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a bt args es.
    (!DF lo d ctx shadow_ctx PG func shadow_func cenv cx ty e es.
       (~is_word_type (expr_type e) ==>
        !tvt. evaluate_type (get_tenv cx) (lowered_value_type cenv e) =
                SOME tvt ==> type_memory_size tvt = 0) /\
       expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
         cenv cx ty e es /\
       (!sa. ?t op sb. compile_expr cenv ty e sa = (StackValue t op,sb)) /\
       (!s tv s'. eval_expr cx e s = (INL tv,s') ==> ?v. tv = Value v) ==>
       expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
         cenv cx ty e es) /\
    (bt = Ceil \/ bt = Floor) /\
    (builtin_args_length_ok bt (LENGTH args) ==> body_exprs_full_ok cx args) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin a bt args) es ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a bt args) es /\
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a bt args) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `a = BaseT (IntT 256) /\
   MAP expr_type args = [BaseT DecimalT]` by
    (Cases_on `bt = Ceil` >>
     gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def,
       LENGTH_EQ_NUM_compute]) >>
  `?e. args = [e] /\ expr_type e = BaseT DecimalT` by
    (Cases_on `args` >> gvs[]) >>
  qpat_x_assum `args = [e]` SUBST_ALL_TAC >>
  qpat_x_assum `a = BaseT (IntT 256)` SUBST_ALL_TAC >>
  `!n. bt <> Slice n` by (Cases_on `bt = Ceil` >> gvs[]) >>
  `expr_body_pre cenv cx env e es` by
    (irule expr_body_pre_builtin_arg >> conj_tac
     >- (Cases_on `bt = Ceil` >> gvs[expr_body_pre_def]) >>
     qexistsl [`BaseT (IntT 256)`, `[e]`, `bt`, `es`] >> simp[]) >>
  `is_word_type (expr_type e) /\
   is_word_type (expr_type (Builtin (BaseT (IntT 256)) bt [e]))` by
    simp[vyperASTTheory.expr_type_def, is_word_type_def] >>
  (`expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin (BaseT (IntT 256)) bt [e]) es` suffices_by
    (strip_tac >> conj_tac >- asm_rewrite_tac[] >> first_x_assum irule >>
     simp[vyperASTTheory.expr_type_def, is_word_type_def] >>
     conj_tac
     >- (gen_tac >>
         Cases_on `compile_expr cenv ty (Builtin (BaseT (IntT 256)) bt [e]) sa` >>
         drule_all compile_rounding_stack >> strip_tac >> metis_tac[]) >>
     metis_tac[eval_expr_builtin_value]) >>
  `expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty e es` by
    (gvs[builtin_args_length_ok_def, body_exprs_full_ok_def,
         body_expr_full_ok_def] >> metis_tac[]) >>
  rewrite_tac[expr_sim_full_def] >> rpt gen_tac >> strip_tac >>
  drule_all lower_value_rounding >> strip_tac >>
  rename1 `(if bt = Ceil then compile_ceil x 10000000000 else compile_floor x 10000000000) s1 = (op,sb)` >>
  Cases_on `lower_value compile_expr cenv ty
              (gas_shadow_expr e) shadow_sa` >>
  rename1 `lower_value _ _ _ _ shadow_sa = (shadow_x,shadow_s1)` >>
  `shadow_x = x /\ gas_shadow_state s1 shadow_s1` by
    (mp_tac (Q.INST [`cenv` |-> `cenv`, `ty` |-> `ty`, `e` |-> `e`]
      gas_shadow_stmt_lower_value) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >> metis_tac[pairTheory.FST, pairTheory.SND]) >>
  drule_all expr_body_pre_lower_value_word_shape >> strip_tac >>
  `straight_fresh
    (if bt = Ceil then compile_ceil x 10000000000 else compile_floor x 10000000000)` by
    metis_tac[straight_fresh_rounding] >>
  `cs_extends s1 sb /\ s1.cs_next_var <= sb.cs_next_var` by
    (qpat_assum `(if _ then _ else _) _ = _`
       (mp_then Any mp_tac straight_fresh_cs_extends) >>
     simp[CONV_RULE (DEPTH_CONV ETA_CONV) straight_fresh_rounding]) >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `fn_has_code shadow_sa shadow_s1 shadow_func` by
    (`lower_value compile_expr cenv ty
        (Builtin (BaseT (IntT 256)) bt [gas_shadow_expr e]) shadow_sa =
          (op,shadow_sb)` by
       (Cases_on `bt = Ceil` >>
        gvs[gasShadowTheory.gas_shadow_expr_def, gasShadowTheory.gas_shadow_builtin_def]) >>
     mp_tac (Q.INST [`e` |-> `gas_shadow_expr e`, `sa` |-> `shadow_sa`,
       `sb` |-> `shadow_sb`, `ann` |-> `BaseT (IntT 256)`] lower_value_rounding) >>
     asm_rewrite_tac[] >> strip_tac >>
     `cs_extends shadow_s1 shadow_sb` by
       (Cases_on `bt = Ceil` >> gvs[] >>
        metis_tac[straight_fresh_cs_extends, straight_fresh_ceil, straight_fresh_floor]) >>
     `cs_extends shadow_sa shadow_s1` by metis_tac[exprLoweringPropsTheory.compile_expr_grows] >>
     metis_tac[fragExecTheory.fn_has_code_split]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule unop_operand_admissible >>
     qexistsl [`BaseT (IntT 256)`, `bt`] >>
     Cases_on `bt = Ceil` >>
     gvs[builtin_args_length_ok_def, vyperInterpreterTheory.precompile_builtin_def]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ e _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `s1`, `shadow_sa`, `shadow_s1`,
                           `x`, `s0`, `G0`, `tn0`] mp_tac) >>
  simp[] >> disch_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ RoundingChildPost _` >>
  `bt <> Len /\ ~precompile_builtin bt /\ builtin_args_length_ok bt 1` by
    (Cases_on `bt = Ceil` >>
     gvs[builtin_args_length_ok_def, vyperInterpreterTheory.precompile_builtin_def]) >>
  simp[eval_expr_unop_action_general] >>
  irule gas_outcome_full_bind_all >>
  conj_tac
  >- (gen_tac >> simp[vyperStorageTraceTheory.storage_trace_frame_def,
                     unop_result_def]) >>
  conj_tac
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
      metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >>
      simp[]) >>
  conj_tac
  >- (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
           vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
  qexists_tac `\H res ee G tn t. RoundingChildPost H res ee G tn t /\ ~t.vs_halted` >>
  reverse conj_tac
  >- (qpat_assum `gas_outcome_full _ _ _ _ _ _ RoundingChildPost _`
        (mp_then Any mp_tac gas_outcome_full_post_source) >>
      disch_then irule >> simp[] >> rpt gen_tac >>
      Cases_on `res` >> simp[]) >>
  rpt gen_tac >> strip_tac >> disj1_tac >> BETA_TAC >>
  simp[vyperASTTheory.expr_type_def, is_word_type_def] >>
  qpat_assum `expr_type e = BaseT DecimalT`
    (fn ty_eq => irule (SIMP_RULE (srw_ss())
       [ty_eq, vyperASTTheory.expr_type_def, is_word_type_def]
       (Q.INST [`e` |-> `e`] rounding_continuation_full))) >>
  simp[Abbr `RoundingChildPost`, NoAsms] >>
  asm_rewrite_tac[] >>
  rpt conj_tac
  >- (qexists_tac `marks` >> asm_rewrite_tac[])
  >- (qexistsl_tac [`s1`, `x`] >> simp[] >> metis_tac[]) >>
  qexists_tac `env` >> asm_rewrite_tac[])
QED
