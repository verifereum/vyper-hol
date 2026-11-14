(* Two-child PowMod256 composition under the agreed suffix interface. *)
Theory bodyFullBuiltinWordPowCompose
Ancestors
  bodyFullPreds bodySimFull bodyFullShared gasOutcomeFullCompose
  exprSimWordBuiltins exprSimSource gasShadowCompileStmtHelpers
  fragGasSeqPtr bodyFullGhostFrame bodyFullBuiltinWordPowPost wordArgsPtr
  gasExemptCert vyperStorageTrace exprSimWordArgs exprLoweringProps
  exprSimHypsDefs exprLowering vyperAST vyperTypeSystem list finite_map words

val _ = Parse.hide "body";

Theorem pow_mod256_sim_full_from_suffix:
  (!DF lo explicit ctx func PG d cenv cx st0 ee sm sb x y op t G1 tn1 ann ts (va:bytes32) (vb:bytes32).
    compile_pow_mod256 x y sm = (op,sb) /\
    eval_operand x t = SOME va /\ eval_operand y t = SOME vb /\
    op_taint tn1 x = {} /\ op_taint tn1 y = {} /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    ~ctx_has_dalloca ctx /\ local_ptrs_reserved cenv sm /\
    (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
    (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
    ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func t /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
         stmt_state_rel H ctx func cenv cx ee t /\
         ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 t) ==>
    ?t' G2 tn2.
      builtin_result cx ee.accounts ann PowMod256 ts
        [IntV (&w2n va); IntV (&w2n vb)] =
        INL (IntV (&w2n (word_exp va vb))) /\
      eval_operand op t' = SOME (word_exp va vb) /\
      op_taint tn2 op = {} /\ op_prov G2 op = NONE /\
      ~t'.vs_halted /\ t'.vs_current_bb = sb.cs_current_bb /\
      t'.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t' /\
      t'.vs_alloca_next = t.vs_alloca_next /\ t'.vs_allocas = t.vs_allocas /\
      t'.vs_memory = t.vs_memory /\ t'.vs_call_ctx = t.vs_call_ctx /\
      t'.vs_accounts = t.vs_accounts /\ t'.vs_transient = t.vs_transient /\
      t'.vs_immutables = t.vs_immutables /\
      t'.vs_gas_readings = t.vs_gas_readings /\
      tn2.t_mem = tn1.t_mem /\ tn2.t_stor = tn1.t_stor /\
      tn2.t_trans = tn1.t_trans /\ tn2.t_imm = tn1.t_imm /\
      (!z. not_fresh_at sm z ==>
         lookup_var z t' = lookup_var z t /\
         FLOOKUP G2 z = FLOOKUP G1 z /\
         op_taint tn2 (Var z) = op_taint tn1 (Var z)) /\
      ghost_kept_at lo cenv ee sm G1 tn1 t G2 tn2 /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
         gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
           (t,G1,tn1) [] (OK t',G2,tn2) /\
         stmt_state_rel H ctx func cenv cx ee t' /\
         ghost_inv_at (DF H) lo d cenv cx ee G2 tn2 t')) ==>
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a args es.
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
    (builtin_args_length_ok PowMod256 (LENGTH args) ==> body_exprs_full_ok cx args) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin a PowMod256 args) es ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a PowMod256 args) es /\
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a PowMod256 args) es
Proof
  disch_then (markerLib.mk_asm "suffix") >>
  rpt gen_tac >> strip_tac >>
  `well_typed_builtin_app a PowMod256 (MAP expr_type args)` by
    gvs[expr_body_pre_def, well_typed_expr_def] >>
  drule (word_builtin_modular_types |> Q.SPECL [`a`, `PowMod256`] |> SIMP_RULE (srw_ss()) []) >>
  strip_tac >>
  gvs[MAP_EQ_CONS] >>
  conj_asm1_tac
  >- (rw[expr_sim_full_def] >>
      drule lower_value_pow_mod256 >> strip_tac >>
      `expr_body_pre cenv cx env x0 es` by
        (drule expr_body_pre_builtin_arg >>
         disch_then (qspecl_then [`x0`, `es`] mp_tac) >>
         simp[] >>
         `expr_sim_inv cenv cx env es` by gvs[expr_body_pre_def] >>
         simp[]) >>
      `body_expr_full_ok cx x0` by
        gvs[vyperContextTheory.builtin_args_length_ok_def, body_exprs_full_ok_def] >>
      `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
         cenv cx ty x0 es` by
        metis_tac[body_expr_full_ok_def] >>
      Cases_on `lower_value compile_expr cenv ty (gas_shadow_expr x0) shadow_sa` >>
      rename1 `lower_value compile_expr cenv ty (gas_shadow_expr x0) shadow_sa = (sx,ss1)` >>
      `sx = x /\ gas_shadow_state s1 ss1` by
        (mp_tac (gas_shadow_stmt_lower_value |> Q.INST [`cenv` |-> `cenv`, `ty` |-> `ty`, `e` |-> `x0`]) >>
         simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
         disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[]) >>
      gvs[] >>
      `cs_extends sa s1 /\ cs_extends s1 s2` by
        metis_tac[CONJUNCT2 exprLoweringPropsTheory.compile_expr_grows] >>
      `cs_extends s2 sb` by
        metis_tac[builtinMathTheory.compile_pow_mod256_def,
                  exprSimAccountsTheory.emit_op_extends_next_var] >>
      `fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
       fn_has_code s2 sb func` by
        metis_tac[fragExecTheory.fn_has_code_split, compileEnvTheory.cs_extends_trans] >>
      `lower_value compile_expr cenv ty
        (Builtin (BaseT (UintT 256)) PowMod256
          [gas_shadow_expr x0; gas_shadow_expr x0']) shadow_sa = (op,shadow_sb)` by
        gvs[gasShadowTheory.gas_shadow_expr_def, gasShadowTheory.gas_shadow_builtin_def] >>
      drule_at (Pat `lower_value _ _ _ (Builtin _ _ _) shadow_sa = _`)
        lower_value_pow_mod256 >> strip_tac >>
      gvs[] >>
      rename1 `lower_value compile_expr cenv ty (gas_shadow_expr x0) shadow_sa = (x,shadow_s1)` >>
      rename1 `lower_value compile_expr cenv ty (gas_shadow_expr x0') shadow_s1 = (shadow_y,shadow_s2)` >>
      `cs_extends shadow_sa shadow_s1 /\ cs_extends shadow_s1 shadow_s2` by
        metis_tac[CONJUNCT2 exprLoweringPropsTheory.compile_expr_grows] >>
      `cs_extends shadow_s2 shadow_sb` by
        metis_tac[builtinMathTheory.compile_pow_mod256_def,
                  exprSimAccountsTheory.emit_op_extends_next_var] >>
      `fn_has_code shadow_sa shadow_s1 shadow_func` by
        metis_tac[fragExecTheory.fn_has_code_split, compileEnvTheory.cs_extends_trans] >>
      qpat_x_assum `expr_sim_full _ _ _ _ x0 es`
        (mp_tac o ONCE_REWRITE_RULE [expr_sim_full_def]) >>
      disch_then (qspecl_then [`st0`, `sa`, `s1`, `shadow_sa`, `shadow_s1`,
                              `x`, `s0`, `G0`, `tn0`] mp_tac) >>
      simp[] >>
      `gas_admissible (bind (eval_expr cx x0) (read_result cx)) expr_res_ok es` by
        metis_tac[expr_body_pre_gas_admissible] >>
      simp[] >> strip_tac >>
      qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _`
        (fn th => assume_tac th) >>
      qmatch_asmsub_abbrev_tac `gas_outcome_full cfg cxt cx st0 src start Qchild Rchild` >>
      `gas_outcome_full cfg cxt cx st0 src start
         (\H res ee G tn t. ~t.vs_halted /\ Qchild H res ee G tn t /\ ee.gas_obs = []) Rchild` by
        (Cases_on `cfg` >> PairCases_on `r` >> Cases_on `start` >> PairCases_on `r` >>
         irule gas_outcome_full_post_source >>
         qexistsl_tac [`Qchild`, `Rchild`] >> simp[]) >>
      qpat_x_assum `gas_outcome_full _ _ _ _ _ _ Qchild _` kall_tac >>
      unabbrev_all_tac >>
      `bind (eval_expr cx (Builtin (BaseT (UintT 256)) PowMod256 [x0;x0']))
          (read_result cx) =
       bind (bind (eval_expr cx x0) (read_result cx))
         (\v. bind (bind (eval_expr cx x0') (read_result cx))
           (\w ee. (builtin_result cx ee.accounts (BaseT (UintT 256)) PowMod256
                       [expr_type x0;expr_type x0'] [v;w],ee)))` by
        (`eval_exprs cx [] = return []` by
           simp[FUN_EQ_THM, exprSimWordArgsTheory.eval_exprs_nil, vyperStateTheory.return_def] >>
         simp[exprSimWordArgsTheory.eval_expr_builtin_action,
              exprSimWordArgsTheory.eval_exprs_cons_action,
              vyperContextTheory.builtin_args_length_ok_def,
              vyperInterpreterTheory.precompile_builtin_def,
              vyperInterpreterTheory.code_slice_source_def,
              exprSimWordArgsTheory.eval_exprs_nil,
              vyperStateTheory.bind_assoc, vyperStateTheory.bind_return]) >>
      once_asm_rewrite_tac[] >>
      irule gas_outcome_full_bind_all >>
      irule_at Any (Q.INST [`Q'` |-> `Q`] gasOutcomeFullTheory.gas_outcome_full_post_mono) >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >> simp[] >>
      conj_tac
      >- (rpt gen_tac >> Cases_on `res` >> simp[exprSimDefsTheory.expr_exit_INL]) >>
      conj_tac
      >- (gen_tac >> irule storage_trace_frame_bind_all >>
          simp[evaluate_storage_trace_frame, storage_trace_frame_read_result] >>
          conj_tac
          >- (gen_tac >> simp[storage_trace_frame_def]) >>
          irule storage_trace_frame_bind_all >>
          simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
      conj_tac
      >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >> metis_tac[]) >>
      conj_tac
      >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[]) >>
      conj_tac
      >- (irule storage_trace_frame_bind_all >>
          simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
           rpt gen_tac >> strip_tac >>
           `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
             gvs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
           qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
             (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
           impl_tac >- first_assum ACCEPT_TAC >>
           BETA_TAC >> strip_tac >> gvs[] >>
           `expr_sim_inv cenv cx env mid` by
             (qpat_assum `!tail. _ = (INL v,_)`
                (qspec_then `mid.gas_obs` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
              `expr_body_pre cenv cx env x0
                 (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ mid.gas_obs)` by
                simp[expr_body_pre_def] >>
              metis_tac[exprSimSourceTheory.expr_body_pre_eval]) >>
           `expr_body_pre cenv cx env x0' mid` by
             (irule expr_body_pre_builtin_arg >>
              conj_tac >- first_assum ACCEPT_TAC >>
              qexistsl_tac [`BaseT (UintT 256)`, `[x0;x0']`, `PowMod256`, `es`] >> simp[]) >>
           `body_expr_full_ok cx x0'` by
             (qpat_assum `!tail. _ = (INL v,_)`
                (qspec_then `mid.gas_obs`
                  (strip_assume_tac o SIMP_RULE (srw_ss())
                    [vyperStateTheory.bind_def, AllCaseEqs()])) >>
              gvs[vyperContextTheory.builtin_args_length_ok_def, body_exprs_full_ok_def] >>
              metis_tac[]) >>
           `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
              cenv cx ty x0' mid` by metis_tac[body_expr_full_ok_def] >>
           `shadow_y = y /\ gas_shadow_state s2 shadow_s2` by
             (mp_tac (gas_shadow_stmt_lower_value |> Q.INST
               [`cenv` |-> `cenv`, `ty` |-> `ty`, `e` |-> `x0'`]) >>
              simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
              disch_then (qspecl_then [`s1`, `shadow_s1`] mp_tac) >> simp[]) >>
           gvs[] >>
           rename1 `lower_value compile_expr cenv ty x0' s1 = (y,s2)` >>
           `fn_has_code shadow_s1 shadow_s2 shadow_func` by
             metis_tac[fragExecTheory.fn_has_code_split, compileEnvTheory.cs_extends_trans] >>
           qpat_x_assum `expr_sim_full _ _ _ _ x0' mid`
             (mp_tac o ONCE_REWRITE_RULE [expr_sim_full_def]) >>
           disch_then (qspecl_then [`st0`, `s1`, `s2`, `shadow_s1`, `shadow_s2`,
                                   `y`, `t`, `G1`, `tn1`] mp_tac) >>
           simp[] >>
           impl_tac
           >- (`local_ptrs_reserved cenv s1` by
                 (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
                  qexists_tac `sa` >> simp[] >>
                  metis_tac[CONJUNCT2 exprLoweringPropsTheory.compile_expr_grows]) >>
               `gas_admissible (bind (eval_expr cx x0') (read_result cx)) expr_res_ok mid` by
                 metis_tac[expr_body_pre_gas_admissible] >>
               `expr_post (storage_trace_horizon mid.storage_trace) ctx func cenv cx
                  x0 es sa s1 s0 mid v x t` by metis_tac[] >>
               fs[loweringPostsTheory.expr_post_def] >>
               `sa.cs_next_var <= s1.cs_next_var` by
                 metis_tac[CONJUNCT2 exprLoweringPropsTheory.compile_expr_grows] >>
               conj_tac >- metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
               conj_tac >- metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
               irule bodyMemoryDefsTheory.return_buf_frame_frame >>
               qexistsl_tac [`cenv`, `s0`, `sa`] >> simp[]) >>
           strip_tac >>
           qmatch_asmsub_abbrev_tac `gas_outcome_full cfg cxt cx st0 src (mid,t,G1,tn1) Qsecond Rsecond` >>
           `gas_outcome_full cfg cxt cx st0 src (mid,t,G1,tn1)
              (\H res ee G tn t. ~t.vs_halted /\ Qsecond H res ee G tn t /\ ee.gas_obs = []) Rsecond` by
             (Cases_on `cfg` >> PairCases_on `r` >>
              irule gas_outcome_full_post_source >>
              qexistsl_tac [`Qsecond`, `Rsecond`] >> simp[]) >>
           qpat_x_assum `gas_outcome_full _ _ _ _ _ _ Qsecond _` kall_tac >>
           unabbrev_all_tac >>
           irule gas_outcome_full_bind_all >>
           irule_at Any (Q.INST [`Q'` |-> `Q`] gasOutcomeFullTheory.gas_outcome_full_post_mono) >>
           qpat_assum `gas_outcome_full _ _ _ _ _ (mid,t,G1,tn1) _ _` (irule_at Any) >> simp[] >>
           conj_tac
           >- (rpt gen_tac >> Cases_on `res` >> simp[exprSimDefsTheory.expr_exit_INL]) >>
           conj_tac
           >- (gen_tac >> simp[storage_trace_frame_def]) >>
           conj_tac
           >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >> metis_tac[]) >>
           conj_tac
           >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[]) >>
           conj_tac
           >- (irule storage_trace_frame_bind_all >>
               simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
               rpt gen_tac >> strip_tac >>
               `valid_horizon cx st0 (storage_trace_horizon mid'.storage_trace) mid'.storage_trace` by
                 gvs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
               qpat_assum `!H. valid_horizon _ _ H mid'.storage_trace ==> _`
                 (qspec_then `storage_trace_horizon mid'.storage_trace` mp_tac) >>
               impl_tac >- first_assum ACCEPT_TAC >>
               BETA_TAC >> strip_tac >> gvs[] >>
               `value_has_type (BaseTV (UintT 256)) v /\
                value_has_type (BaseTV (UintT 256)) v'` by
                 (conj_tac
                  >- (mp_tac (Q.SPECL [`cenv`, `cx`, `env`, `x0`,
                        `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
                        `v`, `mid with gas_obs := []`]
                        (CONV_RULE (DEPTH_CONV ETA_CONV) expr_body_pre_word_value)) >>
                      (impl_tac
                       >- (conj_tac >- simp[expr_body_pre_def] >>
                           conj_tac >- simp[compileEnvTheory.is_word_type_def] >>
                           qpat_assum `!tail. bind (eval_expr cx x0) _ _ = _`
                             (qspec_then `[]`
                               (ACCEPT_TAC o PURE_REWRITE_RULE [APPEND_NIL])))) >>
                      simp[vyperValueTheory.evaluate_type_def]) >>
                  mp_tac (Q.SPECL [`cenv`, `cx`, `env`, `x0'`,
                    `mid with gas_obs := gas_explicit marks' t.vs_gas_readings`,
                    `v'`, `mid' with gas_obs := []`]
                    (CONV_RULE (DEPTH_CONV ETA_CONV) expr_body_pre_word_value)) >>
                  (impl_tac
                   >- (conj_tac >- simp[expr_body_pre_def] >>
                       conj_tac >- simp[compileEnvTheory.is_word_type_def] >>
                       qpat_assum `!tail. bind (eval_expr cx x0') _ _ = _`
                         (qspec_then `[]`
                           (ACCEPT_TAC o PURE_REWRITE_RULE [APPEND_NIL])))) >>
                  simp[vyperValueTheory.evaluate_type_def]) >>
               `word_value v /\ word_value v'` by
                 (mp_tac (Q.SPECL [`BaseT (UintT 256)`, `get_tenv cx`,
                                   `BaseTV (UintT 256)`, `v`] exprSimSourceTheory.word_value_type_typed) >>
                  mp_tac (Q.SPECL [`BaseT (UintT 256)`, `get_tenv cx`,
                                   `BaseTV (UintT 256)`, `v'`] exprSimSourceTheory.word_value_type_typed) >>
                  simp[vyperValueTheory.evaluate_type_def, exprSimHypsDefsTheory.word_value_type_def]) >>
               `eval_operand x t = SOME (val_to_w256 v)` by
                 (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
                    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
                  impl_tac >- first_assum ACCEPT_TAC >>
                  strip_tac >> drule exprSimWordArgsTheory.expr_post_word_operand >>
                  simp[compileEnvTheory.is_word_type_def, vyperValueTheory.evaluate_type_def]) >>
               `eval_operand y t' = SOME (val_to_w256 v')` by
                 (qpat_assum `!H. valid_horizon _ _ H mid'.storage_trace ==> _`
                    (qspec_then `storage_trace_horizon mid'.storage_trace` mp_tac) >>
                  impl_tac >- first_assum ACCEPT_TAC >>
                  strip_tac >> drule exprSimWordArgsTheory.expr_post_word_operand >>
                  simp[compileEnvTheory.is_word_type_def, vyperValueTheory.evaluate_type_def]) >>
               `(!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l)` by
                 (qpat_assum `lower_value compile_expr cenv ty x0 sa = (x,s1)`
                    (mp_then Any mp_tac expr_body_pre_lower_value_word_shape) >>
                  simp[compileEnvTheory.is_word_type_def] >> metis_tac[]) >>
               `expr_post (storage_trace_horizon mid'.storage_trace) ctx func cenv cx
                  x0' mid s1 s2 t mid' v' y t'` by metis_tac[] >>
               `eval_operand x t' = SOME (val_to_w256 v)` by
                 (Cases_on `x` >> gvs[venomStateTheory.eval_operand_def] >>
                  fs[loweringPostsTheory.expr_post_def] >> metis_tac[]) >>
               `op_taint tn1 x = {} /\ op_taint tn1' y = {}` by
                 metis_tac[bodyPtrDefsTheory.ptr_val_ok_def] >>
               `op_taint tn1' x = {}` by
                 (Cases_on `x` >> fs[bodyPtrDefsTheory.ghost_kept_at_def,
                                    ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
               `local_ptrs_reserved cenv s2` by
                 (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
                  qexists_tac `sa` >> simp[] >>
                  metis_tac[CONJUNCT2 exprLoweringPropsTheory.compile_expr_grows,
                            arithmeticTheory.LESS_EQ_TRANS]) >>
               `!H. valid_horizon cx st0 H mid'.storage_trace ==>
                  stmt_state_rel H ctx func cenv cx mid' t' /\
                  ghost_inv_at (DF H) lo d cenv cx mid' G1' tn1' t'` by
                 (gen_tac >> disch_tac >>
                  qpat_assum `!H. valid_horizon _ _ H mid'.storage_trace ==> _`
                    (qspec_then `H` mp_tac) >>
                  impl_tac >- first_assum ACCEPT_TAC >>
                  strip_tac >> fs[loweringPostsTheory.expr_post_def]) >>
               markerLib.asm "suffix" (fn th =>
                 pop_assum (mp_then Any mp_tac th)) >>
               disch_then (fn th =>
                 qpat_assum `compile_pow_mod256 x y s2 = (op,sb)`
                   (mp_then Any mp_tac th)) >>
               disch_then (fn th =>
                 qpat_assum `eval_operand x t' = SOME (val_to_w256 v)`
                   (mp_then Any mp_tac th)) >>
               disch_then (fn th =>
                 qpat_assum `eval_operand y t' = SOME (val_to_w256 v')`
                   (mp_then Any mp_tac th)) >>
               disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`, `PG`,
                   `BaseT (UintT 256)`, `[BaseT (UintT 256); BaseT (UintT 256)]`] mp_tac) >>
               impl_tac
               >- (simp[] >>
                   `sa.cs_next_var <= s2.cs_next_var` by
                     metis_tac[CONJUNCT2 exprLoweringPropsTheory.compile_expr_grows,
                               arithmeticTheory.LESS_EQ_TRANS] >>
                   conj_tac
                   >- metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
                   metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]) >>
               disch_then (qx_choose_then `u` (qx_choose_then `G2`
                 (qx_choose_then `tn2` strip_assume_tac))) >>
               `v = IntV (&w2n (val_to_w256 v)) /\
                v' = IntV (&w2n (val_to_w256 v'))` by
                 metis_tac[uint_value_word_rep, arithmeticTheory.LESS_EQ_REFL] >>
               `builtin_result cx mid'.accounts (BaseT (UintT 256)) PowMod256
                  [BaseT (UintT 256);BaseT (UintT 256)] [v;v'] =
                INL (IntV (&w2n (word_exp (val_to_w256 v) (val_to_w256 v'))))` by
                 metis_tac[] >>
               `mid with gas_obs := [] = mid` by
                 (qpat_assum `mid.gas_obs = []` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
               `mid' with gas_obs := [] = mid'` by
                 (qpat_assum `mid'.gas_obs = []` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
               `bind (eval_expr cx x0) (read_result cx)
                  (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,mid)` by
                 (qpat_assum `mid with gas_obs := [] = mid` (fn empty =>
                    qpat_assum `!tail. bind (eval_expr cx x0) _ _ = _`
                      (qspec_then `[]`
                        (ACCEPT_TAC o PURE_REWRITE_RULE [APPEND_NIL, empty])))) >>
               `bind (eval_expr cx x0') (read_result cx)
                  (mid with gas_obs := gas_explicit marks' t.vs_gas_readings) = (INL v',mid')` by
                 (qpat_assum `mid' with gas_obs := [] = mid'` (fn empty =>
                    qpat_assum `!tail. bind (eval_expr cx x0') _ _ = _`
                      (qspec_then `[]`
                        (ACCEPT_TAC o PURE_REWRITE_RULE [APPEND_NIL, empty])))) >>
               `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
                 (mp_tac (Q.SPECL [`cx`, `x0`,
                    `es with gas_obs := gas_explicit marks s0.vs_gas_readings`, `INL v`, `mid`]
                    (CONV_RULE (DEPTH_CONV ETA_CONV) forced_eval_expr_preserves_scopes_dom)) >>
                  simp[]) >>
               `MAP FDOM mid.scopes = MAP FDOM mid'.scopes` by
                 (mp_tac (Q.SPECL [`cx`, `x0'`,
                    `mid with gas_obs := gas_explicit marks' t.vs_gas_readings`, `INL v'`, `mid'`]
                    (CONV_RULE (DEPTH_CONV ETA_CONV) forced_eval_expr_preserves_scopes_dom)) >>
                  simp[]) >>
               `MAP FDOM es.scopes = MAP FDOM mid'.scopes` by metis_tac[] >>
               `storage_trace_frame (bind (eval_expr cx x0) (read_result cx))` by
                 (irule storage_trace_frame_bind_all >>
                  simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
               `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) es.storage_trace` by
                 (mp_tac (Q.INST
                    [`f` |-> `bind (eval_expr cx x0) (read_result cx)`,
                     `st` |-> `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
                     `res` |-> `INL v`, `st'` |-> `mid`,
                     `H` |-> `storage_trace_horizon mid.storage_trace`]
                    (INST_TYPE [alpha |-> ``:value``]
                       vyperStorageFootprintTheory.valid_horizon_frame)) >> simp[]) >>
               `stmt_state_rel (storage_trace_horizon mid.storage_trace)
                  ctx func cenv cx es s0` by metis_tac[] >>
               `expr_post (storage_trace_horizon mid.storage_trace) ctx func cenv cx
                  x0 es sa s1 s0 mid v x t` by metis_tac[] >>
               `wb_frame cenv es mid sa s0 t /\ wb_frame cenv mid mid' s1 t t'` by
                 metis_tac[expr_post_frame] >>
               `sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
                s1.cs_next_var <= s2.cs_next_var /\ s1.cs_next_id <= s2.cs_next_id` by
                 (qpat_assum `lower_value compile_expr cenv ty x0 sa = (x,s1)`
                    (mp_then Any strip_assume_tac
                      (CONJUNCT2 exprLoweringPropsTheory.compile_expr_grows)) >>
                  qpat_assum `lower_value compile_expr cenv ty x0' s1 = (y,s2)`
                    (mp_then Any strip_assume_tac
                      (CONJUNCT2 exprLoweringPropsTheory.compile_expr_grows)) >>
                  asm_rewrite_tac[]) >>
               `sa.cs_next_var <= s2.cs_next_var /\ sa.cs_next_id <= s2.cs_next_id` by
                 (conj_tac
                  >- (irule arithmeticTheory.LESS_EQ_TRANS >>
                      qexists_tac `s1.cs_next_var` >> simp[]) >>
                  irule arithmeticTheory.LESS_EQ_TRANS >>
                  qexists_tac `s1.cs_next_id` >> simp[]) >>
               `wb_frame cenv es mid' sa s0 t'` by
                 (irule (INST_TYPE [alpha |-> ``:256``] wb_frame_trans) >>
                  conj_tac >- first_assum ACCEPT_TAC >>
                  conj_tac
                  >- (qexistsl_tac [`mid`, `s1`, `t`] >> simp[]) >>
                  qexistsl_tac [`storage_trace_horizon mid.storage_trace`, `ctx`, `cx`, `func`] >>
                  simp[]) >>
               `ghost_kept_at lo cenv es sa G0 tn0 s0 G1' tn1'` by
                 (`ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
                   ghost_kept_at lo cenv mid s1 G1 tn1 t G1' tn1' /\
                   sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
                   stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx es s0 /\
                   local_ptrs_reserved cenv sa /\ MAP FDOM es.scopes = MAP FDOM mid.scopes /\
                   wb_frame cenv es mid sa s0 t`
                    suffices_by (disch_then (ACCEPT_TAC o MATCH_MP
                      (SPEC_ALL wordArgsPtrTheory.ghost_kept_at_wb_trans))) >> simp[]) >>
               `ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2` by
                 (`ghost_kept_at lo cenv es sa G0 tn0 s0 G1' tn1' /\
                   ghost_kept_at lo cenv mid' s2 G1' tn1' t' G2 tn2 /\
                   sa.cs_next_var <= s2.cs_next_var /\ sa.cs_next_id <= s2.cs_next_id /\
                   stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx es s0 /\
                   local_ptrs_reserved cenv sa /\ MAP FDOM es.scopes = MAP FDOM mid'.scopes /\
                   wb_frame cenv es mid' sa s0 t'`
                    suffices_by (disch_then (ACCEPT_TAC o MATCH_MP
                      (SPEC_ALL wordArgsPtrTheory.ghost_kept_at_wb_trans))) >> simp[]) >>
               irule gas_outcome_full_intro >>
               qexistsl_tac [`G2`, `mid'`, `[]`, `OK u`,
                 `INL (IntV (&w2n (word_exp (val_to_w256 v) (val_to_w256 v'))))`, `tn2`] >>
               simp[gasSummaryTheory.gas_explicit_def] >> rpt strip_tac >>
               `expr_post H ctx func cenv cx x0' mid s1 s2 t mid' v' y t'` by
                 metis_tac[] >>
               simp[loweringPostsTheory.post_value_type_word,
                    vyperASTTheory.expr_type_def,
                    compileEnvTheory.is_word_type_def,
                    bodyPtrDefsTheory.ptr_val_ok_def,
                    exprSimMemDefsTheory.expr_store_bound_word]
               >~ [`expr_post _ _ _ _ _ (Builtin _ PowMod256 _) _ _ _ _ _ _ _ _`]
               >- (`stmt_state_rel H ctx func cenv cx mid' u` by metis_tac[] >>
                   `storage_well_formed_on cx mid' (FST H)` by
                     (qpat_assum `expr_post H ctx func cenv cx x0' mid s1 s2 t mid' v' y t'`
                        (strip_assume_tac o PURE_REWRITE_RULE [loweringPostsTheory.expr_post_def]) >>
                      first_assum ACCEPT_TAC) >>
                   irule (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``, gamma |-> ``:256``]
                     pow_mod256_parent_post) >>
                   simp[compileEnvTheory.is_word_type_def,
                        loweringSliceTheory.word_value_def,
                        valueEncodingTheory.val_to_w256_def,
                        integer_wordTheory.i2w_w2n] >>
                   conj_tac
                   >- (qexists_tac `storage_trace_horizon mid.storage_trace` >>
                       first_assum ACCEPT_TAC) >>
                   qexistsl_tac [`storage_trace_horizon mid.storage_trace`, `H`,
                     `mid`, `s1`, `s2`, `t`, `t'`, `v`, `v'`, `x`, `y`] >> simp[]) >>
               qpat_x_assum `~is_word_type (expr_type (Builtin _ PowMod256 _))`
                 (mp_tac o SIMP_RULE (srw_ss())
                   [vyperASTTheory.expr_type_def, compileEnvTheory.is_word_type_def]) >>
               simp[]) >>
  qpat_x_assum `!DF lo d ctx shadow_ctx PG func shadow_func cenv cx ty e es. _ ==> expr_vv_sim_full _ _ _ _ _ _`
    match_mp_tac >>
  simp[vyperASTTheory.expr_type_def, compileEnvTheory.is_word_type_def] >>
  conj_tac
  >- (gen_tac >>
      qmatch_goalsub_abbrev_tac `compile_expr cenv ty ee sa` >>
      Cases_on `compile_expr cenv ty ee sa` >> fs[Abbr `ee`] >>
      drule_at Any compile_word_builtin_stack >> simp[] >>
      strip_tac >> gvs[] >> metis_tac[]) >>
  metis_tac[eval_expr_builtin_value]
QED
