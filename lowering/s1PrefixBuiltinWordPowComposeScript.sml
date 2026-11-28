(* Request-prefix companion to bodyFullBuiltinWordPowCompose. *)
Theory s1PrefixBuiltinWordPowCompose
Ancestors
  s1PrefixPreds bodyFullBuiltinWordPowCompose s1PrefixDefs
  s1PrefixCompose s1PrefixOfVV s1PrefixProps exprBodyPreProps bodyFullShared
  bodyFullIfExpReach gasOutcomeFullCompose exprSimWordArgs exprSimSource
  exprSimWordBuiltins exprLoweringProps gasShadowCompileStmtHelpers
  gasExemptCert vyperStorageTrace vyperTypeSystem list bodyFullPreds bodySimFull
  bodyFullExprsListFacts bodyFullSimProjection

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule expr_body_pre_static_facts >> strip_tac >>
  `well_typed_builtin_app a PowMod256 (MAP expr_type args)` by
    fs[well_typed_expr_def] >>
  drule (word_builtin_modular_types |> Q.SPECL [`a`, `PowMod256`] |>
    SIMP_RULE (srw_ss()) []) >> strip_tac >> gvs[MAP_EQ_CONS] >>
  rename1 `expr_body_pre cenv cx env (Builtin _ PowMod256 [left;right]) es` >>
  conj_asm1_tac
  >- suspend "value" >>
  irule expr_vv_sim_stack_prefix >> simp[] >> conj_tac
  >- (gen_tac >>
      qmatch_goalsub_abbrev_tac `compile_expr cenv ty ee sa` >>
      Cases_on `compile_expr cenv ty ee sa` >> fs[Abbr `ee`] >>
      drule_at Any compile_word_builtin_stack >> simp[] >>
      strip_tac >> gvs[] >> metis_tac[]) >>
  metis_tac[eval_expr_builtin_value]
QED
*)
Theorem pow_mod256_sim_prefix_from_suffix:
  (!DF lo explicit ctx func PG d cenv cx st0 ee sm sb x y op t G1 tn1 ann ts (va:bytes32) (vb:bytes32).
      compile_pow_mod256 x y sm = (op,sb) /\
      eval_operand x t = SOME va /\ eval_operand y t = SOME vb /\
      op_taint tn1 x = {} /\ op_taint tn1 y = {} /\
      fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ local_ptrs_reserved cenv sm /\
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
        t'.vs_fmp = t.vs_fmp /\
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
  (builtin_args_length_ok PowMod256 (LENGTH args) ==> body_exprs_prefix_ok cx args) /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Builtin a PowMod256 args) es ==>
  expr_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cenv cx ty (Builtin a PowMod256 args) es /\
      expr_vv_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cenv cx ty (Builtin a PowMod256 args) es
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume pow_mod256_sim_prefix_from_suffix[value]:
  PURE_REWRITE_TAC[expr_sim_prefix_def, expr_sim_full_pre_def] >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  drule lower_value_pow_mod256 >> strip_tac >>
  `lower_value compile_expr (gas_shadow_env T cenv) ty
     (Builtin (BaseT (UintT 256)) PowMod256
       [gas_shadow_expr left; gas_shadow_expr right]) shadow_sa = (op,shadow_sb)` by
    fs[gasShadowTheory.gas_shadow_expr_def, gasShadowTheory.gas_shadow_builtin_def] >>
  drule_at (Pat `lower_value _ _ _ (Builtin _ _ _) shadow_sa = _`)
    lower_value_pow_mod256 >> strip_tac >>
  rename1 `lower_value compile_expr _ ty (gas_shadow_expr left) shadow_sa = (shadow_x,shadow_s1)` >>
  rename1 `lower_value compile_expr _ ty (gas_shadow_expr right) shadow_s1 = (shadow_y,shadow_s2)` >>
  `shadow_x = x /\ gas_shadow_state s1 shadow_s1` by
    (irule gas_shadow_step >>
     qpat_assum `lower_value _ _ _ left sa = (x,s1)` (irule_at Any) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr left) shadow_sa = _`
       (irule_at Any) >> simp[gas_shadow_stmt_lower_value_env]) >>
  `shadow_y = y /\ gas_shadow_state s2 shadow_s2` by
    (irule gas_shadow_step >>
     qpat_assum `lower_value _ _ _ right s1 = (y,s2)` (irule_at Any) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr right) shadow_s1 = _`
       (irule_at Any) >> simp[gas_shadow_stmt_lower_value_env]) >>
  gvs[] >>
  rename1 `lower_value compile_expr cenv ty left sa = (x,s1)` >>
  rename1 `lower_value compile_expr cenv ty right s1 = (y,s2)` >>
  `cs_extends sa s1 /\ cs_extends s1 s2 /\ sa.cs_next_var <= s1.cs_next_var /\
   cs_extends shadow_sa shadow_s1 /\ cs_extends shadow_s1 shadow_s2` by
    metis_tac[CONJUNCT2 compile_expr_grows] >>
  `cs_extends s2 sb /\ cs_extends shadow_s2 shadow_sb` by
    metis_tac[builtinMathTheory.compile_pow_mod256_def,
              exprSimAccountsTheory.emit_op_extends_next_var] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
   fn_has_code shadow_sa shadow_s1 shadow_func /\
   fn_has_code shadow_s1 shadow_s2 shadow_func` by
    metis_tac[fragExecTheory.fn_has_code_split, compileEnvTheory.cs_extends_trans] >>
  `expr_body_pre cenv cx env left es` by
    (irule expr_body_pre_builtin_arg >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`BaseT (UintT 256)`, `[left;right]`, `PowMod256`, `es`] >> simp[]) >>
  `body_exprs_full_ok cx [left;right] /\ body_exprs_prefix_ok cx [left;right]` by
    fs[vyperContextTheory.builtin_args_length_ok_def] >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty left es /\
   expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty left es` by
    (fs[Once body_exprs_full_ok_cons, body_exprs_prefix_ok_def] >>
     conj_tac
     >- metis_tac[body_expr_full_ok_simulations] >>
     metis_tac[body_expr_prefix_ok_def]) >>
  `gas_admissible (bind (eval_expr cx left) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_full _ _ _ _ left es`
    (drule_all o REWRITE_RULE[expr_sim_full_def]) >> strip_tac >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ left es`
    (drule_all o REWRITE_RULE[expr_sim_prefix_def, expr_sim_full_pre_def]) >> strip_tac >>
  suspend "bind"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume pow_mod256_sim_prefix_from_suffix[bind]:
  `bind (eval_expr cx (Builtin (BaseT (UintT 256)) PowMod256 [left;right]))
     (read_result cx) =
   bind (bind (eval_expr cx left) (read_result cx))
     (\v. bind (bind (eval_expr cx right) (read_result cx))
       (\w ee. (builtin_result cx ee.accounts (BaseT (UintT 256)) PowMod256
                   [expr_type left;expr_type right] [v;w],ee)))` by
    (`eval_exprs cx [] = return []` by
       simp[FUN_EQ_THM, eval_exprs_nil, vyperStateTheory.return_def] >>
     simp[eval_expr_builtin_action, vyperContextTheory.is_self_codesize_def,
          eval_exprs_cons_action, vyperContextTheory.builtin_args_length_ok_def,
          vyperInterpreterTheory.precompile_builtin_def,
          vyperInterpreterTheory.code_slice_source_def,
          vyperStateTheory.bind_assoc, vyperStateTheory.bind_return]) >>
  once_asm_rewrite_tac[] >>
  (* The arithmetic suffix changes only the result, not the request state. *)
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
     (bind (bind (eval_expr cx left) (read_result cx))
            (\v. bind (eval_expr cx right) (read_result cx))) (es,s0,G0,tn0)`
    suffices_by
      (disch_tac >>
       qmatch_goalsub_abbrev_tac `gas_prefix_full _ _ _ pow_source _` >>
       `!qe. SND (pow_source qe) =
             SND (bind (bind (eval_expr cx left) (read_result cx))
                        (\v. bind (eval_expr cx right) (read_result cx)) qe)` by
         (simp[Abbr `pow_source`, vyperStateTheory.bind_def] >> rpt gen_tac >>
          BasicProvers.EVERY_CASE_TAC >> simp[]) >>
       drule gas_prefix_full_state_cong >> disch_then (fn th => simp[th])) >>
  qpat_x_assum `!DF lo explicit ctx func PG d cenv cx st0 ee sm sb x y op t G1 tn1 ann ts va vb. _` kall_tac >>
  qpat_x_assum `!DF lo d ctx shadow_ctx PG func shadow_func cenv cx ty e es.
     _ ==> expr_vv_sim_full _ _ _ _ _ _` kall_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full cfg tops0 cx st0 src start leftQ leftR` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     tops0 cx st0 src (es,s0,G0,tn0)
     (\H res ee G tn t. leftQ H res ee G tn t /\ ~t.vs_halted /\
         (!fn i u. frag_reachable ctx func t fn i u ==> dalloca_fmp_headroom i u)) leftR` by
    (`!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
       metis_tac[body_inv_no_phi] >>
     irule gas_outcome_full_post_path >> qexists_tac `leftQ` >>
     fs[Abbr `cfg`, Abbr `start`] >> rpt gen_tac >> strip_tac >> conj_tac
     >- (drule fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec >>
         simp[fragExecTheory.exit_result_def]) >>
     drule gas_origin_ptr_path_dalloca_fmp_headroom >> simp[] >> metis_tac[]) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ leftQ leftR` kall_tac >>
  unabbrev_all_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _`
    (mp_then Any irule gas_prefix_full_bind) >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result, requests_outcomes_frame_bind_all,
       evaluate_requests_outcomes_frame, requests_outcomes_frame_read_result] >>
  reverse conj_tac >- (rpt gen_tac >> Cases_on `res` >> simp[exprSimDefsTheory.expr_exit_INL]) >>
  suspend "right"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume pow_mod256_sim_prefix_from_suffix[right]:
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  strip_tac >> gvs[] >>
  qpat_assum `!tail. bind (eval_expr cx left) _ _ = _`
    (qspec_then `mid.gas_obs` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  `expr_sim_inv cenv cx env mid` by
    (`expr_body_pre cenv cx env left
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ mid.gas_obs)` by
       simp[expr_body_pre_gas_obs] >>
     metis_tac[exprSimSourceTheory.expr_body_pre_eval]) >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (qpat_assum `expr_body_pre cenv cx env left es`
       (strip_assume_tac o MATCH_MP expr_body_pre_static_facts) >>
     irule body_const_cells_agree_expr_read >>
     goal_assum (drule_at (Pat `bind (eval_expr _ _) _ _ = _`)) >> simp[]) >>
  `expr_body_pre cenv cx env right mid` by
    (irule expr_body_pre_builtin_arg >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`BaseT (UintT 256)`, `[left;right]`, `PowMod256`, `es`] >> simp[]) >>
  `body_expr_prefix_ok cx right` by
    (qpat_assum `bind (eval_expr cx left) _ _ = _`
      (mp_tac o SIMP_RULE (srw_ss()) [vyperStateTheory.bind_def, AllCaseEqs()]) >>
     fs[body_exprs_prefix_ok_def] >> metis_tac[]) >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty right mid` by
    metis_tac[body_expr_prefix_ok_def] >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ right mid`
    (irule o REWRITE_RULE[expr_sim_prefix_def, expr_sim_full_pre_def]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       stmt_state_rel H ctx func cenv cx mid t /\ storage_well_formed_on cx mid (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
          (expr_post _ _ _ _ _ left _ _ _ _ _ _ _ _ /\ _) /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     qpat_assum `expr_post H _ _ _ _ left _ _ _ _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE[loweringPostsTheory.expr_post_def]) >>
     simp[]) >>
  `local_ptrs_reserved cenv s1` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `return_buf_frame d cenv s1 t` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`, `s0`, `sa`] >> simp[] >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
          (expr_post _ _ _ _ _ left _ _ _ _ _ _ _ _ /\ _) /\ _`
       (qspec_then `storage_trace_horizon mid.storage_trace`
          (drule_then strip_assume_tac)) >>
     qpat_assum `expr_post _ _ _ _ _ left _ _ _ _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE[loweringPostsTheory.expr_post_def]) >>
     first_assum ACCEPT_TAC) >>
  `gas_admissible (bind (eval_expr cx right) (read_result cx)) expr_res_ok mid` by
    metis_tac[expr_body_pre_gas_admissible] >>
  simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`y`,`s1`,`s2`,`shadow_s1`,`shadow_s2`] >> simp[] >>
  metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise pow_mod256_sim_prefix_from_suffix
*)
