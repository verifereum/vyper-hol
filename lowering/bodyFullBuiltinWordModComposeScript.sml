(* Three-child full composition, conditional on the modular suffix interface. *)
Theory bodyFullBuiltinWordModCompose
Ancestors
  bodyFullPreds bodySimFull bodyFullShared gasOutcomeFullCompose
  bodyFullBuiltinWordModPost bodyFullGhostFrame
  exprSimWordBuiltins exprSimSource exprSimHypsDefs exprLowering
  compileEnv exprLoweringProps vyperTyping vyperTypeSystem list finite_map
  gasShadowCompileStmtHelpers gasShadowState builtinMath fragExec wordArgsPtr

val _ = Parse.hide "body";

Theorem modular_sim_full_from_suffix:
  (!DF lo explicit ctx func PG d cenv cx st0 ee sm sb bt x y z op t G1 tn1 ann ts (va:bytes32) (vb:bytes32) (vc:bytes32).
    (bt = AddMod \/ bt = MulMod) /\
    (if bt = AddMod then compile_addmod else compile_mulmod) x y z sm = (op,sb) /\
    eval_operand x t = SOME va /\ eval_operand y t = SOME vb /\
    eval_operand z t = SOME vc /\
    op_taint tn1 x = {} /\ op_taint tn1 y = {} /\ op_taint tn1 z = {} /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    ~ctx_has_dalloca ctx /\ local_ptrs_reserved cenv sm /\
    (!q sz. cenv.ce_return_buf = SOME (PtrVar (Var q) sz) ==> not_fresh_at sm q) /\
    (!q sz. cenv.ce_return_pc = SOME (PtrVar (Var q) sz) ==> not_fresh_at sm q) /\
    ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func t /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func cenv cx ee t /\
      ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 t) ==>
    ?r t' G2 tn2.
      (vc = 0w ==>
        r = Abort Revert_abort t' /\ G2 = G1 /\ tn2 = tn1 /\
        builtin_result cx ee.accounts ann bt ts
          [IntV (&w2n va); IntV (&w2n vb); IntV (&w2n vc)] =
          INR (Error (RuntimeError (if bt = AddMod then
            "AddMod division by zero" else "MulMod division by zero"))) /\
        exit_result r /\
        expr_exit (builtin_result cx ee.accounts ann bt ts
          [IntV (&w2n va); IntV (&w2n vb); IntV (&w2n vc)]) r) /\
      (vc <> 0w ==>
        r = OK t' /\
        builtin_result cx ee.accounts ann bt ts
          [IntV (&w2n va); IntV (&w2n vb); IntV (&w2n vc)] =
          INL (IntV (&w2n ((if bt = AddMod then addmod else mulmod) va vb vc))) /\
        eval_operand op t' = SOME ((if bt = AddMod then addmod else mulmod) va vb vc) /\
        op_taint tn2 op = {} /\ op_prov G2 op = NONE /\
        ~t'.vs_halted /\ t'.vs_current_bb = sb.cs_current_bb /\
        t'.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func t' /\
        t'.vs_alloca_next = t.vs_alloca_next /\ t'.vs_allocas = t.vs_allocas /\
        t'.vs_memory = t.vs_memory /\ t'.vs_call_ctx = t.vs_call_ctx /\
        t'.vs_accounts = t.vs_accounts /\ t'.vs_transient = t.vs_transient /\
        t'.vs_immutables = t.vs_immutables /\
        t'.vs_gas_readings = t.vs_gas_readings /\
        tn2.t_mem = tn1.t_mem /\ tn2.t_stor = tn1.t_stor /\
        tn2.t_trans = tn1.t_trans /\ tn2.t_imm = tn1.t_imm /\
        (!q. not_fresh_at sm q ==>
          lookup_var q t' = lookup_var q t /\
          FLOOKUP G2 q = FLOOKUP G1 q /\
          op_taint tn2 (Var q) = op_taint tn1 (Var q)) /\
        ghost_kept_at lo cenv ee sm G1 tn1 t G2 tn2) /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
          (t,G1,tn1) [] (r,G2,tn2) /\
        (vc <> 0w ==>
          stmt_state_rel H ctx func cenv cx ee t' /\
          ghost_inv_at (DF H) lo d cenv cx ee G2 tn2 t'))) ==>
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a bt args es.
    (!DF lo d ctx shadow_ctx PG func shadow_func cenv cx ty e es.
      (~is_word_type (expr_type e) ==>
        !tvt. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tvt ==>
          type_memory_size tvt = 0) /\
      expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es /\
      (!sa. ?t op sb. compile_expr cenv ty e sa = (StackValue t op,sb)) /\
      (!s tv s'. eval_expr cx e s = (INL tv,s') ==> ?v. tv = Value v) ==>
      expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es) /\
    (bt = AddMod \/ bt = MulMod) /\
    (builtin_args_length_ok bt (LENGTH args) ==> body_exprs_full_ok cx args) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin a bt args) es ==>
    expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin a bt args) es /\
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin a bt args) es
Proof
  disch_then (markerLib.mk_asm "suffix") >> rpt gen_tac >> strip_tac >>
  (
  (`a = BaseT (UintT 256) /\
   MAP expr_type args = [BaseT (UintT 256); BaseT (UintT 256); BaseT (UintT 256)]` by
    (fs[expr_body_pre_def, well_typed_expr_def] >>
     imp_res_tac word_builtin_modular_types >>
     gvs[]) >>
  `?e1 e2 e3. args = [e1;e2;e3]` by
    (gvs[MAP_EQ_CONS, MAP_EQ_NIL] >> metis_tac[]) >>
  gvs[] >>
  conj_asm1_tac
  >- (rw[expr_sim_full_def] >>
      drule_at Any lower_value_ternary_modular >> simp[] >> strip_tac >>
      `expr_body_pre cenv cx env e1 es` by
        (drule expr_body_pre_builtin_arg >>
         disch_then (qspecl_then [`e1`, `es`] mp_tac) >>
         simp[] >> fs[expr_body_pre_def]) >>
      `body_expr_full_ok cx e1` by
        (fs[vyperContextTheory.builtin_args_length_ok_def, body_exprs_full_ok_def]) >>
      `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e1 es` by
        (fs[body_expr_full_ok_def] >> metis_tac[]) >>
      `!e. MEM e [e1;e2;e3] ==> expr_body_pre cenv cx env e es` by
        (gen_tac >> strip_tac >> drule expr_body_pre_builtin_arg >>
         disch_then (qspecl_then [`e`, `es`] mp_tac) >>
         simp[] >> fs[expr_body_pre_def]) >>
      `cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var /\
       sa.cs_next_id <= s1.cs_next_id /\
       (!q. x = Var q ==> not_fresh_at s1 q)` by
        (qpat_assum `lower_value _ _ _ e1 _ = _`
           (mp_then Any mp_tac expr_body_pre_lower_value_word_shape) >>
         simp[is_word_type_def] >>
         disch_then (qspecl_then [`cx`, `env`, `es`] mp_tac) >> simp[]) >>
      `cs_extends s1 s2 /\ cs_extends s2 s3` by
        (conj_tac
         >- (qpat_assum `lower_value _ _ _ e2 s1 = _`
               (ACCEPT_TAC o CONJUNCT1 o MATCH_MP (cj 2 compile_expr_grows))) >>
         qpat_assum `lower_value _ _ _ e3 s2 = _`
           (ACCEPT_TAC o CONJUNCT1 o MATCH_MP (cj 2 compile_expr_grows))) >>
      `cs_extends s3 sb` by
        (qpat_x_assum `f x y z s3 = (op,sb)` mp_tac >>
         simp[compile_addmod_def, compile_mulmod_def, comp_bind_def,
              comp_ignore_bind_def] >>
         rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
         metis_tac[cs_appends_emit_helpers, cs_appends_def, cs_extends_trans]) >>
      `cs_extends s2 sb` by
        (irule cs_extends_trans >> qexists_tac `s3` >> asm_rewrite_tac[]) >>
      `cs_extends s1 sb` by
        (irule cs_extends_trans >> qexists_tac `s2` >> asm_rewrite_tac[]) >>
      `fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
       fn_has_code s2 s3 func /\ fn_has_code s3 sb func` by
        (mp_tac (Q.SPECL [`sa`, `s1`, `sb`, `func`] fn_has_code_split) >>
         asm_rewrite_tac[] >> strip_tac >>
         mp_tac (Q.SPECL [`s1`, `s2`, `sb`, `func`] fn_has_code_split) >>
         asm_rewrite_tac[] >> strip_tac >>
         mp_tac (Q.SPECL [`s2`, `s3`, `sb`, `func`] fn_has_code_split) >>
         asm_rewrite_tac[] >> strip_tac >> asm_rewrite_tac[]) >>
      `?sh1. lower_value compile_expr cenv ty (gas_shadow_expr e1) shadow_sa = (x,sh1) /\
        gas_shadow_state s1 sh1` by
        (Cases_on `lower_value compile_expr cenv ty (gas_shadow_expr e1) shadow_sa` >>
         mp_tac (Q.INST [`cenv` |-> `cenv`, `ty` |-> `ty`, `e` |-> `e1`] gas_shadow_stmt_lower_value) >>
         simp[gas_shadow_compiles_def] >>
         disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[]) >>
      `?sh2. lower_value compile_expr cenv ty (gas_shadow_expr e2) sh1 = (y,sh2) /\
        gas_shadow_state s2 sh2` by
        (Cases_on `lower_value compile_expr cenv ty (gas_shadow_expr e2) sh1` >>
         mp_tac (Q.INST [`cenv` |-> `cenv`, `ty` |-> `ty`, `e` |-> `e2`] gas_shadow_stmt_lower_value) >>
         simp[gas_shadow_compiles_def] >>
         disch_then (qspecl_then [`s1`, `sh1`] mp_tac) >> simp[]) >>
      `?sh3. lower_value compile_expr cenv ty (gas_shadow_expr e3) sh2 = (z,sh3) /\
        gas_shadow_state s3 sh3` by
        (Cases_on `lower_value compile_expr cenv ty (gas_shadow_expr e3) sh2` >>
         mp_tac (Q.INST [`cenv` |-> `cenv`, `ty` |-> `ty`, `e` |-> `e3`] gas_shadow_stmt_lower_value) >>
         simp[gas_shadow_compiles_def] >>
         disch_then (qspecl_then [`s2`, `sh2`] mp_tac) >> simp[]) >>
      `cs_extends shadow_sa sh1 /\ cs_extends sh1 sh2 /\ cs_extends sh2 sh3` by
        (rpt conj_tac
         >- (qpat_assum `lower_value _ _ _ (gas_shadow_expr e1) shadow_sa = _`
               (ACCEPT_TAC o CONJUNCT1 o MATCH_MP (cj 2 compile_expr_grows)))
         >- (qpat_assum `lower_value _ _ _ (gas_shadow_expr e2) sh1 = _`
               (ACCEPT_TAC o CONJUNCT1 o MATCH_MP (cj 2 compile_expr_grows))) >>
         qpat_assum `lower_value _ _ _ (gas_shadow_expr e3) sh2 = _`
           (ACCEPT_TAC o CONJUNCT1 o MATCH_MP (cj 2 compile_expr_grows))) >>
      `cs_extends sh3 shadow_sb` by
        (qpat_x_assum `lower_value _ _ _ (gas_shadow_expr (Builtin _ _ _)) _ = _` mp_tac >>
         qpat_x_assum `lower_value _ _ _ (Builtin _ _ _) _ = _` kall_tac >>
         simp[gasShadowTheory.gas_shadow_expr_def] >> strip_tac >>
         drule_at Any lower_value_ternary_modular >>
         simp[gasShadowTheory.gas_shadow_builtin_def] >> strip_tac >> gvs[] >>
         qpat_x_assum `f x y z sh3 = (op,shadow_sb)` mp_tac >>
         rpt (pop_assum kall_tac) >>
         simp[compile_addmod_def, compile_mulmod_def, comp_bind_def,
              comp_ignore_bind_def] >>
         rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
         metis_tac[cs_appends_emit_helpers, cs_appends_def, cs_extends_trans]) >>
      `cs_extends sh2 shadow_sb` by
        (irule cs_extends_trans >> qexists_tac `sh3` >> asm_rewrite_tac[]) >>
      `cs_extends sh1 shadow_sb` by
        (irule cs_extends_trans >> qexists_tac `sh2` >> asm_rewrite_tac[]) >>
      `fn_has_code shadow_sa sh1 shadow_func /\ fn_has_code sh1 sh2 shadow_func /\
       fn_has_code sh2 sh3 shadow_func` by
        (mp_tac (Q.SPECL [`shadow_sa`, `sh1`, `shadow_sb`, `shadow_func`] fn_has_code_split) >>
         asm_rewrite_tac[] >> strip_tac >>
         mp_tac (Q.SPECL [`sh1`, `sh2`, `shadow_sb`, `shadow_func`] fn_has_code_split) >>
         asm_rewrite_tac[] >> strip_tac >>
         mp_tac (Q.SPECL [`sh2`, `sh3`, `shadow_sb`, `shadow_func`] fn_has_code_split) >>
         asm_rewrite_tac[] >> strip_tac >> asm_rewrite_tac[]) >>
      qpat_x_assum `expr_sim_full _ _ _ _ e1 es`
        (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
      disch_then (qspecl_then [`st0`, `sa`, `s1`, `shadow_sa`, `sh1`, `x`, `s0`, `G0`, `tn0`] mp_tac) >>
      (impl_tac >- (simp[] >>
        qpat_assum `expr_body_pre cenv cx env e1 es`
          (ACCEPT_TAC o MATCH_MP expr_body_pre_gas_admissible))) >>
      disch_tac >>
      qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ P1 E1` >>
      `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (cx_tops cx) cx st0 (bind (eval_expr cx e1) (read_result cx))
         (es,s0,G0,tn0)
         (\H res ee G tn t. ~t.vs_halted /\ ee.gas_obs = [] /\ P1 H res ee G tn t) E1` by
        (irule gas_outcome_full_post_source >>
         qexistsl [`P1`, `E1`] >> simp[]) >>
      qpat_x_assum `gas_outcome_full _ _ _ _ _ _ P1 E1` kall_tac >>
      unabbrev_all_tac >>
      simp[exprSimWordArgsTheory.eval_expr_builtin_action,
           vyperInterpreterTheory.precompile_builtin_def,
           vyperInterpreterTheory.code_slice_source_def,
           vyperContextTheory.builtin_args_length_ok_def,
           exprSimWordArgsTheory.eval_exprs_cons_action, vyperStateTheory.bind_assoc] >>
      once_rewrite_tac[GSYM vyperStateTheory.bind_assoc] >>
      irule gas_outcome_full_bind_all >>
      irule_at Any (Q.INST [`Q'` |-> `Q`] gasOutcomeFullTheory.gas_outcome_full_post_mono) >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
      simp[] >>
      conj_tac
      >- (rpt gen_tac >> Cases_on `res` >> simp[exprSimDefsTheory.expr_exit_INL]) >>
      conj_tac
      >- (gen_tac >>
          `eval_exprs cx [] = return []` by
            simp[FUN_EQ_THM, exprSimWordArgsTheory.eval_exprs_nil, vyperStateTheory.return_def] >>
          simp[vyperStateTheory.bind_return] >>
          rpt (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
               reverse conj_tac >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
                                       vyperStorageTraceTheory.storage_trace_frame_read_result] >>
               gen_tac >> BETA_TAC) >>
          simp[vyperStorageTraceTheory.storage_trace_frame_def]) >>
      conj_tac
      >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
          metis_tac[]) >>
      conj_tac
      >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >> simp[]) >>
      conj_tac
      >- (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
          simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
               vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
      rpt gen_tac >> strip_tac >>
      `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
        fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
      qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
        (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      strip_tac >> gvs[] >>
      `expr_sim_inv cenv cx env (mid with gas_obs := [])` by
        (irule (expr_body_pre_eval |> SPEC_ALL |> UNDISCH |> CONJUNCT1 |>
                DISCH_ALL |> GEN_ALL) >>
         qexistsl [`e1`, `es with gas_obs := gas_explicit marks s0.vs_gas_readings`, `INL v`] >>
         simp[ETA_AX] >>
         qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
         pure_rewrite_tac[APPEND_NIL] >>
         CONV_TAC (DEPTH_CONV ETA_CONV) >> disch_then ACCEPT_TAC) >>
      `expr_sim_inv cenv cx env mid` by fs[] >>
      `expr_body_pre cenv cx env e2 mid` by
        (drule expr_body_pre_builtin_arg >>
         disch_then (qspecl_then [`e2`, `mid`] mp_tac) >> simp[]) >>
      `body_expr_full_ok cx e2` by
        (fs[vyperContextTheory.builtin_args_length_ok_def, body_exprs_full_ok_def] >>
         `?s tv t s1 v t1. eval_expr cx e1 s = (INL tv,t) /\
                            read_result cx tv s1 = (INL v,t1)` suffices_by metis_tac[] >>
         qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
         pure_rewrite_tac[vyperStateTheory.bind_def, APPEND_NIL, AllCaseEqs()] >>
         strip_tac >> Cases_on `x'` >> gvs[] >>
         goal_assum (drule_at Any) >>
         goal_assum (drule_at Any) >> simp[]) >>
      `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e2 mid` by
        (fs[body_expr_full_ok_def] >> metis_tac[]) >>
      qpat_x_assum `expr_sim_full _ _ _ _ e2 mid`
        (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
      disch_then (qspecl_then [`st0`, `s1`, `s2`, `sh1`, `sh2`, `y`, `t`, `G1`, `tn1`] mp_tac) >>
      (impl_tac >- (simp[] >>
        conj_tac >- metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
        conj_tac >- metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
        conj_tac >- metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
        conj_tac >- (qpat_assum `expr_body_pre cenv cx env e2 mid`
          (ACCEPT_TAC o MATCH_MP expr_body_pre_gas_admissible)) >>
        conj_tac >- (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
          qexistsl [`cenv`, `s0`, `sa`] >> simp[] >>
          metis_tac[cj 6 (iffLR loweringPostsTheory.expr_post_def)]) >>
        gen_tac >> strip_tac >>
        qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> expr_post _ _ _ _ _ e1 _ _ _ _ _ _ _ _ /\ _`
          (qspec_then `H` mp_tac) >>
        (impl_tac >- first_assum ACCEPT_TAC) >>
        disch_then (fn th => CONJ_TAC THENL
          [ACCEPT_TAC (MATCH_MP (cj 1 (iffLR loweringPostsTheory.expr_post_def)) (CONJUNCT1 th)),
           ACCEPT_TAC (MATCH_MP (cj 2 (iffLR loweringPostsTheory.expr_post_def)) (CONJUNCT1 th))]))) >>
      disch_tac >>
      qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ (mid,t,G1,tn1) P2 E2` >>
      `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (cx_tops cx) cx st0 (bind (eval_expr cx e2) (read_result cx))
         (mid,t,G1,tn1)
         (\H res ee G tn t. ~t.vs_halted /\ ee.gas_obs = [] /\ P2 H res ee G tn t) E2` by
        (irule gas_outcome_full_post_source >>
         qexistsl [`P2`, `E2`] >> simp[]) >>
      qpat_x_assum `gas_outcome_full _ _ _ _ _ _ P2 E2` kall_tac >>
      unabbrev_all_tac >>
      once_rewrite_tac[GSYM vyperStateTheory.bind_assoc] >>
      irule gas_outcome_full_bind_all >>
      irule_at Any (Q.INST [`Q'` |-> `Q`] gasOutcomeFullTheory.gas_outcome_full_post_mono) >>
      qpat_assum `gas_outcome_full _ _ _ _ _ (mid,t,G1,tn1) _ _` (irule_at Any) >>
      simp[] >>
      conj_tac
      >- (rpt gen_tac >> Cases_on `res` >> simp[exprSimDefsTheory.expr_exit_INL]) >>
      conj_tac
      >- (gen_tac >>
          `eval_exprs cx [] = return []` by
            simp[FUN_EQ_THM, exprSimWordArgsTheory.eval_exprs_nil, vyperStateTheory.return_def] >>
          simp[vyperStateTheory.bind_return] >>
          rpt (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
               reverse conj_tac >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
                                       vyperStorageTraceTheory.storage_trace_frame_read_result] >>
               gen_tac >> BETA_TAC) >>
          simp[vyperStorageTraceTheory.storage_trace_frame_def]) >>
      conj_tac
      >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
          metis_tac[]) >>
      conj_tac
      >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >> simp[]) >>
      conj_tac
      >- (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
          simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
               vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
      rpt gen_tac >> strip_tac >>
      `valid_horizon cx st0 (storage_trace_horizon mid'.storage_trace) mid'.storage_trace` by
        fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
      qpat_assum `!H. valid_horizon _ _ H mid'.storage_trace ==> _`
        (qspec_then `storage_trace_horizon mid'.storage_trace` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      strip_tac >> gvs[] >>
      `expr_sim_inv cenv cx env (mid' with gas_obs := [])` by
        (irule (expr_body_pre_eval |> SPEC_ALL |> UNDISCH |> CONJUNCT1 |>
                DISCH_ALL |> GEN_ALL) >>
         qexistsl [`e2`, `mid with gas_obs := gas_explicit marks' t.vs_gas_readings`, `INL v'`] >>
         simp[ETA_AX] >>
         qpat_assum `!tail. bind _ _ (mid with gas_obs := _) = _` (qspec_then `[]` mp_tac) >>
         pure_rewrite_tac[APPEND_NIL] >>
         CONV_TAC (DEPTH_CONV ETA_CONV) >> disch_then ACCEPT_TAC) >>
      `expr_sim_inv cenv cx env mid'` by fs[] >>
      `expr_body_pre cenv cx env e3 mid'` by
        (drule expr_body_pre_builtin_arg >>
         disch_then (qspecl_then [`e3`, `mid'`] mp_tac) >> simp[]) >>
      `body_expr_full_ok cx e3` by
        (fs[vyperContextTheory.builtin_args_length_ok_def, body_exprs_full_ok_def] >>
         qpat_x_assum `_ ==> _ ==> body_expr_full_ok cx e3` irule >>
         conj_tac
         >- (qpat_assum `!tail. bind _ _ (es with gas_obs := _) = _` (qspec_then `[]` mp_tac) >>
             pure_rewrite_tac[vyperStateTheory.bind_def, APPEND_NIL, AllCaseEqs()] >>
             strip_tac >> Cases_on `x'` >> gvs[] >>
             goal_assum (drule_at Any) >>
             goal_assum (drule_at Any) >> simp[]) >>
         qpat_assum `!tail. bind _ _ (mid with gas_obs := _) = _` (qspec_then `[]` mp_tac) >>
         pure_rewrite_tac[vyperStateTheory.bind_def, APPEND_NIL, AllCaseEqs()] >>
         strip_tac >> Cases_on `x'` >> gvs[] >>
         goal_assum (drule_at Any) >>
         goal_assum (drule_at Any) >> simp[]) >>
      `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e3 mid'` by
        (fs[body_expr_full_ok_def] >> metis_tac[]) >>
      `s1.cs_next_var <= s2.cs_next_var` by
        (qpat_assum `lower_value _ _ _ e2 s1 = _`
           (ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o MATCH_MP (cj 2 compile_expr_grows))) >>
      `local_ptrs_reserved cenv s1` by
        metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
      `local_ptrs_reserved cenv s2` by
        metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
      qpat_x_assum `expr_sim_full _ _ _ _ e3 mid'`
        (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
      disch_then (qspecl_then [`st0`, `s2`, `s3`, `sh2`, `sh3`, `z`, `t'`, `G1'`, `tn1'`] mp_tac) >>
      (impl_tac >- (simp[] >>
        conj_tac >- metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
        conj_tac >- metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
        conj_tac >- (qpat_assum `expr_body_pre cenv cx env e3 mid'`
          (ACCEPT_TAC o MATCH_MP expr_body_pre_gas_admissible)) >>
        conj_tac >- (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
          qexistsl [`cenv`, `t`, `s1`] >> simp[] >>
          conj_tac >- metis_tac[cj 6 (iffLR loweringPostsTheory.expr_post_def)] >>
          irule bodyMemoryDefsTheory.return_buf_frame_frame >>
          qexistsl [`cenv`, `s0`, `sa`] >> simp[] >>
          metis_tac[cj 6 (iffLR loweringPostsTheory.expr_post_def)]) >>
        gen_tac >> strip_tac >>
        qpat_assum `!H. valid_horizon _ _ H mid'.storage_trace ==> expr_post _ _ _ _ _ e2 _ _ _ _ _ _ _ _ /\ _`
          (qspec_then `H` mp_tac) >>
        (impl_tac >- first_assum ACCEPT_TAC) >>
        disch_then (fn th => CONJ_TAC THENL
          [ACCEPT_TAC (MATCH_MP (cj 1 (iffLR loweringPostsTheory.expr_post_def)) (CONJUNCT1 th)),
           ACCEPT_TAC (MATCH_MP (cj 2 (iffLR loweringPostsTheory.expr_post_def)) (CONJUNCT1 th))]))) >>
      disch_tac >>
      qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ (mid',t',G1',tn1') P3 E3` >>
      `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (cx_tops cx) cx st0 (bind (eval_expr cx e3) (read_result cx))
         (mid',t',G1',tn1')
         (\H res ee G tn t. ~t.vs_halted /\ ee.gas_obs = [] /\ P3 H res ee G tn t) E3` by
        (irule gas_outcome_full_post_source >>
         qexistsl [`P3`, `E3`] >> simp[]) >>
      qpat_x_assum `gas_outcome_full _ _ _ _ _ _ P3 E3` kall_tac >>
      unabbrev_all_tac >>
      once_rewrite_tac[GSYM vyperStateTheory.bind_assoc] >>
      irule gas_outcome_full_bind_all >>
      irule_at Any (Q.INST [`Q'` |-> `Q`] gasOutcomeFullTheory.gas_outcome_full_post_mono) >>
      qpat_assum `gas_outcome_full _ _ _ _ _ (mid',t',G1',tn1') _ _` (irule_at Any) >>
      simp[] >>
      conj_tac
      >- (rpt gen_tac >> Cases_on `res` >> simp[exprSimDefsTheory.expr_exit_INL]) >>
      conj_tac
      >- (gen_tac >>
          `eval_exprs cx [] = return []` by
            simp[FUN_EQ_THM, exprSimWordArgsTheory.eval_exprs_nil, vyperStateTheory.return_def] >>
          simp[vyperStateTheory.bind_return] >>
          rpt (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
               reverse conj_tac >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
                                       vyperStorageTraceTheory.storage_trace_frame_read_result] >>
               gen_tac >> BETA_TAC) >>
          simp[vyperStorageTraceTheory.storage_trace_frame_def]) >>
      conj_tac
      >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
          metis_tac[]) >>
      conj_tac
      >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >> simp[]) >>
      conj_tac
      >- (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
          simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
               vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
      rpt gen_tac >> strip_tac >>
      `valid_horizon cx st0 (storage_trace_horizon mid''.storage_trace) mid''.storage_trace` by
        fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
      qpat_assum `!H. valid_horizon _ _ H mid''.storage_trace ==> _`
        (qspec_then `storage_trace_horizon mid''.storage_trace` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      strip_tac >> gvs[] >>
      `eval_exprs cx [] = return []` by
        simp[FUN_EQ_THM, exprSimWordArgsTheory.eval_exprs_nil, vyperStateTheory.return_def] >>
      simp[vyperStateTheory.bind_return] >>
      qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
        (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H mid'.storage_trace ==> _`
        (qspec_then `storage_trace_horizon mid'.storage_trace` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H mid''.storage_trace ==> _`
        (qspec_then `storage_trace_horizon mid''.storage_trace` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
      `expr_result_typed env e1 (Value v)` by
        (irule (cj 3 expr_body_pre_eval) >>
         qexistsl [`cenv`, `cx`, `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
                   `mid with gas_obs := []`] >> simp[ETA_AX] >>
         qpat_assum `!tail. bind _ _ (es with gas_obs := _) = _` (qspec_then `[]` mp_tac) >>
         pure_rewrite_tac[APPEND_NIL] >>
         CONV_TAC (DEPTH_CONV ETA_CONV) >> disch_then ACCEPT_TAC) >>
      `value_has_type (BaseTV (UintT 256)) v` by
        gvs[vyperTypeExprResultTheory.expr_result_typed_def,
           vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
           vyperTypeInvariantsTheory.value_result_typed_def,
           vyperValueTheory.evaluate_type_def] >>
      `v = IntV (&w2n (val_to_w256 v))` by
        (irule uint_value_word_rep >> qexists_tac `256` >> simp[]) >>
      `expr_result_typed env e2 (Value v')` by
        (irule (cj 3 expr_body_pre_eval) >>
         qexistsl [`cenv`, `cx`, `mid with gas_obs := gas_explicit marks' t.vs_gas_readings`,
                   `mid' with gas_obs := []`] >> simp[ETA_AX] >>
         qpat_assum `!tail. bind _ _ (mid with gas_obs := _) = _` (qspec_then `[]` mp_tac) >>
         pure_rewrite_tac[APPEND_NIL] >>
         CONV_TAC (DEPTH_CONV ETA_CONV) >> disch_then ACCEPT_TAC) >>
      `value_has_type (BaseTV (UintT 256)) v'` by
        gvs[vyperTypeExprResultTheory.expr_result_typed_def,
           vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
           vyperTypeInvariantsTheory.value_result_typed_def,
           vyperValueTheory.evaluate_type_def] >>
      `v' = IntV (&w2n (val_to_w256 v'))` by
        (irule uint_value_word_rep >> qexists_tac `256` >> simp[]) >>
      `expr_result_typed env e3 (Value v'')` by
        (irule (cj 3 expr_body_pre_eval) >>
         qexistsl [`cenv`, `cx`, `mid' with gas_obs := gas_explicit marks'' t'.vs_gas_readings`,
                   `mid'' with gas_obs := []`] >> simp[ETA_AX] >>
         qpat_assum `!tail. bind _ _ (mid' with gas_obs := _) = _` (qspec_then `[]` mp_tac) >>
         pure_rewrite_tac[APPEND_NIL] >>
         CONV_TAC (DEPTH_CONV ETA_CONV) >> disch_then ACCEPT_TAC) >>
      `value_has_type (BaseTV (UintT 256)) v''` by
        gvs[vyperTypeExprResultTheory.expr_result_typed_def,
           vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
           vyperTypeInvariantsTheory.value_result_typed_def,
           vyperValueTheory.evaluate_type_def] >>
      `v'' = IntV (&w2n (val_to_w256 v''))` by
        (irule uint_value_word_rep >> qexists_tac `256` >> simp[]) >>
      `expr_val_rel cx (BaseT (UintT 256)) v x t` by
        (qpat_assum `expr_post _ _ _ _ _ e1 _ _ _ _ _ _ _ _`
           (mp_tac o MATCH_MP (cj 3 (iffLR loweringPostsTheory.expr_post_def))) >>
         simp[is_word_type_def]) >>
      `expr_val_rel cx (BaseT (UintT 256)) v' y t'` by
        (qpat_assum `expr_post _ _ _ _ _ e2 _ _ _ _ _ _ _ _`
           (mp_tac o MATCH_MP (cj 3 (iffLR loweringPostsTheory.expr_post_def))) >>
         simp[is_word_type_def]) >>
      `expr_val_rel cx (BaseT (UintT 256)) v'' z t''` by
        (qpat_assum `expr_post _ _ _ _ _ e3 _ _ _ _ _ _ _ _`
           (mp_tac o MATCH_MP (cj 3 (iffLR loweringPostsTheory.expr_post_def))) >>
         simp[is_word_type_def]) >>
      `eval_operand x t = SOME (val_to_w256 v) /\
       eval_operand y t' = SOME (val_to_w256 v') /\
       eval_operand z t'' = SOME (val_to_w256 v'')` by
        (rpt conj_tac >>
         irule exprBopSimPropsTheory.expr_val_rel_word >>
         (conj_tac >- metis_tac[loweringSliceTheory.word_value_def]) >>
         qexistsl [`cx`, `BaseT (UintT 256)`] >>
         simp[is_word_type_def, vyperValueTheory.evaluate_type_def] >>
         first_assum ACCEPT_TAC) >>
      `(!l. x <> Label l) /\ (!l. y <> Label l)` by
        (conj_tac
         >- (qpat_assum `lower_value _ _ _ e1 _ = _` mp_tac >>
             disch_then (mp_then Any mp_tac expr_body_pre_lower_value_word_shape) >>
             simp[is_word_type_def] >>
             disch_then (qspecl_then [`cx`, `env`, `es`] mp_tac) >> simp[]) >>
         qpat_assum `lower_value _ _ _ e2 _ = _` mp_tac >>
         disch_then (mp_then Any mp_tac expr_body_pre_lower_value_word_shape) >>
         simp[is_word_type_def] >>
         disch_then (qspecl_then [`cx`, `env`, `mid`] mp_tac) >> simp[]) >>
      `eval_operand x t' = SOME (val_to_w256 v)` by
        (irule exprBopSimPropsTheory.eval_operand_frame >>
         (conj_tac >- simp[]) >>
         qexistsl [`s1`, `t`] >> simp[] >>
         qpat_assum `expr_post _ _ _ _ _ e2 _ _ _ _ _ _ _ _`
           (mp_tac o MATCH_MP (cj 6 (iffLR loweringPostsTheory.expr_post_def))) >> simp[]) >>
      `!q. x = Var q ==> not_fresh_at s2 q` by
        metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
      `!q. y = Var q ==> not_fresh_at s2 q` by
        (qpat_assum `lower_value _ _ _ e2 _ = _` mp_tac >>
         disch_then (mp_then Any mp_tac expr_body_pre_lower_value_word_shape) >>
         simp[is_word_type_def] >>
         disch_then (qspecl_then [`cx`, `env`, `mid`] mp_tac) >> simp[]) >>
      `eval_operand x t'' = SOME (val_to_w256 v)` by
        (irule exprBopSimPropsTheory.eval_operand_frame >>
         (conj_tac >- simp[]) >>
         qexistsl [`s2`, `t'`] >> simp[] >>
         qpat_assum `expr_post _ _ _ _ _ e3 _ _ _ _ _ _ _ _`
           (mp_tac o MATCH_MP (cj 6 (iffLR loweringPostsTheory.expr_post_def))) >> simp[]) >>
      `eval_operand y t'' = SOME (val_to_w256 v')` by
        (irule exprBopSimPropsTheory.eval_operand_frame >>
         (conj_tac >- simp[]) >>
         qexistsl [`s2`, `t'`] >> simp[] >>
         qpat_assum `expr_post _ _ _ _ _ e3 _ _ _ _ _ _ _ _`
           (mp_tac o MATCH_MP (cj 6 (iffLR loweringPostsTheory.expr_post_def))) >> simp[]) >>
      `op_taint tn1 x = {} /\ op_taint tn1' y = {} /\ op_taint tn1'' z = {}` by
        (rpt conj_tac >>
         first_assum (ACCEPT_TAC o MATCH_MP (cj 1 (iffLR bodyPtrDefsTheory.ptr_val_ok_def)))) >>
      `op_taint tn1' x = {}` by
        (qpat_assum `ghost_kept_at _ _ _ s1 _ _ _ _ _` mp_tac >>
         pure_rewrite_tac[bodyPtrDefsTheory.ghost_kept_at_def] >> strip_tac >>
         Cases_on `x` >> simp[ptrDisciplineTheory.op_taint_def]) >>
      `op_taint tn1'' x = {} /\ op_taint tn1'' y = {}` by
        (qpat_assum `ghost_kept_at _ _ _ s2 _ _ _ _ _` mp_tac >>
         pure_rewrite_tac[bodyPtrDefsTheory.ghost_kept_at_def] >> strip_tac >>
         conj_tac >- (Cases_on `x` >> simp[ptrDisciplineTheory.op_taint_def]) >>
         Cases_on `y` >> simp[ptrDisciplineTheory.op_taint_def]) >>
      `local_ptrs_reserved cenv s3` by
        metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var, cj 2 compile_expr_grows] >>
      `!H. valid_horizon cx st0 H mid''.storage_trace ==>
        stmt_state_rel H ctx func cenv cx mid'' t'' /\
        ghost_inv_at (DF H) lo d cenv cx mid'' G1'' tn1'' t''` by
        (gen_tac >> strip_tac >>
         qpat_assum `!H. valid_horizon _ _ H mid''.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
           (qspec_then `H` mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >>
         strip_tac >> conj_tac
         >- (first_assum (ACCEPT_TAC o MATCH_MP (cj 1 (iffLR loweringPostsTheory.expr_post_def)))) >>
         first_assum ACCEPT_TAC) >>
      qmatch_goalsub_abbrev_tac `builtin_result cx _ (BaseT (UintT 256)) bi _ _` >>
      markerLib.asm_x "suffix" (qspecl_then
        [`DF`, `lo`, `gas_explicit_sites ctx shadow_ctx`, `ctx`, `func`, `PG`,
         `d`, `cenv`, `cx`, `st0`, `mid''`, `s3`, `sb`, `bi`, `x`, `y`, `z`,
         `op`, `t''`, `G1''`, `tn1''`, `BaseT (UintT 256)`,
         `[BaseT (UintT 256); BaseT (UintT 256); BaseT (UintT 256)]`,
         `val_to_w256 v`, `val_to_w256 v'`, `val_to_w256 v''`] mp_tac) >>
      impl_tac
      >- (simp[Abbr `bi`] >>
          `sa.cs_next_var <= s3.cs_next_var` by
            metis_tac[cj 2 compile_expr_grows, arithmeticTheory.LESS_EQ_TRANS] >>
          conj_tac >- metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
          metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]) >>
      disch_then (qx_choose_then `suffix_r` (qx_choose_then `u`
        (qx_choose_then `G2` (qx_choose_then `tn2` strip_assume_tac)))) >>
      `?delta. mid.storage_trace = es.storage_trace ++ delta` by
        (qpat_assum `!tail. bind _ _ (es with gas_obs := _) = _`
           (qspec_then `[]` mp_tac) >>
         pure_rewrite_tac[APPEND_NIL] >>
         disch_then (mp_then Any mp_tac vyperStorageTraceTheory.storage_trace_frame_prefix) >>
         simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
           vyperStorageTraceTheory.evaluate_storage_trace_frame,
           vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
      `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) es.storage_trace` by
        metis_tac[gasOutcomeFullTheory.valid_horizon_append] >>
      `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx es s0` by
        (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
           (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
      `sa.cs_next_var <= s2.cs_next_var /\ sa.cs_next_id <= s2.cs_next_id /\
       sa.cs_next_var <= s3.cs_next_var /\ sa.cs_next_id <= s3.cs_next_id` by
        metis_tac[cj 2 compile_expr_grows, arithmeticTheory.LESS_EQ_TRANS] >>
      `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
        (qpat_assum `expr_post _ _ _ _ _ e1 _ _ _ _ _ _ _ _`
           (ACCEPT_TAC o SYM o
            MATCH_MP (cj 2 (iffLR loweringPostsTheory.locals_kept_def)) o
            MATCH_MP (cj 9 (iffLR loweringPostsTheory.expr_post_def)))) >>
      `MAP FDOM es.scopes = MAP FDOM mid'.scopes` by
        (qpat_assum `expr_post _ _ _ _ _ e2 _ _ _ _ _ _ _ _`
           (ASSUME_TAC o
            MATCH_MP (cj 2 (iffLR loweringPostsTheory.locals_kept_def)) o
            MATCH_MP (cj 9 (iffLR loweringPostsTheory.expr_post_def))) >> fs[]) >>
      `MAP FDOM es.scopes = MAP FDOM mid''.scopes` by
        (qpat_assum `expr_post _ _ _ _ _ e3 _ _ _ _ _ _ _ _`
           (ASSUME_TAC o
            MATCH_MP (cj 2 (iffLR loweringPostsTheory.locals_kept_def)) o
            MATCH_MP (cj 9 (iffLR loweringPostsTheory.expr_post_def))) >> fs[]) >>
      `mid'' with gas_obs := [] = mid''` by
        (qpat_assum `mid''.gas_obs = []` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
      irule gas_outcome_full_intro >>
      qexistsl_tac [`G2`, `mid''`, `[]`, `suffix_r`,
        `builtin_result cx mid''.accounts (BaseT (UintT 256)) bi
          [BaseT (UintT 256); BaseT (UintT 256); BaseT (UintT 256)] [v;v';v'']`, `tn2`] >>
      conj_tac >- simp[gasSummaryTheory.gas_explicit_def] >>
      reverse conj_tac >- first_assum ACCEPT_TAC >>
      gen_tac >> strip_tac >>
      `gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (t'',G1'',tn1'') [] (suffix_r,G2,tn2) /\
       (val_to_w256 v'' <> 0w ==>
        stmt_state_rel H ctx func cenv cx mid'' u /\
        ghost_inv_at (DF H) lo d cenv cx mid'' G2 tn2 u)` by
        (qpat_assum `!H. valid_horizon _ _ H mid''.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
           (qspec_then `H` mp_tac) >> simp[]) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      Cases_on `val_to_w256 v'' = 0w`
      >- (qpat_assum `val_to_w256 v'' = 0w ==> suffix_r = Abort Revert_abort u /\ _`
            (fn th => qpat_assum `val_to_w256 v'' = 0w` (strip_assume_tac o MP th)) >>
          disj2_tac >> conj_tac >- first_assum ACCEPT_TAC >>
          qpat_assum `expr_exit (builtin_result _ _ _ _ _ _) _` mp_tac >>
          qpat_assum `v = IntV _` (fn th => PURE_REWRITE_TAC[GSYM th]) >>
          qpat_assum `v' = IntV _` (fn th => PURE_REWRITE_TAC[GSYM th]) >>
          qpat_assum `v'' = IntV _` (fn th => PURE_REWRITE_TAC[GSYM th]) >> simp[]) >>
      qpat_assum `val_to_w256 v'' <> 0w ==> suffix_r = OK u /\ _`
        (fn th => qpat_assum `val_to_w256 v'' <> 0w` (strip_assume_tac o MP th)) >>
      disj1_tac >> qexists_tac `u` >> simp[] >>
      qexists_tac `IntV (&w2n ((if bi = AddMod then addmod else mulmod)
        (val_to_w256 v) (val_to_w256 v') (val_to_w256 v'')))` >>
      conj_tac
      >- (qpat_assum `builtin_result _ _ _ bi _ [IntV _; IntV _; IntV _] = _` mp_tac >>
          qpat_assum `v = IntV _` (fn th => PURE_REWRITE_TAC[GSYM th]) >>
          qpat_assum `v' = IntV _` (fn th => PURE_REWRITE_TAC[GSYM th]) >>
          qpat_assum `v'' = IntV _` (fn th => PURE_REWRITE_TAC[GSYM th]) >> simp[Abbr `bi`]) >>
      simp[Abbr `bi`, vyperASTTheory.expr_type_def, loweringPostsTheory.post_value_type_word,
        is_word_type_def, bodyPtrDefsTheory.ptr_val_ok_def,
        exprSimMemDefsTheory.expr_store_bound_word] >>
      `expr_post H ctx func cenv cx e3 mid' s2 s3 t' mid'' v'' z t''` by
        (qpat_assum `!H. valid_horizon _ _ H mid''.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
           (qspec_then `H` mp_tac) >> simp[]) >>
      `storage_well_formed_on cx mid'' (FST H)` by
        (qpat_assum `expr_post H _ _ _ _ e3 _ _ _ _ _ _ _ _`
           (ACCEPT_TAC o MATCH_MP (cj 2 (iffLR loweringPostsTheory.expr_post_def)))) >>
      `stmt_state_rel H ctx func cenv cx mid'' u` by
        (qpat_assum `val_to_w256 v'' <> 0w ==> stmt_state_rel H _ _ _ _ _ u /\ _`
           (fn th => qpat_assum `val_to_w256 v'' <> 0w`
             (ACCEPT_TAC o CONJUNCT1 o MP th))) >>
      `s0.vs_alloca_next <= u.vs_alloca_next` by
        (qpat_assum `u.vs_alloca_next = t''.vs_alloca_next` (fn th => rewrite_tac[th]) >>
         MATCH_MP_TAC (Q.SPECL [`s0.vs_alloca_next`, `t.vs_alloca_next`, `t''.vs_alloca_next`]
           arithmeticTheory.LESS_EQ_TRANS) >>
         conj_tac >- first_assum ACCEPT_TAC >>
         MATCH_MP_TAC (Q.SPECL [`t.vs_alloca_next`, `t'.vs_alloca_next`, `t''.vs_alloca_next`]
           arithmeticTheory.LESS_EQ_TRANS) >>
         conj_tac >> first_assum ACCEPT_TAC) >>
      simp[] >>
      rpt conj_tac
      >~ [`expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`]
      >- (irule (INST_TYPE
            (map (fn ty => ty |-> ``:256``) (type_vars_in_term (concl modular_parent_post)))
            modular_parent_post) >>
          simp[is_word_type_def, loweringSliceTheory.word_value_def,
            valueEncodingTheory.val_to_w256_def, integer_wordTheory.i2w_pos] >>
          conj_tac
          >- (qexists_tac `storage_trace_horizon mid.storage_trace` >> first_assum ACCEPT_TAC) >>
          qexistsl_tac [`storage_trace_horizon mid.storage_trace`,
            `storage_trace_horizon mid'.storage_trace`, `H`, `mid`, `mid'`,
            `s1`, `s2`, `s3`, `t`, `t'`, `t''`, `v`, `v'`, `v''`, `x`, `y`, `z`] >>
          simp[] >> rpt conj_tac >> metis_tac[]) >>
      `wb_frame cenv es mid sa s0 t /\
       wb_frame cenv mid mid' s1 t t' /\
       wb_frame cenv mid' mid'' s2 t' t''` by
        (rpt conj_tac >>
         first_assum (ACCEPT_TAC o MATCH_MP exprSimWordArgsTheory.expr_post_frame)) >>
      `wb_frame cenv es mid' sa s0 t'` by
        (MATCH_MP_TAC (Q.SPECL [`func`, `cenv`, `cx`, `es`, `s0`, `sa`,
           `mid`, `mid'`, `s1`, `t`, `t'`, `ctx`]
           (Q.INST [`H` |-> `storage_trace_horizon mid.storage_trace`]
             (INST_TYPE [alpha |-> ``:256``] exprSimWordArgsTheory.wb_frame_trans))) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      `wb_frame cenv es mid'' sa s0 t''` by
        (MATCH_MP_TAC (Q.SPECL [`func`, `cenv`, `cx`, `es`, `s0`, `sa`,
           `mid'`, `mid''`, `s2`, `t'`, `t''`, `ctx`]
           (Q.INST [`H` |-> `storage_trace_horizon mid.storage_trace`]
             (INST_TYPE [alpha |-> ``:256``] exprSimWordArgsTheory.wb_frame_trans))) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      `ghost_kept_at lo cenv es sa G0 tn0 s0 G1' tn1'` by
        (`ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
          ghost_kept_at lo cenv mid s1 G1 tn1 t G1' tn1' /\
          sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
          stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx es s0 /\
          local_ptrs_reserved cenv sa /\ MAP FDOM es.scopes = MAP FDOM mid.scopes /\
          wb_frame cenv es mid sa s0 t` suffices_by
           (disch_then (ACCEPT_TAC o MATCH_MP (SPEC_ALL wordArgsPtrTheory.ghost_kept_at_wb_trans))) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      `ghost_kept_at lo cenv es sa G0 tn0 s0 G1'' tn1''` by
        (`ghost_kept_at lo cenv es sa G0 tn0 s0 G1' tn1' /\
          ghost_kept_at lo cenv mid' s2 G1' tn1' t' G1'' tn1'' /\
          sa.cs_next_var <= s2.cs_next_var /\ sa.cs_next_id <= s2.cs_next_id /\
          stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx es s0 /\
          local_ptrs_reserved cenv sa /\ MAP FDOM es.scopes = MAP FDOM mid'.scopes /\
          wb_frame cenv es mid' sa s0 t'` suffices_by
           (disch_then (ACCEPT_TAC o MATCH_MP (SPEC_ALL wordArgsPtrTheory.ghost_kept_at_wb_trans))) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      `ghost_kept_at lo cenv es sa G0 tn0 s0 G1'' tn1'' /\
       ghost_kept_at lo cenv mid'' s3 G1'' tn1'' t'' G2 tn2 /\
       sa.cs_next_var <= s3.cs_next_var /\ sa.cs_next_id <= s3.cs_next_id /\
       stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx es s0 /\
       local_ptrs_reserved cenv sa /\ MAP FDOM es.scopes = MAP FDOM mid''.scopes /\
       wb_frame cenv es mid'' sa s0 t''` suffices_by
        (disch_then (ACCEPT_TAC o MATCH_MP (SPEC_ALL wordArgsPtrTheory.ghost_kept_at_wb_trans))) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `!DF lo d ctx shadow_ctx PG func shadow_func cenv cx ty e es. _ ==> expr_vv_sim_full _ _ _ _ _ _`
    match_mp_tac >>
  simp[vyperASTTheory.expr_type_def, is_word_type_def] >>
  conj_tac
  >- (gen_tac >>
      qmatch_goalsub_abbrev_tac `compile_expr cenv ty ee sa` >>
      Cases_on `compile_expr cenv ty ee sa` >>
      fs[Abbr `ee`] >>
      drule_at Any compile_word_builtin_stack >> simp[] >>
      strip_tac >> gvs[] >> metis_tac[]) >>
  metis_tac[eval_expr_builtin_value]))
QED
