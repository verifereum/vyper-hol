(* Counted continuation boundaries for EC arithmetic. *)
Theory bodyMemEcArithCompose
Ancestors
  stmtReasonVvMemory gasSummary fragGasPath fragGasMode exprSimDefs vyperState
  bodyMemoryPreds bodyMemEcArithSafe bodyMemEcArithOperands exprSimWordArgs
  exprSimHyps exprLoweringProps exprSimMemorySource exprSimHypsDefs
  exprSimSource compileEnv exprSafeOperand exprSimMemDefs fragExec exprSimOperands

(* Adapter for private exprSimECArith.ec_outcome_then, using the exported
   memory-polymorphic gas_outcome_bind_value rather than duplicating its
   normal/exception/exemption composition proof. *)
Theorem ec_mem_outcome_then:
  gas_outcome T tops (ctx,func)
    (m : evaluation_state -> value evaluation_result) (es,s0)
    (\res ee t. ?v. res = INL v /\ P v ee t) (\res ee r. expr_exit res r) /\
  (!exc ee r. expr_exit (INR exc : value + exception) r ==>
     R (INR exc) ee r) /\
  (!gs v ee t. m (es with gas_obs := gs) = (INL v, ee) /\ ee.gas_obs = [] /\
     P v ee t /\ ~t.vs_halted ==>
     gas_outcome T tops (ctx,func) (k v) (ee,t) Q R) ==>
  gas_outcome T tops (ctx,func) (bind m k) (es,s0) Q R
Proof
  strip_tac >> irule gas_outcome_bind_value >>
  first_assum (irule_at Any) >> conj_tac
  >- (rpt strip_tac >> gvs[] >>
      `~t.vs_halted` by
        metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
      qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
      strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[] >>
      strip_tac >> first_x_assum irule >> simp[] >>
      goal_assum (drule_at Any)) >>
  rpt strip_tac >> Cases_on `res` >> gvs[expr_exit_def] >>
  metis_tac[]
QED

Theorem ec_mem_operands_then:
  expr_body_pre cenv cx env (Builtin ann bt [a;b]) es /\
  body_exprs_mem_ok cx [a;b] /\ body_inv tops ctx cenv cx /\
  (bt = ECAdd \/ bt = ECMul) /\
  expr_type a = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  lower_value compile_expr cenv (expr_type a) a sa = (p,s1) /\
  lower_value compile_expr cenv (expr_type b) b s1 = (q,sm) /\
  cs_extends sm sb /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!exc ee r. expr_exit (INR exc : value + exception) r ==> R (INR exc) ee r) /\
  (!es1 es2 v1 v2 t u.
    expr_post ctx func cenv cx a es sa s1 s0 es1 v1 p t /\
    expr_post ctx func cenv cx b es1 s1 sm t es2 v2 q u /\
    MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    MAP FDOM es1.scopes = MAP FDOM es2.scopes /\
    expr_store_bound cx (expr_type b) v2 q u /\
    expr_val_rel cx (expr_type a) v1 p u /\
    expr_val_at cenv cx (expr_type a) sa sm es2 v1 p u /\
    (?w. eval_operand p u = SOME w /\ w2n w + 64 <= u.vs_alloca_next) /\
    expr_result_typed env a (Value v1) /\ expr_result_typed env b (Value v2) /\
    stmt_state_rel ctx func cenv cx es2 u /\ local_ptrs_reserved cenv sm /\
    fn_has_code sm sb func /\ ~u.vs_halted /\
    u.vs_current_bb = sm.cs_current_bb /\
    u.vs_inst_idx = LENGTH sm.cs_current_insts /\
    alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
    (!z. MEM (Var z) [p;q] ==> not_fresh_at sm z) ==>
    gas_outcome T (cx_tops cx) (ctx,func) (k v1 v2) (es2,u) Q R) ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx a) (read_result cx))
      (\v1. bind (bind (eval_expr cx b) (read_result cx)) (k v1)))
    (es,s0) Q R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `!n. bt <> Slice n` by (rpt strip_tac >> gvs[]) >>
  `expr_body_pre cenv cx env a es` by
    (drule expr_body_pre_builtin_arg >>
     disch_then (qspecl_then [`a`, `es`] mp_tac) >> simp[]) >>
  qpat_assum `lower_value _ _ _ a _ = _`
    (mp_then Any mp_tac (cj 2 exprLoweringPropsTheory.compile_expr_grows)) >> strip_tac >>
  qpat_assum `lower_value _ _ _ b _ = _`
    (mp_then Any mp_tac (cj 2 exprLoweringPropsTheory.compile_expr_grows)) >> strip_tac >>
  `local_ptrs_reserved cenv s1 /\ local_ptrs_reserved cenv sm` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `!z. p = Var z ==> not_fresh_at s1 z` by
    metis_tac[exprOperandVarTheory.compile_lower_value_var] >>
  `cs_extends s1 sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code s1 sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split] >>
  `safe_operand s1 p` by metis_tac[ec_point_lower_value_safe_operand] >>
  `!l. p <> Label l` by gvs[safe_operand_def] >>
  `expr_sim_mem ctx func cenv cx (expr_type a) a es` by
    (gvs[body_exprs_mem_ok_def, body_expr_mem_ok_def] >> metis_tac[]) >>
  irule ec_mem_outcome_then >>
  conj_tac >- simp[] >>
  qexists_tac `\v1 ee t. expr_post ctx func cenv cx a es sa s1 s0 ee v1 p t /\
    expr_store_bound cx (expr_type a) v1 p t /\
    t.vs_current_bb = s1.cs_current_bb /\
    t.vs_inst_idx = LENGTH s1.cs_current_insts /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next` >>
  BETA_TAC >> reverse conj_tac
  >- (qpat_x_assum `expr_sim_mem _ _ _ _ _ a _`
        (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
      disch_then irule >> simp[] >>
      metis_tac[expr_body_pre_gas_admissible]) >>
  suspend "first_success"
QED

Resume ec_mem_operands_then[first_success]:
  qx_genl_tac [`gs1`, `v1`, `es1`, `t`] >> strip_tac >>
  qspecl_then [`cenv`, `cx`, `env`, `a`, `es with gas_obs := gs1`, `INL v1`, `es1`]
    mp_tac (CONV_RULE (DEPTH_CONV ETA_CONV) expr_body_pre_eval) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `expr_result_typed env a (Value v1)` by simp[] >>
  `MAP FDOM es.scopes = MAP FDOM es1.scopes` by
    (qpat_assum `bind (eval_expr cx a) _ _ = _`
       (mp_then Any mp_tac
         (CONV_RULE (DEPTH_CONV ETA_CONV)
            exprSimWordArgsTheory.forced_eval_expr_preserves_scopes_dom)) >> simp[]) >>
  `expr_body_pre cenv cx env b es1` by
    (qpat_assum `expr_body_pre _ _ _ (Builtin _ _ _) _`
       (mp_then Any mp_tac expr_body_pre_builtin_arg) >>
     disch_then (qspecl_then [`b`, `es1`] mp_tac) >> simp[]) >>
  `expr_sim_mem ctx func cenv cx (expr_type b) b es1` by
    (qpat_x_assum `body_exprs_mem_ok _ _` mp_tac >>
     simp[body_exprs_mem_ok_def] >> strip_tac >>
     `?s tv t s1 v t1. eval_expr cx a s = (INL tv,t) /\
                       read_result cx tv s1 = (INL v,t1)` by
       (qpat_x_assum `bind (eval_expr cx a) _ _ = _` mp_tac >>
        simp[vyperStateTheory.bind_def, AllCaseEqs()] >> metis_tac[]) >>
     gvs[body_expr_mem_ok_def] >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx es1 t` by
    metis_tac[exprSimWordArgsTheory.expr_post_state] >>
  irule ec_mem_outcome_then >> conj_tac >- simp[] >>
  qexists_tac `\v2 ee u. expr_post ctx func cenv cx b es1 s1 sm t ee v2 q u /\
    expr_store_bound cx (expr_type b) v2 q u /\
    u.vs_current_bb = sm.cs_current_bb /\
    u.vs_inst_idx = LENGTH sm.cs_current_insts /\
    alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next` >>
  BETA_TAC >> reverse conj_tac
  >- (qpat_x_assum `expr_sim_mem _ _ _ _ _ b _`
        (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
      disch_then irule >> simp[] >> metis_tac[expr_body_pre_gas_admissible]) >>
  suspend "second_success"
QED

Resume ec_mem_operands_then[second_success]:
  qx_genl_tac [`gs2`, `v2`, `es2`, `u`] >> strip_tac >>
  qspecl_then [`cenv`, `cx`, `env`, `b`, `es1 with gas_obs := gs2`, `INL v2`, `es2`]
    mp_tac (CONV_RULE (DEPTH_CONV ETA_CONV) expr_body_pre_eval) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `expr_result_typed env b (Value v2)` by simp[] >>
  `stmt_state_rel ctx func cenv cx es2 u` by
    metis_tac[exprSimWordArgsTheory.expr_post_state] >>
  `MAP FDOM es1.scopes = MAP FDOM es2.scopes` by
    (qpat_assum `bind (eval_expr cx b) _ _ = _`
       (mp_then Any mp_tac
         (CONV_RULE (DEPTH_CONV ETA_CONV)
            exprSimWordArgsTheory.forced_eval_expr_preserves_scopes_dom)) >> simp[]) >>
  `?w. eval_operand p t = SOME w /\ eval_operand p u = SOME w` by
    metis_tac[expr_post_operand_word] >>
  `!w. eval_operand p t = SOME w ==> eval_operand p u = SOME w` by
    metis_tac[optionTheory.SOME_11] >>
  `post_value_type cenv a = expr_type a` by
    (irule post_value_type_ec_point >>
     qexistsl_tac [`cx`,`env`,`es`] >>
     qpat_assum `expr_type a = _` (fn th => simp[th]) >>
     qpat_x_assum `expr_body_pre _ _ _ (Builtin _ _ _) _` mp_tac >>
     simp[expr_body_pre_def, well_typed_expr_def]) >>
  `expr_val_rel cx (expr_type a) v1 p u /\
   expr_val_at cenv cx (expr_type a) sa sm es2 v1 p u` by
    metis_tac[ec_point_operand_kept] >>
  `w2n w + 64 <= u.vs_alloca_next` by
    (metis_tac[ec_point_read_capacity]) >>
  `!z. MEM (Var z) [p;q] ==> not_fresh_at sm z` by
    (simp[] >> metis_tac[exprOperandVarTheory.compile_lower_value_var,
                         freshWritesTheory.not_fresh_at_mono]) >>
  first_x_assum irule >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED
Finalise ec_mem_operands_then
