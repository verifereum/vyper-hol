(* Counted continuation boundaries for EC arithmetic. *)
Theory bodyMemEcArithCompose
Ancestors
  stmtReasonVvMemory gasSummary fragGasPath fragGasMode exprSimDefs vyperState
  bodyMemoryPreds bodyMemEcArithSafe bodyMemEcArithOperands exprSimWordArgs
  exprSimHyps exprLoweringProps exprSimMemorySource exprSimHypsDefs
  exprSimSource compileEnv exprSafeOperand exprSimMemDefs fragExec exprSimOperands
  stmtSimDeclCompose gasOutcome gasStorage vyperStorageTrace vyperStorageFootprint

(* Applies a thm-tactic to an assumption or one of its conjuncts, trying
   each until one closes the goal. *)
fun conj_assum_thm_tac ttac (g as (asl, w)) =
  let fun conjs th =
        if boolSyntax.is_conj (Thm.concl th)
        then conjs (Drule.CONJUNCT1 th) @ conjs (Drule.CONJUNCT2 th)
        else [th]
  in Tactical.FIRST_ASSUM
       (fn th => Tactical.FIRST (map ttac (conjs th))) g end;
val conj_assum_tac = conj_assum_thm_tac Tactic.ACCEPT_TAC;

(* Adapter for private exprSimECArith.ec_outcome_then, using the exported
   memory-polymorphic gas_outcome_bind_value rather than duplicating its
   normal/exception/exemption composition proof.  The continuation is given
   the step's end state and its domain, and P at every valid horizon. *)
Theorem ec_mem_outcome_then:
  gas_outcome T tops (ctx,func) cx st0
    (m : evaluation_state -> value evaluation_result) (es,s0)
    (\H res ee t. ?v. res = INL v /\ P H v ee t)
    (\H res ee r. expr_exit res r) /\
  (!H exc ee r. expr_exit (INR exc : value + exception) r ==>
     R H (INR exc) ee r) /\
  (!v. storage_trace_frame (k v)) /\
  (!marks v ee t.
     gas_marked_exec T (ctx,func) m (es,s0) marks (INL v) ee (OK t) /\
     ee.gas_obs = [] /\ ~t.vs_halted /\
     storage_trace_domain cx st0 ee.storage_trace /\
     (!H. valid_horizon cx st0 H ee.storage_trace ==> P H v ee t) ==>
     gas_outcome T tops (ctx,func) cx st0 (k v) (ee,t) Q R) ==>
  gas_outcome T tops (ctx,func) cx st0 (bind m k) (es,s0) Q R
Proof
  strip_tac >>
  match_mp_tac
    (Q.SPECL [`\H res ee t. ?v. res = INL v /\ P H v ee t`,
              `\H res ee r. expr_exit res r`]
       (Q.GENL [`Qa`, `Ra`] gas_outcome_bind_value)) >>
  BETA_TAC >> rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- (rpt gen_tac >> strip_tac >>
      `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
         mid.storage_trace` by fs[storage_trace_domain_def] >>
      Cases_on `res`
      >- (rename1 `INL v` >>
          `!H. valid_horizon cx st0 H mid.storage_trace ==>
               P H v (mid with gas_obs := []) t` by
            (qx_gen_tac `H` >> strip_tac >>
             qpat_assum `!H'. valid_horizon cx st0 H' mid.storage_trace ==>
                              ?v. _`
               (qspec_then `H` mp_tac) >>
             (impl_tac >- first_assum ACCEPT_TAC) >> simp[]) >>
          qexists_tac `v` >> conj_tac >- REFL_TAC >>
          qpat_x_assum `!marks v ee t. _`
            (qspecl_then [`marks`, `v`, `mid with gas_obs := []`, `t`]
               mp_tac) >>
          (impl_tac
           >- (rpt conj_tac
               >- (irule stmtSimDeclComposeTheory.gas_marked_exec_end_gas_obs >>
                   first_assum ACCEPT_TAC)
               >- simp[]
               >- metis_tac[gas_marked_exec_def, gas_marked_path_exec,
                            gas_path_normal]
               >- (simp[] >> first_assum ACCEPT_TAC)
               >- (simp[] >> first_assum ACCEPT_TAC))) >>
          strip_tac >> first_assum ACCEPT_TAC)
      >- (qpat_x_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
            (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
          (impl_tac >- first_assum ACCEPT_TAC) >> simp[]))
  >- (rpt strip_tac >> Cases_on `res` >> gvs[expr_exit_def] >> metis_tac[])
  >- first_assum ACCEPT_TAC
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
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s0 /\
     storage_well_formed_on cx es (FST H)) /\ alloca_history func s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!H exc ee r. expr_exit (INR exc : value + exception) r ==>
     R H (INR exc) ee r) /\
  (!v1 v2. storage_trace_frame (k v1 v2)) /\
  (!es1 es2 v1 v2 t u.
    (!H. valid_horizon cx st0 H es2.storage_trace ==>
       expr_post H ctx func cenv cx a es sa s1 s0 es1 v1 p t /\
       expr_post H ctx func cenv cx b es1 s1 sm t es2 v2 q u /\
       stmt_state_rel H ctx func cenv cx es2 u) /\
    (?H0. valid_horizon cx st0 H0 es2.storage_trace) /\
    (!H. valid_horizon cx st0 H es2.storage_trace ==>
         valid_horizon cx st0 H es.storage_trace) /\
    MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    MAP FDOM es1.scopes = MAP FDOM es2.scopes /\
    expr_store_bound cx (expr_type b) v2 q u /\
    expr_val_rel cx (expr_type a) v1 p u /\
    expr_val_at cenv cx (expr_type a) sa sm es2 v1 p u /\
    (?w. eval_operand p u = SOME w /\ w2n w + 64 <= u.vs_alloca_next) /\
    expr_result_typed env a (Value v1) /\ expr_result_typed env b (Value v2) /\
    local_ptrs_reserved cenv sm /\
    fn_has_code sm sb func /\ ~u.vs_halted /\
    u.vs_current_bb = sm.cs_current_bb /\
    u.vs_inst_idx = LENGTH sm.cs_current_insts /\
    alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
    (!z. MEM (Var z) [p;q] ==> not_fresh_at sm z) ==>
    gas_outcome T (cx_tops cx) (ctx,func) cx st0 (k v1 v2) (es2,u) Q R) ==>
  gas_outcome T (cx_tops cx) (ctx,func) cx st0
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
  `storage_trace_frame (bind (eval_expr cx a) (read_result cx))` by
    (match_mp_tac storage_trace_frame_bind_all >>
     simp[storage_trace_frame_read_result, evaluate_storage_trace_frame]) >>
  `storage_trace_frame (bind (eval_expr cx b) (read_result cx))` by
    (match_mp_tac storage_trace_frame_bind_all >>
     simp[storage_trace_frame_read_result, evaluate_storage_trace_frame]) >>
  `!v1. storage_trace_frame
          (bind (bind (eval_expr cx b) (read_result cx)) (k v1))` by
    (gen_tac >> match_mp_tac storage_trace_frame_bind_all >> metis_tac[]) >>
  match_mp_tac
    (Q.SPEC `\H v1 ee t. expr_post H ctx func cenv cx a es sa s1 s0 ee v1 p t /\
       expr_store_bound cx (expr_type a) v1 p t /\
       t.vs_current_bb = s1.cs_current_bb /\
       t.vs_inst_idx = LENGTH s1.cs_current_insts /\
       alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next`
     (Q.GEN `P` ec_mem_outcome_then)) >>
  BETA_TAC >> rpt conj_tac
  >- (qpat_x_assum `expr_sim_mem _ _ _ _ _ a _`
        (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
      disch_then irule >> simp[] >>
      metis_tac[expr_body_pre_gas_admissible])
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- suspend "first_success"
QED

Resume ec_mem_operands_then[first_success]:
  qx_genl_tac [`m1`, `v1`, `es1`, `t`] >> strip_tac >>
  `es1 with gas_obs := [] = es1` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  `?gs1. bind (eval_expr cx a) (read_result cx) (es with gas_obs := gs1) =
         (INL v1, es1)` by
    (qexists_tac `gas_explicit m1 s0.vs_gas_readings` >>
     qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >>
     simp[]) >>
  `!H. valid_horizon cx st0 H es1.storage_trace ==>
       valid_horizon cx st0 H es.storage_trace` by
    (`?obs. es1.storage_trace = es.storage_trace ++ obs` by
       (qpat_assum `bind (eval_expr cx a) _ _ = _`
          (mp_then (Pos last) mp_tac storage_trace_frame_prefix) >>
        simp[]) >>
     simp[valid_horizon_def]) >>
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
  `!H. valid_horizon cx st0 H es1.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es1 t /\
       storage_well_formed_on cx es1 (FST H)` by
    (qx_gen_tac `H` >> strip_tac >> res_tac >>
     conj_tac >>
     first_assum (fn th =>
       let val r = REWRITE_RULE [expr_post_def] th in
         ACCEPT_TAC (CONJUNCT1 r) ORELSE
         ACCEPT_TAC (CONJUNCT1 (CONJUNCT2 r))
       end)) >>
  match_mp_tac
    (Q.SPEC `\H v2 ee u. expr_post H ctx func cenv cx b es1 s1 sm t ee v2 q u /\
       expr_store_bound cx (expr_type b) v2 q u /\
       u.vs_current_bb = sm.cs_current_bb /\
       u.vs_inst_idx = LENGTH sm.cs_current_insts /\
       alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next`
     (Q.GEN `P` ec_mem_outcome_then)) >>
  BETA_TAC >> rpt conj_tac
  >- (qpat_x_assum `expr_sim_mem _ _ _ _ _ b _`
        (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
      disch_then irule >> simp[] >>
      metis_tac[expr_body_pre_gas_admissible])
  >- first_assum ACCEPT_TAC
  >- (rpt strip_tac >> first_assum MATCH_ACCEPT_TAC)
  >- suspend "second_success"
QED

Resume ec_mem_operands_then[second_success]:
  qx_genl_tac [`m2`, `v2`, `es2`, `u`] >> strip_tac >>
  `es2 with gas_obs := [] = es2` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  `?gs2. bind (eval_expr cx b) (read_result cx) (es1 with gas_obs := gs2) =
         (INL v2, es2)` by
    (qexists_tac `gas_explicit m2 t.vs_gas_readings` >>
     qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >>
     simp[]) >>
  `!H. valid_horizon cx st0 H es2.storage_trace ==>
       valid_horizon cx st0 H es1.storage_trace` by
    (`?obs. es2.storage_trace = es1.storage_trace ++ obs` by
       (qpat_assum `bind (eval_expr cx b) _ _ = _`
          (mp_then (Pos last) mp_tac storage_trace_frame_prefix) >>
        simp[]) >>
     simp[valid_horizon_def]) >>
  qspecl_then [`cenv`, `cx`, `env`, `b`, `es1 with gas_obs := gs2`, `INL v2`, `es2`]
    mp_tac (CONV_RULE (DEPTH_CONV ETA_CONV) expr_body_pre_eval) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `expr_result_typed env b (Value v2)` by simp[] >>
  `MAP FDOM es1.scopes = MAP FDOM es2.scopes` by
    (qpat_assum `bind (eval_expr cx b) _ _ = _`
       (mp_then Any mp_tac
         (CONV_RULE (DEPTH_CONV ETA_CONV)
            exprSimWordArgsTheory.forced_eval_expr_preserves_scopes_dom)) >> simp[]) >>
  `!H. valid_horizon cx st0 H es2.storage_trace ==>
       valid_horizon cx st0 H es.storage_trace` by
    (qx_gen_tac `H` >> strip_tac >>
     `valid_horizon cx st0 H es1.storage_trace` by
       first_assum (drule_then ACCEPT_TAC) >>
     first_assum (drule_then ACCEPT_TAC)) >>
  `!H. valid_horizon cx st0 H es2.storage_trace ==>
       expr_post H ctx func cenv cx a es sa s1 s0 es1 v1 p t /\
       expr_post H ctx func cenv cx b es1 s1 sm t es2 v2 q u /\
       stmt_state_rel H ctx func cenv cx es2 u` by
    (qx_gen_tac `H` >> strip_tac >>
     `valid_horizon cx st0 H es1.storage_trace` by
       first_assum (drule_then ACCEPT_TAC) >>
     res_tac >>
     conj_tac >- conj_assum_tac >>
     conj_tac >- conj_assum_tac >>
     first_assum (fn th =>
       ACCEPT_TAC (CONJUNCT1 (REWRITE_RULE [expr_post_def] th)))) >>
  `?H0. valid_horizon cx st0 H0 es2.storage_trace` by
    (qexists_tac `storage_trace_horizon es2.storage_trace` >>
     first_assum (fn th =>
       ACCEPT_TAC (REWRITE_RULE [storage_trace_domain_def] th))) >>
  `valid_horizon cx st0 H0 es1.storage_trace` by
    first_assum (drule_then ACCEPT_TAC) >>
  res_tac >>
  qspecl_then [`H0`, `func`, `cenv`, `cx`, `a`, `b`, `es`, `es1`, `es2`, `sa`,
               `s1`, `sm`, `s0`, `t`, `u`, `v1`, `v2`, `p`, `q`, `ctx`] mp_tac
    (Q.GEN `H` exprSimOperandsTheory.expr_post_operand_word) >>
  (impl_tac >- (rpt conj_tac >> conj_assum_tac)) >> strip_tac >>
  `!w. eval_operand p t = SOME w ==> eval_operand p u = SOME w` by
    metis_tac[optionTheory.SOME_11] >>
  `post_value_type cenv a = expr_type a` by
    (irule post_value_type_ec_point >> conj_tac >- simp[] >>
     qexistsl_tac [`cx`,`env`,`es`] >>
     qpat_assum `expr_type a = _` (fn th => simp[th]) >>
     qpat_x_assum `expr_body_pre _ _ _ (Builtin _ _ _) _` mp_tac >>
     simp[expr_body_pre_def, vyperTypeSystemTheory.well_typed_expr_def]) >>
  `expr_val_rel cx (expr_type a) v1 p u /\
   expr_val_at cenv cx (expr_type a) sa sm es2 v1 p u` by
    (qspecl_then [`H0`, `cenv`, `a`, `ctx`, `func`, `cx`, `es`, `sa`, `s1`,
                  `s0`, `es1`, `v1`, `p`, `t`, `b`, `sm`, `es2`, `v2`, `q`, `u`,
                  `env`] mp_tac
       (Q.GENL [`H`, `cenv`, `e1`, `ctx`, `func`, `cx`, `es`, `sa`, `s1`, `s0`,
                `es1`, `v1`, `x`, `t`, `e2`, `s2`, `es'`, `v2`, `y`, `u`, `env`]
          ec_point_operand_kept) >>
     (impl_tac >- (rpt conj_tac >> conj_assum_tac)) >> simp[]) >>
  `expr_store_bound cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v1 p t` by
    (qpat_assum `expr_type _ = _`
       (fn eq => conj_assum_thm_tac
          (fn sb => ACCEPT_TAC (REWRITE_RULE [eq] sb)))) >>
  `w2n w + 64 <= u.vs_alloca_next` by
    (qspecl_then [`cx`, `v1`, `p`, `t`, `w`, `u`] mp_tac
       (Q.GENL [`cx`, `v`, `p`, `t`, `w`, `u`] ec_point_read_capacity) >>
     (impl_tac >- (rpt conj_tac >> conj_assum_tac)) >> simp[]) >>
  `!z. MEM (Var z) [p;q] ==> not_fresh_at sm z` by
    (simp[] >> metis_tac[exprOperandVarTheory.compile_lower_value_var,
                         freshWritesTheory.not_fresh_at_mono]) >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by
    (match_mp_tac arithmeticTheory.LESS_EQ_TRANS >>
     qexists_tac `t.vs_alloca_next` >> conj_tac >> conj_assum_tac) >>
  qpat_x_assum `!es1 es2 v1 v2 t u. _`
    (qspecl_then [`es1`, `es2`, `v1`, `v2`, `t`, `u`] mp_tac) >>
  (impl_tac
   >- (rpt conj_tac >> TRY conj_assum_tac >>
       TRY (qexists_tac `H0` >> conj_assum_tac) >>
       TRY (qexists_tac `w` >> conj_tac >> conj_assum_tac))) >>
  strip_tac >> first_assum ACCEPT_TAC
QED
Finalise ec_mem_operands_then
