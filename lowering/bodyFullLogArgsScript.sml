(*
 * The Log statement's argument evaluation (compile_log_eval_all) over the
 * finite-horizon joint judgment: each argument's joint fragment
 * (expr_sim_full) composed left to right into one gas_outcome_full over
 * eval_exprs.  The statement doesn't depend on the event's field types, so
 * the scalar and aggregate Log arms both build on it.
 *
 * TOP-LEVEL:
 *   compile_log_eval_all_full - the arguments as one joint outcome, given a
 *     readiness predicate R that supplies each head's expr_sim_full and is
 *     kept by the head's successful evaluation.  The arguments are
 *     effect-free, so each later one keeps the whole of every live local
 *     (pure_frame), and an earlier argument's value and pointer facts hold
 *     at the end whatever its type.
 *)
Theory bodyFullLogArgs
Ancestors
  bodySimFull loweringPosts bodyPtrDefs logArgsRunPtr stmtSimLogArgs
  stmtSimLogArgsGrowth gasOutcomeFullCompose gasShadowState gasShadow
  logValueFramePtr logGhostFramePtr exprSimProps exprSimWordArgs
  exprOperandVar exprReasonOperand exprLoweringProps fragExec freshWrites
  bodyMemoryDefs gasShadowCompileHelpers gasShadowCompileStmtHelpers
  gasExemptCert gasOutcomeFull vyperStorageTrace vyperStorageFootprint
  loweringStateRelDefs ptrDiscipline valueEncodingDefs fragGasOriginPtr
  vyperTypeSystem exprSimDefs
  exprLowering stmtLowering supportedExprTraverse compileEnv
  vyperInterpreter vyperState list

(* ===== Frames kept by later effect-free arguments ===== *)

(* ghost_kept_trans at a low-memory bound lo. *)
Theorem ghost_kept_at_trans:
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  ghost_kept_at lo cenv es1 sm G1 tn1 s1 G2 tn2 /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
           FLOOKUP s1.vs_allocas aid = SOME b) /\
  (!n b sz. local_region cenv es1.scopes s1 n b sz <=>
            local_region cenv es.scopes s0 n b sz) ==>
  ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2
Proof
  simp[ghost_kept_at_def] >> rpt strip_tac
  >- (`not_fresh_at sm x` by (gvs[not_fresh_at_def] >> decide_tac) >> metis_tac[])
  >- (`not_fresh_at sm x` by (gvs[not_fresh_at_def] >> decide_tac) >> metis_tac[])
  >- (`i IN tn1.t_mem` suffices_by
        (strip_tac >>
         qpat_x_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _`
           (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >>
         impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
         disch_then ACCEPT_TAC) >>
      qpat_x_assum `!aid off sz i. FLOOKUP s1.vs_allocas aid = _ /\ _ ==> _` irule >>
      conj_tac >- (qexistsl_tac [`aid`,`off`,`sz`] >> simp[] >> metis_tac[]) >> simp[])
  >- (`i IN tn1.t_mem` suffices_by
        (strip_tac >>
         qpat_x_assum `!n b sz i. local_region cenv es.scopes s0 n b sz /\ _ ==> _`
           (qspecl_then [`n`,`b`,`sz`,`i`] mp_tac) >>
         impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
         disch_then ACCEPT_TAC) >>
      qpat_x_assum `!n b sz i. local_region cenv es1.scopes s1 n b sz /\ _ ==> _` irule >>
      conj_tac >- simp[] >> qexistsl_tac [`b`,`n`,`sz`] >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem ghost_kept_at_wb_trans:
  !lo cenv es sa G0 tn0 s0 G1 tn1 es1 sm G2 tn2 s1 H ctx func cx es'.
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  ghost_kept_at lo cenv es1 sm G1 tn1 s1 G2 tn2 /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  stmt_state_rel H ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\ wb_frame cenv es es' sa s0 s1 ==>
  ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2
Proof
  rpt gen_tac >> strip_tac >> irule ghost_kept_at_trans >>
  qexistsl_tac [`G1`,`es1`,`s1`,`sm`,`tn1`] >> simp[] >>
  reverse conj_tac >- (gvs[wb_frame_def] >> metis_tac[]) >>
  rpt gen_tac >> drule_all log_frame_local_region >> simp[]
QED

(* An argument's bytes survive a later effect-free fragment: its own
   allocation by the write-back frame, a live local whole by pure_frame. *)
Theorem pure_argument_footprint_kept:
  !cenv cx func ty tv v op sa sb es ee s t w.
    expr_val_at cenv cx ty sa sb es v op s /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
    eval_operand op s = SOME w /\
    wb_frame cenv es ee sb s t /\ pure_frame cenv func es sb s t ==>
    mem_bytes_at (w2n w) (val_footprint tv v) t.vs_memory =
    mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_val_at_def]) >>
  disch_then (qspec_then `tv` mp_tac) >> simp[] >>
  disch_then strip_assume_tac
  >- (gvs[] >>
      `mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory` by
        (gvs[wb_frame_def] >> first_x_assum irule >>
         conj_tac >- first_assum ACCEPT_TAC >>
         qexists_tac `aid` >> simp[]) >>
      drule valueEncodingProofsTheory.mem_bytes_at_agree_window >>
      strip_tac >> sym_tac >> first_x_assum irule >> simp[])
  >- (gvs[] >>
      `mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory` by
        (fs[pure_frame_def] >>
         qpat_x_assum `!n b sz. local_region _ _ _ _ _ _ ==> _` irule >>
         qexists_tac `n` >> first_assum ACCEPT_TAC) >>
      drule valueEncodingProofsTheory.mem_bytes_at_agree_window >>
      strip_tac >> sym_tac >> first_x_assum irule >> simp[]) >>
  gvs[valueEncodingDefsTheory.mem_bytes_at_def]
QED

Theorem pure_argument_value_kept:
  !cenv cx func ty es ee sa sb s t v op.
    expr_val_rel cx ty v op s /\
    expr_val_at cenv cx ty sa sb es v op s /\
    wb_frame cenv es ee sb s t /\ pure_frame cenv func es sb s t /\
    (!z. op = Var z ==> not_fresh_at sb z) /\ (!l. op <> Label l) ==>
    expr_val_rel cx ty v op t
Proof
  rpt gen_tac >> strip_tac >>
  `?w. eval_operand op s = SOME w` by gvs[expr_val_rel_def] >>
  `eval_operand op t = SOME w` by (drule_all log_frame_operand >> simp[]) >>
  Cases_on `is_word_type ty`
  >- gvs[expr_val_rel_def] >>
  Cases_on `evaluate_type (get_tenv cx) ty`
  >- simp[expr_val_rel_def] >>
  rename1 `evaluate_type _ _ = SOME tv` >>
  `val_wf tv v` by (gvs[expr_val_at_def] >> metis_tac[]) >>
  drule_all pure_argument_footprint_kept >> strip_tac >>
  irule expr_val_rel_footprint_agree >> simp[] >>
  qexists_tac `s` >> simp[]
QED

Theorem pure_argument_taint_kept:
  !lo cenv cx ty tv v op sa sb es s G0 tn0 G tn w i.
    expr_val_at cenv cx ty sa sb es v op s /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
    eval_operand op s = SOME w /\
    ghost_kept_at lo cenv es sb G0 tn0 s G tn /\
    w2n w <= i /\ i < w2n w + val_footprint tv v /\ i IN tn.t_mem ==>
    i IN tn0.t_mem
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_val_at_def]) >>
  disch_then (qspec_then `tv` mp_tac) >> simp[] >> strip_tac
  >- (gvs[] >> fs[ghost_kept_at_def] >>
      qpat_x_assum `!aid off sz i. FLOOKUP _ _ = _ /\ _ ==> _`
        (qspecl_then [`aid`, `b`, `sz`, `i`] mp_tac) >>
      simp[] >> disch_then irule >> metis_tac[])
  >- (gvs[] >> fs[ghost_kept_at_def] >>
      qpat_x_assum `!n b sz i. local_region _ _ _ _ _ _ /\ _ ==> _`
        (qspecl_then [`n`, `b`, `sz`, `i`] mp_tac) >>
      simp[]) >>
  gvs[]
QED

Theorem pure_argument_ptr_val_kept:
  !lo cenv cx func ty v op sa sb es es' s t G0 tn0 G tn.
    ptr_val_ok cx ty v op G0 tn0 s /\ expr_val_rel cx ty v op s /\
    expr_val_at cenv cx ty sa sb es v op s /\
    wb_frame cenv es es' sb s t /\ pure_frame cenv func es sb s t /\
    ghost_kept_at lo cenv es sb G0 tn0 s G tn /\
    (!z. op = Var z ==> not_fresh_at sb z) /\ (!l. op <> Label l) ==>
    ptr_val_ok cx ty v op G tn t
Proof
  rpt gen_tac >> strip_tac >> irule ptr_val_ok_footprint_frame >>
  qexistsl_tac [`G0`, `s`, `tn0`] >> simp[] >>
  conj_tac >- (rpt strip_tac >> gvs[ghost_kept_at_def]) >>
  conj_tac
  >- (rpt strip_tac >>
      `?w0. eval_operand op s = SOME w0` by gvs[expr_val_rel_def] >>
      drule_all log_frame_operand >> simp[]) >>
  reverse conj_tac
  >- (Cases_on `op` >> gvs[ghost_kept_at_def, op_taint_def]) >>
  rpt gen_tac >> strip_tac >>
  `val_wf tv v` by (gvs[expr_val_at_def] >> metis_tac[]) >> simp[] >>
  conj_tac
  >- (irule pure_argument_footprint_kept >>
      goal_assum (drule_at Any) >> metis_tac[]) >>
  rpt strip_tac >> drule_all pure_argument_taint_kept >> simp[]
QED

(* One argument's facts carried from the end of its own fragment (t) over
   the effect-free fragments of the later arguments (to u). *)
Theorem pure_argument_kept:
  expr_val_rel cx ty v op t /\ expr_val_at cenv cx ty sa sm es1 v op t /\
  ptr_val_ok cx ty v op G1 tn1 t /\
  (~is_word_type ty ==> ptr_buf_ok cenv e op G1 t) /\
  stmt_state_rel H ctx func cenv cx es1 t /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es1.scopes = MAP FDOM ee.scopes /\
  sm.cs_next_id <= sb.cs_next_id /\
  wb_frame cenv es1 ee sm t u /\ pure_frame cenv func es1 sm t u /\
  ghost_kept_at lo cenv es1 sm G1 tn1 t G tn /\
  (!z. op = Var z ==> not_fresh_at sm z) /\ (!l. op <> Label l) ==>
  expr_val_rel cx ty v op u /\ expr_val_at cenv cx ty sa sb ee v op u /\
  ptr_val_ok cx ty v op G tn u /\
  (~is_word_type ty ==> ptr_buf_ok cenv e op G u)
Proof
  strip_tac >> rpt conj_tac
  >- (drule_all pure_argument_value_kept >> simp[])
  >- (drule_all log_frame_placement >> simp[])
  >- (drule_all pure_argument_ptr_val_kept >> simp[]) >>
  strip_tac >> irule ptr_buf_ok_frame >> qexistsl_tac [`G1`, `t`] >>
  `?w. eval_operand op t = SOME w` by gvs[expr_val_rel_def] >>
  `eval_operand op u = SOME w` by (drule_all log_frame_operand >> simp[]) >>
  simp[] >> rpt strip_tac >> gvs[ghost_kept_at_def]
QED

(* ===== The argument-list induction ===== *)

(* The normal post of compile_log_eval_all_full, kept opaque inside the
   induction. *)
Definition log_full_post_def:
  log_full_post DF lo d ctx func cenv cx es sa sb s0 G0 tn0 args ops =
    (\H res ee G tn t. ?vs. res = INL vs /\
      stmt_state_rel H ctx func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      wb_frame cenv es ee sa s0 t /\ pure_frame cenv func es sa s0 t /\
      MAP FDOM ee.scopes = MAP FDOM es.scopes /\
      return_buf_frame d cenv sb t /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      LENGTH ops = LENGTH args /\
      MAP SND ops = MAP (lowered_value_type cenv) args /\
      EVERY (\p. (!x. FST p = Var x ==> not_fresh_at sb x) /\
                 (!lab. FST p <> Label lab)) ops /\
      LIST_REL (\(op,e) v.
        expr_val_rel cx (expr_type e) v op t /\
        expr_val_at cenv cx (expr_type e) sa sb ee v op t /\
        ptr_val_ok cx (expr_type e) v op G tn t /\
        (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e op G t) /\
        ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
             value_has_type tv v)
        (ZIP (MAP FST ops, args)) vs)
End

Theorem log_full_post_nil[local]:
  stmt_state_rel H ctx func cenv cx es s0 /\
  storage_well_formed_on cx es (FST H) /\
  ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0 /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  log_full_post DF lo d ctx func cenv cx es sa sa s0 G0 tn0 [] [] H
    (INL []) (es with gas_obs := []) G0 tn0 s0
Proof
  strip_tac >>
  `storage_well_formed_on cx (es with gas_obs := []) (FST H)` by
    (`(es with gas_obs := []).accounts = es.accounts /\
      (es with gas_obs := []).tStorage = es.tStorage` by simp[] >>
     metis_tac[storage_well_formed_on_backends]) >>
  `ghost_inv_at (DF H) lo d cenv cx (es with gas_obs := []) G0 tn0 s0` by
    (fs[ghost_inv_at_def] >> metis_tac[]) >>
  simp[log_full_post_def, wb_frame_gas_obs, wb_frame_refl,
       ghost_kept_at_def]
QED

(* The head argument's post at t composed with the tail's post from t. *)
Theorem log_full_post_cons[local]:
  stmt_state_rel H ctx func cenv cx es s0 /\
  expr_post H ctx func cenv cx e es sa sm s0 es1 v x t /\
  post_value_type cenv e = expr_type e /\ ~expr_has_effect e /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  ptr_val_ok cx (expr_type e) v x G1 tn1 t /\
  (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e x G1 t) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
  (!z. x = Var z ==> not_fresh_at sm z) /\ (!l. x <> Label l) /\
  log_full_post DF lo d ctx func cenv cx es1 sm sb t G1 tn1 args ys H
    (INL vs : value list + exception) ee G tn u ==>
  log_full_post DF lo d ctx func cenv cx es sa sb s0 G0 tn0 (e::args)
    ((x, lowered_value_type cenv e)::ys) H (INL (v::vs)) ee G tn u
Proof
  rewrite_tac[log_full_post_def] >> BETA_TAC >> strip_tac >> gvs[] >>
  `MAP FDOM es1.scopes = MAP FDOM es.scopes /\
   expr_val_rel cx (expr_type e) v x t /\
   expr_val_at cenv cx (expr_type e) sa sm es1 v x t /\
   (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
          lookup_var z t = SOME w)` by
    (qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[expr_post_def, locals_kept_def] >> strip_tac >> gvs[]) >>
  `wb_frame cenv es es1 sa s0 t /\ stmt_state_rel H ctx func cenv cx es1 t /\
   pure_frame cenv func es sa s0 t` by
    metis_tac[expr_post_frame, expr_post_state, expr_post_pure_frame] >>
  `!aid b. FLOOKUP t.vs_allocas aid = SOME b ==>
           FLOOKUP u.vs_allocas aid = SOME b` by
    (qpat_x_assum `wb_frame cenv es1 ee sm t u` mp_tac >>
     rewrite_tac[wb_frame_def] >> metis_tac[]) >>
  `wb_frame cenv es ee sa s0 u` by
    (qspecl_then [`func`,`cenv`,`cx`,`es`,`s0`,`sa`,`es1`,`ee`,`sm`,`t`,
                  `u`,`ctx`] mp_tac wb_frame_trans >> simp[]) >>
  `pure_frame cenv func es sa s0 u` by
    (qspecl_then [`cenv`,`func`,`es`,`es1`,`sa`,`sm`,`s0`,`t`,`u`] mp_tac
       pure_frame_trans >> simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G tn` by
    (qspecl_then [`lo`,`cenv`,`es`,`sa`,`G0`,`tn0`,`s0`,`G1`,`tn1`,`es1`,
                  `sm`,`G`,`tn`,`t`,`H`,`ctx`,`func`,`cx`,`es1`] mp_tac
       ghost_kept_at_wb_trans >> simp[]) >>
  `expr_val_rel cx (expr_type e) v x u /\
   expr_val_at cenv cx (expr_type e) sa sb ee v x u /\
   ptr_val_ok cx (expr_type e) v x G tn u /\
   (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e x G u)` by
    (irule pure_argument_kept >> simp[] >>
     qexistsl_tac [`G1`, `H`, `ctx`, `es1`, `func`, `lo`, `sm`, `t`, `tn1`] >>
     simp[]) >>
  `!z. x = Var z ==> not_fresh_at sb z` by metis_tac[not_fresh_at_mono] >>
  `LIST_REL (\(op,e) v.
      expr_val_rel cx (expr_type e) v op u /\
      expr_val_at cenv cx (expr_type e) sa sb ee v op u /\
      ptr_val_ok cx (expr_type e) v op G tn u /\
      (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e op G u) /\
      ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
           value_has_type tv v) (ZIP (MAP FST ys, args)) vs` by
    (qpat_x_assum `LIST_REL _ (ZIP (MAP FST ys, args)) vs` mp_tac >>
     match_mp_tac LIST_REL_mono >> simp[pairTheory.FORALL_PROD] >>
     rpt strip_tac >> TRY (first_assum ACCEPT_TAC) >>
     irule expr_val_at_start_mono >> goal_assum (drule_at Any) >> simp[]) >>
  simp[] >> metis_tac[]
QED

(* Consing a value onto a list result maps the list outcome. *)
Theorem gas_outcome_full_cons_value[local]:
  gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0
    (eval_exprs cx args) (es, s, G, tn) Q R ==>
  gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0
    (bind (eval_exprs cx args) (\vs. return (v::vs))) (es, s, G, tn)
    (\H raw ee G tn t. ?res. raw = sum_CASE res (\vs. INL (v::vs)) INR /\
                             Q H res ee G tn t)
    (\H raw ee gt r. ?res. raw = sum_CASE res (\vs. INL (v::vs)) INR /\
                           R H res ee gt r)
Proof
  strip_tac >>
  ho_match_mp_tac (GEN_ALL gas_outcome_full_source_map) >>
  qexists_tac `eval_exprs cx args` >> simp[] >>
  qx_gen_tac `st` >>
  Cases_on `eval_exprs cx args st` >>
  rename1 `eval_exprs _ _ _ = (r0, _)` >>
  Cases_on `r0` >> simp[bind_def, return_def]
QED

Theorem compile_log_eval_all_full_ind[local]:
  !DF lo d PG ctx shadow_ctx func shadow_func cenv cx st0 R env.
    (!e tail es. R (e::tail) es ==>
       expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
         cenv cx (expr_type e) e es /\
       !v es1. bind (eval_expr cx e) (read_result cx) es = (INL v, es1) ==>
         R tail es1 /\
         ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
              value_has_type tv v) /\
    (!tail es gs. R tail es ==> R tail (es with gas_obs := gs)) /\
    (!id t. FLOOKUP env.var_types id = SOME t ==>
       ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) ==>
    !args es sa sb shadow_sa shadow_sb ops s0 G0 tn0.
      R args es /\ ~exprs_can_mutate cenv args /\
      EVERY (\e. ~expr_has_effect e) args /\
      EVERY (\e. post_value_type cenv e = expr_type e) args /\
      well_typed_exprs env args /\
      compile_log_eval_all cenv args sa = (ops, sb) /\
      compile_log_eval_all cenv (MAP gas_shadow_expr args) shadow_sa =
        (ops, shadow_sb) /\
      gas_shadow_state sa shadow_sa /\
      gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
      gas_shadow_function func shadow_func /\
      MEM func ctx.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      fn_has_code sa sb func /\
      fn_has_code shadow_sa shadow_sb shadow_func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      gas_admissible (eval_exprs cx args)
        (\r. !exc. r = INR exc ==> expr_res_ok (INR exc : value + exception))
        es /\
      return_buf_frame d cenv sa s0 /\
      alloca_history func s0 /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 /\
        storage_well_formed_on cx es (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome_full
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        (cx_tops cx) cx st0 (eval_exprs cx args) (es, s0, G0, tn0)
        (log_full_post DF lo d ctx func cenv cx es sa sb s0 G0 tn0 args ops)
        (\H res ee gt r. expr_exit res r)
Proof
  rpt gen_tac >> strip_tac >> Induct
  >- (rpt gen_tac >> strip_tac >> gvs[compile_log_eval_all_nil] >>
      irule gas_outcome_full_pure >> reverse conj_tac >- simp[] >>
      qexistsl_tac [`G0`, `es`, `INL []`, `s0`, `tn0`] >>
      simp[Once evaluate_def, return_def] >> rpt strip_tac
      >- simp[gas_origin_ptr_path_rules] >>
      irule log_full_post_nil >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> gvs[expr_can_mutate_def] >>
  `~exprs_can_mutate cenv (MAP gas_shadow_expr args)` by
    simp[gas_shadow_expr_can_mutate] >>
  qpat_x_assum `compile_log_eval_all cenv (e::args) sa = _` mp_tac >>
  qpat_x_assum `compile_log_eval_all cenv (gas_shadow_expr e::_) _ = _` mp_tac >>
  simp[compile_log_eval_all_unsaved_cons] >> rpt strip_tac >> gvs[] >>
  rename1 `lower_value compile_expr cenv (expr_type e) (gas_shadow_expr e)
             shadow_sa = (x, ssm)` >>
  rename1 `lower_value compile_expr cenv (expr_type e) e sa = (x, sm)` >>
  suspend "cons"
QED

Resume compile_log_eval_all_full_ind[cons]:
  `gas_shadow_compiles (lower_value compile_expr cenv (expr_type e) e)
     (lower_value compile_expr cenv (expr_type e) (gas_shadow_expr e))` by
    simp[gas_shadow_stmt_lower_value] >>
  `gas_shadow_state sm ssm` by
    (qpat_x_assum `gas_shadow_compiles _ _`
       (mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
     disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[]) >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\
   sa.cs_next_id <= sm.cs_next_id` by
    (qpat_x_assum `lower_value _ _ _ e sa = _`
       (strip_assume_tac o MATCH_MP (cj 2 compile_expr_grows)) >> simp[]) >>
  `cs_extends shadow_sa ssm` by
    (qpat_x_assum `lower_value _ _ _ (gas_shadow_expr e) _ = _`
       (strip_assume_tac o MATCH_MP (cj 2 compile_expr_grows))) >>
  `cs_extends sm sb /\ sm.cs_next_var <= sb.cs_next_var /\
   sm.cs_next_id <= sb.cs_next_id` by
    (qspecl_then [`args`, `sm`, `ys`, `sb`] mp_tac compile_log_eval_all_grows >>
     simp[]) >>
  `cs_extends ssm shadow_sb` by
    (qspecl_then [`MAP gas_shadow_expr args`, `ssm`, `ys`, `shadow_sb`] mp_tac
       compile_log_eval_all_grows >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func /\
   fn_has_code shadow_sa ssm shadow_func /\
   fn_has_code ssm shadow_sb shadow_func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `well_typed_expr env e /\ well_typed_exprs env args` by
    fs[well_typed_expr_def] >>
  `(!z. x = Var z ==> not_fresh_at sm z) /\ !l. x <> Label l` by
    (conj_tac >- metis_tac[compile_lower_value_var] >>
     drule_all lower_compile_expr_not_label >> simp[]) >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
     cenv cx (expr_type e) e es` by metis_tac[] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule log_head_admissible >> qexists_tac `args` >> simp[]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `shadow_sa`, `ssm`, `x`,
                           `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ headQ _` >>
  rewrite_tac[eval_exprs_cons_bind] >>
  irule gas_outcome_full_bind_all >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      qexistsl [`mid`, `t`, `v`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_return]) >>
  qexists `\H res ee G tn t. headQ H res ee G tn t /\ ~t.vs_halted /\
                             ee.gas_obs = []` >>
  conj_tac
  >~ [`storage_trace_domain _ _ _`]
  >- suspend "tail" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ headQ _` (irule_at Any) >>
  conj_tac >- simp[] >>
  rpt strip_tac >> Cases_on `res` >> fs[expr_exit_def] >>
  metis_tac[expr_exit_INR_type]
QED

Resume compile_log_eval_all_full_ind[tail]:
  qx_genl_tac [`marks`, `res`, `mid`, `G1`, `tn1`, `t`] >>
  BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qunabbrev_tac `headQ` >> BETA_TAC >> strip_tac >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  disj1_tac >> qexists_tac `v` >> conj_tac >- simp[] >> BETA_TAC >>
  `mid with gas_obs := [] = mid` by
    simp[evaluation_state_component_equality] >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
   (INL v, mid)` by
    (qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     simp[]) >>
  `R (e::args) (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    metis_tac[] >>
  `R args mid /\ ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                      value_has_type tv v` by metis_tac[] >>
  `gas_admissible (eval_exprs cx args)
     (\r. !exc. r = INR exc ==> expr_res_ok (INR exc : value + exception))
     mid` by
    (`gas_admissible (eval_exprs cx args)
       (\r. !exc. r = INR exc ==> expr_res_ok (INR exc : value + exception))
       (mid with gas_obs := [])` suffices_by simp[] >>
     irule log_tail_admissible >> metis_tac[]) >>
  `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
    (irule storage_trace_frame_bind_all >>
     simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       valid_horizon cx st0 H es.storage_trace` by
    (rpt strip_tac >> drule_all valid_horizon_frame >> simp[]) >>
  suspend "ih"
QED

Resume compile_log_eval_all_full_ind[ih]:
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s0 /\
     expr_post H ctx func cenv cx e es sa sm s0 mid v x t /\
     ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t /\
     ptr_val_ok cx (expr_type e) v x G1 tn1 t /\
     (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e x G1 t) /\
     ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1` by
    (qx_gen_tac `H1` >> strip_tac >>
     `valid_horizon cx st0 H1 es.storage_trace` by metis_tac[] >>
     qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `H1` mp_tac) >>
     qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (qspec_then `H1` mp_tac) >>
     simp[] >> rpt strip_tac >> gvs[]) >>
  `(!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
          lookup_var z t = SOME w)` by
    (qpat_x_assum `expr_post (storage_trace_horizon _) _ _ _ _ _ _ _ _ _ _ _ _ _`
       mp_tac >> rewrite_tac[expr_post_def] >> metis_tac[]) >>
  `return_buf_frame d cenv sm t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `s0`, `sa`] >>
     simp[]) >>
  `(!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==>
      not_fresh_at sm z) /\
   (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==>
      not_fresh_at sm z)` by metis_tac[not_fresh_at_mono] >>
  qpat_x_assum `!es sa sb shadow_sa shadow_sb ops s0 G0 tn0. _`
    (qspecl_then [`mid`, `sm`, `sb`, `ssm`, `shadow_sb`, `ys`, `t`, `G1`,
                  `tn1`] mp_tac) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >> res_tac >> fs[expr_post_def]) >>
  strip_tac >>
  `gas_outcome_full (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
     (cx_tops cx) cx st0 (eval_exprs cx args) (mid, t, G1, tn1)
     (\H res ee G tn u.
        log_full_post DF lo d ctx func cenv cx mid sm sb t G1 tn1 args ys
          H res ee G tn u /\ valid_horizon cx st0 H mid.storage_trace)
     (\H res ee gt r. expr_exit res r)` by
    (irule gas_outcome_full_post_source >>
     first_assum (irule_at Any) >> simp[] >> rpt strip_tac >>
     first_x_assum (qspec_then `[]` assume_tac) >> fs[] >>
     drule_at (Pos (el 2)) valid_horizon_frame >>
     simp[evaluate_storage_trace_frame]) >>
  drule gas_outcome_full_cons_value >>
  disch_then (qspec_then `v` assume_tac) >>
  drule gas_outcome_full_post_mono >> disch_then irule >>
  reverse conj_tac
  >- (qx_genl_tac [`H2`, `raw`, `ee2`, `gt2`, `rr`] >> BETA_TAC >>
      disch_then (qx_choose_then `r0` strip_assume_tac) >>
      Cases_on `r0` >> gvs[expr_exit_def] >>
      metis_tac[expr_exit_INR_type]) >>
  qx_genl_tac [`H`, `raw`, `ee`, `Gq`, `tnq`, `tq`] >> BETA_TAC >>
  disch_then (qx_choose_then `r0` strip_assume_tac) >>
  `?vs. r0 = INL vs` by fs[log_full_post_def] >> gvs[] >>
  `stmt_state_rel H ctx func cenv cx es s0 /\
   expr_post H ctx func cenv cx e es sa sm s0 mid v x t /\
   ptr_val_ok cx (expr_type e) v x G1 tn1 t /\
   (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e x G1 t) /\
   ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1` by metis_tac[] >>
  irule log_full_post_cons >> simp[] >>
  qexistsl_tac [`G1`, `mid`, `sm`, `t`, `tn1`] >> simp[] >>
  first_assum ACCEPT_TAC
QED

Finalise compile_log_eval_all_full_ind

Theorem compile_log_eval_all_full:
  !DF lo d PG ctx shadow_ctx func shadow_func cenv cx st0 R env.
    (!e tail es. R (e::tail) es ==>
       expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
         cenv cx (expr_type e) e es /\
       !v es1. bind (eval_expr cx e) (read_result cx) es = (INL v, es1) ==>
         R tail es1 /\
         ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
              value_has_type tv v) /\
    (!tail es gs. R tail es ==> R tail (es with gas_obs := gs)) /\
    (!id t. FLOOKUP env.var_types id = SOME t ==>
       ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) ==>
    !args es sa sb shadow_sa shadow_sb ops s0 G0 tn0.
      R args es /\ ~exprs_can_mutate cenv args /\
      EVERY (\e. ~expr_has_effect e) args /\
      EVERY (\e. post_value_type cenv e = expr_type e) args /\
      well_typed_exprs env args /\
      compile_log_eval_all cenv args sa = (ops, sb) /\
      compile_log_eval_all cenv (MAP gas_shadow_expr args) shadow_sa =
        (ops, shadow_sb) /\
      gas_shadow_state sa shadow_sa /\
      gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
      gas_shadow_function func shadow_func /\
      MEM func ctx.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      fn_has_code sa sb func /\
      fn_has_code shadow_sa shadow_sb shadow_func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      gas_admissible (eval_exprs cx args)
        (\r. !exc. r = INR exc ==> expr_res_ok (INR exc : value + exception))
        es /\
      return_buf_frame d cenv sa s0 /\
      alloca_history func s0 /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 /\
        storage_well_formed_on cx es (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome_full
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        (cx_tops cx) cx st0 (eval_exprs cx args) (es, s0, G0, tn0)
        (\H res ee G tn t. ?vs. res = INL vs /\
          stmt_state_rel H ctx func cenv cx ee t /\
          storage_well_formed_on cx ee (FST H) /\
          wb_frame cenv es ee sa s0 t /\ pure_frame cenv func es sa s0 t /\
          MAP FDOM ee.scopes = MAP FDOM es.scopes /\
          return_buf_frame d cenv sb t /\
          alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
          ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
          ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          LENGTH ops = LENGTH args /\
          MAP SND ops = MAP (lowered_value_type cenv) args /\
          EVERY (\p. (!x. FST p = Var x ==> not_fresh_at sb x) /\
                     (!lab. FST p <> Label lab)) ops /\
          LIST_REL (\(op,e) v.
            expr_val_rel cx (expr_type e) v op t /\
            expr_val_at cenv cx (expr_type e) sa sb ee v op t /\
            ptr_val_ok cx (expr_type e) v op G tn t /\
            (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e op G t) /\
            ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                 value_has_type tv v)
            (ZIP (MAP FST ops, args)) vs)
        (\H res ee gt r. expr_exit res r)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qspecl_then [`DF`, `lo`, `d`, `PG`, `ctx`, `shadow_ctx`, `func`,
               `shadow_func`, `cenv`, `cx`, `st0`, `R`, `env`] mp_tac
    compile_log_eval_all_full_ind >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qspecl_then [`args`, `es`, `sa`, `sb`, `shadow_sa`,
                           `shadow_sb`, `ops`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule gas_outcome_full_post_mono >> disch_then irule >>
  simp[log_full_post_def]
QED
