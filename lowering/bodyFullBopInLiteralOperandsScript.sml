(* Joint word operands of literal membership, with one endpoint for all horizons. *)
Theory bodyFullBopInLiteralOperands
Ancestors
  bodyFullPreds bodySimFull exprSimBopInLiteralWord exprSimWordArgs
  gasOutcomeFullCompose gasOutcomeFull gasShadowCompileStmtHelpers
  bodyFullShared bodyMemoryDefs wordArgsPtr
  gasExemptCert gasSummaryCompose gasStorage vyperStorageTrace vyperStorageFootprint
  exprSimHyps exprSimHypsDefs exprSimProps exprLoweringProps freshWrites
  vyperInterpreter vyperState loweringPosts bodyPtrDefs fragGasOriginPtr
  fragExec list finite_map

Theorem bop_in_literal_operands_clean_full:
  !args DF lo d PG tops ctx shadow_ctx func shadow_func cenv cx env
   ann bop e1 a t n elems base tv st0 es sa xs sb shadow_sa s0 G0 tn0.
    expr_body_pre cenv cx env
      (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems]) base /\
    (bop = In \/ bop = NotIn) /\ is_word_type (expr_type e1) /\
    evaluate_type (get_tenv cx) (expr_type e1) = SOME tv /\
    (!e. MEM e args ==> MEM e (e1::elems)) /\
    body_exprs_full_ok cx args /\ body_inv tops ctx cenv cx /\
    expr_sim_inv cenv cx env es /\
    lower_word_args cenv expr_type args sa = (xs,sb) /\
    gas_shadow_state sa shadow_sa /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\
    MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code sa sb func /\
    (!shadow_xs shadow_sb.
       lower_word_args cenv expr_type (MAP gas_shadow_expr args) shadow_sa =
         (shadow_xs,shadow_sb) ==> fn_has_code shadow_sa shadow_sb shadow_func) /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es s0 /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome_full
      (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (eval_exprs cx args) (es,s0,G0,tn0)
      (\H res ee G tn u. ?vs. res = INL vs /\
        stmt_state_rel H ctx func cenv cx ee u /\
        storage_well_formed_on cx ee (FST H) /\
        EVERY (value_has_type tv) vs /\
        LIST_REL (\x v. eval_operand x u = SOME (typed_val_to_w256 tv v)) xs vs /\
        EVERY (\x. op_prov G x = NONE /\ op_taint tn x = {}) xs /\
        wb_frame cenv es ee sa s0 u /\
        (~EXISTS expr_has_effect args ==> pure_frame cenv func es sa s0 u) /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
        ghost_inv_at (DF H) lo d cenv cx ee G tn u /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
      (\H res ee gt r. expr_exit res r)
Proof
  Induct
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      qpat_x_assum `bop = In \/ bop = NotIn` kall_tac >>
      gvs[lower_word_args_nil] >>
      irule gas_outcome_full_pure >>
      conj_tac >- (qexistsl_tac [`G0`, `es`, `INL []`, `s0`, `tn0`] >>
      simp[eval_exprs_nil, return_def] >>
      rpt strip_tac >>
      simp[gas_origin_ptr_path_rules, wb_frame_refl, ghost_kept_at_refl] >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` drule >>
      simp[] >> strip_tac >>
      `storage_well_formed_on cx (es with gas_obs := []) (FST H) =
       storage_well_formed_on cx es (FST H)` by
        (irule storage_well_formed_on_backends >> simp[]) >>
      fs[ghost_inv_at_def] >> first_assum ACCEPT_TAC) >> simp[]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre cenv cx env h es` by
    (irule literal_body_operand_pre >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[listTheory.MEM]) >>
  `gas_admissible (bind (eval_expr cx h) (read_result cx)) expr_res_ok es` by
    (irule exprSimSourceTheory.expr_body_pre_gas_admissible >> metis_tac[]) >>
  qpat_x_assum `lower_word_args _ _ (h::args) _ = _`
    (strip_assume_tac o REWRITE_RULE [lower_word_args_cons]) >>
  `?shadow_s1. lower_value compile_expr cenv (expr_type h)
      (gas_shadow_expr h) shadow_sa = (x,shadow_s1) /\
      gas_shadow_state s1 shadow_s1` by
    (qspecl_then [`cenv`, `expr_type h`, `h`] mp_tac
       (Q.GENL [`cenv`, `ty`, `e`] gas_shadow_stmt_lower_value) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then drule >> simp[] >>
     Cases_on `lower_value compile_expr cenv (expr_type h) (gas_shadow_expr h) shadow_sa` >>
     gvs[]) >>
  `!e. MEM e (h::args) ==> expr_type e = expr_type e1` by
    (drule_all literal_body_typing >> strip_tac >>
     fs[EVERY_MEM] >> metis_tac[listTheory.MEM]) >>
  `is_word_type (expr_type h)` by metis_tac[listTheory.MEM] >>
  `cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var /\
   sa.cs_next_id <= s1.cs_next_id /\
   (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l)` by
    (irule exprSimSourceTheory.expr_body_pre_lower_value_word_shape >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  `!e. MEM e args ==> expr_body_pre cenv cx env e es` by
    (rpt strip_tac >> irule literal_body_operand_pre >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[listTheory.MEM]) >>
  `cs_extends s1 sb` by
    (irule (cj 1 lower_word_args_shape) >>
     goal_assum (drule_at Any) >> rpt gen_tac >> disch_tac >>
     irule exprSimSourceTheory.expr_body_pre_lower_value_word_shape >>
     metis_tac[listTheory.MEM]) >>
  `fn_has_code sa s1 func` by
    metis_tac[fn_has_code_mid, compileEnvTheory.cs_extends_refl] >>
  `!aa ss oo ff.
     lower_word_args cenv expr_type (MAP gas_shadow_expr aa) ss = (oo,ff) ==>
     cs_extends ss ff` by
    (Induct >> simp[lower_word_args_nil, compileEnvTheory.cs_extends_refl] >>
     rpt gen_tac >> simp[lower_word_args_cons] >> rpt strip_tac >>
     metis_tac[cj 2 compile_expr_grows, compileEnvTheory.cs_extends_trans]) >>
  Cases_on `lower_word_args cenv expr_type (MAP gas_shadow_expr args) shadow_s1` >>
  rename1 `lower_word_args _ _ (MAP gas_shadow_expr args) shadow_s1 = (shadow_ys,shadow_sb)` >>
  `fn_has_code shadow_sa shadow_sb shadow_func` by
    (qpat_x_assum `!xx ss. lower_word_args _ _ _ shadow_sa = _ ==> _` irule >>
     simp[lower_word_args_cons] >>
     qexistsl_tac [`x`, `shadow_s1`, `shadow_ys`] >> fs[]) >>
  `fn_has_code shadow_sa shadow_s1 shadow_func` by
    metis_tac[fn_has_code_mid, compileEnvTheory.cs_extends_refl,
              cj 2 compile_expr_grows] >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type h) h es` by
    (qpat_x_assum `body_exprs_full_ok _ (_::_)` mp_tac >>
     simp[Once body_exprs_full_ok_def] >> strip_tac >>
     qpat_x_assum `body_expr_full_ok _ h` mp_tac >>
     simp[Once body_expr_full_ok_def] >> metis_tac[]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ h _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`, `sa`, `s1`, `shadow_sa`, `shadow_s1`,
                           `x`, `s0`, `G0`, `tn0`] mp_tac) >>
  impl_tac
  >- (asm_rewrite_tac[] >> rpt strip_tac >>
      drule contextRawReachableTheory.frag_reachable_members >>
      disch_then drule >> strip_tac >>
      fs[unitMemInvTheory.dalloca_no_wrap_def,
         ptrDisciplineTheory.ctx_has_dalloca_def, EXISTS_MEM] >>
      metis_tac[]) >>
  disch_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ HeadPost _` >>
  rewrite_tac[eval_exprs_cons_action] >>
  irule gas_outcome_full_bind_all >> BETA_TAC >>
  conj_tac >- (gen_tac >> irule storage_trace_frame_bind_all >>
    simp[evaluate_storage_trace_frame, storage_trace_frame_return]) >>
  conj_tac >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> metis_tac[]) >>
  conj_tac >- (irule storage_trace_frame_bind_all >>
    simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  qexists_tac `\H res ee G tn u. HeadPost H res ee G tn u /\
       ~u.vs_halted /\ ee.gas_obs = []` >> reverse conj_tac
  >- (irule gas_outcome_full_post_source >>
      goal_assum (drule_at Any) >> BETA_TAC >>
      conj_tac >- simp[] >>
      rpt gen_tac >> strip_tac >> Cases_on `res` >>
      qpat_x_assum `expr_exit _ _` mp_tac >>
      simp[exprSimDefsTheory.expr_exit_INL,
           stmtSimPropsTheory.expr_exit_INR_type]) >>
  map_every qx_gen_tac [`marks`, `res`, `mid`, `G1`, `tn1`, `t1`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
      mid.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  strip_tac >> qunabbrev_tac `HeadPost` >>
  RULE_ASSUM_TAC BETA_RULE >>
  qpat_x_assum `(?v. _) /\ _` strip_assume_tac >>
  disj1_tac >> qexists_tac `v` >> asm_rewrite_tac[] >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >>
  `bind (eval_expr cx h) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,mid)` by
    (`mid with gas_obs := [] = mid` by
       simp[evaluation_state_component_equality] >>
     qpat_assum `!tail. bind _ _ _ = _`
       (qspec_then `[]` mp_tac) >>
     pure_rewrite_tac[APPEND_NIL] >>
     qpat_x_assum `mid with gas_obs := [] = mid`
       (fn th => rewrite_tac[th])) >>
  `expr_sim_inv cenv cx env mid /\ value_has_type tv v` by
    (`expr_body_pre cenv cx env h
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
     drule_at (Pat `bind _ _ _ = _`)
       (CONV_RULE (DEPTH_CONV ETA_CONV)
          exprSimOperatorsTheory.expr_body_pre_word_type_result) >>
     disch_then (qspecl_then [`cenv`, `env`] mp_tac) >>
     impl_tac >- asm_rewrite_tac[] >>
     strip_tac >> conj_tac >- asm_rewrite_tac[] >>
     first_x_assum (qspec_then `v` mp_tac) >>
     simp[] >> metis_tac[optionTheory.SOME_11]) >>
  `body_exprs_full_ok cx args` by
    (qpat_x_assum `body_exprs_full_ok _ (_::_)` mp_tac >>
     simp[Once body_exprs_full_ok_def] >> strip_tac >>
     first_x_assum irule >>
     qpat_x_assum `bind _ _ _ = (INL v,mid)` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  `gas_outcome_full
      (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (eval_exprs cx args) (mid,t1,G1,tn1)
      (\H res ee G tn u. ?vs. res = INL vs /\
        stmt_state_rel H ctx func cenv cx ee u /\
        storage_well_formed_on cx ee (FST H) /\
        EVERY (value_has_type tv) vs /\
        LIST_REL (\x v. eval_operand x u = SOME (typed_val_to_w256 tv v)) ys vs /\
        EVERY (\x. op_prov G x = NONE /\ op_taint tn x = {}) ys /\
        wb_frame cenv mid ee s1 t1 u /\
        (~EXISTS expr_has_effect args ==> pure_frame cenv func mid s1 t1 u) /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func u /\ t1.vs_alloca_next <= u.vs_alloca_next /\
        ghost_inv_at (DF H) lo d cenv cx ee G tn u /\
        ghost_kept_at lo cenv mid s1 G1 tn1 t1 G tn)
      (\H res ee gt r. expr_exit res r)` by
    (qpat_x_assum `!DF lo d PG tops ctx shadow_ctx func shadow_func cenv cx env ann bop e1 a t n elems base tv st0 es sa xs sb shadow_sa s0 G0 tn0. _` irule >>
     asm_rewrite_tac[] >>
     conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     conj_tac >- (rpt strip_tac >>
       qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _` drule >>
       simp[] >> metis_tac[expr_post_def]) >>
     conj_tac >-
       (qexistsl_tac [`shadow_func`, `shadow_s1`] >> asm_rewrite_tac[] >>
        rpt strip_tac >>
        `shadow_sb' = shadow_sb` by metis_tac[pairTheory.PAIR_EQ] >>
        metis_tac[fn_has_code_mid, compileEnvTheory.cs_extends_refl,
                  cj 2 compile_expr_grows]) >>
     conj_tac >- metis_tac[local_ptrs_reserved_next_var] >>
     conj_tac >- metis_tac[fn_has_code_mid, compileEnvTheory.cs_extends_refl] >>
     conj_tac >- metis_tac[] >>
     conj_tac >-
       (irule return_buf_frame_frame >> goal_assum (drule_at Any) >>
        simp[] >> metis_tac[expr_post_def]) >>
     goal_assum (drule_at Any) >>
     metis_tac[listTheory.MEM]) >>
  irule gas_outcome_full_post_source >>
  irule_at Any (INST_TYPE [alpha |-> ``:value list``, beta |-> ``:value list``]
    gas_outcome_full_source_map) >>
  qexistsl_tac [`eval_exprs cx args`,
                `\r. case r of INL vs => INL (v::vs) | INR ex => INR ex`] >>
  goal_assum (drule_at Any) >> BETA_TAC >>
  conj_tac >-
    (gen_tac >> Cases_on `eval_exprs cx args es'` >>
     rename1 `eval_exprs cx args es' = (rr,ss)` >>
     Cases_on `rr` >> simp[bind_def, return_def]) >>
  simp [] >>
  reverse conj_tac
  >- (rpt gen_tac >> strip_tac >> Cases_on `res'` >>
      gvs[exprSimDefsTheory.expr_exit_INL]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `res' = INL _` SUBST_ALL_TAC >>
  qpat_x_assum `res = _` (SUBST_ALL_TAC o SRULE []) >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (qpat_assum `!tail. bind (eval_exprs _ _) _ _ = _`
       (qspec_then `[]` assume_tac) >>
     drule_at (Pat `f st = _`) valid_horizon_frame >>
     simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
          storage_trace_frame_return]) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (drule_at (Pat `f st = _`) valid_horizon_frame >>
     simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
          storage_trace_frame_read_result]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `H` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (strip_assume_tac o SRULE []) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (qspec_then `H` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (drule (CONV_RULE (DEPTH_CONV ETA_CONV)
       exprBopSimPropsTheory.bop_value_scopes_dom) >> simp[]) >>
  `evaluate_type (get_tenv cx) (expr_type h) = SOME tv` by
    metis_tac[listTheory.MEM] >>
  `stmt_state_rel H ctx func cenv cx ee t' /\
   LIST_REL (\x v. eval_operand x t' = SOME (typed_val_to_w256 tv v))
     (x::ys) (v::vs) /\ wb_frame cenv es ee sa s0 t'` by
    (drule_all literal_word_post_cons >> simp[]) >>
  qpat_x_assum `LIST_REL _ (_::_) (_::_)`
    (strip_assume_tac o SRULE []) >>
  `op_prov G1 x = NONE /\ op_taint tn1 x = {}` by
    fs[ptr_val_ok_def] >>
  `op_prov G' x = NONE /\ op_taint tn' x = {}` by
    (Cases_on `x` >> simp[ptrDisciplineTheory.op_prov_def,
                           ptrDisciplineTheory.op_taint_def] >>
     qpat_x_assum `ghost_kept_at lo cenv mid s1 G1 tn1 t1 G' tn'`
       (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
     first_x_assum (drule_then strip_assume_tac) >>
     fs[ptrDisciplineTheory.op_prov_def, ptrDisciplineTheory.op_taint_def]) >>
  simp[] >>
  conj_tac >-
    (strip_tac >> irule pure_frame_trans >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`mid`, `s1`, `t1`] >>
     qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
     qpat_assum `wb_frame cenv mid ee s1 t1 t'`
       (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
     simp[]) >>
  irule (INST_TYPE [beta |-> ``:256``] ghost_kept_at_wb_trans) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qexistsl_tac [`H`, `ctx`, `cx`, `func`] >>
               first_assum ACCEPT_TAC) >>
  qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  qexistsl_tac [`G1`, `mid`, `mid`, `t1`, `s1`, `tn1`] >>
  simp[wb_frame_def] >> first_assum ACCEPT_TAC
QED

Theorem bop_in_literal_operands_full:
  !args DF lo d PG tops ctx shadow_ctx func shadow_func cenv cx env
   ann bop e1 a t n elems base tv st0 es sa xs sb shadow_sa s0 G0 tn0.
    expr_body_pre cenv cx env
      (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems]) base /\
    (bop = In \/ bop = NotIn) /\ is_word_type (expr_type e1) /\
    evaluate_type (get_tenv cx) (expr_type e1) = SOME tv /\
    (!e. MEM e args ==> MEM e (e1::elems)) /\
    body_exprs_full_ok cx args /\ body_inv tops ctx cenv cx /\
    expr_sim_inv cenv cx env es /\
    lower_word_args cenv expr_type args sa = (xs,sb) /\
    gas_shadow_state sa shadow_sa /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\
    MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code sa sb func /\
    (!shadow_xs shadow_sb.
       lower_word_args cenv expr_type (MAP gas_shadow_expr args) shadow_sa =
         (shadow_xs,shadow_sb) ==> fn_has_code shadow_sa shadow_sb shadow_func) /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es s0 /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome_full
      (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (eval_exprs cx args) (es,s0,G0,tn0)
      (\H res ee G tn u. ?vs. res = INL vs /\
        stmt_state_rel H ctx func cenv cx ee u /\
        storage_well_formed_on cx ee (FST H) /\
        EVERY (value_has_type tv) vs /\
        LIST_REL (\x v. eval_operand x u = SOME (typed_val_to_w256 tv v)) xs vs /\
        wb_frame cenv es ee sa s0 u /\
        (~EXISTS expr_has_effect args ==> pure_frame cenv func es sa s0 u) /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
        ghost_inv_at (DF H) lo d cenv cx ee G tn u /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
      (\H res ee gt r. expr_exit res r)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all bop_in_literal_operands_clean_full >>
  disch_then (qspec_then `PG` assume_tac) >>
  irule gas_outcome_full_post_mono >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
