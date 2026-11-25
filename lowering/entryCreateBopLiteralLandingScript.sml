(* The comparison reads the operands and ghosts of the selected list exit. *)
Theory entryCreateBopLiteralLanding
Ancestors
  entryCreateExprList exprSimBopInLiteralWord exprSimFullBundleProps
  exprSimPrecompiles exprSimWordArgs exprSimHypsDefs bodyFullHashKeccakFixed
  bodyFullIfExpReach bodyPtrDefs vyperStorageFootprint vyperStorageTrace
  fragGasPath fragGasOriginPtr loweringPosts vyperInterpreter vyperState
  venomState list

Theorem literal_zip_homogeneous[local]:
  LENGTH args = LENGTH values /\
  EVERY (\e. expr_type e = et) args /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  LIST_REL (\x ev. eval_operand x s = SOME
    (typed_val_to_w256 (THE (evaluate_type (get_tenv cx) (expr_type (FST ev))))
      (SND ev))) ops (ZIP (args,values)) ==>
  LIST_REL (\x v. eval_operand x s = SOME (typed_val_to_w256 tv v)) ops values
Proof
  simp[LIST_REL_EL_EQN, EVERY_EL, LENGTH_ZIP] >> strip_tac >>
  qx_gen_tac `i` >> strip_tac >>
  qpat_x_assum `!n. n < LENGTH ops ==> _` (qspec_then `i` mp_tac) >>
  simp[EL_ZIP]
QED

Theorem literal_landing_gas_obs[local]:
  (storage_well_formed_on cx (ee with gas_obs := gs) R <=>
   storage_well_formed_on cx ee R) /\
  (ghost_inv_at D lo d cenv cx (ee with gas_obs := gs) G tn s <=>
   ghost_inv_at D lo d cenv cx ee G tn s)
Proof
  conj_tac >- (irule storage_well_formed_on_backends >> simp[]) >>
  simp[ghost_inv_at_def]
QED

Theorem literal_member_args_landing:
  expr_body_pre cenv cx env
    (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems]) es /\
  (bop = In \/ bop = NotIn) /\ is_word_type (expr_type e1) /\
  lower_word_args cenv expr_type (e1::elems) sa = (needle::xs,sm) /\
  (!tail. eval_exprs cx (e1::elems)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (res,ee with gas_obs := tail)) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  EVERY (\x. op_prov G x = NONE) (needle::xs) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    create_word_args_post (DF,lo,d,ctx,func) cenv cx (es,sa,sm,s0,G0,tn0)
      (e1::elems) (needle::xs) H res ee G tn s /\
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (s0,G0,tn0) marks (OK s,G,tn)) ==>
  ?v vs tv. res = INL (v::vs) /\
    evaluate_type (get_tenv cx) (expr_type e1) = SOME tv /\
    value_has_type tv v /\ EVERY (value_has_type tv) vs /\
    LIST_REL (\x v. eval_operand x s = SOME (typed_val_to_w256 tv v)) xs vs /\
    eval_operand needle s = SOME (typed_val_to_w256 tv v) /\
    EVERY (\x. !p. x = Var p ==> not_fresh_at sm p) (needle::xs) /\
    op_prov G needle = NONE /\ op_taint tn needle = {} /\
    EVERY (\x. op_prov G x = NONE /\ op_taint tn x = {}) xs /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts /\
    sa.cs_next_var <= sm.cs_next_var /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func cenv cx (ee with gas_obs := []) s /\
      storage_well_formed_on cx (ee with gas_obs := []) (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx (ee with gas_obs := []) G tn s /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      wb_frame cenv es (ee with gas_obs := []) sa s0 s /\
      (~expr_has_effect e1 /\ EVERY ($~ o expr_has_effect) elems ==>
        pure_frame cenv func es sa s0 s))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all literal_body_typing >> strip_tac >>
  drule_all literal_body_evaluate_types >> strip_tac >>
  `wb_args_shape cenv expr_type (e1::elems)` by
    (drule_all literal_args_shape >> simp[]) >>
  drule_all lower_word_args_shape_ready >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
      ee.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `create_word_args_post _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE
      [create_word_args_post_def, typed_args_post_def, expr_sim_full_endpoint_def]) >>
  rename1 `res = INL values` >>
  qpat_x_assum `res = INL values` SUBST_ALL_TAC >>
  `expr_sim_inv cenv cx env
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    fs[expr_body_pre_def] >>
  qpat_assum `!tail. eval_exprs _ _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  `EVERY (value_has_type tv) values` by
    (`!e. MEM e (e1::elems) ==> MEM e (e1::elems)` by simp[] >>
     drule_all (Q.SPEC `e1::elems` literal_eval_exprs_typed) >> simp[]) >>
  `LIST_REL (\x v. eval_operand x s = SOME (typed_val_to_w256 tv v))
      (needle::xs) values` by
    (irule literal_zip_homogeneous >>
     qexistsl_tac [`e1::elems`,`cx`,`expr_type e1`] >>
     first_assum (irule_at Any) >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
  `~s.vs_halted` by
    (drule gas_origin_ptr_path_erase >> strip_tac >> drule gas_path_normal >> simp[]) >>
  reverse (Cases_on `values`) >-
    (rename1 `LIST_REL _ (needle::xs) (v::vs)` >>
     qexistsl_tac [`v`,`vs`,`tv`] >>
     qpat_x_assum `LIST_REL _ (needle::xs) (v::vs)`
       (strip_assume_tac o SIMP_RULE bool_ss [LIST_REL_def]) >>
     ntac 4 (qpat_x_assum `EVERY _ (_::_)`
       (strip_assume_tac o SIMP_RULE bool_ss [EVERY_DEF])) >>
     simp[] >>
     conj_tac
     >- (qpat_assum `EVERY (\x. _ /\ (!l. x <> Label l)) xs` mp_tac >>
         simp[NoAsms, EVERY_MEM] >> metis_tac[]) >>
     conj_tac
     >- (qpat_assum `EVERY (\x. op_prov G x = NONE) xs` mp_tac >>
         qpat_assum `EVERY (\x. op_taint tn x = {}) xs` mp_tac >>
         simp[NoAsms, EVERY_MEM] >> metis_tac[]) >>
     qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
       (drule_then strip_assume_tac) >>
     qpat_x_assum `create_word_args_post _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [create_word_args_post_def, typed_args_post_def]) >>
     simp[wb_frame_gas_obs, literal_landing_gas_obs] >>
     fs[NOT_EXISTS]) >>
  qpat_x_assum `LENGTH (e1::elems) = LENGTH []` mp_tac >> simp[]
QED
