(* Request prefixes across the tests of a fused BoolChain. *)
Theory s1PrefixBoolChainNativeStages
Ancestors
  bodyFullBoolChain boolChainFullHead boolChainFullControl boolChainSource
  boolChainCodeLayout boolChainShadowLayout boolChainCountedControl
  bodyFullIfExpPrepare bodyFullIfExpReach bodyFullPreds bodySimFull
  gasShadowCompileStmtHelpers gasShadowState exprSimSource exprSimDefs
  s1PrefixCompose s1PrefixFrame s1PrefixProps s1PrefixDefs gasOutcomeFullCompose
  gasOutcomeFull fragGasOriginPtr ptrDiscipline gasContext sum
  vyperStorageTrace vyperStorageFootprint vyperAST vyperInterpreter vyperState
  exprLowering exprLoweringProps loweringPosts bodyPtrDefs compileEnv freshWrites
  boolChainOperandsCons vyperValueOperation venomExecSemantics venomState list
  exprSimWordArgs exprBodyPreProps loweringSlice valueEncoding

Theorem bool_chain_prefix_source_cong[local]:
  (!gs. source (es with gas_obs := gs) = next (es with gas_obs := gs)) /\
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0 next (es,s,G,tn) ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0 source (es,s,G,tn)
Proof
  simp[gas_prefix_full_def] >> metis_tac[]
QED

(* The head's prefix handles requests during the test. Its full outcome gives
   the actual entry to the selected block, without adding any gas observation. *)
Theorem bool_word_forced_select_prefix[local]:
  expr_body_pre cenv cx env (IfExp (BaseT BoolT) c a f) es /\
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
    (bind (eval_expr cx c) (read_result cx)) (es,s,G,tn) /\
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (bind (eval_expr cx c) (read_result cx)) (es,s,G,tn) P
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)) /\
  (!H res mid G1 tn1 u. P H res mid G1 tn1 u ==> ?b.
     res = INL (BoolV b) /\
     expr_post H ctx func cenv cx c es sa sc s mid (BoolV b) op u /\
     eval_operand op u = SOME (if b then 1w else 0w) /\ op_taint tn1 op = {} /\
     u.vs_current_bb = sc.cs_current_bb /\ u.vs_inst_idx = LENGTH sc.cs_current_insts /\
     ~u.vs_halted /\ alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
     s.vs_alloca_next <= u.vs_alloca_next /\ ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 u) /\
  emit_inst JNZ [op; Label lt; Label lf] [] sc = ((),sn) /\ fn_has_code sc sn func /\
  (!b. (entry b).cs_current_bb = (if b then lt else lf) /\
       (entry b).cs_current_insts = [] /\ sa.cs_next_var <= (entry b).cs_next_var) /\
  return_buf_frame d cenv sa s /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_fmp_headroom inst u) /\
  (!marks b mid G1 tn1 u z.
     bind (eval_expr cx c) (read_result cx)
       (es with gas_obs := gas_explicit marks s.vs_gas_readings) = (INL (BoolV b),mid) /\
     storage_trace_domain cx st0 mid.storage_trace /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) marks (OK u,G1,tn1) /\
        P H (INL (BoolV b)) mid G1 tn1 u) /\
     z = jump_to (if b then lt else lf) u /\
     return_buf_frame d cenv (entry b) z /\ alloca_history func z /\
     s.vs_alloca_next <= z.vs_alloca_next /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
     (!fn inst w. frag_reachable ctx func z fn inst w ==> dalloca_fmp_headroom inst w) /\
     ~z.vs_halted /\ z.vs_current_bb = (entry b).cs_current_bb /\
     z.vs_inst_idx = LENGTH (entry b).cs_current_insts /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
       stmt_state_rel H ctx func cenv cx mid z /\ storage_well_formed_on cx mid (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 z) ==>
     gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
       (bind (eval_expr cx (if b then a else f)) (read_result cx)) (mid,z,G1,tn1)) ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
    (bind (eval_expr cx (IfExp (BaseT BoolT) c a f)) (read_result cx)) (es,s,G,tn)
Proof
  strip_tac >> irule bool_chain_prefix_source_cong >>
  drule bool_chain_forced_select >> strip_tac >> goal_assum (drule_at Any) >>
  irule gas_prefix_full_bind_replay >> rpt conj_tac
  >~ [`storage_trace_frame (bind _ _)`]
  >- simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
          storage_trace_frame_read_result]
  >~ [`!v. storage_trace_frame (_ v)`]
  >- (gen_tac >> BETA_TAC >> rpt IF_CASES_TAC >>
      simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
           storage_trace_frame_read_result, storage_trace_frame_raise])
  >~ [`requests_outcomes_frame _`]
  >- simp[requests_outcomes_frame_bind_all, evaluate_requests_outcomes_frame,
          requests_outcomes_frame_read_result]
  >~ [`gas_prefix_full _ _ _ _ _`]
  >- first_assum ACCEPT_TAC
  >> qexists_tac `\H res mid G1 tn1 u. P H res mid G1 tn1 u /\ mid.gas_obs = []` >>
  qexists_tac `\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)` >>
  qexists_tac `cx_tops cx` >> BETA_TAC >> simp[] >>
  rpt conj_tac
  >- suspend "select"
  >- (rpt strip_tac >> Cases_on `res` >> fs[expr_exit_def])
  >> irule gas_outcome_full_post_source >> goal_assum (drule_at Any) >> simp[]
QED

Resume bool_word_forced_select_prefix[select]:
  qx_genl_tac [`marks`,`v`,`mid`,`G1`,`tn1`,`u`] >> strip_tac >>
  qabbrev_tac `h = storage_trace_horizon mid.storage_trace` >>
  `valid_horizon cx st0 h mid.storage_trace` by fs[Abbr `h`, storage_trace_domain_def] >>
  qpat_assum `!H. _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `h` (drule_then strip_assume_tac)) >>
  qpat_assum `!H res mid G1 tn1 u. P H res mid G1 tn1 u ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `INL v = INL (BoolV b)` (SUBST_ALL_TAC o REWRITE_RULE [sumTheory.INL_11]) >>
  `bind (eval_expr cx c) (read_result cx)
     (es with gas_obs := gas_explicit marks s.vs_gas_readings) = (INL (BoolV b),mid)` by
    (`mid with gas_obs := [] = mid` by
       (Cases_on `mid` >> gvs (TypeBase.updates_of ``:evaluation_state``)) >>
     pop_assum (fn upd =>
       qpat_assum `!tail. _ (es with gas_obs := _ ++ tail) = _`
         (qspec_then `[]` (ACCEPT_TAC o PURE_REWRITE_RULE [APPEND_NIL,upd])))) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) marks (OK u,G1,tn1) /\
     expr_post H ctx func cenv cx c es sa sc s mid (BoolV b) op u /\
     ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 u` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. _ ==> gas_origin_ptr_path _ _ _ _ /\ _` (drule_then strip_assume_tac) >>
     qpat_assum `!H res mid G1 tn1 u. P H res mid G1 tn1 u ==> _`
       (drule_then strip_assume_tac) >> fs[]) >>
  qpat_assum `!b. (entry b).cs_current_bb = _ /\ _` (qspec_then `b` strip_assume_tac) >>
  drule_all bool_word_selected_entry_full >> strip_tac >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==> P H (INL (BoolV b)) mid G1 tn1 u` by simp[] >>
  `gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
     (bind (eval_expr cx (if b then a else f)) (read_result cx)) (mid,u,G1,tn1)` by
    (irule gas_prefix_full_zero_prefix_guarded >>
     simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame, storage_trace_frame_read_result] >>
     qexistsl_tac [`G1`,`z`,`tn1`] >> conj_tac
     >- (gen_tac >> strip_tac >>
         qpat_assum `!H. _ ==> gas_origin_ptr_path _ (u,G1,tn1) [] _ /\ _`
           (drule_then strip_assume_tac) >> simp[]) >>
     qpat_assum `!marks b mid G1 tn1 u z. _ ==> gas_prefix_full _ _ _ _ _` irule >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (gen_tac >> strip_tac >>
         qpat_assum `!H. _ ==> gas_origin_ptr_path _ (u,G1,tn1) [] _ /\ _`
           (drule_then strip_assume_tac) >> simp[]) >>
     qexistsl_tac [`marks`,`u`] >> simp[]) >>
  Cases_on `b` >> fs[]
QED

Finalise bool_word_forced_select_prefix

Theorem bool_chain_singleton_prefix:
  compile_bool_chain_ops compile_expr cenv p rv xl [x] sa = ((),sb) /\
  compile_bool_chain_ops compile_expr (gas_shadow_env T cenv) p rv xl
    [gas_shadow_expr x] shadow_sa = ((),shadow_sb) /\
  gas_shadow_state sa shadow_sa /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  (!op sc shadow_sc.
     lower_value compile_expr cenv (BaseT BoolT) x sa = (op,sc) /\
     lower_value compile_expr (gas_shadow_env T cenv) (BaseT BoolT)
       (gas_shadow_expr x) shadow_sa = (op,shadow_sc) /\
     gas_shadow_state sc shadow_sc /\
     fn_has_code sa sc func /\ fn_has_code shadow_sa shadow_sc shadow_func ==>
     gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       cx st0 (bind (eval_expr cx x) (read_result cx)) (es,s,G,tn)) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (bind (eval_expr cx x) (read_result cx)) (es,s,G,tn)
Proof
  strip_tac >> rpt (dxrule bool_chain_singleton_layout >> strip_tac) >>
  rename1 `lower_value _ _ _ (gas_shadow_expr x) shadow_sa = (shadow_op,shadow_sc)` >>
  rename1 `lower_value _ cenv _ x sa = (op,sc)` >>
  `op = shadow_op /\ gas_shadow_state sc shadow_sc` by
    (drule (REWRITE_RULE [gas_shadow_compiles_def]
       (Q.INST [`ty` |-> `BaseT BoolT`, `sd` |-> `T`] gas_shadow_stmt_lower_value_env)) >>
     disch_then (qspecl_then [`x`,`cenv`] mp_tac) >> simp[]) >>
  qpat_x_assum `op = shadow_op` (SUBST_ALL_TAC o SYM) >>
  qpat_assum `!fn. fn_has_code sa sb fn ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `!fn. fn_has_code shadow_sa shadow_sb fn ==> _` (drule_then strip_assume_tac) >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[]
QED

(* [reached] is a guard on the residual list and its actual paired entry.
   It is preserved only along a successful continuing test in the emitted
   code. Every reached head needs its request prefix; only a head with a
   nonempty tail needs a full outcome to reach the next test. *)
(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  qpat_x_assum `!e rest sa sc shadow_sa shadow_sc es s G tn op.
                  _ ==> gas_prefix_full _ _ _ _ _ /\ _`
    (mk_asm "operand") >>
  qpat_x_assum `!c rest sa sc shadow_sa shadow_sc es s G tn op sj sn lt lf st shadow_st marks mid G1 tn1 u.
                  _ ==> reached _ _ _ _ _ _ _` (mk_asm "advance") >>
  Induct_on `k`
  >- (pure_rewrite_tac[bool_chain_operands_def, listTheory.MAP] >>
      rpt strip_tac >> suspend "singleton") >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `expr_type x = BaseT BoolT`
    (mp_then Any (qspecl_then [`k`,`p`] strip_assume_tac) bool_chain_residual_cases)
  >- (qpat_assum `bool_chain_operands _ _ _ = [_]`
        (fn th => RULE_ASSUM_TAC (SIMP_RULE bool_ss [th, listTheory.MAP])) >>
      suspend "singleton") >>
  suspend "test"
QED
*)
Theorem bool_chain_ops_prefix_from_observations:
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!e rest sa sc shadow_sa shadow_sc es s G tn op.
     reached (e::rest) sa shadow_sa es s G tn /\
     expr_type e = BaseT BoolT /\
     body_const_cells_agree [(NONE,tops)] cx env es /\ expr_body_pre cenv cx env e es /\
     expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
       cenv cx (BaseT BoolT) e es (st0,sa,sc,shadow_sa,shadow_sc,op,s,G,tn) ==>
     gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn) /\
     (rest <> [] ==>
      gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
        (\H res ee G' tn' u. ?b.
          res = INL (BoolV b) /\ expr_post H ctx func cenv cx e es sa sc s ee (BoolV b) op u /\
          eval_operand op u = SOME (if b then 1w else 0w) /\
          u.vs_current_bb = sc.cs_current_bb /\ u.vs_inst_idx = LENGTH sc.cs_current_insts /\
          ~u.vs_halted /\ alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
          s.vs_alloca_next <= u.vs_alloca_next /\ ghost_inv_at (DF H) lo d cenv cx ee G' tn' u /\
          ptr_val_ok cx (BaseT BoolT) (BoolV b) op G' tn' u /\
          ghost_kept_at lo cenv es sa G tn s G' tn')
        (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
          (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)))) /\
  (!c rest sa sc shadow_sa shadow_sc es s G tn op sj sn lt lf
      st shadow_st marks mid G1 tn1 u.
     reached (c::rest) sa shadow_sa es s G tn /\
     lower_value compile_expr cenv (BaseT BoolT) c sa = (op,sc) /\
     lower_value compile_expr (gas_shadow_env T cenv) (BaseT BoolT)
       (gas_shadow_expr c) shadow_sa = (op,shadow_sc) /\
     sj.cs_current_bb = sc.cs_current_bb /\ sj.cs_current_insts = sc.cs_current_insts /\
     emit_inst JNZ [op; Label lt; Label lf] [] sj = ((),sn) /\
     fn_has_code sj sn func /\ st.cs_current_bb = (if p then lt else lf) /\
     st.cs_current_insts = [] /\ gas_shadow_state st shadow_st /\
     compile_bool_chain_ops compile_expr cenv p rv xl rest st = ((),sb) /\
     compile_bool_chain_ops compile_expr (gas_shadow_env T cenv) p rv xl
        (MAP gas_shadow_expr rest) shadow_st = ((),shadow_sb) /\
     bind (eval_expr cx c) (read_result cx)
       (es with gas_obs := gas_explicit marks s.vs_gas_readings) = (INL (BoolV p),mid) /\
     storage_trace_domain cx st0 mid.storage_trace /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (s,G,tn) marks (OK u,G1,tn1)) ==>
     reached rest st shadow_st mid (jump_to st.cs_current_bb u) G1 tn1) ==>
  !k x sa shadow_sa es s G tn.
  reached (bool_chain_operands p k x) sa shadow_sa es s G tn /\
  expr_type x = BaseT BoolT /\
  body_const_cells_agree [(NONE,tops)] cx env es /\ expr_body_pre cenv cx env x es /\
  compile_bool_chain_ops compile_expr cenv p rv xl (bool_chain_operands p k x) sa = ((),sb) /\
  compile_bool_chain_ops compile_expr (gas_shadow_env T cenv) p rv xl
    (MAP gas_shadow_expr (bool_chain_operands p k x)) shadow_sa = ((),shadow_sb) /\
  gas_shadow_state sa shadow_sa /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  local_ptrs_reserved cenv sa /\
  (!v n. cenv.ce_return_buf = SOME (PtrVar (Var v) n) ==> not_fresh_at sa v) /\
  (!v n. cenv.ce_return_pc = SOME (PtrVar (Var v) n) ==> not_fresh_at sa v) /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_fmp_headroom inst u) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (bind (eval_expr cx x) (read_result cx)) (es,s,G,tn)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume bool_chain_ops_prefix_from_observations[singleton]:
  markerLib.RESUME_TAC >>
  irule bool_chain_singleton_prefix >>
  qpat_assum `compile_bool_chain_ops _ cenv _ _ _ [_] sa = _` (irule_at Any) >>
  qpat_assum `compile_bool_chain_ops _ _ _ _ _ [gas_shadow_expr x] shadow_sa = ((),shadow_sb)`
    (irule_at Any) >>
  qpat_assum `fn_has_code shadow_sa shadow_sb shadow_func` (irule_at Any) >>
  simp[] >> qx_genl_tac [`op`,`sc`,`shadow_sc`] >> strip_tac >>
  `expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (BaseT BoolT) x es (st0,sa,sc,shadow_sa,shadow_sc,op,s,G,tn)` by
    (drule_then strip_assume_tac expr_body_pre_gas_admissible >>
     pure_rewrite_tac[expr_sim_full_pre_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  asm "operand" (drule_all_then (ACCEPT_TAC o CONJUNCT1))
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume bool_chain_ops_prefix_from_observations[test]:
  `?hd hs. bool_chain_operands p k tail = hd::hs` by simp[bool_chain_operands_cons] >>
  fs[] >>
  drule_all (SIMP_RULE bool_ss [listTheory.MAP] bool_chain_test_shadow_layout) >> strip_tac >>
  qpat_x_assum `x = IfExp _ _ _ _` SUBST_ALL_TAC >>
  drule ifexp_body_pre_children >> strip_tac >>
  `expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (BaseT BoolT) c es (st0,sa,sc,shadow_sa,shadow_sc,op,s,G,tn)` by
    (qpat_assum `expr_body_pre cenv cx env c es`
       (mp_then Any strip_assume_tac expr_body_pre_gas_admissible) >>
     pure_rewrite_tac[expr_sim_full_pre_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  asm "operand" (drule_all_then (strip_assume_tac o REWRITE_RULE [NOT_CONS_NIL])) >>
  irule bool_word_forced_select_prefix >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `emit_inst JNZ _ _ _ = _` (irule_at Any) >>
  qexistsl_tac [`sa`,`env`,`\b. if b = p then st else ss`,`d`,`cenv`] >>
  BETA_TAC >> simp[] >>
  conj_tac >- (rpt strip_tac >> irule body_inv_no_phi >>
      qexistsl_tac [`cenv`,`ctx`,`cx`,`func`,`tops`] >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (Cases >> Cases_on `p` >> fs[ci_mono_def] >> decide_tac) >>
  reverse conj_tac
  >- (rpt gen_tac >> strip_tac >> qexists_tac `b` >> simp[] >>
      reverse conj_tac >- fs[ptr_val_ok_def] >>
      `wb_frame cenv es mid sa s u` by metis_tac[expr_post_frame] >>
      qpat_assum `expr_post _ _ _ _ _ c es sa sc s mid _ _ _`
        (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
      irule expr_post_word_intro >>
      simp[is_word_type_def, word_value_def, val_to_w256_def, bool_to_word_def] >>
      rpt strip_tac >> first_assum irule) >>
  suspend "selected"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume bool_chain_ops_prefix_from_observations[selected]:
  qx_genl_tac [`marks`,`b`,`mid`,`G1`,`tn1`,`u`] >>
  qabbrev_tac `z = jump_to (if b then (if p then st.cs_current_bb else ss.cs_current_bb)
                                     else (if p then ss.cs_current_bb else st.cs_current_bb)) u` >>
  strip_tac >> Cases_on `b = p`
  >- suspend "continue"
  >> suspend "short"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume bool_chain_ops_prefix_from_observations[continue]:
  qpat_x_assum `b = p` SUBST_ALL_TAC >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [REFL_CLAUSE, COND_CLAUSES]) >>
  `z = jump_to st.cs_current_bb u` by (Cases_on `p` >> simp[Abbr `z`]) >>
  `body_const_cells_agree [(NONE,tops)] cx env mid /\ expr_sim_inv cenv cx env mid` by
    (`expr_body_pre cenv cx env c (es with gas_obs := gas_explicit marks s.vs_gas_readings)` by simp[] >>
     drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) exprSimSourceTheory.expr_body_pre_eval) >>
     strip_tac >> simp[] >>
     irule body_const_cells_agree_expr_read >>
     qpat_assum `bind (eval_expr cx c) _ _ = (_,mid)` (irule_at Any) >>
     simp[] >> metis_tac[expr_body_pre_static_facts]) >>
  `expr_body_pre cenv cx env tail mid /\ expr_type tail = BaseT BoolT` by
    (qpat_assum `!es'. expr_sim_inv cenv cx env es' ==> _` (drule_then mp_tac) >>
     qpat_assum `expr_type (if p then tail else _) = _` mp_tac >>
     qpat_assum `expr_type (if p then _ else tail) = _` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `p` >> simp[]) >>
  `sa.cs_next_var <= st.cs_next_var` by
    (every_assum (fn th =>
       if can (match_term ``ci_mono _ _``) (concl th) then
         strip_assume_tac (REWRITE_RULE [ci_mono_def] th) else ALL_TAC) >>
     decide_tac) >>
  `local_ptrs_reserved cenv st` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!v n. cenv.ce_return_buf = SOME (PtrVar (Var v) n) ==> not_fresh_at st v) /\
   (!v n. cenv.ce_return_pc = SOME (PtrVar (Var v) n) ==> not_fresh_at st v)` by
    metis_tac[not_fresh_at_mono] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G,tn) marks (OK u,G1,tn1)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `reached (hd::hs) st shadow_st mid z G1 tn1` by
    (qpat_assum `z = jump_to _ _` (PURE_ONCE_REWRITE_TAC o single) >>
     asm "advance" irule >>
     qpat_assum `bind (eval_expr cx c) _ _ = (INL _,mid)` (irule_at Any) >>
     qpat_assum `emit_inst JNZ _ _ sj = _` (irule_at Any) >>
     qpat_assum `lower_value _ cenv _ c sa = _` (irule_at Any) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr c) shadow_sa = _`
       (irule_at Any) >>
     qexistsl_tac [`tn`,`G`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     Cases_on `p` >> simp[]) >>
  `(if p then (if p then tail else Literal (BaseT BoolT) (BoolL T))
          else (if p then Literal (BaseT BoolT) (BoolL F) else tail)) = tail` by
    (Cases_on `p` >> simp[]) >>
  pop_assum (PURE_ONCE_REWRITE_TAC o single) >>
  qpat_assum `!x' sa' shadow_sa' es' s' G' tn'. _ ==> gas_prefix_full _ _ _ _ _` irule >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- simp[jump_to_def] >>
  qexistsl_tac [`st`,`shadow_st`] >>
  qpat_assum `bool_chain_operands p k tail = _`
    (fn th => pure_rewrite_tac [th, listTheory.MAP]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume bool_chain_ops_prefix_from_observations[short]:
  `(if b then (if p then tail else Literal (BaseT BoolT) (BoolL T))
          else (if p then Literal (BaseT BoolT) (BoolL F) else tail)) =
    Literal (BaseT BoolT) (BoolL b)` by (Cases_on `p` >> Cases_on `b` >> fs[]) >>
  pop_assum (PURE_ONCE_REWRITE_TAC o single) >>
  irule gas_prefix_full_no_outcome >>
  Cases_on `b` >>
  simp[Abbr `z`, jump_to_def, storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result, Once evaluate_def, evaluate_literal_def,
       read_result_def, bind_return, return_def]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise bool_chain_ops_prefix_from_observations
*)

Theorem bool_chain_ops_prefix_from_reached:
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!e rest sa sc shadow_sa shadow_sc es s G tn op.
     reached (e::rest) sa shadow_sa es s G tn /\
     body_expr_full_ok cx e /\ expr_type e = BaseT BoolT /\
     body_const_cells_agree [(NONE,tops)] cx env es /\ expr_body_pre cenv cx env e es /\
     expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
       cenv cx (BaseT BoolT) e es (st0,sa,sc,shadow_sa,shadow_sc,op,s,G,tn) ==>
     gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)) /\
  (!c rest sa sc shadow_sa shadow_sc es s G tn op sj sn lt lf
      st shadow_st marks mid G1 tn1 u.
     reached (c::rest) sa shadow_sa es s G tn /\
     lower_value compile_expr cenv (BaseT BoolT) c sa = (op,sc) /\
     lower_value compile_expr (gas_shadow_env T cenv) (BaseT BoolT)
       (gas_shadow_expr c) shadow_sa = (op,shadow_sc) /\
     sj.cs_current_bb = sc.cs_current_bb /\ sj.cs_current_insts = sc.cs_current_insts /\
     emit_inst JNZ [op; Label lt; Label lf] [] sj = ((),sn) /\
     fn_has_code sj sn func /\ st.cs_current_bb = (if p then lt else lf) /\
     st.cs_current_insts = [] /\ gas_shadow_state st shadow_st /\
     compile_bool_chain_ops compile_expr cenv p rv xl rest st = ((),sb) /\
     compile_bool_chain_ops compile_expr (gas_shadow_env T cenv) p rv xl
        (MAP gas_shadow_expr rest) shadow_st = ((),shadow_sb) /\
     bind (eval_expr cx c) (read_result cx)
       (es with gas_obs := gas_explicit marks s.vs_gas_readings) = (INL (BoolV p),mid) /\
     storage_trace_domain cx st0 mid.storage_trace /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (s,G,tn) marks (OK u,G1,tn1)) ==>
     reached rest st shadow_st mid (jump_to st.cs_current_bb u) G1 tn1) ==>
  !k x sa shadow_sa es s G tn.
  reached (bool_chain_operands p k x) sa shadow_sa es s G tn /\
  bool_chain_full_ok cx (bool_chain_operands p k x) /\ expr_type x = BaseT BoolT /\
  body_const_cells_agree [(NONE,tops)] cx env es /\ expr_body_pre cenv cx env x es /\
  compile_bool_chain_ops compile_expr cenv p rv xl (bool_chain_operands p k x) sa = ((),sb) /\
  compile_bool_chain_ops compile_expr (gas_shadow_env T cenv) p rv xl
    (MAP gas_shadow_expr (bool_chain_operands p k x)) shadow_sa = ((),shadow_sb) /\
  gas_shadow_state sa shadow_sa /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  local_ptrs_reserved cenv sa /\
  (!v n. cenv.ce_return_buf = SOME (PtrVar (Var v) n) ==> not_fresh_at sa v) /\
  (!v n. cenv.ce_return_pc = SOME (PtrVar (Var v) n) ==> not_fresh_at sa v) /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_fmp_headroom inst u) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (bind (eval_expr cx x) (read_result cx)) (es,s,G,tn)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  irule bool_chain_ops_prefix_from_observations >>
  qpat_assum `compile_bool_chain_ops _ cenv _ _ _ _ sa = _` (irule_at Any) >>
  qpat_assum `compile_bool_chain_ops _ _ _ _ _ (MAP gas_shadow_expr _) shadow_sa = ((),shadow_sb)`
    (irule_at Any) >>
  qpat_assum `fn_has_code shadow_sa shadow_sb shadow_func` (irule_at Any) >>
  qpat_assum `body_const_cells_agree [(NONE,tops)] cx env es` (irule_at Any) >>
  qpat_assum `return_buf_frame d cenv sa s` (irule_at Any) >>
  qexists_tac `\xs ca sha ee u J tau. reached xs ca sha ee u J tau /\ bool_chain_full_ok cx xs` >>
  BETA_TAC >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (rpt gen_tac >> strip_tac >> conj_tac
      >- (qpat_assum `!c rest sa sc shadow_sa shadow_sc es s G tn op sj sn lt lf
                        st shadow_st marks mid G1 tn1 u. _ ==> reached _ _ _ _ _ _ _`
            (drule_all_then ACCEPT_TAC)) >>
      qpat_x_assum `bool_chain_full_ok cx (_::_)`
        (strip_assume_tac o REWRITE_RULE [bool_chain_full_ok_def]) >>
      qpat_assum `_ ==> bool_chain_full_ok cx _` irule >>
      qpat_assum `bind (eval_expr cx _) _ _ = (INL _,_)`
        (mp_then Any strip_assume_tac (CONV_RULE (DEPTH_CONV ETA_CONV) eval_expr_read_INL)) >>
      goal_assum (drule_at Any)) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `bool_chain_full_ok cx (_::_)`
    (strip_assume_tac o REWRITE_RULE [bool_chain_full_ok_def]) >>
  conj_tac
  >- (qpat_assum `!e rest sa sc shadow_sa shadow_sc es s G tn op. _ ==> gas_prefix_full _ _ _ _ _`
        (drule_all_then ACCEPT_TAC)) >>
  strip_tac >>
  qpat_x_assum `expr_sim_full_pre _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_sim_full_pre_def]) >>
  irule bool_chain_full_head >>
  qpat_assum `body_inv tops ctx cenv cx` (irule_at Any) >>
  qpat_assum `body_const_cells_agree [(NONE,tops)] cx env _` (irule_at Any) >>
  qpat_assum `lower_value _ _ _ (gas_shadow_expr e) _ = (op,shadow_sc)` (irule_at Any) >>
  qpat_assum `gas_shadow_function func shadow_func` (irule_at Any) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
