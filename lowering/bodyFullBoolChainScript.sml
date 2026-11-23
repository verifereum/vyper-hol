(*
 * Joint body simulation: an and/or chain (BoolChain)
 *
 * The joint (full) twin of exprSimBoolChain's compile_bool_chain_case, as
 * bodyFullIfExp's ifexp_expr_full_ok is the conditional's: the chain is
 * ok when its operands are, each later operand where the one before
 * evaluates.
 *
 * TOP-LEVEL:
 *   bool_chain_full_ok_def    - the operands' body predicates, in order
 *   bool_chain_expr_full_ok   - the chain's body predicate from its operands'
 *)
Theory bodyFullBoolChain
Ancestors
  bodyFullIfExp exprSimBoolChain bodyFullOfVV bodyFullPreds bodySimFull
  exprSimIfExp exprSimDefs exprLowering boolChainOperandsCons
  boolChainFullSelect boolChainFullSingleton boolChainShadowLayout
  boolChainFullHead boolChainFullFinish boolChainCountedControl
  bodyFullWordStackBuiltin boolChainSource boolChainWrapperRead boolChainCodeLayout
  gasShadowBoolChainOperands gasShadow[qualified] gasShadowState bodyFullShared[qualified]
  bodyMemoryDefs wordArgsPtr exprSimMemDefs
  bodyFullIfExpPrepare bodyFullIfExpReach exprBodyPreProps exprSimSource
  exprSimExtract32Post exprSimWordArgs gasOutcomeFullCompose gasOutcomeFull
  vyperStorageTrace vyperStorageFootprint exprLoweringProps loweringPosts
  loweringShapeDefs loweringSlice bodyPtrDefs compileEnv freshWrites valueEncoding
  venomExecSemantics vyperAST vyperInterpreter vyperState vyperValueOperation venomState list

(* Each operand is ok, a later one where the one before evaluates. *)
Definition bool_chain_full_ok_def:
  bool_chain_full_ok cx [] = T /\
  bool_chain_full_ok cx (e::es) =
    (body_expr_full_ok cx e /\
     ((?s tv s'. eval_expr cx e s = (INL tv, s')) ==>
      bool_chain_full_ok cx es))
End

Theorem bool_chain_ops_outcome_full:
  !k x sa shadow_sa es s G tn.
  bool_chain_full_ok cx (bool_chain_operands p k x) /\ expr_type x = BaseT BoolT /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\ expr_body_pre cenv cx env x es /\
  compile_bool_chain_ops compile_expr cenv p rv xl (bool_chain_operands p k x) sa = ((),sb) /\
  compile_bool_chain_ops compile_expr (gas_shadow_env T cenv) p rv xl
    (MAP gas_shadow_expr (bool_chain_operands p k x)) shadow_sa = ((),shadow_sb) /\
  gas_shadow_state sa shadow_sa /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_fmp_headroom inst u) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  expr_type root = BaseT BoolT /\ (~expr_has_effect root ==> ~expr_has_effect x) /\
  local_ptrs_reserved cenv sa0 /\ ~not_fresh_at sa0 rv /\
  (!v n. cenv.ce_return_buf = SOME (PtrVar (Var v) n) ==> not_fresh_at sa0 v) /\
  (!v n. cenv.ce_return_pc = SOME (PtrVar (Var v) n) ==> not_fresh_at sa0 v) /\
  sa0.cs_next_var <= sa.cs_next_var /\ sa0.cs_next_id <= sa.cs_next_id /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es0 s0) /\
  wb_frame cenv es0 es sa0 s0 s /\
  (~expr_has_effect root ==> pure_frame cenv func es0 sa0 s0 s) /\
  ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 G tn /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  exit.cs_current_bb = xl /\ exit.cs_current_insts = [] ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_expr cx x) (read_result cx)) (es,s,G,tn)
    (\H res ee Gz tf z. ?b. res = INL (BoolV b) /\
      expr_post H ctx func cenv cx root es0 sa0 exit s0 ee (BoolV b) (Var rv) z /\
      z.vs_current_bb = exit.cs_current_bb /\ z.vs_inst_idx = LENGTH exit.cs_current_insts /\
      alloca_history func z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
      s0.vs_alloca_next <= z.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee Gz tf z /\
      ptr_val_ok cx (BaseT BoolT) (BoolV b) (Var rv) Gz tf z /\
      ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 Gz tf)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  Induct_on `k`
  >- (pure_rewrite_tac[bool_chain_operands_def, bool_chain_full_ok_def, listTheory.MAP] >>
      rpt strip_tac >> suspend "singleton") >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `expr_type x = BaseT BoolT`
    (mp_then Any (qspecl_then [`k`,`p`] strip_assume_tac) bool_chain_residual_cases)
  >- (qpat_assum `bool_chain_operands _ _ _ = [_]`
        (fn th => RULE_ASSUM_TAC (SIMP_RULE bool_ss [th, listTheory.MAP, bool_chain_full_ok_def])) >>
      suspend "singleton") >>
  suspend "test"
QED

Resume bool_chain_ops_outcome_full[singleton]:
  markerLib.RESUME_TAC >>
  drule_all_then (qspec_then `PG` ACCEPT_TAC) bool_chain_full_singleton
QED

Resume bool_chain_ops_outcome_full[test]:
  `?hd hs. bool_chain_operands p k tail = hd::hs` by
    simp[bool_chain_operands_cons] >>
  fs[bool_chain_full_ok_def] >>
  drule_all (SIMP_RULE bool_ss [listTheory.MAP] bool_chain_test_shadow_layout) >> strip_tac >>
  qpat_x_assum `x = IfExp _ _ _ _` SUBST_ALL_TAC >>
  drule ifexp_body_pre_children >> strip_tac >>
  `local_ptrs_reserved cenv sa` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!v n. cenv.ce_return_buf = SOME (PtrVar (Var v) n) ==> not_fresh_at sa v) /\
   (!v n. cenv.ce_return_pc = SOME (PtrVar (Var v) n) ==> not_fresh_at sa v)` by
    metis_tac[not_fresh_at_mono] >>
  drule_all_then (qspec_then `PG` assume_tac) bool_chain_full_head >>
  irule bool_word_forced_select_full >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `emit_inst JNZ _ _ _ = _` (irule_at Any) >>
  qexistsl_tac [`sa`,`env`,`\b. if b = p then st else ss`,`d`,`cenv`] >>
  BETA_TAC >> simp[] >>
  conj_tac >- (rpt strip_tac >> irule body_inv_no_phi >>
      qexistsl_tac [`cenv`,`ctx`,`cx`,`func`,`tops`] >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (Cases >> Cases_on `p` >> fs[ci_mono_def] >> decide_tac) >>
  reverse conj_tac
  >- (rpt gen_tac >> strip_tac >> qexists_tac `b` >> simp[] >>
      reverse conj_tac >- fs[ptr_val_ok_def] >>
      `wb_frame cenv es mid sa s u` by metis_tac[expr_post_frame] >>
      qpat_assum `expr_post _ _ _ _ _ c es sa sc s mid _ _ _`
        (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
      irule expr_post_word_intro >>
      simp[is_word_type_def, word_value_def, val_to_w256_def, bool_to_word_def] >>
      rpt strip_tac >> first_assum irule) >>
  qx_genl_tac [`marks`,`b`,`mid`,`G1`,`tn1`,`u`] >>
  qabbrev_tac `z = jump_to (if b then (if p then st.cs_current_bb else ss.cs_current_bb)
                                     else (if p then ss.cs_current_bb else st.cs_current_bb)) u` >>
  strip_tac >>
  `~expr_has_effect root ==> ~expr_has_effect c` by (Cases_on `p` >> fs[]) >>
  `~expr_has_effect root ==> ~expr_has_effect tail` by (Cases_on `p` >> fs[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==> valid_horizon cx st0 H es.storage_trace` by
    (`storage_trace_frame (bind (eval_expr cx c) (read_result cx))` by
       simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame, storage_trace_frame_read_result] >>
     drule_all storage_trace_frame_prefix >> simp[] >> strip_tac >>
     rpt strip_tac >> irule valid_horizon_append >> qexists_tac `observations` >>
     qpat_assum `mid.storage_trace = _` (pure_rewrite_tac o single o SYM) >>
     first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     expr_post H ctx func cenv cx root es0 sa0 sc s0 mid (BoolV b) op z /\
     ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 G1 tn1` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. _ ==> expr_post _ _ _ _ _ c es sa sc s _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     `stmt_state_rel H ctx func cenv cx es0 s0` by metis_tac[] >>
     drule_all bool_chain_full_accumulate >> strip_tac >> simp[] >>
     simp[Abbr `z`] >> irule bool_chain_word_post_jump >> simp[] >>
     goal_assum (drule_at Any)) >>
  Cases_on `b = p`
  >- suspend "continue" >> suspend "short"
QED

Resume bool_chain_ops_outcome_full[continue]:
  `b = p` by simp[] >> qpat_x_assum `b = p` SUBST_ALL_TAC >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==> stmt_state_rel H ctx func cenv cx es0 s0` by
    metis_tac[] >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  `wb_frame cenv es0 mid sa0 s0 z /\
   (~expr_has_effect root ==> pure_frame cenv func es0 sa0 s0 z) /\
   ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 G1 tn1` by
    (qpat_assum `!H. _ ==> expr_post _ _ _ _ _ root es0 sa0 sc s0 mid _ _ z /\ _`
       (drule_then strip_assume_tac) >> metis_tac[expr_post_frame, expr_post_pure_frame]) >>
  `body_const_cells_agree [(NONE,tops)] cx env mid /\ expr_sim_inv cenv cx env mid` by
    (`expr_body_pre cenv cx env c (es with gas_obs := gas_explicit marks s.vs_gas_readings)` by simp[] >>
     drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) exprSimSourceTheory.expr_body_pre_eval) >>
     strip_tac >> simp[] >>
     irule body_const_cells_agree_expr_read >>
     qpat_assum `bind (eval_expr cx c) _ _ = (_,mid)` (irule_at Any) >>
     simp[] >> metis_tac[expr_body_pre_static_facts]) >>
  `bool_chain_full_ok cx (bool_chain_operands p k tail)` by
    (simp[bool_chain_full_ok_def] >> first_x_assum irule >>
     qabbrev_tac `src = es with gas_obs := gas_explicit marks s.vs_gas_readings` >>
     qpat_assum `bind (eval_expr cx c) _ src = (INL _,mid)`
       (mp_then Any (qx_choose_then `raw` (qx_choose_then `after` strip_assume_tac))
          (CONV_RULE (DEPTH_CONV ETA_CONV) eval_expr_read_INL)) >>
     qexistsl_tac [`src`,`raw`,`after`] >> simp[]) >>
  `expr_body_pre cenv cx env tail mid /\ expr_type tail = BaseT BoolT` by
    (Cases_on `p` >> fs[]) >>
  `sa0.cs_next_var <= st.cs_next_var /\ sa0.cs_next_id <= st.cs_next_id /\
   s0.vs_alloca_next <= z.vs_alloca_next` by (fs[ci_mono_def] >> decide_tac) >>
  `(if p then (if p then tail else Literal (BaseT BoolT) (BoolL T))
          else (if p then Literal (BaseT BoolT) (BoolL F) else tail)) = tail` by
    (Cases_on `p` >> simp[]) >>
  simp[] >>
  qpat_assum `!x' sa' shadow_sa' es' s'' G' tn'. _ ==> gas_outcome_full _ _ _ _ _ _ _ _` irule >>
  simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp[Abbr `z`, jump_to_def] >>
  qexistsl_tac [`st`,`shadow_st`] >> fs[]
QED

Resume bool_chain_ops_outcome_full[short]:
  `(if b then (if p then tail else Literal (BaseT BoolT) (BoolL T))
          else (if p then Literal (BaseT BoolT) (BoolL F) else tail)) =
    Literal (BaseT BoolT) (BoolL b)` by (Cases_on `p` >> Cases_on `b` >> fs[]) >>
  `z.vs_current_bb = ss.cs_current_bb /\ z.vs_inst_idx = LENGTH ss.cs_current_insts` by fs[] >>
  `~z.vs_halted` by simp[Abbr `z`, jump_to_def] >>
  `s0.vs_alloca_next <= z.vs_alloca_next` by decide_tac >>
  `eval_operand (Lit (if p then 0w else 1w)) z = SOME (val_to_w256 (BoolV b))` by
    (qpat_assum `b <> p` mp_tac >> rpt (pop_assum kall_tac) >>
     Cases_on `p` >> Cases_on `b` >> simp[eval_operand_def, val_to_w256_def, bool_to_word_def]) >>
  `ptr_val_ok cx (BaseT BoolT) (BoolV b) (Lit (if p then 0w else 1w)) G1 tn1 z` by
    simp[ptr_val_ok_def, is_word_type_def, ptrDisciplineTheory.op_taint_def] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     expr_post H ctx func cenv cx root es0 sa0 sc s0 mid (BoolV b) op z /\
     ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 z` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. _ ==> expr_post _ _ _ _ _ root es0 sa0 sc s0 mid _ _ z /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!H. _ ==> stmt_state_rel _ _ _ _ _ mid z /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 G1 tn1` by
    (`valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
       fs[storage_trace_domain_def] >>
     qpat_assum `!H. _ ==> expr_post _ _ _ _ _ root es0 sa0 sc s0 mid _ _ z /\
                           ghost_kept_at _ _ _ _ _ _ _ _ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  drule_all bool_chain_full_finish >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`, `PG`]
    (qx_choose_then `fin` (qx_choose_then `Gf` (qx_choose_then `tf` assume_tac)))) >>
  simp[] >> irule gas_outcome_full_pure >> simp[] >>
  qexistsl_tac [`Gf`, `mid`, `INL (BoolV b)`, `fin`, `tf`] >> conj_tac
  >- (gen_tac >> Cases_on `b` >>
      simp[Once evaluate_def, evaluate_literal_def, read_result_def, bind_return, return_def]) >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. _ ==> gas_origin_ptr_path _ _ [] _ /\ _` (drule_then strip_assume_tac) >>
  fs[extract32_expr_post_end_gas_obs] >>
  qpat_x_assum `ghost_inv_at (DF H) lo d cenv cx mid Gf tf fin` mp_tac >>
  rpt (pop_assum kall_tac) >> simp[ghost_inv_at_def] >> strip_tac >> first_assum ACCEPT_TAC
QED

Finalise bool_chain_ops_outcome_full

Theorem bool_chain_expr_full_ok:
  !cx ann is_and n e.
    bool_chain_full_ok cx (bool_chain_operands is_and (n - 1) e) ==>
    body_expr_full_ok cx (Builtin ann (BoolChain is_and n) [e])
Proof
  rpt gen_tac >> strip_tac >>
  irule word_stack_builtin_body_full_intro >> simp[] >>
  rpt gen_tac >> strip_tac >>
  drule_then assume_tac bool_chain_wrapper_read_action >>
  drule_then strip_assume_tac bool_chain_wrapper_action >>
  qpat_x_assum `!gs. eval_expr _ (Builtin _ _ _) _ = _` kall_tac >> gvs[] >>
  simp[expr_type_def, is_word_type_def, post_value_type_word] >>
  conj_tac
  >- (gen_tac >>
      Cases_on `compile_expr cenv ty (Builtin (BaseT BoolT) (BoolChain is_and n) [e]) sa` >>
      drule_then strip_assume_tac bool_chain_root_layout >> simp[]) >>
  simp[expr_sim_full_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `compile_expr cenv ty (Builtin (BaseT BoolT) (BoolChain is_and n) [e]) sa` >>
  drule_then strip_assume_tac bool_chain_root_layout >>
  Cases_on `compile_expr (gas_shadow_env T cenv) ty
    (Builtin (BaseT BoolT) (BoolChain is_and n) [gas_shadow_expr e]) shadow_sa` >>
  qpat_assum `compile_expr _ _ (Builtin _ _ [gas_shadow_expr e]) shadow_sa = _`
    (mp_then Any strip_assume_tac bool_chain_root_layout) >>
  gvs[gasShadowTheory.gas_shadow_expr_def, gasShadowTheory.gas_shadow_builtin_def,
      gas_shadow_bool_chain_operands,
      lower_value_def, comp_bind_def, unwrap_value_def, comp_return_def] >>
  rename1 `fn_has_code sa sb func` >>
  rename1 `fn_has_code shadow_sa shadow_sb shadow_func` >>
  rename1 `fresh_var sa = (rv,sr)` >>
  rename1 `fresh_var shadow_sa = (rv,shadow_sr)` >>
  rename1 `fresh_label "bool_exit" sr = (_,sg)` >>
  rename1 `fresh_label "bool_exit" shadow_sr = (_,shadow_sg)` >>
  `gas_shadow_state sr shadow_sr` by
    (mp_then (Pos hd) (drule_all o GEN_ALL) bodyFullSharedTheory.gas_shadow_step
       gas_shadow_compiles_fresh_var >> simp[]) >>
  `gas_shadow_state sg shadow_sg` by
    (mp_then (Pos hd) (drule_all o GEN_ALL) bodyFullSharedTheory.gas_shadow_step
       gas_shadow_compiles_fresh_label >> simp[]) >>
  `shadow_sb.cs_current_bb = sb.cs_current_bb` by gvs[gas_shadow_state_def] >>
  qabbrev_tac `root = Builtin (BaseT BoolT) (BoolChain is_and n) [e]` >>
  irule gas_outcome_full_source_cong >>
  qexists_tac `bind (eval_expr cx e) (read_result cx)` >> conj_tac
  >- simp[Abbr `root`] >>
  suspend "outcome"
QED

Resume bool_chain_expr_full_ok[outcome]:
  irule gas_outcome_full_post_mono >>
  qexistsl_tac
    [`\H res ee Gz tf z. ?b. res = INL (BoolV b) /\
        expr_post H ctx func cenv cx root es sa sb s0 ee (BoolV b) (Var rv) z /\
        z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
        s0.vs_alloca_next <= z.vs_alloca_next /\ ghost_inv_at (DF H) lo d cenv cx ee Gz tf z /\
        ptr_val_ok cx (BaseT BoolT) (BoolV b) (Var rv) Gz tf z /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 Gz tf`,
     `\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)`] >>
  BETA_TAC >> conj_tac
  >- (rpt gen_tac >> strip_tac >> qexists_tac `BoolV b` >>
      simp[Abbr `root`, expr_type_def, is_word_type_def, expr_store_bound_word]) >>
  conj_tac >- simp[] >>
  rename1 `compile_bool_chain_ops _ (gas_shadow_env T cenv) _ _ _ _ shadow_sg = ((),shadow_sf)` >>
  qpat_assum `!fn. fn_has_code sa sb fn ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `!fn. fn_has_code shadow_sa shadow_sb fn ==> _` (drule_then strip_assume_tac) >>
  `return_buf_frame d cenv sg s0` by
    (drule return_buf_frame_frame >> disch_then irule >> simp[]) >>
  irule bool_chain_ops_outcome_full >>
  simp[Abbr `root`, expr_type_def, wb_frame_refl, ghost_kept_at_refl] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qexistsl_tac [`n - 1`,`is_and`,`sg`,`sf`,`shadow_func`,`shadow_sg`,`shadow_sf`] >>
      simp[] >>
      qpat_assum `shadow_sb.cs_current_bb = sb.cs_current_bb` (once_rewrite_tac o single o SYM) >>
      first_assum ACCEPT_TAC) >>
  qexistsl_tac [`env`,`tops`] >> simp[]
QED

Finalise bool_chain_expr_full_ok
