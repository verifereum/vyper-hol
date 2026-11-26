(* Complete the singleton region, leaving the abnormal head outcomes intact. *)
Theory boolChainFullSingleton
Ancestors
  boolChainFullHead boolChainFullFinish boolChainCodeLayout
  gasShadowCompileStmtHelpers gasOutcomeFullCompose gasOutcomeFull vyperStorageTrace
  vyperStorageFootprint exprLoweringProps loweringShapeDefs gasShadowState list

Theorem bool_chain_full_singleton:
  body_expr_full_ok cx x /\ expr_type x = BaseT BoolT /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\ expr_body_pre cenv cx env x es /\
  compile_bool_chain_ops compile_expr cenv p rv xl [x] sa = ((),sb) /\
  compile_bool_chain_ops compile_expr (gas_shadow_env T cenv) p rv xl
    [gas_shadow_expr x] shadow_sa = ((),shadow_sb) /\
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
  strip_tac >>
  qpat_x_assum `compile_bool_chain_ops _ cenv _ _ _ _ _ = _`
    (strip_assume_tac o MATCH_MP bool_chain_singleton_layout) >>
  qpat_x_assum `compile_bool_chain_ops _ (gas_shadow_env _ _) _ _ _ _ _ = _`
    (strip_assume_tac o MATCH_MP bool_chain_singleton_layout) >>
  rename1 `lower_value _ cenv _ x sa = (op,sc)` >>
  rename1 `lower_value _ (gas_shadow_env T cenv) _ _ shadow_sa = (shadow_op,shadow_sc)` >>
  `op = shadow_op /\ gas_shadow_state sc shadow_sc` by
    (drule (REWRITE_RULE [gas_shadow_compiles_def]
       (Q.INST [`ty` |-> `BaseT BoolT`, `sd` |-> `T`] gas_shadow_stmt_lower_value_env)) >>
     disch_then (qspecl_then [`x`,`cenv`] mp_tac) >> simp[]) >>
  qpat_x_assum `op = shadow_op` (SUBST_ALL_TAC o SYM) >>
  `local_ptrs_reserved cenv sa` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!v n. cenv.ce_return_buf = SOME (PtrVar (Var v) n) ==> not_fresh_at sa v) /\
   (!v n. cenv.ce_return_pc = SOME (PtrVar (Var v) n) ==> not_fresh_at sa v)` by
    metis_tac[not_fresh_at_mono] >>
  qpat_assum `!fn. fn_has_code sa sb fn ==> _` (qspec_then `func` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_assum `!fn. fn_has_code shadow_sa shadow_sb fn ==> _` (qspec_then `shadow_func` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  drule_all_then (qspec_then `PG` assume_tac) bool_chain_full_head >>
  irule gas_outcome_full_zero_suffix >>
  qexists_tac `\H res ee G1 tn1 u. ?b. res = INL (BoolV b) /\
    expr_post H ctx func cenv cx root es0 sa0 sc s0 ee (BoolV b) op u /\
    eval_operand op u = SOME (if b then 1w else 0w) /\
    u.vs_current_bb = sc.cs_current_bb /\ u.vs_inst_idx = LENGTH sc.cs_current_insts /\
    ~u.vs_halted /\ alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    s0.vs_alloca_next <= u.vs_alloca_next /\ ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 u /\
    ptr_val_ok cx (BaseT BoolT) (BoolV b) op G1 tn1 u /\
    ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 G1 tn1` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >> goal_assum (drule_at Any) >>
      simp[] >> rpt strip_tac >>
      `storage_trace_frame (bind (eval_expr cx x) (read_result cx))` by
        (irule storage_trace_frame_bind_all >>
         simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
      `valid_horizon cx st0 H es.storage_trace` by
        (qpat_assum `!tail. bind _ _ _ = _`
           (qspec_then `[]` (assume_tac o REWRITE_RULE [APPEND_NIL])) >>
         drule_all storage_trace_frame_prefix >> simp[] >> strip_tac >>
         gvs[] >> metis_tac[valid_horizon_append]) >>
      `stmt_state_rel H ctx func cenv cx es0 s0` by simp[] >>
      drule_all bool_chain_full_accumulate >> strip_tac >>
      qexists_tac `b` >> simp[] >> decide_tac) >>
  rpt strip_tac >> pop_assum (mk_asm "midpost") >>
  asm "midpost" (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- fs[storage_trace_domain_def]) >> simp[] >> strip_tac >>
  qpat_x_assum `res = INL (BoolV b)` SUBST_ALL_TAC >>
  `eval_operand op t = SOME (val_to_w256 (BoolV b))` by
    (Cases_on `b` >> fs[valueEncodingTheory.val_to_w256_def, venomExecSemanticsTheory.bool_to_word_def]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     expr_post H ctx func cenv cx root es0 sa0 sc s0 ee (BoolV b) op t /\
     ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 t` by
    (rpt gen_tac >> strip_tac >>
     asm "midpost" (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> simp[]) >>
  drule_all bool_chain_full_finish >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`z`,`Gz`,`tf`] >> rpt strip_tac >> res_tac >> simp[]
QED
