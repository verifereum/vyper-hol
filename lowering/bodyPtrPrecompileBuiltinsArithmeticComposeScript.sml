Theory bodyPtrPrecompileBuiltinsArithmeticCompose
Ancestors bodyPtrPrecompileBuiltinsECMulRunner bodyPtrPrecompileBuiltinsOperandCompose
          bodyPtrDefs bodyPtrPreds exprSimHypsDefs exprSimDefs stmtSimProps
          gasSummaryComposePtr exprLowering compileEnv vyperState
          exprSimWordArgs wordArgsPtr exprSimCalldataSlice

Theorem precompile_operand_bind_ptr:
  expr_sim_ptr d ctx PG fn cenv cx ty e es /\
  expr_body_pre cenv cx env e es /\
  lower_value compile_expr cenv ty e sa = (op,sb) /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx fn cenv cx es s0 /\
  ghost_inv d cenv cx es G0 tn0 s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!v ee G tn t.
    expr_post ctx fn cenv cx e es sa sb s0 ee v op t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_inv d cenv cx ee G tn t /\ ptr_val_ok cx (expr_type e) v op G tn t /\
    (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e op G t) /\
    ghost_kept cenv es sa G0 tn0 s0 G tn /\
    expr_sim_inv cenv cx env ee /\ expr_result_typed env e (Value v) /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\ ee.gas_obs = [] /\ ~t.vs_halted /\
    (?ss tt. bind (eval_expr cx e) (read_result cx) ss = (INL v,tt)) ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,fn) PG (next v) (ee,t,G,tn)
      Q (\res ee gt r. expr_exit res r)) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,fn) PG
    (bind (bind (eval_expr cx e) (read_result cx)) next) (es,s0,G0,tn0)
    Q (\res ee gt r. expr_exit res r)
Proof
  strip_tac >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then drule >> simp[] >>
  disch_then (qspecl_then [`s0`,`G0`,`tn0`] mp_tac) >> simp[] >> strip_tac >>
  drule_all precompile_operand_source_facts >> strip_tac >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ (\res ee G tn t. ?v. _) _` kall_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_ptr _ _ _ _ _ _ P _` >>
  irule pointer_outcome_bind_success >> qexists `P` >>
  reverse conj_tac
  >- (irule gas_outcome_ptr_conseq >> goal_assum (drule_at Any) >>
      simp[expr_exit_def] >> rpt strip_tac >> Cases_on `res` >>
      gvs[expr_exit_def, expr_exit_INR_type]) >>
  rpt strip_tac >> gvs[Abbr `P`] >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED


Theorem precompile_two_operand_entry_rebase:
  stmt_state_rel ctx fn cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  MAP FDOM ee.scopes = MAP FDOM ee'.scopes /\
  sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
  s1.cs_next_var <= sm.cs_next_var /\ s1.cs_next_id <= sm.cs_next_id /\
  expr_post ctx fn cenv cx a es sa s1 s0 ee va opa t /\
  expr_post ctx fn cenv cx b ee s1 sm t ee' vb opb t' /\
  ghost_kept cenv es sa G0 tn0 s0 G1 tn1 /\
  ghost_kept cenv ee s1 G1 tn1 t G2 tn2 /\
  vv_post ctx fn cenv cx e ee' sm sb t' fin tv vv u /\
  ghost_kept cenv ee' sm G2 tn2 t' Gf tnf ==>
  vv_post ctx fn cenv cx e es sa sb s0 fin tv vv u /\
  ghost_kept cenv es sa G0 tn0 s0 Gf tnf
Proof
  strip_tac >>
  `wb_frame cenv es sa s0 t` by metis_tac[expr_post_frame] >>
  `wb_frame cenv ee s1 t t'` by metis_tac[expr_post_frame] >>
  `wb_frame cenv es sa s0 t'` by
    (irule wb_frame_trans >>
     qpat_assum `wb_frame _ ee s1 t t'` (irule_at Any) >> simp[] >> metis_tac[]) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by decide_tac >>
  `MAP FDOM es.scopes = MAP FDOM ee'.scopes` by metis_tac[] >>
  `ghost_kept cenv es sa G0 tn0 s0 G2 tn2` by
    (irule ghost_kept_wb_trans >>
     qpat_assum `ghost_kept _ ee s1 _ _ _ G2 tn2` (irule_at Any) >> simp[] >> metis_tac[]) >>
  reverse conj_tac >-
    (irule ghost_kept_wb_trans >>
     qpat_assum `ghost_kept _ ee' sm _ _ _ Gf tnf` (irule_at Any) >> simp[] >> metis_tac[]) >>
  irule vv_post_prefix_frame >>
  qpat_assum `vv_post _ _ _ _ _ ee' sm _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> metis_tac[]
QED
