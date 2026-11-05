(* Memory-safe invocation of the range loop body. *)
Theory stmtForRangeMemoryLoop
Ancestors
  stmtForRangeMemoryEntry stmtForRangeMemoryRound bodyMemoryDefs
  stmtSimForLoop stmtSimDefs stmtSimProps stmtLowering compileEnv
  loweringPosts exprLoweringProps vyperState allocaHistory

Theorem for_body_outcome_mem:
  for_code func cenv bc ty stmts id tyv p sz ainst cv ev dv nv
    cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
  st.cs_next_var <= sb0.cs_next_var /\
  ret_pc_ok cenv st cc /\ return_buf_frame d cenv st cc /\
  (!x. not_fresh_at st x ==> x <> dv) /\
  (!x. x <> dv ==> lookup_var x s2 = lookup_var x cc) /\
  s2.vs_alloca_next = cc.vs_alloca_next /\ alloca_history func s2 /\
  ~s2.vs_halted /\ s2.vs_current_bb = body_lbl /\ s2.vs_inst_idx = 1 /\
  stmt_state_rel ctx func bc cx E s2 /\
  gas_admissible (eval_stmts cx stmts) (stmt_res_ok (InLoop exit_lbl incr_lbl)) E /\
  stmt_frag_mem d ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
    (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts) E ==>
  gas_outcome T (cx_tops cx) (ctx,func) (eval_stmts cx stmts) (E,s2)
    (\res ee t. ?cenv''.
      stmt_lands (InLoop exit_lbl incr_lbl) sb1 res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb1 /\
        cenv'' = FST (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts sb0)) /\
      cenv_top_ext bc cenv'' ee.scopes /\ stmt_state_rel ctx func cenv'' cx ee t /\
      (!x w. not_fresh_at sb0 x /\ lookup_var x s2 = SOME w ==>
             lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s2.vs_allocas aid = SOME b ==>
               FLOOKUP t.vs_allocas aid = SOME b) /\
      return_buf_frame d cenv'' sb1 t /\ alloca_history func t /\
      s2.vs_alloca_next <= t.vs_alloca_next)
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  strip_tac >>
  `bc.ce_return_pc = cenv.ce_return_pc /\ bc.ce_return_buf = cenv.ce_return_buf` by
    (fs[for_code_def] >>
     qpat_x_assum `_ = cenv` (SUBST1_TAC o SYM) >> simp[]) >>
  `!x w. not_fresh_at st x /\ lookup_var x cc = SOME w ==>
         lookup_var x s2 = SOME w` by metis_tac[] >>
  `ret_pc_ok bc sb0 s2` by
    (irule ret_pc_ok_frame >> qexistsl_tac [`cenv`, `cc`, `st`] >> simp[]) >>
  `return_buf_frame d bc sb0 s2` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `cc`, `st`] >> simp[]) >>
  qpat_x_assum `stmt_frag_mem _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[stmt_frag_mem_def] >>
  disch_then (qspecl_then [`sb0`, `sb1`, `s2`,
    `FST (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts sb0)`] mp_tac) >>
  impl_tac
  >- (fs[for_code_def, compile_stmts_env] >> metis_tac[pairTheory.PAIR]) >> simp[]
QED

Theorem for_body_original_frame_mem:
  return_buf_frame d cenv st cc /\ st.cs_next_var <= sb0.cs_next_var /\
  (!x. not_fresh_at st x ==> x <> dv) /\
  (!x. x <> dv ==> lookup_var x s2 = lookup_var x cc) /\
  s2.vs_alloca_next = cc.vs_alloca_next /\
  (!x w. not_fresh_at sb0 x /\ lookup_var x s2 = SOME w ==>
         lookup_var x t = SOME w) /\
  alloca_history func t /\ s2.vs_alloca_next <= t.vs_alloca_next ==>
  return_buf_frame d cenv st t /\ alloca_history func t /\
  cc.vs_alloca_next <= t.vs_alloca_next /\
  (!x w. not_fresh_at st x /\ lookup_var x cc = SOME w ==>
         lookup_var x t = SOME w)
Proof
  strip_tac >>
  `!x w. not_fresh_at st x /\ lookup_var x cc = SOME w ==>
         lookup_var x t = SOME w` by
    (rpt strip_tac >>
     `not_fresh_at sb0 x` by (fs[not_fresh_at_def] >> decide_tac) >>
     metis_tac[]) >>
  simp[] >> irule return_buf_frame_frame >>
  qexistsl_tac [`cenv`, `cc`, `st`] >> simp[]
QED
