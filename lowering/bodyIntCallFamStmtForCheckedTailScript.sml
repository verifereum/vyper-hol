(* Checked Range tail: the history-free setup followed by the body producer. *)
Theory bodyIntCallFamStmtForCheckedTail
Ancestors
  bodyIntCallFamStmtForRange bodyIntCallFamStmtForCheckedSetup
  bodyIntCallFamStmtForSetup stmtSimForRange stmtSimDeclCompose
  exprSimSubscriptMap bodyIntCallJointContract compileEnv finite_map
  venomInst venomState vyperInterpreter vyperState list
Libs
  monadsyntax

Theorem intcall_for_checked_tail:
  aa = mk_inst aid ALLOCA [Lit (n2w sz)] [p] /\
  32 <= sz /\ sz < dimword (:256) /\
  lookup_block s0.vs_current_bb fp.jc_func.fn_blocks =
    SOME <|bb_label := start_lbl; bb_instructions :=
      pre ++ [aa; mk_inst j JMP [Label lbl] []]|> /\
  lookup_block lbl fp.jc_func.fn_blocks =
    SOME <|bb_label := lbl; bb_instructions :=
      [mk_inst i ASSIGN [op1] [cv];
       mk_inst (i+1) SUB [op2;op1] [rv];
       mk_inst (i+2) (if is_signed_type fty then SGT else GT) [op1;op2] [g1];
       mk_inst (i+3) ISZERO [Var g1] [z1];
       mk_inst (i+4) ASSERT [Var z1] [];
       mk_inst (i+5) GT [Var rv;Lit (n2w bound)] [g2];
       mk_inst (i+6) ISZERO [Var g2] [z2];
       mk_inst (i+7) ASSERT [Var z2] [];
       mk_inst (i+8) ADD [op1;Var rv] [ev];
       mk_inst (i+9) JMP [Label cond_lbl] []]|> /\
  s0.vs_inst_idx = LENGTH pre /\ ~s0.vs_halted /\
  eval_operand op1 s0 = SOME (i2w n1) /\ eval_operand op2 s0 = SOME (i2w n2) /\
  ALL_DISTINCT [p;cv;rv;g1;z1;g2;z2;ev] /\
  (!x. op1 = Var x \/ op2 = Var x ==> ~MEM x [p;cv;rv;g1;z1;g2;z2;ev]) /\
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s0 /\
  local_ptrs_reserved ce sa /\
  MEM aa (fn_insts fp.jc_func) /\ fn_inst_ids_distinct fp.jc_func /\
  not_local_ptr ce es.scopes p /\
  (!x. not_fresh_at sa x ==> ~MEM x [p;cv;rv;g1;z1;g2;z2;ev]) /\
  is_int_type fty /\ evaluate_type (get_tenv fp.jc_cx) fty = SOME tyv /\
  value_has_type tyv (IntV n1) /\ value_has_type tyv (IntV n2) /\
  bound < dimword (:256) /\
  for_code fp.jc_func ce bc
    (if fp.jc_ret_ty = NoneT then BaseT BoolT else fp.jc_ret_ty)
    stmts id tyv p sz aa cv ev dv nv
    cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
  intcall_stmts_producer fp stmts /\
  declare_local ce id fty sd = (bc,sd') /\ ce.ce_alloca_locals /\
  FLOOKUP ce.ce_vars id = NONE /\ id NOTIN FDOM env.var_types /\
  type_memory_bytes ce fty < 2 ** 64 /\
  sa.cs_next_var <= sb0.cs_next_var /\
  (!x. not_fresh_at sa x ==> not_fresh_at sb0 x /\ x <> dv /\ x <> cv /\ x <> nv) /\
  (!scs. lookup_scopes id scs = NONE ==> not_local_ptr bc (FEMPTY :: scs) p) /\
  local_ptrs_reserved ce sb1 /\
  (!op x. fp.jc_reserved op /\ op = Var x ==> not_fresh_at sa x) /\
  (!op. fp.jc_reserved op ==> op <> Var cv /\ op <> Var nv /\ op <> Var dv) /\
  body_inv fp.jc_tops fp.jc_ctx bc fp.jc_cx /\
  supported_program fp.jc_tops /\ get_module_code fp.jc_cx NONE = SOME fp.jc_tops /\
  supported_stmts fp.jc_tops bindings stmts /\
  (!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) stmts ==>
     occurs_abi_decode_target target fp.jc_tops) /\
  type_stmts (extend_local env id fty F) fp.jc_ret_ty stmts = SOME env_b /\
  IS_SOME (type_stmts ((extend_local env id fty F) with bare_global_assignable := FEMPTY)
    fp.jc_ret_ty stmts) /\
  EVERY (stmt_exprs_ok bc) stmts /\
  calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_stmts stmts) /\
  call_evaluation_safe fp.jc_cx (int_calls_stmts stmts) /\
  stmts_env bc (InLoop exit_lbl incr_lbl)
    (if fp.jc_ret_ty = NoneT then BaseT BoolT else fp.jc_ret_ty) stmts sb0 = (ce_b,sb1) /\
  (n1 <= n2 /\ Num (n2 - n1) <= bound ==>
    gas_admissible (eval_for fp.jc_cx tyv id stmts
      (GENLIST (\j. IntV (n1 + &j)) (Num (n2 - n1)))) (stmt_res_ok lctx) es) ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (do rl <- lift_sum (get_range_limits (IntV n1) (IntV n2));
        check (compatible_bound (Dynamic bound) (SND rl)) "For too long";
        eval_for fp.jc_cx tyv id stmts
          (GENLIST (\j. IntV (FST rl + &j)) (SND rl)) od)
    (es,s0)
    (\res ee t. res = INL () /\ t.vs_current_bb = exit_lbl /\
      t.vs_inst_idx = 0 /\ ~t.vs_halted /\ intcall_joint_res fp ce env ee sa t /\
      (!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==> lookup_var x t = SOME z) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      s0.vs_alloca_next <= t.vs_alloca_next)
    (intcall_stmt_exit fp)
Proof
  strip_tac >>
  irule intcall_for_checked_range_outcome >> simp[] >>
  `MEM (if is_signed_type fty then SGT else GT) [SGT;GT]` by
    (Cases_on `is_signed_type fty` >> simp[]) >>
  `(if is_signed_type fty then SGT else GT) = SGT <=> is_signed_type fty` by
    (Cases_on `is_signed_type fty` >> simp[]) >>
  drule_all intcall_for_checked_start_no_history >>
  simp[] >> strip_tac >> simp[] >>
  reverse conj_tac >- (qexists_tac `fty` >> simp[] >>
    qpat_x_assum `_ \/ _ ==> ?t. _` ACCEPT_TAC) >>
  strip_tac >>
  drule_at (Pat `evaluate_type _ _ = _`) range_end_words >>
  disch_then (qspecl_then [`n1`, `n2`] mp_tac) >> simp[] >> strip_tac >>
  `?cc w. gas_marked_path F fp.jc_ctx fp.jc_func s0 0 (OK cc) /\
    cc.vs_current_bb = cond_lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
    intcall_joint_res fp ce env es sa cc /\
    lookup_var cv cc = SOME (i2w n1) /\ lookup_var ev cc = SOME (i2w n2) /\
    lookup_var p cc = SOME w /\ FLOOKUP cc.vs_allocas aid = SOME (w2n w,sz) /\
    (!x. not_fresh_at sa x ==> lookup_var x cc = lookup_var x s0) /\
    (!id ent. FLOOKUP s0.vs_allocas id = SOME ent ==> FLOOKUP cc.vs_allocas id = SOME ent) /\
    s0.vs_alloca_next <= cc.vs_alloca_next /\
    cc.vs_memory = s0.vs_memory /\ cc.vs_labels = s0.vs_labels` by
    (qpat_x_assum `_ /\ _ ==> ?cc w. _` irule >> simp[] >> intLib.ARITH_TAC) >>
  suspend "iterations"
QED

Resume intcall_for_checked_tail[iterations]:
  `Num (n2 - n1) < dimword (:256)` by
    (drule_at (Pat `evaluate_type _ _ = _`) range_end_words >>
     disch_then (qspecl_then [`n1`, `n2`] mp_tac) >> simp[]) >>
  `!k. k < Num (n2 - n1) ==> value_has_type tyv (IntV (n1 + &k))` by
    metis_tac[range_value_has_type] >>
  irule gas_outcome_zero_prefix >> qexists_tac `cc` >> simp[] >>
  `gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (eval_for fp.jc_cx tyv id stmts
      (DROP 0 (GENLIST (\j. IntV (n1 + &j)) (Num (n2 - n1))))) (es,cc)
    (\res ee t. res = INL () /\ t.vs_current_bb = exit_lbl /\
      t.vs_inst_idx = 0 /\ ~t.vs_halted /\ intcall_joint_res fp ce env ee sa t /\
      (!x z. not_fresh_at sa x /\ lookup_var x cc = SOME z ==> lookup_var x t = SOME z) /\
      (!aid b. FLOOKUP cc.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      cc.vs_alloca_next <= t.vs_alloca_next)
    (\res ee r. ?ex. res = INR ex /\ intcall_stmt_exit fp (INR ex) ee r)` by
    (irule (SRULE [LET_THM] intcall_for_range_producer_iterations) >>
     qhdtm_assum `for_code` (irule_at Any) >> simp[] >>
     qhdtm_assum `declare_local` (irule_at Any) >> simp[] >>
     qexistsl_tac [`lctx`, `bindings`] >> simp[venomInstTheory.mk_inst_def] >>
     fs[]) >>
  fs[listTheory.DROP_0] >>
  irule gas_outcome_conseq >>
  qhdtm_assum `gas_outcome` (irule_at Any) >> simp[]
  >- (rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >> simp[]
QED
Finalise intcall_for_checked_tail
