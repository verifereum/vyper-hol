(* Compiler-layout boundary for the checked Range tail. *)
Theory bodyIntCallFamStmtForCheckedCompiled
Ancestors
  bodyIntCallFamStmtForCheckedTail bodyIntCallFamStmtForCheckedStatic
  stmtSimForRange stmtSimForParts stmtSimProps stmtLoweringMono
  exprLoweringProps bodyExprPreFacts stmtSimReturn
  ASCIInumbers finite_map bodySim compileEnv bodyIntCallJointContract
Libs
  monadsyntax

Theorem intcall_for_checked_compiled_tail:
  for_range_checked_code ce lctx
    (if fp.jc_ret_ty = NoneT then BaseT BoolT else fp.jc_ret_ty)
    id fty bound stmts op1 op2 st = ((),sf) /\
  fn_has_code st sf fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  cs_extends sa st /\ sa.cs_next_var <= st.cs_next_var /\ intcall_frame_ok fp /\
  intcall_joint_res fp ce env es sa s /\
  body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\ ~s.vs_halted /\
  eval_operand op1 s = SOME (i2w n1) /\ eval_operand op2 s = SOME (i2w n2) /\
  (!x. op1 = Var x \/ op2 = Var x ==> not_fresh_at st x) /\
  is_int_type fty /\ evaluate_type (get_tenv fp.jc_cx) fty = SOME tyv /\
  value_has_type tyv (IntV n1) /\ value_has_type tyv (IntV n2) /\
  bound < dimword (:256) /\
  FLOOKUP ce.ce_vars id = NONE /\ id NOTIN FDOM env.var_types /\
  intcall_stmts_producer fp stmts /\
  supported_stmts fp.jc_tops bindings stmts /\
  (!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) stmts ==>
     occurs_abi_decode_target target fp.jc_tops) /\
  type_stmts (extend_local env id fty F) fp.jc_ret_ty stmts = SOME env_b /\
  IS_SOME (type_stmts ((extend_local env id fty F) with bare_global_assignable := FEMPTY)
    fp.jc_ret_ty stmts) /\ EVERY (stmt_exprs_ok ce) stmts /\
  calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_stmts stmts) /\
  (n1 <= n2 /\ Num (n2 - n1) <= bound ==>
    gas_admissible (eval_for fp.jc_cx tyv id stmts
      (GENLIST (\j. IntV (n1 + &j)) (Num (n2 - n1)))) (stmt_res_ok lctx) es) ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (do rl <- lift_sum (get_range_limits (IntV n1) (IntV n2));
        check (compatible_bound (Dynamic bound) (SND rl)) "For too long";
        eval_for fp.jc_cx tyv id stmts
          (GENLIST (\j. IntV (FST rl + &j)) (SND rl)) od)
    (es,s)
    (\res ee t. res = INL () /\ t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = 0 /\ ~t.vs_halted /\ intcall_joint_res fp ce env ee sa t /\
      (!x z. not_fresh_at sa x /\ lookup_var x s = SOME z ==> lookup_var x t = SOME z) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      s.vs_alloca_next <= t.vs_alloca_next)
    (intcall_stmt_exit fp)
Proof
  strip_tac >>
  `ce.ce_alloca_locals` by fs[body_inv_def] >>
  `!c lc a b. compile_stmts c lc
      (if fp.jc_ret_ty = NoneT then BaseT BoolT else fp.jc_ret_ty) stmts a = ((),b) ==>
      cs_extends a b` by
    metis_tac[compile_stmt_cs_mono, fragExecTheory.cs_mono_def] >>
  drule_at (Pat `for_range_checked_code _ _ _ _ _ _ _ _ _ _ = _`)
    for_range_checked_parts >>
  disch_then (qspecl_then [`st`, `fp.jc_func`] mp_tac) >>
  (impl_tac >- (simp[cs_extends_refl] >> metis_tac[])) >>
  disch_then (qx_choosel_then
    [`p`, `cv`, `rv`, `g1`, `z1`, `g2`, `z2`, `ev`, `dv`, `entry_lbl`,
     `cond_lbl`, `body_lbl`, `incr_lbl`, `exit_lbl`, `bc`, `sb0`, `sb1`,
     `sj`, `nv`] strip_assume_tac) >>
  `sb0.cs_next_var <= sb1.cs_next_var` by
    metis_tac[compile_stmt_cs_mono, fragExecTheory.cs_mono_def] >>
  `local_ptrs_reserved ce st` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     fs[intcall_joint_res_def, intcall_expr_res_def, cs_extends_def]) >>
  `(!scs. not_local_ptr ce scs p) /\ (!scs. not_local_ptr ce scs cv) /\
   (!scs. not_local_ptr ce scs ev) /\ (!scs. not_local_ptr ce scs dv) /\
   (!scs. not_local_ptr ce scs nv)` by
    (rpt conj_tac >> gen_tac >>
     rpt (qpat_x_assum `_ = STRING #"%" (toString _)` SUBST1_TAC) >>
     irule local_ptrs_reserved_fresh >> qexists_tac `st` >> simp[]) >>
  `is_word_type fty` by
    (Cases_on `fty` >> gvs[vyperTypeSystemTheory.is_int_type_def] >>
     rename1 `is_int_type (BaseT bt)` >> Cases_on `bt` >>
     gvs[vyperTypeSystemTheory.is_int_type_def, is_word_type_def]) >>
  `type_memory_bytes ce fty = 32 /\ type_memory_size tyv = 32` by
    (drule_all word_type_sizes >> disch_then (qspec_then `ce` mp_tac) >> simp[]) >>
  `local_ptrs_reserved bc sb0` by
    (irule local_ptrs_reserved_next_var >>
     qexists_tac `st with cs_next_var := st.cs_next_var + 1` >> simp[] >>
     irule declare_local_reserved >> metis_tac[]) >>
  drule_all stmtSimPropsTheory.declare_local_ptr >> strip_tac >>
  `MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes ce fty))] [p])
     (fn_insts fp.jc_func)` by
    (qpat_assum `lookup_block st.cs_current_bb _ = _`
       (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
         fragExecTheory.lookup_block_fn_insts)) >> simp[]) >>
  `for_code fp.jc_func ce bc
     (if fp.jc_ret_ty = NoneT then BaseT BoolT else fp.jc_ret_ty)
     stmts id tyv p (type_memory_bytes ce fty)
     (mk_inst st.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes ce fty))] [p])
     cv ev dv nv cond_lbl exit_lbl body_lbl incr_lbl
     (st.cs_next_id + 12) (st.cs_next_id + 13) (st.cs_next_id + 14) bbb
     sj.cs_next_id (sj.cs_next_id + 1) (sj.cs_next_id + 2) sb0 sb1 sj` by
    (simp[stmtSimForLoopTheory.for_code_def] >>
     conj_tac >- simp[block_is_terminated_def, venomInstTheory.mk_inst_def,
                      venomInstTheory.is_terminator_def] >>
     simp[not_fresh_at_def] >> metis_tac[]) >>
  `same_frame ce bc` by
    (irule bodySimDeclCasesTheory.declare_local_same_frame >>
     qhdtm_assum `declare_local` (irule_at Any) >> simp[]) >>
  `body_inv fp.jc_tops fp.jc_ctx bc fp.jc_cx` by
    metis_tac[body_inv_same_frame] >>
  `EVERY (stmt_exprs_ok bc) stmts` by
    metis_tac[stmt_exprs_ok_same_frame, listTheory.EVERY_MONOTONIC] >>
  `?ce_b. stmts_env bc (InLoop exit_lbl incr_lbl)
      (if fp.jc_ret_ty = NoneT then BaseT BoolT else fp.jc_ret_ty) stmts sb0 = (ce_b,sb1)` by
    (qmatch_goalsub_abbrev_tac `stmts_env bc lc rt stmts sb0` >>
     Cases_on `stmts_env bc lc rt stmts sb0` >>
     metis_tac[compile_stmts_env, pairTheory.SND]) >>
  `local_ptrs_reserved ce sb1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `st` >> simp[]) >>
  `supported_program fp.jc_tops /\ get_module_code fp.jc_cx NONE = SOME fp.jc_tops` by
    fs[body_inv_def] >>
  `call_evaluation_safe fp.jc_cx (int_calls_stmts stmts)` by
    (fs[intcall_frame_ok_def, vyperTypeCallStackSoundnessTheory.call_evaluation_safe_def] >>
     metis_tac[]) >>
  `!op x. fp.jc_reserved op /\ op = Var x ==> not_fresh_at sa x` by
    fs[intcall_joint_res_def, intcall_expr_res_def] >>
  `!op. fp.jc_reserved op ==> op <> Var cv /\ op <> Var nv /\ op <> Var dv` by
    (gen_tac >> strip_tac >>
     `?x z. op = Var x /\ lookup_var x fp.jc_oorig = SOME z` by
       (fs[intcall_frame_ok_def] >> metis_tac[]) >>
     `not_fresh_at sa x` by metis_tac[] >> gvs[not_fresh_at_def]) >>
  qpat_assum `sf.cs_current_bb = _` SUBST1_TAC >>
  irule intcall_for_checked_tail >> simp[] >>
  conj_tac >- (qexists_tac `lctx` >> simp[]) >>
  conj_tac >- fs[intcall_joint_res_def, intcall_expr_res_def] >>
  conj_tac >- (qexists_tac `bindings` >> simp[]) >>
  gvs[] >>
  qhdtm_assum `for_code` (irule_at Any) >> simp[] >>
  qhdtm_assum `declare_local` (irule_at Any) >> simp[] >>
  qexistsl_tac [`STRING #"%" (toString (st.cs_next_var + 6))`,
    `STRING #"%" (toString (st.cs_next_var + 4))`,
    `STRING #"%" (toString (st.cs_next_var + 2))`, `op2`, `op1`,
    `fresh_label_output "for_entry" st.cs_next_label`, `st.cs_next_id + 1`,
    `st.cs_next_id + 2`, `STRING #"%" (toString (st.cs_next_var + 5))`,
    `STRING #"%" (toString (st.cs_next_var + 3))`] >>
  simp[ASCIInumbersTheory.toString_inj, wordsTheory.dimword_def] >>
  conj_tac >- (gen_tac >> strip_tac >>
    `not_fresh_at st x` by metis_tac[] >>
    qpat_x_assum `not_fresh_at st x` mp_tac >>
    pure_rewrite_tac[not_fresh_at_def] >>
    disch_tac >> rpt conj_tac >> first_x_assum irule >> simp[]) >>
  conj_tac >- (simp[not_fresh_at_def] >> fs[not_fresh_at_def]) >>
  conj_tac >- (simp[not_fresh_at_def] >> fs[not_fresh_at_def]) >>
  gen_tac >> strip_tac >>
  irule exprLoweringPropsTheory.local_ptrs_reserved_not_live >>
  conj_tac >- (qexistsl_tac [`id`, `32`] >> simp[vyperStateTheory.lookup_scopes_def]) >>
  metis_tac[]
QED
