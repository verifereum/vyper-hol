(* Compiler intervals for a linked If and its gas shadow. *)
Theory bodyIfPairedIntervalsMods
Ancestors
  bodyFullShared bodyExprPreFacts stmtSimIfProps stmtSimProps stmtLoweringMono
  loweringPosts gasShadowCompileStmtBase
  stmtLowering exprLoweringProps compileEnv emitHelper emitHelperProps fragExec
  gasShadowCompileStmtHelpers gasShadowStmtEnv gasShadowState gasShadow

Theorem if_compile_chain[local]:
  !cenv lctx ty c yes no sa sb.
    compile_stmt cenv lctx ty (If c yes no) sa = ((), sb) ==>
    ?op s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 tl el xl x5 x8.
      lower_value compile_expr cenv (BaseT BoolT) c sa = (op, s1) /\
      fresh_label "then" s1 = (tl, s2) /\
      fresh_label "else" s2 = (el, s3) /\
      fresh_label "if_exit" s3 = (xl, s4) /\
      emit_inst JNZ [op; Label tl; Label el] [] s4 = ((), s5) /\
      new_block tl s5 = (x5, s6) /\
      compile_stmts cenv lctx ty yes s6 = ((), s7) /\
      (if block_is_terminated s7 then s8 = s7
       else emit_inst JMP [Label xl] [] s7 = ((), s8)) /\
      new_block el s8 = (x8, s9) /\
      compile_stmts cenv lctx ty no s9 = ((), s10) /\
      (if block_is_terminated s10 then s11 = s10
       else emit_inst JMP [Label xl] [] s10 = ((), s11)) /\
      (~block_is_terminated s7 \/ ~block_is_terminated s10 ==>
       ?x11. new_block xl s11 = (x11, sb)) /\
      (block_is_terminated s7 /\ block_is_terminated s10 ==> sb = s11)
Proof
  rpt gen_tac >>
  simp[compile_stmt_def, comp_bind_def, comp_ignore_bind_def, comp_get_def,
       emit_jmp_if_not_terminated_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> fs[oneTheory.one] >>
  rename1 `compile_stmts _ _ _ yes _ = ((), s7)` >>
  rename1 `new_block else_lbl s8 = (x8, s9)` >>
  rename1 `compile_stmts _ _ _ no s9 = ((), s10)` >>
  rename1 `(if block_is_terminated s10 then _ else _) s10 = ((), s11)` >>
  qexistsl_tac [`s8`, `s9`, `s10`, `s11`, `x8`] >>
  Cases_on `block_is_terminated s7` >> Cases_on `block_is_terminated s10` >>
  gvs[comp_return_def, comp_bind_def] >> rpt (pairarg_tac >> gvs[])
QED

Theorem if_emit_extends[local]:
  emit_inst opc ops outs a = ((), b) ==> cs_extends a b
Proof
  metis_tac[CONJUNCT1 cs_appends_emit_helpers, cs_appends_def]
QED

Theorem if_arm_growth[local]:
  compile_stmts cenv lctx ty ss a = ((), b) ==>
  cs_extends a b /\ a.cs_next_var <= b.cs_next_var /\ a.cs_next_id <= b.cs_next_id
Proof
  strip_tac >>
  `cs_mono (stmts_env cenv lctx ty ss)` by simp[stmts_env_cs_mono] >>
  drule_all if_branch_compiler_mono >> strip_tac >> simp[] >>
  qspecl_then [`cenv`, `lctx`, `ty`, `ss`, `a`] mp_tac
    (CONJUNCT2 compile_stmt_ci_mono) >> simp[ci_mono_def]
QED

Theorem if_jump_growth[local]:
  (if block_is_terminated a then b = a
   else emit_inst JMP [Label xl] [] a = ((), b)) ==>
  cs_extends a b /\ a.cs_next_var = b.cs_next_var /\ a.cs_next_id <= b.cs_next_id
Proof
  Cases_on `block_is_terminated a` >> simp[cs_extends_refl] >>
  strip_tac >> drule emit_inst_extends >> drule if_emit_extends >> simp[]
QED

Theorem if_exit_block_growth[local]:
  (~block_is_terminated left \/ ~block_is_terminated right ==>
   ?x. new_block xl a = (x, b)) /\
  (block_is_terminated left /\ block_is_terminated right ==> b = a) ==>
  cs_extends a b /\ a.cs_next_var = b.cs_next_var /\
  (~block_is_terminated left \/ ~block_is_terminated right ==>
   b.cs_current_bb = xl /\ b.cs_current_insts = [])
Proof
  Cases_on `block_is_terminated left` >> Cases_on `block_is_terminated right` >>
  simp[cs_extends_refl] >> rpt strip_tac >>
  drule new_block_props >> drule cs_extends_new_block >> simp[]
QED

(* Follow the compiler state chain in either direction from an endpoint. *)
val extends_via = fn mid => irule cs_extends_trans >> qexists_tac mid >> simp[];
val code_between =
  qpat_assum `fn_has_code sa sb _`
    (mp_then Any (fn th => irule th >> simp[cs_extends_refl]) fn_has_code_mid);

Theorem if_chain_intervals[local]:
  !cenv lctx ty c yes no sa sb func.
    compile_stmt cenv lctx ty (If c yes no) sa = ((), sb) /\
    fn_has_code sa sb func ==>
    ?op s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 tl el xl x5 x8.
      lower_value compile_expr cenv (BaseT BoolT) c sa = (op, s1) /\
      fresh_label "then" s1 = (tl, s2) /\
      fresh_label "else" s2 = (el, s3) /\
      fresh_label "if_exit" s3 = (xl, s4) /\
      emit_inst JNZ [op; Label tl; Label el] [] s4 = ((), s5) /\
      new_block tl s5 = (x5, s6) /\
      compile_stmts cenv lctx ty yes s6 = ((), s7) /\
      (if block_is_terminated s7 then s8 = s7
       else emit_inst JMP [Label xl] [] s7 = ((), s8)) /\
      new_block el s8 = (x8, s9) /\
      compile_stmts cenv lctx ty no s9 = ((), s10) /\
      (if block_is_terminated s10 then s11 = s10
       else emit_inst JMP [Label xl] [] s10 = ((), s11)) /\
      fn_has_code sa s1 func /\ cs_extends sa s1 /\
      sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_var <= sb.cs_next_var /\
      s4.cs_current_bb = s1.cs_current_bb /\
      s4.cs_current_insts = s1.cs_current_insts /\
      fn_has_code s4 s5 func /\
      s6.cs_current_bb = tl /\ s6.cs_current_insts = [] /\
      cs_extends sa s6 /\ sa.cs_next_var <= s6.cs_next_var /\
      sa.cs_next_id <= s6.cs_next_id /\
      cs_extends s6 s7 /\ cs_extends s7 sb /\
      s7.cs_next_var <= sb.cs_next_var /\
      fn_has_code s6 s7 func /\ fn_has_code s7 s8 func /\
      (~block_is_terminated s7 ==>
       sb.cs_current_bb = xl /\ sb.cs_current_insts = []) /\
      s9.cs_current_bb = el /\ s9.cs_current_insts = [] /\
      cs_extends sa s9 /\ sa.cs_next_var <= s9.cs_next_var /\
      sa.cs_next_id <= s9.cs_next_id /\
      cs_extends s9 s10 /\ cs_extends s10 sb /\
      s10.cs_next_var <= sb.cs_next_var /\
      fn_has_code s9 s10 func /\ fn_has_code s10 s11 func /\
      (~block_is_terminated s10 ==>
       sb.cs_current_bb = xl /\ sb.cs_current_insts = [])
Proof
  rpt gen_tac >> strip_tac >>
  drule if_compile_chain >>
  disch_then (qx_choosel_then [`op`, `s1`, `s2`, `s3`, `s4`, `s5`, `s6`,
    `s7`, `s8`, `s9`, `s10`, `s11`, `tl`, `el`, `xl`, `x5`, `x8`]
    strip_assume_tac) >>
  drule (CONJUNCT2 compile_expr_grows) >> strip_tac >>
  imp_res_tac fresh_label_props >> imp_res_tac cs_extends_fresh_label >>
  imp_res_tac new_block_props >> imp_res_tac cs_extends_new_block >>
  imp_res_tac if_arm_growth >> imp_res_tac if_jump_growth >>
  drule emit_inst_extends >> strip_tac >>
  drule if_emit_extends >> strip_tac >>
  `cs_extends s11 sb /\ s11.cs_next_var = sb.cs_next_var /\
   (~block_is_terminated s7 \/ ~block_is_terminated s10 ==>
    sb.cs_current_bb = xl /\ sb.cs_current_insts = [])` by
    (irule if_exit_block_growth >> metis_tac[]) >>
  `cs_extends sa s2` by extends_via `s1` >>
  `cs_extends sa s3` by extends_via `s2` >>
  `cs_extends sa s4` by extends_via `s3` >>
  `cs_extends sa s5` by extends_via `s4` >>
  `cs_extends sa s6` by extends_via `s5` >>
  `cs_extends sa s7` by extends_via `s6` >>
  `cs_extends sa s8` by extends_via `s7` >>
  `cs_extends sa s9` by extends_via `s8` >>
  `cs_extends sa s10` by extends_via `s9` >>
  `cs_extends s10 sb` by extends_via `s11` >>
  `cs_extends s9 sb` by extends_via `s10` >>
  `cs_extends s8 sb` by extends_via `s9` >>
  `cs_extends s7 sb` by extends_via `s8` >>
  `cs_extends s6 sb` by extends_via `s7` >>
  `cs_extends s5 sb` by extends_via `s6` >>
  `cs_extends s4 sb` by extends_via `s5` >>
  `cs_extends s3 sb` by extends_via `s4` >>
  `cs_extends s2 sb` by extends_via `s3` >>
  `cs_extends s1 sb` by extends_via `s2` >>
  `sa.cs_next_var <= sb.cs_next_var /\
   sa.cs_next_var <= s6.cs_next_var /\ sa.cs_next_var <= s9.cs_next_var /\
   s7.cs_next_var <= sb.cs_next_var /\ s10.cs_next_var <= sb.cs_next_var /\
   sa.cs_next_id <= s6.cs_next_id /\ sa.cs_next_id <= s9.cs_next_id` by decide_tac >>
  `fn_has_code sa s1 func` by code_between >>
  `fn_has_code s4 s5 func` by code_between >>
  `fn_has_code s6 s7 func` by code_between >>
  `fn_has_code s7 s8 func` by code_between >>
  `fn_has_code s9 s10 func` by code_between >>
  `fn_has_code s10 s11 func` by code_between >>
  qexistsl_tac [`op`, `s1`, `s2`, `s3`, `s4`, `s5`, `s6`, `s7`, `s8`, `s9`,
                `s10`, `s11`, `tl`, `el`, `xl`, `x5`, `x8`] >>
  simp[]
QED

Theorem if_stmt_env_compile[local]:
  stmt_env cenv lctx ty (If c yes no) sa = (cenv', sb) <=>
  cenv' = cenv /\ compile_stmt cenv lctx ty (If c yes no) sa = ((), sb)
Proof
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_stmt cenv lctx ty (If c yes no) sa` >> simp[oneTheory.one] >>
  metis_tac[]
QED

Theorem if_paired_arms_env[local]:
  gas_shadow_state a sa /\
  compile_stmts cenv lctx ty ss a = ((), b) /\
  compile_stmts (gas_shadow_env T cenv) lctx ty (MAP gas_shadow_stmt ss) sa = ((), sb) ==>
  ?cenvb. stmts_env cenv lctx ty ss a = (cenvb, b) /\
    stmts_env (gas_shadow_env T cenv) lctx ty (MAP gas_shadow_stmt ss) sa =
      (gas_shadow_env T cenvb, sb) /\ gas_shadow_state b sb
Proof
  strip_tac >>
  qspecl_then [`ss`, `cenv`, `lctx`, `ty`]
    (mp_tac o REWRITE_RULE [gas_shadow_compiles_env_def])
    (Q.INST [`sd` |-> `T`] gas_shadow_stmts_env_env) >>
  disch_then (qspecl_then [`a`, `sa`] mp_tac) >>
  full_simp_tac std_ss [compile_stmts_env, pairTheory.PAIR_EQ] >>
  metis_tac[pairTheory.PAIR]
QED

Theorem if_paired_intervals_mods:
  !cenv cenv' lctx ty c yes no sa sb ta tb func sfunc.
    stmt_env cenv lctx ty (If c yes no) sa = (cenv', sb) /\
    stmt_env (gas_shadow_env T cenv) lctx ty (gas_shadow_stmt (If c yes no)) ta =
      (gas_shadow_env T cenv', tb) /\
    gas_shadow_state sa ta /\ fn_has_code sa sb func /\ fn_has_code ta tb sfunc ==>
    cenv' = cenv /\
    ?op cond scond pre post tl el xl.
      lower_value compile_expr cenv (BaseT BoolT) c sa = (op, cond) /\
      lower_value compile_expr (gas_shadow_env T cenv) (BaseT BoolT) (gas_shadow_expr c) ta =
        (op, scond) /\
      gas_shadow_state cond scond /\
      fn_has_code sa cond func /\ fn_has_code ta scond sfunc /\
      cs_extends sa cond /\ sa.cs_next_var <= cond.cs_next_var /\
      sa.cs_next_var <= sb.cs_next_var /\
      pre.cs_current_bb = cond.cs_current_bb /\
      pre.cs_current_insts = cond.cs_current_insts /\
      emit_inst JNZ [op; Label tl; Label el] [] pre = ((), post) /\
      fn_has_code pre post func /\
      !b. ?entry last after sentry slast cenvb.
        stmts_env cenv lctx ty (if b then yes else no) entry = (cenvb, last) /\
        stmts_env (gas_shadow_env T cenv) lctx ty (MAP gas_shadow_stmt (if b then yes else no)) sentry =
          (gas_shadow_env T cenvb, slast) /\
        gas_shadow_state entry sentry /\ gas_shadow_state last slast /\
        fn_has_code sentry slast sfunc /\
        entry.cs_current_bb = (if b then tl else el) /\
        entry.cs_current_insts = [] /\
        cs_extends sa entry /\ sa.cs_next_var <= entry.cs_next_var /\
        sa.cs_next_id <= entry.cs_next_id /\
        cs_extends entry last /\ cs_extends last sb /\
        last.cs_next_var <= sb.cs_next_var /\
        fn_has_code entry last func /\ fn_has_code last after func /\
        (if block_is_terminated last then after = last
         else emit_inst JMP [Label xl] [] last = ((), after)) /\
        (~block_is_terminated last ==>
         sb.cs_current_bb = xl /\ sb.cs_current_insts = [])
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ (If _ _ _) _ = _`
    (strip_assume_tac o REWRITE_RULE [if_stmt_env_compile]) >>
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _`
    (strip_assume_tac o REWRITE_RULE [gas_shadow_stmt_def, if_stmt_env_compile]) >>
  simp[] >>
  qpat_assum `compile_stmt _ _ _ (If c _ _) sa = _`
    (mp_then Any drule_all if_chain_intervals) >>
  disch_then (qx_choosel_then [`op`, `s1`, `s2`, `s3`, `s4`, `s5`, `s6`,
    `s7`, `s8`, `s9`, `s10`, `s11`, `tl`, `el`, `xl`, `x5`, `x8`]
    strip_assume_tac) >>
  qpat_assum `compile_stmt _ _ _ (If (gas_shadow_expr c) _ _) ta = _`
    (mp_then Any drule_all if_chain_intervals) >>
  disch_then (qx_choosel_then [`op'`, `t1`, `t2`, `t3`, `t4`, `t5`, `t6`,
    `t7`, `t8`, `t9`, `t10`, `t11`, `tl'`, `el'`, `xl'`, `y5`, `y8`]
    strip_assume_tac) >>
  `op' = op /\ gas_shadow_state s1 t1` by
    metis_tac[gas_shadow_step, gas_shadow_stmt_lower_value_env] >>
  `tl' = tl /\ gas_shadow_state s2 t2` by
    metis_tac[gas_shadow_step, gas_shadow_compiles_fresh_label] >>
  `el' = el /\ gas_shadow_state s3 t3` by
    metis_tac[gas_shadow_step, gas_shadow_compiles_fresh_label] >>
  `xl' = xl /\ gas_shadow_state s4 t4` by
    metis_tac[gas_shadow_step, gas_shadow_compiles_fresh_label] >>
  qpat_x_assum `op' = op` SUBST_ALL_TAC >>
  qpat_x_assum `tl' = tl` SUBST_ALL_TAC >>
  qpat_x_assum `el' = el` SUBST_ALL_TAC >>
  qpat_x_assum `xl' = xl` SUBST_ALL_TAC >>
  `gas_shadow_state s5 t5` by
    metis_tac[gas_shadow_step, gas_shadow_compiles_emit_inst] >>
  `gas_shadow_state s6 t6` by
    metis_tac[gas_shadow_step, gas_shadow_compiles_new_block] >>
  qpat_assum `compile_stmts _ _ _ yes s6 = _`
    (mp_then Any drule_all if_paired_arms_env) >>
  disch_then (qx_choose_then `env_yes` strip_assume_tac) >>
  `block_is_terminated t7 = block_is_terminated s7` by
    metis_tac[gas_shadow_terminated] >>
  `gas_shadow_state s8 t8` by
    (Cases_on `block_is_terminated s7` >> gvs[] >>
     metis_tac[gas_shadow_step, gas_shadow_compiles_emit_inst]) >>
  `gas_shadow_state s9 t9` by
    metis_tac[gas_shadow_step, gas_shadow_compiles_new_block] >>
  qpat_assum `compile_stmts _ _ _ no s9 = _`
    (mp_then Any drule_all if_paired_arms_env) >>
  disch_then (qx_choose_then `env_no` strip_assume_tac) >>
  qexistsl_tac [`op`, `s1`, `t1`, `s4`, `s5`, `tl`, `el`, `xl`] >>
  simp[] >> gen_tac >> Cases_on `b` >> simp[]
  >- (qexistsl_tac [`s6`, `s7`, `s8`, `t6`, `t7`, `env_yes`] >> simp[]) >>
  qexistsl_tac [`s9`, `s10`, `s11`, `t9`, `t10`, `env_no`] >> simp[]
QED
