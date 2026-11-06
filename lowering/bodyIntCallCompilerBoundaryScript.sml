Theory bodyIntCallCompilerBoundary
Ancestors
  exprLoweringProps stmtLoweringMono fragExec compileEnv exprLowering

Theorem compiler_fragment_boundary:
  ci_mono sa si /\ ci_mono si sj /\ ci_mono sj sb /\
  fn_has_code sa sb func /\ local_ptrs_reserved ce sa ==>
  fn_has_code si sj func /\ local_ptrs_reserved ce si /\
  sa.cs_next_var <= si.cs_next_var
Proof
  simp[ci_mono_def] >> strip_tac >>
  conj_tac >- (irule fn_has_code_mid >> goal_assum (drule_at Any) >>
    goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  irule local_ptrs_reserved_next_var >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem intcall_compiler_prefix:
  compile_multi_vvs compile_expr ce es sa = (vals,s1) /\
  ci_mono s1 s2 /\
  compile_stage_intcall_args ce vals flags tys s2 = (ops,si) /\
  local_ptrs_reserved ce sa ==>
  cs_extends sa si /\ local_ptrs_reserved ce si /\
  sa.cs_next_var <= si.cs_next_var /\ s2.cs_next_var <= si.cs_next_var
Proof
  strip_tac >>
  `ci_mono sa s1` by
    (qspecl_then [`compile_expr`,`ce`,`es`,`sa`] mp_tac
       ci_mono_compile_multi_vvs >>
     simp[cj 1 ci_mono_compile_expr_sa]) >>
  `ci_mono s2 si` by
    (mp_tac (Q.SPECL [`ce`,`vals`,`flags`,`tys`,`s2`]
      ci_mono_compile_stage_intcall_args) >> simp[]) >>
  fs[ci_mono_def] >>
  `sa.cs_next_var <= si.cs_next_var` by decide_tac >>
  conj_tac >- metis_tac[cs_extends_trans] >>
  simp[] >> irule local_ptrs_reserved_next_var >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem intcall_void_compiler_boundary:
  compile_multi_vvs compile_expr ce es sa = (vals,s1) /\
  ci_mono s1 s2 /\
  compile_stage_intcall_args ce vals flags tys s2 = (args,si) /\
  emit_void opc ops si = (u,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved ce sa ==>
  fn_has_code si sb func
Proof
  strip_tac >> drule_all intcall_compiler_prefix >> strip_tac >>
  `ci_mono si sb` by
    (qspecl_then [`opc`,`ops`,`si`] mp_tac ci_mono_emit_void >> simp[]) >>
  fs[ci_mono_def] >> drule_all fn_has_code_split >> simp[]
QED

Theorem intcall_stack_compiler_boundary:
  compile_multi_vvs compile_expr ce es sa = (vals,s1) /\
  ci_mono s1 s2 /\
  compile_stage_intcall_args ce vals flags tys s2 = (args,si) /\
  emit_multi_op opc ops n si = (results,sj) /\
  store_multi_results buf results off sj = (u,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved ce sa ==>
  fn_has_code si sj func /\ fn_has_code sj sb func /\
  local_ptrs_reserved ce si /\
  sa.cs_next_var <= si.cs_next_var /\ s2.cs_next_var <= si.cs_next_var
Proof
  strip_tac >> drule_all intcall_compiler_prefix >> strip_tac >>
  `ci_mono si sj` by
    (qspecl_then [`opc`,`ops`,`n`,`si`] mp_tac ci_mono_emit_multi_op >> simp[]) >>
  `ci_mono sj sb` by
    (qspecl_then [`buf`,`results`,`off`,`sj`] mp_tac ci_mono_store_multi_results >> simp[]) >>
  fs[ci_mono_def] >>
  `cs_extends si sb` by metis_tac[cs_extends_trans] >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all fn_has_code_split >> simp[]
QED
