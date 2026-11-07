(* Compiler boundaries for sequential bytestring digest operands. *)
Theory bodyMemBopHeldOperand
Ancestors
  bodyMemBopHeldHash bodyMemBopHeldFacts exprBopLowering
  exprLoweringProps exprOperandVar exprLowering compileEnv emitHelper
  list rich_list fragExec
Libs
  pairLib

Theorem held_lower_value_compare:
  (bop = Eq \/ bop = NotEq) /\
  is_bytestring_type (expr_type e1) /\ expr_type e2 = expr_type e1 ==>
  lower_value compile_expr cenv ty (Builtin ann (Bop bop) [e1;e2]) sa =
  (let (h1,s1) =
     (case bytestring_literal_hash e1 of
        SOME h => (Lit h,sa)
      | NONE => let (p,sm) = lower_value compile_expr cenv (expr_type e1) e1 sa in
                compile_bytestring_hash p sm) in
   let (h2,s2) =
     (case bytestring_literal_hash e2 of
        SOME h => (Lit h,s1)
      | NONE => let (p,sm) = lower_value compile_expr cenv (expr_type e2) e2 s1 in
                compile_bytestring_hash p sm) in
   if bop = Eq then emit_op EQ [h1;h2] s2
   else let (q,sm) = emit_op EQ [h1;h2] s2 in emit_op ISZERO [q] sm)
Proof
  strip_tac >>
  simp[Once lower_value_def, comp_bind_def, compile_expr_bop] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def, lower_value_child_call] >>
  Cases_on `bytestring_literal_hash e1` >>
  Cases_on `bytestring_literal_hash e2` >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[as_stack_val_pair, unwrap_value_def, comp_return_def] >>
  RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV ETA_CONV)) >> gvs[]
QED

Theorem held_hash_compiler:
  compile_bytestring_hash p sa = (h,sb) ==>
  ci_mono sa sb /\ (!z. h = Var z ==> not_fresh_at sb z)
Proof
  simp[compile_bytestring_hash_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def, emit_op_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  simp[ci_mono_def, cs_extends_def, not_fresh_at_def,
       rich_listTheory.IS_PREFIX_APPEND, GSYM APPEND_ASSOC]
QED

Theorem held_digest_operand_compiler:
  (case bytestring_literal_hash e of
     SOME w => (Lit w,sa)
   | NONE => let (p,sm) = lower_value compile_expr cenv (expr_type e) e sa in
             compile_bytestring_hash p sm) = (h,sb) ==>
  ci_mono sa sb /\ (!z. h = Var z ==> not_fresh_at sb z) /\
  (local_ptrs_reserved cenv sa ==> local_ptrs_reserved cenv sb)
Proof
  Cases_on `bytestring_literal_hash e`
  >- (simp[] >> pairarg_tac >> strip_tac >> gvs[] >>
      drule held_hash_compiler >> strip_tac >>
      `ci_mono sa (SND (lower_value compile_expr cenv (expr_type e) e sa))` by
        (irule ci_mono_lower_value_cfn >> simp[compile_expr_ci_mono]) >>
      gvs[] >>
      `ci_mono sa sb` by
        (fs[ci_mono_def] >> metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]) >>
      metis_tac[compiler_ci_mono_reserved]) >>
  simp[] >> strip_tac >> gvs[] >>
  simp[ci_mono_def, cs_extends_refl]
QED

Theorem held_compare_tail_compiler:
  (if bop = Eq then emit_op EQ [h1;h2] sa
   else let (q,sm) = emit_op EQ [h1;h2] sa in emit_op ISZERO [q] sm) = (op,sb) ==>
  ci_mono sa sb
Proof
  Cases_on `bop = Eq` >> simp[]
  >- metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  `ci_mono sa sm` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `ci_mono sm sb` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  fs[ci_mono_def] >> metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem held_digest_runtime_cut:
  lower_value compile_expr cenv (expr_type e) e sa = (p,sm) /\
  compile_bytestring_hash p sm = (h,sb) /\
  cs_extends start sa /\ cs_extends sb last_st /\
  fn_has_code start last_st func /\ local_ptrs_reserved cenv sa ==>
  ci_mono sa sm /\ ci_mono sm sb /\
  local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sb /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  (!z. h = Var z ==> not_fresh_at sb z)
Proof
  strip_tac >>
  `ci_mono sa (SND (lower_value compile_expr cenv (expr_type e) e sa))` by
    (irule ci_mono_lower_value_cfn >> simp[compile_expr_ci_mono]) >>
  gvs[] >> drule held_hash_compiler >> strip_tac >>
  `local_ptrs_reserved cenv sm` by metis_tac[compiler_ci_mono_reserved] >>
  `local_ptrs_reserved cenv sb` by metis_tac[compiler_ci_mono_reserved] >>
  fs[ci_mono_def] >> metis_tac[fn_has_code_mid, cs_extends_trans]
QED

Theorem held_compare_cuts:
  (case bytestring_literal_hash e1 of
     SOME w => (Lit w,sa)
   | NONE => let (p,sm) = lower_value compile_expr cenv (expr_type e1) e1 sa in
             compile_bytestring_hash p sm) = (h1,s1) /\
  (case bytestring_literal_hash e2 of
     SOME w => (Lit w,s1)
   | NONE => let (p,sm) = lower_value compile_expr cenv (expr_type e2) e2 s1 in
             compile_bytestring_hash p sm) = (h2,s2) /\
  (if bop = Eq then emit_op EQ [h1;h2] s2
   else let (q,sm) = emit_op EQ [h1;h2] s2 in emit_op ISZERO [q] sm) = (op,sb) /\
  local_ptrs_reserved cenv sa /\ fn_has_code sa sb func ==>
  ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 sb /\
  local_ptrs_reserved cenv s1 /\ local_ptrs_reserved cenv s2 /\
  fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\ fn_has_code s2 sb func /\
  (!z. h1 = Var z ==> not_fresh_at s1 z) /\
  (!z. h2 = Var z ==> not_fresh_at s2 z)
Proof
  strip_tac >>
  drule_all held_digest_operand_compiler >> strip_tac >>
  drule_all held_compare_tail_compiler >> strip_tac >>
  `ci_mono sa s1 /\ (!z. h1 = Var z ==> not_fresh_at s1 z) /\
   local_ptrs_reserved cenv s1` by
    metis_tac[held_digest_operand_compiler] >>
  `ci_mono s1 s2 /\ (!z. h2 = Var z ==> not_fresh_at s2 z) /\
   local_ptrs_reserved cenv s2` by
    metis_tac[held_digest_operand_compiler] >>
  fs[ci_mono_def] >> metis_tac[fn_has_code_split, cs_extends_trans]
QED
