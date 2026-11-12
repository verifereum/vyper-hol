(* Compiler-only interfaces shared by reason-bearing statements. *)
Theory reasonCompilerProps
Ancestors
  revertReasonLayout exprLoweringProps stmtLowering exprLowering compileEnv
  context emitHelper emitHelperProps fragExec loweringPosts stmtSimDefs
  localPtrsProps loweringSlice list rich_list arithmetic literalCapacityPtr exprSimUnwrap

Theorem compile_revert_reason_extends:
  compile_revert_with_reason cenv vv mt ms sa = ((),sb) ==> cs_extends sa sb
Proof
  strip_tac >> drule compile_revert_reason_chunks >> strip_tac >>
  metis_tac[cs_extends_trans]
QED

Theorem compile_reason_message_cases:
  compile_reason_message cenv r sa = (vv,sb) ==>
  (?mx str buf. r = Literal (BaseT (StringT mx)) (StringL str) /\
    compile_bytelike_literal (MAP (n2w o ORD) str) mx sa = (buf,sb) /\
    vv = LocatedValue (BaseT (StringT (LENGTH str))) (base_ptr buf)) \/
  ((!mx str. r <> Literal (BaseT (StringT mx)) (StringL str)) /\
    compile_expr cenv (expr_type r) r sa = (vv,sb))
Proof
  Cases_on `?mx str. r = Literal (BaseT (StringT mx)) (StringL str)`
  >- (gvs[compile_reason_message_def, comp_bind_def, comp_return_def,
          AllCaseEqs()] >> pairarg_tac >> gvs[]) >>
  `compile_reason_message cenv r = compile_expr cenv (expr_type r) r` by
    (Cases_on `r` >> simp[compile_reason_message_def] >>
     rename1 `Literal t l` >> Cases_on `l` >> simp[compile_reason_message_def] >>
     Cases_on `t` >> gvs[compile_reason_message_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> gvs[compile_reason_message_def]) >>
  simp[] >> metis_tac[]
QED

Theorem compile_raise_reason_parts:
  stmt_env cenv lctx ty (Raise (RaiseReason r)) sa = (cenv',sb) ==>
  cenv' = cenv /\
  ?vv sm. compile_reason_message cenv r sa = (vv,sm) /\
    compile_revert_with_reason cenv vv (expr_type r)
      (type_memory_bytes cenv (expr_type r)) sm = ((),sb)
Proof
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_reason_message cenv r sa` >> rename1 `_ = (vv,sm)` >> simp[] >>
  Cases_on `compile_revert_with_reason cenv vv (expr_type r)
    (type_memory_bytes cenv (expr_type r)) sm` >>
  simp[] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem compile_reason_message_extends:
  compile_reason_message cenv r sa = (vv,sb) ==> cs_extends sa sb
Proof
  strip_tac >> drule compile_reason_message_cases >> strip_tac
  >- (qspec_then `sa` mp_tac
       (Q.SPECL [`MAP (n2w o ORD) str`,`mx`] ci_mono_compile_bytelike_literal) >>
      gvs[ci_mono_def]) >>
  drule compile_expr_extends >> simp[]
QED

Theorem compile_raise_reason_extends:
  stmt_env cenv lctx ty (Raise (RaiseReason r)) sa = (cenv',sb) ==> cs_extends sa sb
Proof
  strip_tac >> drule compile_raise_reason_parts >> strip_tac >>
  drule compile_reason_message_extends >> strip_tac >>
  drule compile_revert_reason_extends >> metis_tac[cs_extends_trans]
QED

Theorem raise_reason_compiler_code:
  compile_reason_message cenv r sa = (vv,sm) /\
  compile_revert_with_reason cenv vv mt ms sm = ((),sb) /\
  fn_has_code sa sb func ==>
  fn_has_code sa sm func /\ fn_has_code sm sb func
Proof
  strip_tac >> drule compile_reason_message_extends >> strip_tac >>
  drule compile_revert_reason_extends >> strip_tac >>
  drule_all fn_has_code_split >> simp[]
QED

Theorem compile_assert_reason_parts:
  stmt_env cenv lctx ty (Assert e (AssertReason r)) sa = (cenv',sb) ==>
  ?op s1 ok s2 fl s3 s4 entry last.
    cenv' = cenv /\
    lower_value compile_expr cenv (BaseT BoolT) e sa = (op,s1) /\
    fresh_label "assert_ok" s1 = (ok,s2) /\
    fresh_label "assert_fail" s2 = (fl,s3) /\
    emit_inst JNZ [op; Label ok; Label fl] [] s3 = ((),s4) /\
    new_block fl s4 = (s4.cs_current_bb,entry) /\
    stmt_env cenv lctx ty (Raise (RaiseReason r)) entry = (cenv,last) /\
    new_block ok last = (last.cs_current_bb,sb)
Proof
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `lower_value compile_expr cenv (BaseT BoolT) e sa` >>
  rename1 `_ = (op,s1)` >> simp[] >>
  Cases_on `fresh_label "assert_ok" s1` >> rename1 `_ = (ok,s2)` >> simp[] >>
  Cases_on `fresh_label "assert_fail" s2` >> rename1 `_ = (fl,s3)` >> simp[] >>
  Cases_on `emit_inst JNZ [op; Label ok; Label fl] [] s3` >>
  rename1 `_ = (u,s4)` >> Cases_on `u` >> simp[] >>
  Cases_on `new_block fl s4` >> rename1 `_ = (v,entry)` >> simp[] >>
  Cases_on `compile_reason_message cenv r entry` >>
  rename1 `_ = (msg,sm)` >> simp[] >>
  Cases_on `compile_revert_with_reason cenv msg (expr_type r)
    (type_memory_bytes cenv (expr_type r)) sm` >>
  rename1 `_ = (u,last)` >> Cases_on `u` >> simp[] >>
  Cases_on `new_block ok last` >> rename1 `_ = (x,sb1)` >>
  simp[] >> strip_tac >> gvs[] >>
  imp_res_tac new_block_props >> gvs[]
QED

Theorem assert_reason_compiler_code:
  lower_value compile_expr cenv (BaseT BoolT) e sa = (op,s1) /\
  fresh_label "assert_ok" s1 = (ok,s2) /\
  fresh_label "assert_fail" s2 = (fl,s3) /\
  emit_inst JNZ [op; Label ok; Label fl] [] s3 = ((),s4) /\
  new_block fl s4 = (x5,entry) /\
  stmt_env cenv lctx ty (Raise (RaiseReason r)) entry = (cenv,last) /\
  new_block ok last = (x7,sb) /\ fn_has_code sa sb func ==>
  fn_has_code sa s1 func /\ fn_has_code s3 s4 func /\
  fn_has_code entry last func /\
  s3.cs_current_bb = s1.cs_current_bb /\
  s3.cs_current_insts = s1.cs_current_insts /\
  entry.cs_current_bb = fl /\ entry.cs_current_insts = [] /\
  sb.cs_current_bb = ok /\ sb.cs_current_insts = [] /\
  sa.cs_next_var <= entry.cs_next_var
Proof
  strip_tac >> drule (cj 2 compile_expr_grows) >> strip_tac >>
  drule compile_raise_reason_extends >> strip_tac >>
  imp_res_tac fresh_label_props >> imp_res_tac new_block_props >>
  `cs_extends s1 s2 /\ cs_extends s2 s3 /\ cs_extends s3 s4 /\
   cs_extends s4 entry /\ cs_extends last sb` by
    metis_tac[cs_extends_fresh_label, cs_extends_new_block,
              cs_appends_emit_helpers, cs_appends_def] >>
  `s3.cs_next_var = s4.cs_next_var` by
    (qpat_x_assum `emit_inst _ _ _ _ = _` mp_tac >>
     simp[emit_inst_def, comp_bind_def, comp_return_def, fresh_id_def, emit_def] >>
     strip_tac >> gvs[]) >>
  simp[] >>
  metis_tac[fn_has_code_split, fn_has_code_mid, cs_extends_trans,
            cs_extends_refl]
QED
