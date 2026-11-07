(* Compiler-only framing for the Convert operand/suffix boundary. *)
Theory bodyPtrTypeBuiltinsConvertFrame
Ancestors exprLowering exprLoweringProps compileEnv builtinBytes
  emitHelper emitHelperProps bodyPtrTypeBuiltinsConvert vyperAST

Theorem convert_widen_copy_ci_mono:
  !d v sz sa. ci_mono sa (SND (compile_bytestring_widen_copy d v sz sa))
Proof
  rw[compile_bytestring_widen_copy_def] >>
  irule ci_mono_bind >> simp[ci_mono_compile_alloc_buffer] >> rpt gen_tac >>
  irule ci_mono_ignore_bind >>
  simp[ci_mono_compile_copy_memory, ci_mono_comp_return]
QED

Theorem convert_load_bytestring_ci_mono:
  !v shift_opc sa. ci_mono sa (SND (load_bytestring_as_word v shift_opc sa))
Proof
  rpt gen_tac >> Cases_on `shift_opc = SAR` >> (
  simp_tac pure_ss [load_bytestring_as_word_def] >>
  asm_rewrite_tac[] >> BETA_TAC >>
  ntac 3 (ho_match_mp_tac ci_mono_bind >>
          conj_tac >- simp[ci_mono_emit_op] >> rpt gen_tac) >>
  ho_match_mp_tac ci_mono_bind >> conj_tac
  >- (rpt gen_tac >>
      rpt (ho_match_mp_tac ci_mono_bind >>
           conj_tac >- simp[ci_mono_emit_op] >> rpt gen_tac) >>
      simp[ci_mono_emit_op, ci_mono_comp_return]) >>
  rpt gen_tac >>
  ntac 3 (ho_match_mp_tac ci_mono_bind >>
          conj_tac >- simp[ci_mono_emit_op] >> rpt gen_tac) >>
  simp[ci_mono_comp_return])
QED

Theorem convert_type_ci_mono:
  !v conv_op sa. ci_mono sa (SND (compile_type_convert v conv_op sa))
Proof
  rpt gen_tac >> Cases_on `conv_op` >>
  rw[compile_type_convert_def] >>
  simp[ci_mono_bind, ci_mono_ignore_bind, ci_mono_emit_op, ci_mono_emit_void,
       ci_mono_comp_return, ci_mono_compile_alloc_buffer,
       convert_load_bytestring_ci_mono, ci_mono_compile_int_clamp] >>
  pure_rewrite_tac[comp_ignore_bind_def] >>
  rpt (ho_match_mp_tac ci_mono_bind >> conj_tac
       >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return,
               convert_load_bytestring_ci_mono, ci_mono_compile_int_clamp] >>
       rpt gen_tac >> rw[]) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return,
       convert_load_bytestring_ci_mono, ci_mono_compile_int_clamp] >>
  PairCases_on `av` >> rw[] >>
  rpt (ho_match_mp_tac ci_mono_bind >> conj_tac
       >- simp[ci_mono_emit_op, ci_mono_emit_void] >> rpt gen_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return,
       ci_mono_compile_int_clamp]
QED

Theorem convert_as_stack_snd[simp]:
  !ann p. SND (as_stack_val ann p) = SND p
Proof
  Cases_on `p` >> simp[as_stack_val_def]
QED

Theorem convert_dispatch_suffix_ci_mono:
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) ==>
  ci_mono sm (SND (compile_type_builtin_dispatch_body compile_expr cenv ann ty Convert typ [e] sa))
Proof
  strip_tac >> Cases_on `typ` >> rw[compile_type_builtin_dispatch_body_def] >>
  simp[convert_type_ci_mono, convert_widen_copy_ci_mono, ci_mono_refl]
QED

Theorem convert_as_stack_shape:
  !ann p vv sb. as_stack_val ann p = (vv,sb) ==> ?op. vv = StackValue ann op
Proof
  Cases_on `p` >> simp[as_stack_val_def] >> metis_tac[]
QED

Theorem convert_dispatch_stack_shape:
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_type_builtin_dispatch_body compile_expr cenv ann ty Convert typ [e] sa = (vv,sb) ==>
  ?op. vv = StackValue ann op
Proof
  strip_tac >> Cases_on `typ` >>
  gvs[compile_type_builtin_dispatch_body_def, AllCaseEqs()] >>
  metis_tac[convert_as_stack_shape]
QED

Theorem convert_compiler_split:
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_type_builtin_dispatch_body compile_expr cenv ann ty Convert typ [e] sa = (vv,sb) ==>
  (?op. vv = StackValue ann op) /\ ci_mono sa sm /\ ci_mono sm sb
Proof
  strip_tac >> conj_tac
  >- metis_tac[convert_dispatch_stack_shape] >>
  conj_tac
  >- (`ci_mono sa (SND (lower_value compile_expr cenv (expr_type e) e sa))` by
        (irule ci_mono_lower_value_cfn >> simp[compile_expr_ci_mono]) >>
      metis_tac[pairTheory.SND]) >>
  drule convert_dispatch_suffix_ci_mono >>
  disch_then (qspecl_then [`typ`,`ty`,`ann`] mp_tac) >> simp[]
QED

Theorem convert_compiler_code_split:
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_type_builtin_dispatch_body compile_expr cenv ann ty Convert typ [e] sa = (vv,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) ==>
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!z. x = Var z ==> not_fresh_at sm z) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p)
Proof
  strip_tac >> drule_all convert_compiler_split >> strip_tac >>
  fs[ci_mono_def] >>
  drule_all fragExecTheory.fn_has_code_split >> strip_tac >>
  `!z. x = Var z ==> not_fresh_at sm z` by
    metis_tac[exprOperandVarTheory.compile_lower_value_var] >>
  metis_tac[local_ptrs_reserved_next_var, freshWritesTheory.not_fresh_at_mono]
QED

Theorem convert_compile_entry:
  compile_expr cenv ty (TypeBuiltin ann Convert typ [e]) sa = (vv,sb) ==>
  ?x sm op.
    lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
    compile_type_builtin_dispatch_body compile_expr cenv ann ty Convert typ [e] sa =
      (StackValue ann op,sb) /\ vv = StackValue ann op /\
    ci_mono sa sm /\ ci_mono sm sb
Proof
  strip_tac >>
  `compile_type_builtin_dispatch_body compile_expr cenv ann ty Convert typ [e] sa = (vv,sb)` by
    (qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
     pure_once_rewrite_tac[compile_expr_def] >>
     simp[compile_type_builtin_dispatch_component_eq,
          lowered_value_type_def, expr_type_def, lower_value_def,
          comp_bind_def, exprCallBoundsTheory.expr_child_callback_def,
          compile_type_builtin_dispatch_body_def]) >>
  Cases_on `lower_value compile_expr cenv (expr_type e) e sa` >>
  rename1 `lower_value compile_expr cenv (expr_type e) e sa = (x,sm)` >>
  drule_all convert_compiler_split >> strip_tac >>
  qexistsl_tac [`x`,`sm`,`op`] >> simp[]
QED

Theorem convert_lower_entry:
  lower_value compile_expr cenv ty (TypeBuiltin ann Convert typ [e]) sa = (op,sb) ==>
  ?x sm.
    lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
    compile_type_builtin_dispatch_body compile_expr cenv ann ty Convert typ [e] sa =
      (StackValue ann op,sb) /\ ci_mono sa sm /\ ci_mono sm sb
Proof
  strip_tac >> Cases_on `compile_expr cenv ty (TypeBuiltin ann Convert typ [e]) sa` >>
  drule convert_compile_entry >> strip_tac >>
  gvs[lower_value_def, comp_bind_def, unwrap_value_def, comp_return_def] >>
  qexistsl_tac [`x`,`sm`] >> simp[]
QED
