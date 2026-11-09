(* Compiler and resource boundaries for the pointer Concat proof. *)
Theory bodyPtrBytestringBuiltinsConcatCompile
Ancestors
  bodyPtrBytestringBuiltinsConcatPrefix bodyPtrBytestringBuiltinsConcatArgs
  exprSimConcatResult exprLoweringProps exprLowering compileEnv
  fragExec context emitHelper emitHelperProps loweringPosts words list pair arithmetic

Theorem concat_ptr_compile_cuts:
  compile_expr cenv ty (Builtin ann (Concat n) args) sa = (vv,sb) /\
  fn_has_code sa sb fn ==>
  ?buf s1 data s2 ob s3 s4 s5 fo s6.
    compile_alloc_buffer (concat_alloc_size (MAP expr_type args)) sa = (buf,s1) /\
    emit_op ADD [buf.buf_operand; Lit 32w] s1 = (data,s2) /\
    compile_alloc_buffer 64 s2 = (ob,s3) /\
    emit_void MSTORE [ob.buf_operand; Lit 0w] s3 = ((),s4) /\
    compile_concat compile_expr cenv args data
      (MAP (\e. if is_bytestring_type (expr_type e) then (T,0:num)
         else case expr_type e of BaseT (BytesT (Fixed m)) => (F,m)
              | _ => (F,32:num)) args) ob.buf_operand s4 = ((),s5) /\
    emit_op MLOAD [ob.buf_operand] s5 = (fo,s6) /\
    emit_void MSTORE [buf.buf_operand; fo] s6 = ((),sb) /\
    vv = LocatedValue ann (base_ptr buf) /\
    fn_has_code sa s4 fn /\ fn_has_code s4 s5 fn /\
    fn_has_code s5 s6 fn /\ fn_has_code s6 sb fn /\
    ci_mono sa s4 /\ ci_mono s4 s5 /\ ci_mono s5 s6 /\ ci_mono s6 sb
Proof
  strip_tac >> drule concat_compile_shape >> strip_tac >>
  Cases_on `u` >> Cases_on `u'` >>
  `ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\ ci_mono s3 s4 /\
   ci_mono s5 s6 /\ ci_mono s6 sb` by
    metis_tac[ci_mono_compile_alloc_buffer, ci_mono_emit_op, ci_mono_emit_void, SND] >>
  `!ce ty e st. ci_mono st (SND (compile_expr ce ty e st))` by
    simp[compile_expr_ci_mono] >>
  `ci_mono s4 s5` by
    (qpat_assum `compile_concat _ _ _ _ _ _ _ = _` mp_tac >>
     simp[] >> metis_tac[ci_mono_compile_concat_cfn, SND]) >>
  `ci_mono sa s4` by (fs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  `cs_extends s4 sb /\ cs_extends s5 sb` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sa s4 fn /\ fn_has_code s4 sb fn` by
    metis_tac[fn_has_code_split, ci_mono_def] >>
  `fn_has_code s4 s5 fn /\ fn_has_code s5 sb fn` by
    metis_tac[fn_has_code_split, ci_mono_def] >>
  `fn_has_code s5 s6 fn /\ fn_has_code s6 sb fn` by
    metis_tac[fn_has_code_split, ci_mono_def] >>
  qexistsl_tac [`buf`,`s1`,`d`,`s2`,`ob`,`s3`,`s4`,`s5`,`fo`,`s6`] >>
  fs[]
QED
