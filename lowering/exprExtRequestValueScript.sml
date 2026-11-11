Theory exprExtRequestValue
Ancestors
  exprExtRequestKwargs exprExtRequestRetained loweringPosts exprLowering
  vyperTypeExtCallSoundness vyperInterpreter vyperTyping vyperValue
  valueEncoding venomState integer_word words integer list option

Theorem extrequest_value_static:
  extrequest_kwarg_selection cenv cx ret EKValue
    (ext_call_kwarg EKValue opts vs)
    (OPTION_MAP (\op. (op,dty)) compiled) ee sp t ==>
  (stat <=>
    (if stat then NONE else case ext_call_kwarg EKValue opts vs of
       NONE => SOME 0 | SOME v => dest_NumV v) = NONE)
Proof
  Cases_on `stat` >> simp[] >>
  Cases_on `compiled` >> Cases_on `ext_call_kwarg EKValue opts vs` >>
  simp[extrequest_kwarg_selection_def] >> strip_tac >>
  fs[extrequest_retained_value_def, evaluate_type_def] >>
  Cases_on `x'` >> fs[value_has_type_def, dest_NumV_def, INT_NOT_LT]
QED

Theorem extrequest_value_operand:
  ext_call_opts_ok stat opts /\
  extrequest_kwarg_selection cenv cx ret EKValue
    (ext_call_kwarg EKValue opts vs)
    (OPTION_MAP (\op. (op,dty)) compiled) ee sp t ==>
  ?w. eval_operand (case compiled of NONE => Lit 0w | SOME op => op) t = SOME w /\
    w2n w = (case (if stat then NONE else case ext_call_kwarg EKValue opts vs of
       NONE => SOME 0 | SOME v => dest_NumV v) of NONE => 0 | SOME n => n)
Proof
  rpt strip_tac >>
  `stat ==> ext_call_kwarg EKValue opts vs = NONE` by
    (fs[ext_call_opts_ok_def] >> strip_tac >>
     irule (INST_TYPE [alpha |-> ``:ext_call_kw``, beta |-> ``:value``]
       (GEN_ALL ext_call_kwarg_not_mem)) >> simp[]) >>
  Cases_on `compiled`
  >- (gvs[extrequest_kwarg_selection_def, eval_operand_def] >>
      Cases_on `stat` >> simp[]) >>
  Cases_on `ext_call_kwarg EKValue opts vs` >>
  gvs[extrequest_kwarg_selection_def] >>
  fs[extrequest_retained_value_def, expr_val_rel_def, evaluate_type_def,
     compileEnvTheory.is_word_type_def] >>
  Cases_on `x'` >> gvs[value_has_type_def, dest_NumV_def, INT_NOT_LT,
    typed_val_to_w256_def, val_to_w256_def] >>
  `~(i < 0)` by simp[INT_NOT_LT] >>
  simp[integer_wordTheory.i2w_def, wordsTheory.w2n_n2w,
       wordsTheory.dimword_def]
QED
