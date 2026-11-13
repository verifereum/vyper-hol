(* Concrete compiler cut for a nonword default keyword. *)
Theory extcallKeywordStagesMemory
Ancestors
  exprLowering exprLoweringProps exprOperandVar compileEnv fragExec

Theorem extcall_nonword_keyword_stages:
  compile_ext_call_kwarg compile_expr ce rt EKDefault e sa = ((op,lt),sb) /\
  ~is_word_type rt /\ fn_has_code sa sb func /\
  local_ptrs_reserved ce sa ==>
  ?vv sm. lt = lowered_value_type ce e /\
    compile_expr ce (expr_type e) e sa = (vv,sm) /\
    compile_materialize_vv ce lt vv sm = (op,sb) /\
    ci_mono sa sm /\ ci_mono sm sb /\
    fn_has_code sa sm func /\ fn_has_code sm sb func /\
    local_ptrs_reserved ce sm /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sm x)
Proof
  strip_tac >>
  qpat_x_assum `compile_ext_call_kwarg _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_ext_call_kwarg_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_expr ce (expr_type e) e sa = (vv,sm)` >>
  `ci_mono sa sm /\ ci_mono sm sb` by
    (mp_tac (cj 1 compile_expr_ci_mono) >>
     mp_tac ci_mono_compile_materialize_vv >> metis_tac[pairTheory.SND]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split]) >>
  `local_ptrs_reserved ce sm` by
    (fs[ci_mono_def] >> metis_tac[local_ptrs_reserved_next_var]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    metis_tac[cj 1 compiler_compile_var] >>
  gvs[]
QED
