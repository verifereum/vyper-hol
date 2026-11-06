Theory bodyPtrIfExpAllocCaller
Ancestors
  exprOperandVar exprLoweringProps exprLowering compileEnv context fragExec
  vyperEvalExprPreservesScopesDom vyperState vyperValue finite_map exprSimUnwrap

Theorem ifexp_selected_arm_allocation_premises:
  compile_expr cenv (expr_type e) e sa = (vv,sb) /\
  local_ptrs_reserved cenv sa /\ eval_expr cx e es = (INL raw,es') /\
  ~is_word_type res_ty /\ ~same_memory_layout cenv arm_ty res_ty /\
  compile_ifexp_arm cenv res_ty arm_ty vv sb = (op,sd) /\
  fn_has_code sb sd fn ==>
  (!x. vv_operand vv = Var x ==> not_fresh_at sb x) /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  ?buf sc src sn.
    compile_alloc_buffer (type_memory_bytes cenv res_ty) sb = (buf,sc) /\
    unwrap_value cenv vv sc = (src,sn) /\
    compile_store_memory cenv src buf.buf_operand res_ty arm_ty sn = ((),sd) /\
    op = buf.buf_operand /\ fn_has_code sb sc fn
Proof
  strip_tac >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sb x` by
    metis_tac[cj 1 compiler_compile_var] >>
  `ci_mono sa sb` by
    (qspec_then `cenv` mp_tac (cj 1 compile_expr_ci_mono) >>
     disch_then (qspecl_then [`expr_type e`, `e`, `sa`] mp_tac) >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM es'.scopes` by
    metis_tac[eval_expr_preserves_scopes_dom] >>
  `sa.cs_next_id <= sb.cs_next_id` by
    (drule compile_expr_extends >> simp[]) >>
  simp[] >> conj_tac >- gvs[ci_mono_def] >>
  qpat_x_assum `compile_ifexp_arm _ _ _ _ _ = _` mp_tac >>
  simp[compile_ifexp_arm_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `compile_alloc_buffer _ sb = (buf,sc)` >>
  rename1 `unwrap_value _ _ sc = (src,sn)` >>
  rename1 `compile_store_memory _ _ _ _ _ sn = ((),sd)` >>
  `ci_mono sb sc` by
    metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND] >>
  `ci_mono sc sn` by metis_tac[ci_mono_unwrap_value, pairTheory.SND] >>
  `cs_extends sn sd` by
    metis_tac[ci_mono_compile_store_memory, ci_mono_def, pairTheory.SND] >>
  gvs[ci_mono_def] >> metis_tac[fn_has_code_split, cs_extends_trans]
QED
