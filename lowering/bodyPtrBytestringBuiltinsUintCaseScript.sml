Theory bodyPtrBytestringBuiltinsUintCase
Ancestors
  bodyPtrBytestringBuiltinsUnary bodyPtrBytestringBuiltinsUintCompile
  bodyPtrPreds exprPtrUnwrap exprSimHypsDefs exprSimUint2Str
  exprLowering exprBopLowering exprSimSource compileEnv fragExec vyperAST vyperContext list

Theorem uint2str_body_operand_ptr:
  (builtin_args_length_ok (Uint2Str n) (LENGTH args) ==>
    body_exprs_ptr_ok cx args) /\
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Builtin ann (Uint2Str n) args) es ==>
  ?e k. args = [e] /\ ann = BaseT (StringT n) /\
    expr_type e = BaseT (UintT k) /\ 78 <= n /\
    expr_body_pre cenv cx env e es /\
    expr_sim_ptr d ctx PG func cenv cx cty e es
Proof
  strip_tac >>
  `well_typed_expr env (Builtin ann (Uint2Str n) args)` by
    fs[expr_body_pre_def] >>
  drule uint2str_expr_types >> strip_tac >> gvs[] >>
  `body_exprs_ptr_ok cx [e]` by fs[builtin_args_length_ok_def] >>
  `expr_body_pre cenv cx env e es` by
    (drule expr_body_pre_builtin_arg >>
     disch_then irule >> fs[expr_body_pre_def]) >>
  simp[] >>
  fs[body_exprs_ptr_ok_def, body_expr_ptr_ok_def] >> metis_tac[]
QED

Theorem uint2str_compile_cut:
  compile_expr cenv ty (Builtin ann (Uint2Str n) [e]) sa = (vv,sb) ==>
  ?op sm. lower_value compile_expr cenv ty e sa = (op,sm) /\
    as_ptr_val ann LocMemory
      (compile_uint2str op n (type_memory_bytes cenv ann) sm) = (vv,sb)
Proof
  `!bt args. names_builtin bt args ==> bt <> Uint2Str n` by
    (ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]) >>
  `~names_builtin (Uint2Str n) [e]` by metis_tac[] >>
  simp[compile_expr_builtin_dispatch] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[lower_value_child_call, vyperASTTheory.expr_size_def, list_size_def] >>
  pairarg_tac >> simp[] >> strip_tac >> metis_tac[]
QED

Theorem uint2str_code_appends:
  cs_appends (\sm. as_ptr_val ann LocMemory
    (compile_uint2str x n N sm))
Proof
  rw[cs_appends_def] >>
  Cases_on `compile_uint2str x n N sm` >> gvs[as_ptr_val_def] >>
  mp_tac (Q.INST [`op` |-> `x`, `sz` |-> `N`] uint2str_suffix_appends) >>
  simp[cs_appends_def] >> metis_tac[]
QED
