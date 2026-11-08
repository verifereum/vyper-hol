Theory bodyPtrSubscriptCurrentRootCase
Ancestors
  bodyPtrSubscriptCurrentRootEndpoint bodyPtrSubscriptSignedSelector
  exprSimSource vyperArith integer_word vyperTyping compileEnv
  exprSimHypsDefs vyperTypeSystem exprLowering exprSimProps
  exprSimNameValue vyperAST exprSimAttributeProps bodyPtrPreds
  bodyPtrSubscriptNamedIndex bodyPtrDefs bodySim exprLoweringProps
  gasSummaryComposePtr vyperState context fragExec vyperInterpreter
Libs
  pairLib

(* Source typing, not just nonnegativity, rules out signed word wrap. *)
Theorem signed_integer_index_word_nonnegative:
  expr_body_pre cenv cx env idx es /\
  is_int_type (expr_type idx) /\ is_signed_type (expr_type idx) /\
  vyperState$bind (eval_expr cx idx) (\result. read_result cx result) es =
    (INL (IntV i),ee) /\ 0 <= i ==>
  0 <= w2i (n2w (Num i):bytes32)
Proof
  strip_tac >>
  `word_value_type (expr_type idx)` by
    (Cases_on `expr_type idx` >> gvs[is_int_type_def, word_value_type_def] >>
     Cases_on `b` >> gvs[is_int_type_def, word_value_type_def]) >>
  drule_all expr_body_pre_word_result >> strip_tac >>
  first_x_assum (qspec_then `IntV i` mp_tac) >> simp[] >> strip_tac >>
  Cases_on `expr_type idx` >> gvs[is_int_type_def, is_signed_type_def] >>
  Cases_on `b` >> gvs[is_int_type_def, is_signed_type_def] >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(), value_has_type_def] >>
  drule_all w2i_i2w_within_signed >>
  `~(i < 0)` by intLib.ARITH_TAC >>
  simp[integer_wordTheory.i2w_def]
QED

Theorem dynamic_array_subscript_compile:
  compile_expr cenv ty (Subscript ann obj idx) sa = (vv,sc) /\
  place_type cenv obj = ValPT (ArrayT et (Dynamic cap)) ==>
  ?bvv sb iop sk q.
    compile_expr cenv ty obj sa = (bvv,sb) /\
    lower_value compile_expr cenv ty idx sb = (iop,sk) /\
    compile_array_subscript (vv_operand bvv) iop T 0 (word_scale (vv_loc bvv))
      (elem_size_in_location cenv (vv_loc bvv) et) (is_signed_type (expr_type idx))
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca (vv_loc bvv)) sk = (q,sc) /\
    vv = LocatedValue ann (mk_ptr q (vv_loc bvv))
Proof
  strip_tac >>
  qpat_x_assum `compile_expr _ _ (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def,
       compile_subscript_def, comp_bind_def, comp_return_def,
       vyperASTTheory.expr_size_def, vyperASTTheory.expr_type_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[comp_return_def, vv_loc_def, lower_value_def, comp_bind_def,
      exprCallBoundsTheory.expr_child_callback_def, expr_size_def] >>
  rpt (pairarg_tac >> gvs[exprCallBoundsTheory.expr_child_callback_def]) >>
  metis_tac[]
QED


Theorem dynamic_named_subscript_operand_typing:
  expr_body_pre cenv cx env
    (Subscript ann (Name (ArrayT et (Dynamic cap)) id) idx) es ==>
  well_typed_expr env (Name (ArrayT et (Dynamic cap)) id) /\
  well_typed_expr env idx
Proof
  strip_tac >>
  `well_typed_expr env
    (Subscript ann (Name (ArrayT et (Dynamic cap)) id) idx)` by
    fs[expr_body_pre_def] >>
  qpat_x_assum `well_typed_expr _ (Subscript _ _ _)` mp_tac >>
  simp[well_typed_expr_def]
QED

Theorem dynamic_named_subscript_operand_pre:
  expr_body_pre cenv cx env
    (Subscript ann (Name (ArrayT et (Dynamic cap)) id) idx) es ==>
  expr_body_pre cenv cx env (Name (ArrayT et (Dynamic cap)) id) es /\
  expr_body_pre cenv cx env idx es
Proof
  strip_tac >> drule dynamic_named_subscript_operand_typing >> strip_tac >>
  qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
  simp[expr_body_pre_def,
       vyperTypeCallGraphTheory.int_calls_expr_def, byte_widths_expr_def,
       allocLimitsTheory.alloc_limits_expr_def,
       supportedExprTraverseTheory.expr_has_evm_run_thm] >>
  strip_tac >>
  `call_evaluation_safe cx []` by
    (irule vyperTypeCallStackSoundnessTheory.call_evaluation_safe_mono >>
     goal_assum (drule_at Any) >> simp[]) >>
  rpt strip_tac >>
  gvs[supportedExprTraverseTheory.supported_expr_exists_def]
QED

Theorem subscript_source_sequence:
  eval_expr cx (Subscript ann obj idx) =
  bind (bind (eval_expr cx obj)
    (\base. bind (bind (eval_expr cx idx) (read_result cx))
      (\v. return (base,v))))
    (\bv. select_result cx (expr_type obj) (FST bv) (ValueSubscript (SND bv)))
Proof
  simp[FUN_EQ_THM, Once evaluate_def, bind_def, return_def] >>
  gen_tac >> Cases_on `eval_expr cx obj x` >> Cases_on `q` >> simp[] >>
  Cases_on `eval_expr cx idx r` >> Cases_on `q` >> simp[] >>
  Cases_on `read_result cx x'' r''` >> Cases_on `q` >> simp[]
QED

