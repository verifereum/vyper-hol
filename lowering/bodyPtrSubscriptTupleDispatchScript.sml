(* Typed tuple dispatch: the literal index has no target code interval. *)
Theory bodyPtrSubscriptTupleDispatch
Ancestors
  exprSimTuple exprSimAttributeProps exprSimHypsDefs exprSimDefs exprSimProps exprSimNameValue
  loweringPosts exprLowering exprLoweringProps vyperTyping vyperTypeSystem
  vyperAST vyperTypeCallGraph supportedExprTraverse allocLimits
  vyperInterpreter vyperState vyperValueOperation compileEnv finite_map placeTypingProps context

Theorem tuple_subscript_pre:
  expr_body_pre cenv cx env (Subscript ann obj idx) es /\
  expr_type obj = TupleT tys ==>
  expr_body_pre cenv cx env obj es /\
  ?ity k. idx = Literal ity (IntL (&k)) /\ k < LENGTH tys /\ EL k tys = ann
Proof
  strip_tac >>
  `well_typed_expr env obj /\ subscript_type_ok (TupleT tys) idx ann` by
    (qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
     simp[expr_body_pre_def, Once well_typed_expr_def] >>
     rpt strip_tac >> gvs[] >>
     drule type_place_expr_vtype_annotation >>
     Cases_on `vt` >> TRY (rename1 `Type t` >> Cases_on `t`) >>
     gvs[subscript_vtype_def, vtype_annotation_ok_def]) >>
  `?ity k. idx = Literal ity (IntL (&k)) /\ k < LENGTH tys /\ EL k tys = ann` by
    (gvs[subscript_type_ok_def] >>
     Cases_on `idx` >> gvs[] >> rename1 `Literal _ l` >> Cases_on `l` >> gvs[] >>
     rename1 `IntL n` >> qexists_tac `Num n` >> simp[integerTheory.INT_OF_NUM]) >>
  gvs[expr_body_pre_def, well_typed_expr_def,
      int_calls_expr_def, byte_widths_expr_def, alloc_limits_expr_def,
      expr_has_evm_run_thm] >> rpt strip_tac >>
  gvs[supported_expr_exists_def]
QED

Theorem tuple_subscript_compile:
  compile_expr cenv ty (Subscript ann obj idx) sa = (vv,sc) /\
  place_type cenv obj = ValPT (TupleT tys) ==>
  ?bvv sb q.
    compile_expr cenv ty obj sa = (bvv,sb) /\
    emit_op ADD [vv_operand bvv;
      Lit (n2w (SUM (TAKE (literal_int_index idx)
        (MAP (elem_size_in_location cenv (vv_loc bvv)) tys))))] sb = (q,sc) /\
    vv = LocatedValue ann (mk_ptr q (vv_loc bvv))
Proof
  strip_tac >>
  qpat_x_assum `compile_expr _ _ (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def,
       compile_subscript_def, compile_tuple_subscript_def, comp_bind_def,
       comp_return_def, vyperASTTheory.expr_size_def, vyperASTTheory.expr_type_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[comp_return_def, vv_loc_def]
QED

Theorem tuple_subscript_source:
  eval_expr cx (Subscript ann obj (Literal ity (IntL (&k)))) es =
  (bind (eval_expr cx obj)
    (\r. select_result cx (expr_type obj) r (ValueSubscript (IntV (&k))))) es
Proof
  simp[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx obj es` >> rename1 `_ = (rr,es1)` >>
  Cases_on `rr` >> simp[] >>
  simp[Once evaluate_def, evaluate_literal_def, return_def, read_result_def]
QED

Theorem named_tuple_subscript_dispatch:
  expr_body_pre cenv cx env (Subscript ann (Name (TupleT tys) id) idx) es /\
  place_type cenv (Name (TupleT tys) id) = ValPT (TupleT tys) /\
  compile_expr cenv ty (Subscript ann (Name (TupleT tys) id) idx) sa = (vv,sc) ==>
  expr_body_pre cenv cx env (Name (TupleT tys) id) es /\
  ?ity k p sz q.
    idx = Literal ity (IntL (&k)) /\ k < LENGTH tys /\ EL k tys = ann /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    compile_expr cenv ty (Name (TupleT tys) id) sa =
      (LocatedValue (TupleT tys) (mk_ptr (Var p) LocMemory),sa) /\
    emit_op ADD [Var p; Lit (n2w
      (SUM (TAKE k (MAP (elem_size_in_location cenv LocMemory) tys))))] sa = (q,sc) /\
    vv = LocatedValue ann (mk_ptr q LocMemory)
Proof
  strip_tac >> drule tuple_subscript_pre >> simp[expr_type_def] >> strip_tac >>
  `?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    gvs[expr_body_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  drule compile_name_value_ptr >>
  disch_then (qspecl_then [`ty`, `sa`, `TupleT tys`] assume_tac) >>
  drule_all tuple_subscript_compile >> strip_tac >>
  gvs[vv_loc_def, vv_operand_def, vv_location_def, mk_ptr_def,
      literal_int_index_def]
QED
