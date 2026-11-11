(* Expression-level composition for the memory ABI decoder. *)
Theory abiDecodePtrExpr
Ancestors
  abiDecodePtrOutcome abiDecodePtrTarget bodyPtrHashBuiltinsUnary
  exprSimExtract32Source exprSimHyps exprSimHypsDefs vyperTypeBuiltins vyperTypeSystem
  vyperInterpreter vyperContext vyperState list

Theorem type_builtin_body_pre_arity:
  expr_body_pre cenv cx env (TypeBuiltin ann tb typ args) es ==>
  type_builtin_args_length_ok tb (LENGTH args)
Proof
  simp[expr_body_pre_def, well_typed_expr_def] >> strip_tac >>
  drule well_typed_type_builtin_args_length >> simp[]
QED

Theorem eval_expr_unary_type_builtin_action:
  type_builtin_args_length_ok tb 1 ==>
  eval_expr cx (TypeBuiltin ann tb typ [e]) =
  bind (bind (eval_expr cx e) (read_result cx))
    (\v. bind (lift_sum (evaluate_type_builtin cx tb typ [expr_type e] [v]))
       (\w. return (Value w)))
Proof
  strip_tac >> simp[Once evaluate_def] >>
  simp[type_check_def, assert_def, return_def, ignore_bind_def,
       Once evaluate_def, bind_assoc] >>
  simp[Once evaluate_def, assert_def, bind_def, return_def, FUN_EQ_THM]
QED

Theorem abi_decode_body_pre_shape:
  expr_body_pre cenv cx env (TypeBuiltin ann (AbiDecode b) typ args) es ==>
  ?e cap. args = [e] /\ expr_type e = BaseT (BytesT (Dynamic cap)) /\
    ann = typ /\ expr_body_pre cenv cx env e es
Proof
  strip_tac >>
  `LENGTH args = 1` by
    (drule type_builtin_body_pre_arity >> simp[type_builtin_args_length_ok_def]) >>
  Cases_on `args` >> gvs[] >>
  rename1 `TypeBuiltin ann (AbiDecode b) typ [e]` >>
  `expr_body_pre cenv cx env e es` by
    (irule exprOpenFirstOperandTheory.expr_body_pre_type_builtin_head >>
     goal_assum (drule_at Any)) >>
  gvs[expr_body_pre_def, well_typed_expr_def,
      well_typed_type_builtin_args_def, type_builtin_result_ok_def]
QED
