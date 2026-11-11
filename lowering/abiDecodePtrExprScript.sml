(* Expression-level composition for the memory ABI decoder. *)
Theory abiDecodePtrExpr
Ancestors
  abiDecodePtrOutcome abiDecodePtrTarget bodyPtrHashBuiltinsUnary
  exprSimExtract32Source exprSimHyps exprSimHypsDefs vyperTypeBuiltins vyperTypeSystem
  exprLowering exprCallBounds context builtinAbi compileEnv
  vyperInterpreter vyperContext vyperState vyperAST list

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

Theorem compile_abi_decode_stages:
  compile_expr cenv ty (TypeBuiltin ann (AbiDecode b) typ [e]) sa =
    (let (op,sm) = lower_value compile_expr cenv (expr_type e) e sa in
     let target = if b /\ needs_external_call_wrap typ then TupleT [typ] else typ in
     as_ptr_val ann LocMemory
       (lower_abi_decode op (type_to_abi_dec_info cenv.ce_struct_fields cenv target)
         (abi_static_size cenv.ce_struct_fields target)
         (abi_size_bound cenv.ce_struct_fields target)
         (type_memory_bytes cenv target) sm))
Proof
  rewrite_tac[compile_expr_type_builtin_dispatch] >>
  simp[Once compile_type_builtin_dispatch_component_eq,
       lower_value_def, comp_bind_def, expr_child_callback_def,
       list_size_def, expr_size_def] >>
  pairarg_tac >> simp[]
QED
