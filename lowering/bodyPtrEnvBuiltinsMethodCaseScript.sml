(* MethodId's runtime consumer and literal-family assembly. *)
Theory bodyPtrEnvBuiltinsMethodCase
Ancestors bodyPtrEnvBuiltinsMethodRuntime bodyPtrEnvBuiltinsMethodSource
  bodyPtrEnvBuiltinsMethodTyping bodyPtrEnvBuiltinsDynamicLiteral
  bodyPtrEnvBuiltinsMethodShape bodyPtrEnvBuiltinsBoundary
  exprSimHash exprSimSource exprSimHypsDefs exprSimHyps exprSimProps
  exprLowering exprLoweringProps exprSimDefs exprSimWordArgs
  bodyPtrDefs bodyPtrPreds gasSummaryComposePtr gasSummary fragGasPathPtr
  compileEnv context freshWrites vyperAST vyperValue vyperContext
  vyperInterpreter vyperState venomState finite_map list fragExec

Theorem method_id_runtime_compile:
  method_id_literal e = NONE /\
  compile_expr cenv ty
    (Builtin (BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4))) MethodId [e]) sa =
    (vv,sb) ==>
  ?arg sm op. lower_value compile_expr cenv (expr_type e) e sa = (arg,sm) /\
    compile_method_id_runtime (expr_type e) arg fixed sm = (op,sb) /\
    vv = (if fixed then StackValue (BaseT (BytesT (Fixed 4))) op else
      LocatedValue (BaseT (BytesT (Dynamic 4))) (mk_ptr op LocMemory))
Proof
  strip_tac >> gvs[compile_method_id_singleton_runtime] >>
  pairarg_tac >> Cases_on `compile_method_id_runtime (expr_type e) v fixed sm` >>
  Cases_on `fixed` >> gvs[as_stack_val_def, as_ptr_val_def, mk_ptr_def]
QED
