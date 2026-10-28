Theory sourceOrdinaryBridgeTest
Ancestors
  sourceOrdinaryBridge sourceExprTest sourceExprElaborate sourceExprDefs
  sourceSyntax sourceResolve sourceConstEval sourceConstAST jsonToVyperExpr
  jsonToVyperType jsonAST vyperAST vyperTypeSystem vyperTypeContract vyperContext
  finite_map sourceConstBuiltinTest
Libs
  sourceSyntaxLib vyperCheckContractLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../tests/fixtures/check_contract/source_ordinary/concat_residual.vy",
  "../tests/fixtures/check_contract/source_ordinary/concat_residual_source.json"]

Definition ordinary_bridge_ctx_def:
  ordinary_bridge_ctx = (0, NONE, [], [], [], [], []) :
    int # num option # (string # num) list # string list #
    (string # type) list # ((num option # string) # type) list #
    (((num option # string) # (num option # string)) list)
End

Definition ordinary_bridge_concat_source_def:
  ordinary_bridge_concat_source = SX_Call (SX_Name "concat")
    [SX_Name "a"; SX_Name "b"] []
End

Definition ordinary_bridge_concat_designator_def:
  ordinary_bridge_concat_designator =
    JE_Name "concat" (SOME "builtin_function") JMissingSource JT_None
End

(* These are explicit legacy dynamic leaves, not failed source elaborations.
   The complete bridge must derive their residual classification/shape witness
   from the paired trees before invoking the layer. *)
Definition ordinary_bridge_dynamic_def:
  ordinary_bridge_dynamic name = translate_expr ordinary_bridge_ctx
    (JE_Name name NONE JMissingSource (JT_Bytes 4))
End

Theorem ordinary_bridge_concat_residual_only:
  source_ordinary_call_layer ordinary_bridge_ctx ordinary_bridge_concat_source
    ordinary_bridge_concat_designator
    [(SX_Name "a", SC_Value (ordinary_bridge_dynamic "a"));
     (SX_Name "b", SC_Value (ordinary_bridge_dynamic "b"))]
    [] (JT_Bytes 8) JMissingSource =
  SC_Value (Builtin (BaseT (BytesT (Dynamic 8))) (Concat 8)
    [Name (BaseT (BytesT (Dynamic 4))) "a";
     Name (BaseT (BytesT (Dynamic 4))) "b"])
Proof
  EVAL_TAC
QED

(* The inherited result bound is deliberately NOT presented as source-derived.
   A parent can keep its claim without changing verified child expressions. *)
Theorem ordinary_bridge_residual_retains_result_claim:
  source_ordinary_call_layer ordinary_bridge_ctx ordinary_bridge_concat_source
    ordinary_bridge_concat_designator
    [(SX_Name "a", SC_Value (ordinary_bridge_dynamic "a"));
     (SX_Name "b", SC_Value (ordinary_bridge_dynamic "b"))]
    [] (JT_Bytes 9) JMissingSource =
  SC_Value (Builtin (BaseT (BytesT (Dynamic 9))) (Concat 9)
    [Name (BaseT (BytesT (Dynamic 4))) "a";
     Name (BaseT (BytesT (Dynamic 4))) "b"])
Proof
  EVAL_TAC
QED

Definition ordinary_bridge_method_source_def:
  ordinary_bridge_method_source = SX_Call (SX_Name "method_id")
    [SX_Literal (SCL_String "foo()")] []
End

Theorem ordinary_bridge_verified_child_in_residual_call:
  source_ordinary_call_layer ordinary_bridge_ctx
    (SX_Call (SX_Name "concat") [SX_Name "a"; ordinary_bridge_method_source] [])
    ordinary_bridge_concat_designator
    [(SX_Name "a", SC_Value (ordinary_bridge_dynamic "a"));
     (ordinary_bridge_method_source,
      source_ordinary_verified 6
        (source_expr_test_env env (BaseT (BytesT (Dynamic 4))))
        source_expr_test_scopes source_expr_test_table []
        (source_expr_test_variables (BaseT (BytesT (Dynamic 4))))
        (BaseT (BytesT (Dynamic 4))) ordinary_bridge_method_source)]
    [] (JT_Bytes 8) JMissingSource =
  SC_Value (Builtin (BaseT (BytesT (Dynamic 8))) (Concat 8)
    [Name (BaseT (BytesT (Dynamic 4))) "a";
     Literal (BaseT (BytesT (Dynamic 4))) (BytesL [194w;152w;85w;120w])])
Proof
  simp[source_ordinary_verified_def, ordinary_bridge_method_source_def,
       GSYM source_expr_test_elaborate_def, source_expr_method_id_original_string] >>
  EVAL_TAC
QED

(* Errors are propagated, not converted into another legacy translation. *)
Theorem ordinary_bridge_child_errors_do_not_retry:
  source_ordinary_call_layer ordinary_bridge_ctx ordinary_bridge_concat_source
    ordinary_bridge_concat_designator
    [(SX_Name "a", SC_NotConstant); (SX_Name "b", SC_Invalid SCErr_ZeroDivisor)]
    [] (JT_Bytes 8) JMissingSource = SC_Invalid SCErr_ZeroDivisor /\
  source_ordinary_call_layer ordinary_bridge_ctx ordinary_bridge_concat_source
    ordinary_bridge_concat_designator
    [(SX_Name "a", SC_Value (ordinary_bridge_dynamic "a"));
     (SX_Name "b", SC_Unsupported SCS_Call)]
    [] (JT_Bytes 8) JMissingSource = SC_Unsupported SCS_Call
Proof
  EVAL_TAC
QED

Theorem ordinary_bridge_invalid_source_child:
  let bad = SX_Binary SCB_FloorDiv
    (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 0)) in
  source_ordinary_call_layer ordinary_bridge_ctx
    (SX_Call (SX_Name "concat") [SX_Name "a"; bad] [])
    ordinary_bridge_concat_designator
    [(SX_Name "a", SC_Value (ordinary_bridge_dynamic "a"));
     (bad, source_ordinary_verified 6
       (source_expr_test_env env (BaseT (UintT 256)))
       source_expr_test_scopes source_expr_test_table []
       (source_expr_test_variables (BaseT (UintT 256))) (BaseT (UintT 256)) bad)]
    [] (JT_Bytes 8) JMissingSource = SC_Invalid SCErr_ZeroDivisor
Proof
  EVAL_TAC
QED

Theorem ordinary_bridge_correspondence_is_structural:
  source_ordinary_call_layer ordinary_bridge_ctx ordinary_bridge_concat_source
    ordinary_bridge_concat_designator
    [(SX_Name "b", SC_Value (ordinary_bridge_dynamic "a"));
     (SX_Name "a", SC_Value (ordinary_bridge_dynamic "b"))]
    [] (JT_Bytes 8) JMissingSource = SC_Invalid SCErr_Domain
Proof
  EVAL_TAC
QED

(* Check the retained source fixture rather than just documenting the example. *)
val fixture = JSONDecode.decodeFile sourceSyntaxLib.wrapped_annotated_ast
  "../tests/fixtures/check_contract/source_ordinary/concat_residual_source.json";
val expected = ``SourceProgram (SourceModule [
  SD_Function "f" [SX_Name "external"; SX_Name "pure"]
    [SourceArg "a" (SOME (sourceConstAnnotation$SCA_Bytes (SCE_Literal (SCL_Int 4))));
     SourceArg "b" (SOME (sourceConstAnnotation$SCA_Bytes (SCE_Literal (SCL_Int 4))))]
    [] (SOME (sourceConstAnnotation$SCA_Bytes (SCE_Literal (SCL_Int 8))))
    [SS_Return (SOME (SX_Call (SX_Name "concat") [SX_Name "a"; SX_Name "b"] []))]
  ]) []``;
val () = if aconv fixture expected then () else raise Fail "concat residual original fixture";
val _ = save_thm ("ordinary_bridge_concat_fixture_original", REFL fixture);

(* Check the actual runtime expression produced by the residual layer. This is
   inherited legacy acceptance, not independently derived source concat typing. *)
val residual_body = case strip_comb (rhs (concl ordinary_bridge_concat_residual_only)) of
    (ctor,[e]) => if same_const ctor ``SC_Value : expr -> expr source_const_result``
      then e else raise Fail "concat residual layer failed"
  | _ => raise Fail "concat residual layer malformed result";
val residual_modules = ``[(NONE : num option, [FunctionDecl External Pure F F "f"
  [("a",BaseT (BytesT (Dynamic 4))); ("b",BaseT (BytesT (Dynamic 4)))]
  [] (BaseT (BytesT (Dynamic 8))) [Return (SOME ^residual_body)]])]``;
val _ = save_thm ("ordinary_bridge_concat_runtime_check",
  vyperCheckContractLib.check_contract
    {in_deploy=true, address=``0w:address``, modules=residual_modules,
     layouts=``[(0w:address, ([]:storage_layout, []:storage_layout))]``});
