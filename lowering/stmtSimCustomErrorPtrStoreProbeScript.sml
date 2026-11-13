(* Store-interface diagnostic: pure arguments cannot select unequal-layout
   recursive typed copies.  Pointer execution is not inferred from this fact. *)
Theory stmtSimCustomErrorPtrStoreProbe
Ancestors
  bodyMemAggregateStore bodyExprPreFacts typedWordArgsReadyPtr
  annAssignPtrDestination bodyPtrDefs context exprLowering compileEnv
  vyperTypeSystem supportedExprs

Theorem custom_error_pure_store_dispatch:
  !ce e env src dst tops.
    supported_pure_expr tops e /\ well_typed_expr env e ==>
    compile_store_memory ce src dst (expr_type e) (lowered_value_type ce e) =
      (if is_word_type (expr_type e) then emit_void MSTORE [dst; src]
       else if is_bytestring_type (expr_type e) then compile_store_bytestring src dst
       else compile_copy_memory dst src (type_memory_bytes ce (expr_type e)))
Proof
  rpt strip_tac >>
  `int_calls_expr e = []` by metis_tac[supported_pure_int_calls] >>
  `compile_store_memory ce src dst (expr_type e) (lowered_value_type ce e) =
   compile_store_memory ce src dst (expr_type e) (expr_type e)` by
    metis_tac[aggregate_mem_store_lowered_elem] >>
  asm_rewrite_tac[] >> simp[compile_store_memory_def]
QED
