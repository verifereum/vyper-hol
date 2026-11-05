(* Concrete syntax fixture for the extcode Slice evaluation-order probe.
   Abbreviating the AST keeps the independent admissibility checks readable. *)
Theory bodyPtrBytestringBuiltinsOrderProbe
Ancestors
  allocLimits vyperTypeSystem vyperTypeCallGraph vyperInterpreter
  exprSimHypsDefs supportedExprTraverse

Definition order_probe_expr_def:
  order_probe_expr =
    Builtin (BaseT (BytesT (Dynamic 1))) (Slice 1)
      [Builtin (BaseT (BytesT (Dynamic 24576))) (Acc Code)
         [Pop (BaseT AddressT) (NameTarget "arr")];
       Builtin (BaseT (UintT 256)) Len
         [Name (ArrayT (BaseT AddressT) (Dynamic 2)) "arr"];
       Literal (BaseT (UintT 256)) (IntL 1)]
End

Theorem order_probe_no_internal_calls:
  int_calls_expr order_probe_expr = []
Proof
  EVAL_TAC
QED

Theorem order_probe_extcode_source:
  is_extcode (HD (case order_probe_expr of Builtin _ _ es => es | _ => []))
Proof
  EVAL_TAC
QED

Theorem order_probe_well_typed:
  !env.
    well_typed_expr
      (env with <|var_types := FEMPTY |+ ("arr", ArrayT (BaseT AddressT) (Dynamic 2));
                  var_assignable := FEMPTY |+ ("arr", T)|>) order_probe_expr
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256] >>
  EVAL_TAC >> CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  qexists_tac `Dynamic 24576` >> simp[]
QED

Theorem order_probe_byte_widths:
  byte_widths_expr order_probe_expr
Proof
  EVAL_TAC
QED

Theorem order_probe_no_evm_run:
  ~expr_has_evm_run order_probe_expr
Proof
  EVAL_TAC
QED

Theorem order_probe_alloc_limits:
  !cenv. alloc_limits_expr cenv order_probe_expr
Proof
  simp[order_probe_expr_def, alloc_limits_expr_def,
       exprLoweringTheory.is_extcode_def, exprLoweringTheory.extcode_addr_expr_def] >>
  EVAL_TAC >> simp[]
QED
