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

(* Concrete local scopes, abbreviated only to keep evaluation probes small. *)
Definition order_probe_scopes_def:
  order_probe_scopes =
    [FEMPTY |+ ("arr", <|assignable := T;
      type := ArrayTV (BaseTV AddressT) (Dynamic 2);
      value := ArrayV (DynArrayV [AddressV 1w; AddressV 2w]); popped := []|>)]
End

Theorem order_probe_len_before:
  !cx st.
    eval_expr cx
      (Builtin (BaseT (UintT 256)) Len
        [Name (ArrayT (BaseT AddressT) (Dynamic 2)) "arr"])
      (st with scopes := order_probe_scopes) =
    (INL (Value (IntV 2)), st with scopes := order_probe_scopes)
Proof
  rpt gen_tac >> EVAL_TAC >> simp[vyperStateTheory.return_def]
QED

Theorem order_probe_pop_read:
  !cx st.
    FST ((do r <- eval_expr cx (Pop (BaseT AddressT) (NameTarget "arr"));
             read_result cx r od) (st with scopes := order_probe_scopes)) =
    INL (AddressV 2w)
Proof
  rpt gen_tac >> EVAL_TAC >> simp[vyperStateTheory.return_def]
QED

Theorem order_probe_len_after:
  !cx st.
    FST ((do eval_expr cx (Pop (BaseT AddressT) (NameTarget "arr"));
             eval_expr cx
               (Builtin (BaseT (UintT 256)) Len
                 [Name (ArrayT (BaseT AddressT) (Dynamic 2)) "arr"])
          od) (st with scopes := order_probe_scopes)) =
    INL (Value (IntV 1))
Proof
  rpt gen_tac >> EVAL_TAC >> simp[vyperStateTheory.return_def]
QED

Theorem order_probe_offset_first:
  !cx st.
    FST ((do offset <- eval_expr cx
               (Builtin (BaseT (UintT 256)) Len
                 [Name (ArrayT (BaseT AddressT) (Dynamic 2)) "arr"]);
             r <- eval_expr cx (Pop (BaseT AddressT) (NameTarget "arr"));
             addr <- read_result cx r;
             return (addr,offset)
          od) (st with scopes := order_probe_scopes)) =
    INL (AddressV 2w, Value (IntV 2))
Proof
  rpt gen_tac >> EVAL_TAC >> simp[vyperStateTheory.return_def,
    vyperStateTheory.bind_def]
QED

Theorem order_probe_address_first:
  !cx st.
    FST ((do r <- eval_expr cx (Pop (BaseT AddressT) (NameTarget "arr"));
             addr <- read_result cx r;
             offset <- eval_expr cx
               (Builtin (BaseT (UintT 256)) Len
                 [Name (ArrayT (BaseT AddressT) (Dynamic 2)) "arr"]);
             return (addr,offset)
          od) (st with scopes := order_probe_scopes)) =
    INL (AddressV 2w, Value (IntV 1))
Proof
  rpt gen_tac >> EVAL_TAC >> simp[vyperStateTheory.return_def,
    vyperStateTheory.bind_def] >> EVAL_TAC
QED
