Theory bodyPtrBytestringBuiltinsSliceGuardFixture
Ancestors
  allocLimits vyperTypeSystem vyperInterpreter exprSimHypsDefs

(* AST abbreviations only: the address converts a closed checked Div0. *)
Definition slice_guard_source_def:
  slice_guard_source =
    Builtin (BaseT (BytesT (Dynamic 24576))) (Acc Code)
      [TypeBuiltin (BaseT AddressT) Convert (BaseT AddressT)
        [Builtin (BaseT (UintT 256)) (Bop Div)
          [Literal (BaseT (UintT 256)) (IntL 1);
           Literal (BaseT (UintT 256)) (IntL 0)]]]
End

Theorem slice_guard_source_typed:
  !env. well_typed_expr env slice_guard_source
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256]
QED

Theorem slice_guard_source_fails:
  !cx st. eval_expr cx slice_guard_source st =
    (INR (Error (RuntimeError "Div0")), st)
Proof
  rpt gen_tac >> EVAL_TAC >> simp[vyperStateTheory.return_def]
QED

Theorem slice_guard_no_success:
  !cx. ~(?s tv t s1 v t1.
    eval_expr cx slice_guard_source s = (INL tv,t) /\
    read_result cx tv s1 = (INL v,t1))
Proof
  simp[slice_guard_source_fails]
QED

Theorem slice_guard_source_extcode:
  is_extcode slice_guard_source
Proof
  EVAL_TAC
QED

Theorem slice_guard_slice_typed:
  !env. well_typed_expr env
    (Builtin (BaseT (BytesT (Dynamic 1))) (Slice 1)
      [slice_guard_source;
       Literal (BaseT (UintT 256)) (IntL 0);
       Literal (BaseT (UintT 256)) (IntL 1)])
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256] >>
  EVAL_TAC >> CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  qexists_tac `Dynamic 24576` >> simp[]
QED

Theorem slice_guard_source_static_checks:
  !cenv. byte_widths_expr slice_guard_source /\
    ~alloc_limits_expr cenv slice_guard_source /\
    int_calls_expr slice_guard_source = [] /\
    ~expr_has_evm_run slice_guard_source
Proof
  gen_tac >> EVAL_TAC
QED

Theorem slice_guard_slice_alloc_limits:
  !cenv. alloc_limits_expr cenv
    (Builtin (BaseT (BytesT (Dynamic 1))) (Slice 1)
      [slice_guard_source;
       Literal (BaseT (UintT 256)) (IntL 0);
       Literal (BaseT (UintT 256)) (IntL 1)])
Proof
  gen_tac >>
  simp[slice_guard_source_def, alloc_limits_expr_def,
       exprLoweringTheory.is_extcode_def, exprLoweringTheory.extcode_addr_expr_def] >>
  EVAL_TAC
QED

Theorem slice_guard_source_no_body_pre:
  !cenv cx env es. ~expr_body_pre cenv cx env slice_guard_source es
Proof
  simp[expr_body_pre_def, slice_guard_source_static_checks]
QED
