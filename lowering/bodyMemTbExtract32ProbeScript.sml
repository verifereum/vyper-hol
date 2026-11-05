(* Checked domain/representation probes for the frozen Extract32 case. *)
Theory bodyMemTbExtract32Probe
Ancestors
  exprSimHypsDefs exprLowering builtinBytes vyperTypeSystem compileEnv emitHelper

Theorem extract32_fixed32_args_admitted:
  well_typed_type_builtin_args Extract32 (BaseT (UintT 256))
    [BaseT (BytesT (Fixed 32)); BaseT (UintT 256)]
Proof
  simp[well_typed_type_builtin_args_def, is_int_type_def,
       extract32_result_base_ok_def] >> qexists_tac `Fixed 32` >> simp[]
QED

Theorem extract32_fixed32_well_typed:
  !env. well_typed_expr env
    (TypeBuiltin (BaseT (UintT 256)) Extract32 (BaseT (UintT 256))
      [Literal (BaseT (BytesT (Fixed 32))) (BytesL (REPLICATE 32 0w));
       Literal (BaseT (UintT 256)) (IntL 0)])
Proof
  simp[well_typed_expr_def, extract32_fixed32_args_admitted,
       vyperASTTheory.expr_type_def, well_typed_literal_def] >> EVAL_TAC >> simp[]
QED

Theorem extract32_fixed32_widths:
  byte_widths_expr
    (TypeBuiltin (BaseT (UintT 256)) Extract32 (BaseT (UintT 256))
      [Literal (BaseT (BytesT (Fixed 32))) (BytesL (REPLICATE 32 0w));
       Literal (BaseT (UintT 256)) (IntL 0)])
Proof
  EVAL_TAC
QED

Theorem extract32_fixed32_alloc_limits:
  !cenv. alloc_limits_expr cenv
    (TypeBuiltin (BaseT (UintT 256)) Extract32 (BaseT (UintT 256))
      [Literal (BaseT (BytesT (Fixed 32))) (BytesL (REPLICATE 32 0w));
       Literal (BaseT (UintT 256)) (IntL 0)])
Proof
  gen_tac >> EVAL_TAC >> simp[]
QED

Theorem extract32_fixed32_literal_word:
  !st. compile_literal_vv (BaseT (BytesT (Fixed 32)))
    (BytesL (REPLICATE 32 0w)) st =
    (StackValue (BaseT (BytesT (Fixed 32))) (Lit 0w), st)
Proof
  gen_tac >> EVAL_TAC >> simp[]
QED

Theorem extract32_fixed32_lowered_operand:
  !cenv ty st. lower_value compile_expr cenv ty
    (Literal (BaseT (BytesT (Fixed 32))) (BytesL (REPLICATE 32 0w))) st =
    (Lit 0w, st)
Proof
  rpt gen_tac >>
  simp[lower_value_def, compile_expr_def, extract32_fixed32_literal_word,
       comp_bind_def, comp_return_def, unwrap_value_def,
       vyperASTTheory.expr_type_def]
QED

Theorem extract32_fixed32_preparation:
  compile_bytestring_src (Lit 0w) =
    comp_bind (emit_op MLOAD [Lit 0w]) (\src_len.
      comp_bind (emit_op ADD [Lit 0w; Lit 32w]) (\src_data.
        comp_return (src_len, src_data)))
Proof
  simp[compile_bytestring_src_def]
QED
