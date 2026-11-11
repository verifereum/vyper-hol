(* Non-vacuity witness: membership over an array of a prim word type
   typechecks.  (String elements no longer do: the checker requires
   is_prim_word_type for In over an array.) *)
Theory bodyPtrBopInEvidenceTyping
Ancestors exprLoweringProps exprLowering vyperTypeSystem vyperValueOperation
  venomExecSemantics venomState venomInst venomMemProps compileEnv context emitHelper words

Theorem word_membership_expression_typing_probe:
  well_typed_expr env
     (Builtin (BaseT BoolT) (Bop In)
       [Literal (BaseT (UintT 256)) (IntL 1);
        Builtin (ArrayT (BaseT (UintT 256)) (Fixed 1))
          (MakeArray (SOME (BaseT (UintT 256))) (Fixed 1))
          [Literal (BaseT (UintT 256)) (IntL 1)]])
Proof
  simp[well_typed_expr_def, well_typed_builtin_app_def,
       well_typed_binop_def] >>
  EVAL_TAC >> simp[dimword_def, dimindex_256] >> EVAL_TAC
QED
