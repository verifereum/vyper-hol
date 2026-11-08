(* Source typing used by the retained checked counterexample frame. *)
Theory bodyPtrBopInEvidenceTyping
Ancestors exprLoweringProps exprLowering vyperTypeSystem vyperValueOperation
  venomExecSemantics venomState venomInst venomMemProps compileEnv context emitHelper words

Theorem string_membership_expression_typing_probe:
  well_typed_expr env
     (Builtin (BaseT BoolT) (Bop In)
       [Literal (BaseT (StringT 1)) (StringL "a");
        Builtin (ArrayT (BaseT (StringT 1)) (Fixed 1))
          (MakeArray (SOME (BaseT (StringT 1))) (Fixed 1))
          [Literal (BaseT (StringT 1)) (StringL "a")]])
Proof
  simp[well_typed_expr_def, well_typed_builtin_app_def,
       well_typed_binop_def] >>
  EVAL_TAC >> simp[dimword_def, dimindex_256] >> EVAL_TAC
QED
