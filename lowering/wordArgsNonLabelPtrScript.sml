(* Compiler metadata is independent of successful runtime evaluation. *)
Theory wordArgsNonLabelPtr
Ancestors exprReasonOperand exprSimWordArgs list

Theorem lower_word_args_nonLabel:
  !es sa xs sb.
    lower_word_args cenv arg_ty es sa = (xs,sb) /\
    well_typed_exprs env es /\
    (!id t. FLOOKUP env.var_types id = SOME t ==>
      ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) ==>
    EVERY (\op. !l. op <> Label l) xs
Proof
  Induct >> simp[exprSimWordArgsTheory.lower_word_args_nil,
    exprSimWordArgsTheory.lower_word_args_cons,
    vyperTypeSystemTheory.well_typed_expr_def] >>
  rpt strip_tac >> gvs[] >> conj_tac
  >- (drule_all exprReasonOperandTheory.lower_compile_expr_not_label >> simp[]) >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[]
QED
