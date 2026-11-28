(* Call requirements project to the syntax used by the prefix induction. *)
Theory s1PrefixSyntaxCalls
Ancestors
  vyperTypeCallGraph vyperTypeEvalProofs vyperAST supportedExprs
  targetPlaceSimCasesBase exprCallBounds exprLowering vyperInterpreter list sorting

Theorem int_calls_exprs_members:
  EVERY P (int_calls_exprs es) <=>
  !e. MEM e es ==> EVERY P (int_calls_expr e)
Proof
  Induct_on `es` >> simp[int_calls_expr_def, EVERY_APPEND, DISJ_IMP_THM] >> metis_tac[]
QED

Theorem int_calls_target_indices:
  EVERY P (int_calls_target t) <=>
  !e. MEM e (target_indices t) ==> EVERY P (int_calls_expr e)
Proof
  qid_spec_tac `t` >> ho_match_mp_tac base_assignment_target_induct >>
  simp[int_calls_expr_def, target_indices_def, EVERY_APPEND, DISJ_IMP_THM] >> metis_tac[]
QED

Theorem ordered_custom_error_calls:
  order_custom_error_args params err = SOME es /\
  EVERY P (int_calls_exprs (custom_error_exprs err)) ==>
  EVERY P (int_calls_exprs es)
Proof
  strip_tac >> drule order_custom_error_args_perm >>
  fs[int_calls_exprs_members] >> metis_tac[MEM_PERM]
QED

Theorem code_slice_source_calls:
  code_slice_source bt es = SOME (ty,addr) /\
  EVERY P (int_calls_exprs es) ==>
  EVERY P (int_calls_expr addr) /\ EVERY P (int_calls_exprs (TL es))
Proof
  simp[code_slice_source_SOME] >> strip_tac >>
  gvs[int_calls_expr_def, EVERY_APPEND]
QED
