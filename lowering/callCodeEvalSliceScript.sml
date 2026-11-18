(* The self-code guard for the special code-slice evaluator branch. *)
Theory callCodeEvalSlice
Ancestors
  vyperInterpreter vyperContext vyperAST exprLowering supportedExprTraverse list

Theorem no_self_code_slice_operands:
  code_slice_source bt es = SOME (ct,addr) /\
  ~supported_exprs_exists is_self_code es ==>
  ~is_self_addr addr /\
  ~supported_exprs_exists is_self_code (TL es) /\
  ~supported_exprs_exists is_self_code [addr]
Proof
  rw[code_slice_source_SOME] >> gvs[supported_expr_exists_def] >>
  `is_self_addr addr ==> is_self_code (Builtin ct (Acc Code) [addr])` by
    (qid_spec_tac `addr` >> ho_match_mp_tac is_self_addr_ind >>
     simp[is_self_code_def]) >>
  metis_tac[]
QED
