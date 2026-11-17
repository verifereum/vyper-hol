(* Stable conjunct projections from the compiler simulation relations. *)
Theory stateRelProj
Ancestors
  loweringStateRelDefs exprLoweringProps vyperTypeSystem supportedStmts

Theorem state_rel_local_ptrs_rel:
  state_rel H func cenv cx vs ss ==> local_ptrs_rel func cenv vs.scopes ss
Proof
  simp[state_rel_def]
QED

Theorem stmt_state_rel_local_ptrs_alloca:
  stmt_state_rel H ctx func cenv cx vs ss ==>
  local_ptrs_rel func cenv vs.scopes ss /\ alloca_inv ss
Proof
  metis_tac[stmt_state_rel_def, state_rel_local_ptrs_rel]
QED

Theorem type_stmt_raise_reason:
  type_stmt env ret_ty (Raise (RaiseReason e)) =
    (if well_typed_expr env e /\ (?n. expr_type e = BaseT (StringT n))
     then SOME env else NONE)
Proof
  simp[Once type_stmt_def]
QED

Theorem supported_stmt_raise_reason:
  supported_stmt tops bindings (Raise (RaiseReason e)) =
    supported_raise_reason tops (RaiseReason e)
Proof
  simp[Once supported_stmt_def]
QED
