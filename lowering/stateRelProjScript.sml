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

Theorem state_rel_vars_rels:
  state_rel H func cenv cx vs ss ==>
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx
Proof
  simp[state_rel_def]
QED

Theorem stmt_state_rel_vars_rels:
  stmt_state_rel H ctx func cenv cx vs ss ==>
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx
Proof
  metis_tac[stmt_state_rel_def, state_rel_vars_rels]
QED

Theorem stmt_state_rel_state_rel:
  stmt_state_rel H ctx func cenv cx vs ss ==> state_rel H func cenv cx vs ss
Proof
  simp[stmt_state_rel_def]
QED

Theorem stmt_state_rel_alloca_room:
  stmt_state_rel H ctx func cenv cx vs ss ==> alloca_room ctx func ss
Proof
  simp[stmt_state_rel_def]
QED

Theorem state_rel_call_ctx_rel:
  state_rel H func cenv cx vs ss ==>
  call_ctx_rel cx.txn ss.vs_call_ctx ss.vs_tx_ctx ss.vs_block_ctx
Proof
  simp[state_rel_def]
QED

Theorem state_rel_immutables_rel:
  state_rel H func cenv cx vs ss ==>
  immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor vs ss
Proof
  simp[state_rel_def]
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
