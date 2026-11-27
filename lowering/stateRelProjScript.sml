(* Stable conjunct projections from the compiler simulation relations. *)
Theory stateRelProj
Ancestors
  loweringStateRelDefs exprLoweringProps vyperTypeSystem supportedStmts
  venomInst venomState finite_map words

Theorem state_rel_local_ptrs_rel:
  state_rel H func cenv cx vs ss ==> local_ptrs_rel func cenv vs.scopes ss
Proof
  simp[state_rel_def]
QED

Theorem state_rel_scopes_nil_func:
  state_rel H f1 cenv cx (vs with scopes := []) ss <=>
  state_rel H f2 cenv cx (vs with scopes := []) ss
Proof
  simp[state_rel_def, local_ptrs_rel_def, local_region_def,
       vyperStateTheory.lookup_scopes_def]
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

Theorem stmt_state_rel_alloca_size:
  stmt_state_rel H ctx func cenv cx vs s ==>
  !i w b sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
    i.inst_operands = [Lit w] /\
    FLOOKUP s.vs_allocas i.inst_id = SOME (b,sz) ==> sz = w2n w
Proof
  simp[stmt_state_rel_def] >> strip_tac >> first_assum ACCEPT_TAC
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

Theorem stmt_state_rel_fmp_room:
  stmt_state_rel H ctx func cenv cx vs ss ==> fmp_room ctx func ss
Proof
  simp[stmt_state_rel_def]
QED

Theorem stmt_state_rel_immutable_base_zero:
  stmt_state_rel H ctx func cenv cx vs ss ==> immutable_base_zero cenv ss
Proof
  simp[stmt_state_rel_def]
QED

Theorem stmt_state_rel_intro:
  state_rel H func cenv cx vs ss /\ alloca_inv ss /\ alloca_room ctx func ss /\
  fmp_room ctx func ss /\ immutable_alloca_sep func cenv cx vs ss /\
  immutable_base_zero cenv ss /\
  (!src tops. ALOOKUP cenv.ce_modules src = SOME tops ==>
     immutable_alloca_sep func (cenv with ce_module := src) cx vs ss) /\
  (!inst n base sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\
    FLOOKUP ss.vs_allocas inst.inst_id = SOME (base,sz) ==> sz = w2n n) ==>
  stmt_state_rel H ctx func cenv cx vs ss
Proof
  simp[stmt_state_rel_def] >> strip_tac >> first_assum ACCEPT_TAC
QED
