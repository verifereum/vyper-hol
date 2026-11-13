Theory runtimeSymSrcStatementAssignClosed
Ancestors
  runtimeSymSrcStatementAssignFamily runtimeSymSrcAssignUpdates runtimeSymSrcContextComplete
  runtimeSymSrcBinops runtimeSymSrcOpenValues runtimeSymSrcGeneratorContracts

(* Residual ledger for the statement recursion consumer:
   - BaseAssign: supported_assignment-selected compile_get_target_ptr contract.
   - TupleAssign: supported_target-selected compile_get_target_ptr contract.
   - AugAssign: supported_target/supported_aug_target-selected pointer contract.
     These target interfaces belong to C1.1.3; expression contracts to C1.1.4.
   - Append: the literal nonlabel/opcode-guarded compile_dynarray_append
     contract below (C1.1.3). All unwrap, snapshot, binop, allocation and
     memory-store premises are discharged by their published boundaries.
   No whole-statement callback assumption is used. *)

Theorem runtime_sym_assignment_annassign_closed:
  runtime_sym_expr_contract tops compile_expr ce (expr_type e) e ==>
  runtime_sym_stmt_contract tops bindings compile_stmt ce lc ty (AnnAssign id vtyp e)
Proof
  strip_tac >> irule runtime_sym_assignment_annassign >>
  simp[] >> metis_tac[runtime_sym_unwrap_value]
QED

Theorem runtime_sym_assignment_baseassign_closed:
  runtime_sym_expr_contract tops compile_expr ce (expr_type e) e /\
  (!s op loc pt s'. runtime_sym_env ce /\
    supported_assignment tops bindings (BaseTarget bt) e /\
    ~supported_target_exists is_self_code bt /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_get_target_ptr compile_expr ce bt s = ((op,loc,pt),s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) ==>
  runtime_sym_stmt_contract tops bindings compile_stmt ce lc ty (Assign (BaseTarget bt) e)
Proof
  strip_tac >> match_mp_tac runtime_sym_assignment_baseassign >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (rpt gen_tac >> strip_tac >> drule_all runtime_sym_unwrap_value >> simp[]) >>
  rpt gen_tac >> strip_tac >> drule_all runtime_sym_snapshot_vv >> simp[]
QED

Theorem runtime_sym_assignment_tupleassign_closed:
  runtime_sym_expr_contract tops compile_expr ce (expr_type e) e /\
  (!bt s op loc pt s'. runtime_sym_env ce /\
    supported_target tops bindings bt /\
    ~supported_target_exists is_self_code bt /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_get_target_ptr compile_expr ce bt s = ((op,loc,pt),s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) ==>
  runtime_sym_stmt_contract tops bindings compile_stmt ce lc ty (Assign (TupleTarget targets) e)
Proof
  strip_tac >> match_mp_tac runtime_sym_assignment_tupleassign >>
  simp[] >> metis_tac[runtime_sym_unwrap_value]
QED

Theorem runtime_sym_assignment_augassign_closed:
  (!s op loc pt s'. runtime_sym_env ce /\
    (supported_target tops bindings bt \/ supported_aug_target tops bindings bt) /\
    ~supported_target_exists is_self_code bt /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_get_target_ptr compile_expr ce bt s = ((op,loc,pt),s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  runtime_sym_expr_contract tops compile_expr ce target_ty e ==>
  runtime_sym_stmt_contract tops bindings compile_stmt ce lc ty
    (AugAssign target_ty bt bop e)
Proof
  strip_tac >> irule runtime_sym_stmt_augassign >>
  reverse conj_tac >- metis_tac[runtime_sym_binop] >>
  mp_tac runtime_sym_lower_value >>
  impl_tac >- metis_tac[runtime_sym_unwrap_value] >>
  simp[runtime_sym_lower_value_clause_def] >> metis_tac[]
QED

Theorem runtime_sym_assignment_append_closed:
  (!t. runtime_sym_expr_contract tops compile_expr ce t val_e) /\
  (!base v ws es et st cap prim load store s u s'.
    ~is_label_operand base /\ ~is_label_operand v /\
    load <> CODESIZE /\ load <> CODECOPY /\
    store <> CODESIZE /\ store <> CODECOPY /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_dynarray_append ce base v ws es et st cap prim load store s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) ==>
  runtime_sym_stmt_contract tops bindings compile_stmt ce lc ty (Append target val_e)
Proof
  strip_tac >> irule runtime_sym_assignment_append >>
  conj_tac >- first_assum ACCEPT_TAC >>
  mp_tac runtime_sym_lower_value >>
  impl_tac >- metis_tac[runtime_sym_unwrap_value] >>
  simp[runtime_sym_lower_value_clause_def] >> metis_tac[]
QED
