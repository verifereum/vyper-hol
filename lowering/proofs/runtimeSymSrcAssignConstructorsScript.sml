Theory runtimeSymSrcAssignConstructors
Ancestors
  runtimeSymSrcInterfaces runtimeSymSrcEmission stmtLowering compileEnv
  supportedStmts supportedStmtTraverse context venomInst stackPlanTypes

(* Ledger: expression callbacks belong to C1.1.4; unwrap and snapshot to
   C1.1.3.2. Local alloca, assign-value, store-at-location and tuple-unpack
   implications are discharged by the assignment/statement joins. *)
Theorem runtime_sym_stmt_annassign:
  runtime_sym_expr_contract tops compile_expr ce (expr_type e) e /\
  (!s s'. EVERY runtime_sym_inst (state_insts s) /\
    emit_local_alloca ce id s = ((),s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!v s op s'. runtime_sym_env ce /\ runtime_sym_value v /\ EVERY runtime_sym_inst (state_insts s) /\
    unwrap_value ce v s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!d loc v prim sl dt st da n s u s'.
    ~is_label_operand d /\ ~is_label_operand v /\
    (!b. ce.ce_imm_alloca = SOME b ==> ~is_label_operand b) /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_assign_value ce d loc v prim sl dt st da n s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) ==>
  runtime_sym_stmt_contract tops bindings compile_stmt ce lc ty (AnnAssign id vtyp e)
Proof
  strip_tac >> simp[runtime_sym_stmt_contract_def] >> rpt strip_tac >>
  fs[supported_stmt_def, supported_stmt_expr_exists_def] >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_stmt_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  rename1 `emit_local_alloca ce id s = (u,sa)` >> Cases_on `u` >>
  first_assum drule_all >> strip_tac >>
  fs[runtime_sym_expr_contract_def] >>
  qpat_x_assum `!s v s'. _` drule_all >> strip_tac >>
  qpat_x_assum `!d loc v prim sl dt st da n s s'. _` (mk_asm "assign") >>
  Cases_on `has_length_word vtyp /\ is_empty_value_expr e` >> simp[]
  >- (rpt strip_tac >>
      Cases_on `FLOOKUP ce.ce_vars id` >> gvs[comp_return_def]
      >- (drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >> simp[]) >>
      Cases_on `x` >> gvs[] >>
      drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >>
      simp[is_label_operand_def] >>
      metis_tac[runtime_sym_env_local, runtime_sym_loc_def]) >>
  qpat_x_assum `~(has_length_word _ /\ _)` kall_tac >>
  pairarg_tac >> simp[] >> rpt strip_tac >>
  first_assum drule_all >> strip_tac >>
  Cases_on `FLOOKUP ce.ce_vars id` >> gvs[]
  >- (drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >> simp[]) >>
  (Cases_on `x` >> gvs[])
  >>~- ([`emit_void INVALID [] _ = _`],
        drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >> simp[]) >>
  `~is_label_operand (Lit 0w)` by simp[is_label_operand_def] >>
  imp_res_tac runtime_sym_env_local >>
  fs[runtime_sym_loc_def, runtime_sym_env_def] >>
  asm "assign" (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[is_label_operand_def]
QED

Theorem runtime_sym_stmt_tupleassign:
  runtime_sym_expr_contract tops compile_expr ce (expr_type e) e /\
  (!v s op s'. runtime_sym_env ce /\ runtime_sym_value v /\ EVERY runtime_sym_inst (state_insts s) /\
    unwrap_value ce v s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!st mem op s u s'.
    runtime_sym_env ce /\
    supported_assignment tops bindings (TupleTarget targets) e /\
    ~supported_assignments_exists is_self_code targets /\
    ~is_label_operand op /\
    (!b. ce.ce_imm_alloca = SOME b ==> ~is_label_operand b) /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_tuple_unpack ce st mem targets op s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) ==>
  runtime_sym_stmt_contract tops bindings compile_stmt ce lc ty
    (Assign (TupleTarget targets) e)
Proof
  strip_tac >> simp[runtime_sym_stmt_contract_def] >> rpt strip_tac >>
  fs[supported_stmt_def, supported_assignment_def,
     supported_stmt_expr_exists_def, supported_assignment_exists_def,
     runtime_sym_expr_contract_def] >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_stmt_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  qpat_x_assum `!s v s'. _` drule_all >> strip_tac >>
  first_assum drule_all >> strip_tac >>
  fs[runtime_sym_env_def] >>
  first_assum (drule_at (Pat `compile_tuple_unpack _ _ _ _ _ _ = _`)) >>
  simp[supported_assignment_def, runtime_sym_env_def]
QED

(* The target premise is guarded by precisely the assignment domain and
   target traversal. The target family discharges it using its recursive
   expression contracts; no arbitrary PtrVar payload is assumed nonlabel. *)
Theorem runtime_sym_stmt_baseassign:
  runtime_sym_expr_contract tops compile_expr ce (expr_type e) e /\
  (!s op loc pt s'. runtime_sym_env ce /\
    supported_assignment tops bindings (BaseTarget bt) e /\
    ~supported_target_exists is_self_code bt /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_get_target_ptr compile_expr ce bt s = ((op,loc,pt),s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!v s op s'. runtime_sym_env ce /\ runtime_sym_value v /\ EVERY runtime_sym_inst (state_insts s) /\
    unwrap_value ce v s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!v s out s'. runtime_sym_env ce /\ runtime_sym_value v /\ EVERY runtime_sym_inst (state_insts s) /\
    compile_snapshot_vv ce T v s = (out,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value out) /\
  (!d loc v prim sl dt st da n s u s'.
    ~is_label_operand d /\ ~is_label_operand v /\
    (!b. ce.ce_imm_alloca = SOME b ==> ~is_label_operand b) /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_assign_value ce d loc v prim sl dt st da n s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!d v loc s u s'. ~is_label_operand d /\ ~is_label_operand v /\
    (!b. ce.ce_imm_alloca = SOME b ==> ~is_label_operand b) /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_store_at_loc ce.ce_imm_alloca d v loc s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) ==>
  runtime_sym_stmt_contract tops bindings compile_stmt ce lc ty
    (Assign (BaseTarget bt) e)
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "expr")
    (CONJUNCTS_THEN2 (mk_asm "target")
    (CONJUNCTS_THEN2 (mk_asm "unwrap")
    (CONJUNCTS_THEN2 (mk_asm "snapshot")
    (CONJUNCTS_THEN2 (mk_asm "assign") (mk_asm "store")))))) >>
  simp[runtime_sym_stmt_contract_def] >> rpt strip_tac >>
  fs[supported_stmt_def, supported_stmt_expr_exists_def,
     supported_assignment_exists_def] >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_stmt_def] >>
  Cases_on `has_length_word (expr_type e) /\ is_empty_value_expr e` >> simp[]
  >- (simp[comp_bind_def] >> pairarg_tac >> simp[] >>
      PairCases_on `tgt_result` >> simp[] >> strip_tac >>
      asm "target" drule_all >> strip_tac >>
      fs[runtime_sym_env_def] >>
      asm "store" (drule_at (Pat `compile_store_at_loc _ _ _ _ _ = _`)) >>
      simp[is_label_operand_def]) >>
  qpat_x_assum `~(has_length_word _ /\ _)` kall_tac >>
  simp[comp_bind_def, comp_return_def] >> pairarg_tac >> simp[] >>
  `supported_expr tops e` by fs[supported_assignment_def] >>
  asm "expr" mp_tac >> simp[runtime_sym_expr_contract_def] >>
  disch_then (drule_at (Pat `compile_expr _ _ _ _ = _`)) >> simp[] >> strip_tac >>
  Cases_on `expr_can_mutate ce (target_to_expr bt)` >> simp[]
  >- suspend "snapshot"
  >> suspend "direct"
QED

Resume runtime_sym_stmt_baseassign[snapshot]:
  pairarg_tac >> simp[] >>
  `runtime_sym_value (vv_with_type (lowered_value_type ce e) src_vv0)` by
    (Cases_on `src_vv0` >> fs[vv_with_type_def, runtime_sym_value_def]) >>
  asm "snapshot" drule_all >> strip_tac >>
  suspend "finish_snapshot"
QED

Resume runtime_sym_stmt_baseassign[direct]:
  simp[comp_return_def] >> suspend "finish_direct"
QED

Resume runtime_sym_stmt_baseassign[finish_snapshot]:
  pairarg_tac >> simp[] >> PairCases_on `tgt_result` >> simp[] >>
  pairarg_tac >> simp[] >> strip_tac >>
  asm "target" drule_all >> strip_tac >>
  asm "unwrap" drule_all >> strip_tac >>
  Cases_on `tgt_result1` >> gvs[]
  >- (drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >> simp[]) >>
  fs[runtime_sym_env_def] >>
  asm "assign" (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)) >> simp[]
QED

Resume runtime_sym_stmt_baseassign[finish_direct]:
  pairarg_tac >> simp[] >> PairCases_on `tgt_result` >> simp[] >>
  pairarg_tac >> simp[] >> strip_tac >>
  asm "target" drule_all >> strip_tac >>
  asm "unwrap" drule_all >> strip_tac >>
  Cases_on `tgt_result1` >> gvs[]
  >- (drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >> simp[]) >>
  fs[runtime_sym_env_def] >>
  asm "assign" (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)) >> simp[]
QED

Finalise runtime_sym_stmt_baseassign
