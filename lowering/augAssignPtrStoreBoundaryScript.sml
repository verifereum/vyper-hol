(* Store values need clean taint, not absent provenance.  Memory-store
   checks and byte clearing are already ptr_inst_ok_mstore and
   mstore_word_clean in fragExecPtr; do not duplicate them here. *)
Theory augAssignPtrStoreBoundary
Ancestors fragExecPtr ptrSafeRun ptrDiscipline venomExecSemantics
  venomInst venomState codegenRel contextCodegenRel finite_map pred_set

Theorem storage_store_ptr_inst_ok:
  !D lo fuel ctx fn G tn s id opc a v.
    (opc = SSTORE \/ opc = TSTORE) /\
    op_taint tn a = {} /\ op_taint tn v = {} /\
    allocas_from lo s /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    (!s'. step_inst fuel ctx (mk_inst id opc [a;v] []) s = OK s' ==>
          LENGTH s'.vs_requests <= LENGTH s.vs_requests) /\
    (!s'. step_inst fuel ctx (mk_inst id opc [a;v] []) s <> Halt s') ==>
    ptr_inst_ok D lo fuel ctx fn G tn (mk_inst id opc [a;v] []) s
Proof
  rpt strip_tac >> gvs[mk_inst_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  metis_tac[arithmeticTheory.NOT_LESS_EQUAL]
QED

Theorem storage_store_taint_subset:
  !opc id a v s s' tn.
    (opc = SSTORE \/ opc = TSTORE) /\ op_taint tn v = {} ==>
    (step_taint (mk_inst id opc [a;v] []) s s' tn).t_stor SUBSET tn.t_stor /\
    (step_taint (mk_inst id opc [a;v] []) s s' tn).t_trans SUBSET tn.t_trans
Proof
  rpt strip_tac >> gvs[] >>
  simp[step_taint_def, store_taint_def, adopt_reset_def, mk_inst_def] >>
  Cases_on `eval_operand a s` >> simp[key_update_def, SUBSET_DEF] >>
  metis_tac[]
QED
