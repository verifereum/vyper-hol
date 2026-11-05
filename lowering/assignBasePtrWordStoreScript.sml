(* Counted word-store edges at the supplied continuation state. *)
Theory assignBasePtrWordStore
Ancestors
  fragExecPtr fragGasSeqPtr emitHelper venomInst ptrSafeRun ptrDiscipline
  venomExecSemantics venomState memLocDefs contextCodegenRel codegenRel

Theorem assign_base_mstore_edge_ptr:
  !s fn bb id dst src tn G ctx u D PG.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MSTORE [Var dst; src] []) /\
    ptr_covers G tn dst s 32 /\ op_taint tn src = {} /\
    ~ctx_has_dalloca ctx /\
    step_inst_base (mk_inst id MSTORE [Var dst; src] []) s = OK u ==>
    gas_path_ptr_edge D 0 ctx fn PG G tn s 0
      (step_prov PG G (mk_inst id MSTORE [Var dst; src] []) u)
      (step_taint (mk_inst id MSTORE [Var dst; src] []) s u tn)
      (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn
     (mk_inst id MSTORE [Var dst; src] []) s` by
    (irule ptr_inst_ok_mstore >> simp[]) >>
  mp_tac (Q.INST
    [`i` |-> `mk_inst id MSTORE [Var dst; src] []`,
     `lo` |-> `0`] straight_line_ptr_edge) >>
  simp[mk_inst_def, is_terminator_def]
QED

Theorem assign_base_ptr_inst_ok_storage_word:
  !D ctx fn G tn s id opc addr src fuel.
    (opc = SSTORE \/ opc = TSTORE) /\
    op_taint tn addr = {} /\ op_taint tn src = {} /\
    ~ctx_has_dalloca ctx ==>
    ptr_inst_ok D 0 fuel ctx fn G tn
      (mk_inst id opc [addr; src] []) s
Proof
  rpt strip_tac >> gvs[] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def] >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds, opcode_case_def] >>
  simp[exec_write2_def, AllCaseEqs(), sstore_def, tstore_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem assign_base_storage_word_edge_ptr:
  !s fn bb id opc addr src tn G ctx u D PG.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id opc [addr; src] []) /\
    (opc = SSTORE \/ opc = TSTORE) /\
    op_taint tn addr = {} /\ op_taint tn src = {} /\
    ~ctx_has_dalloca ctx /\
    step_inst_base (mk_inst id opc [addr; src] []) s = OK u ==>
    gas_path_ptr_edge D 0 ctx fn PG G tn s 0
      (step_prov PG G (mk_inst id opc [addr; src] []) u)
      (step_taint (mk_inst id opc [addr; src] []) s u tn)
      (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn
     (mk_inst id opc [addr; src] []) s` by
    (irule assign_base_ptr_inst_ok_storage_word >> simp[]) >>
  mp_tac (Q.INST
    [`i` |-> `mk_inst id opc [addr; src] []`,
     `lo` |-> `0`] straight_line_ptr_edge) >>
  gvs[mk_inst_def, is_terminator_def]
QED
