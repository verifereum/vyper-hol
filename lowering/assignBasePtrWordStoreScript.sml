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
    op_taint tn addr = {} /\
    ~ctx_has_dalloca ctx ==>
    ptr_inst_ok D 0 fuel ctx fn G tn
      (mk_inst id opc [addr; src] []) s
Proof
  rpt strip_tac >> gvs[] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def] >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accessors, instruction_accfupds, opcode_case_def, combinTheory.K_THM] >>
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
    op_taint tn addr = {} /\
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

(* Stores transfer value taint without changing memory or variable ghosts. *)
Theorem assign_base_storage_word_ghost:
  !opc id addr src s u PG G tn key.
    (opc = SSTORE \/ opc = TSTORE) /\
    eval_operand addr s = SOME key /\ u.vs_allocas = s.vs_allocas /\
    u.vs_fmp = s.vs_fmp ==>
    step_prov PG G (mk_inst id opc [addr; src] []) u = G /\
    step_taint (mk_inst id opc [addr; src] []) s u tn =
      (if opc = SSTORE then
         tn with t_stor := key_update tn.t_stor key (op_taint tn src)
       else tn with t_trans := key_update tn.t_trans key (op_taint tn src))
Proof
  rpt strip_tac >> gvs[] >>
  simp[step_prov_def, set_prov_def, step_taint_def, mk_inst_def,
       store_taint_def, adopt_reset_def, imm_taint_def,
       mem_taint_def, step_writes_def, source_memory_write_ranges_def] >>
  simp[set_var_taint_def, taint_component_equality,
       finite_mapTheory.DRESTRICT_UNIV, new_site_bytes_def,
       range_bytes_def, written_taint_def, mk_inst_def,
       finite_mapTheory.FLOOKUP_DEF, pred_setTheory.EXTENSION] >>
  metis_tac[]
QED

Theorem assign_base_storage_word_state_frame:
  !opc id addr src s u.
    (opc = SSTORE \/ opc = TSTORE) /\
    step_inst_base (mk_inst id opc [addr; src] []) s = OK u ==>
    u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp /\
    u.vs_memory = s.vs_memory /\ u.vs_vars = s.vs_vars
Proof
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def, instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_write2_def, AllCaseEqs(), sstore_def, tstore_def] >>
  rpt strip_tac >> gvs[]
QED
