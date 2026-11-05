(* Nonmemory word loads: safety is independent of output cleanliness. *)
Theory bodyPtrStructLitNonmemoryLoad
Ancestors
  bodyPtrStructLitMemoryUnwrap fragGasSeqPtr fragGasPathPtr ptrSafeRun
  ptrDiscipline venomExecSemantics venomInstProofs venomInst venomState list
  memLocDefs contextCodegenRel codegenRel

Theorem nonmemory_word_load_ptr_inst_ok:
  MEM opc [SLOAD; TLOAD; CALLDATALOAD; DLOAD] /\
  op_taint tn src = {} /\ ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id opc [src] [out]) s
Proof
  simp[MEM] >> strip_tac >> gvs[] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accfupds, instruction_accessors,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[mk_inst_def, exec_read1_def, update_var_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

Theorem nonmemory_word_load_counted:
  MEM opc [SLOAD; TLOAD; CALLDATALOAD; DLOAD] /\
  op_taint tn src = {} /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc [src] [out]) /\
  step_inst_base (mk_inst id opc [src] [out]) s = OK u ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id opc [src] [out]) u)
    (step_taint (mk_inst id opc [src] [out]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id opc [src] [out]) s` by
    (irule nonmemory_word_load_ptr_inst_ok >> simp[]) >>
  `opc <> INVOKE /\ ~is_terminator opc /\ opc <> GAS` by
    gvs[MEM, is_terminator_def] >>
  `step_inst 0 ctx (mk_inst id opc [src] [out]) s = OK u` by
    simp[step_inst_non_invoke, mk_inst_def] >>
  `~u.vs_halted` by
    (drule_at (Pat `step_inst _ _ _ _ = _`) step_preserves_halted >> simp[]) >>
  ` (mk_inst id opc [src] [out]).inst_opcode <> INVOKE /\
    ~is_terminator (mk_inst id opc [src] [out]).inst_opcode` by
    simp[mk_inst_def] >>
  drule_all straight_line_ptr_edge >>
  simp[mk_inst_def] >>
  disch_then (qspec_then `PG` assume_tac) >>
  drule (cj 2 gas_path_ptr_rules) >>
  simp[gas_path_ptr_rules]
QED
