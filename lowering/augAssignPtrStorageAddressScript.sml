(* Storage addresses are clean scalar words, not memory pointers. *)
Theory augAssignPtrStorageAddress
Ancestors
  augAssignPtrInterfaces fragGasSeqPtr fragGasPathPtr bodyPtrDefs
  venomInst venomState venomExecSemantics ptrSafeRun ptrDiscipline
  emitHelper compileEnv fragExec contextCodegenRel codegenRel finite_map

Theorem ptr_inst_ok_storage_address_load_ptr:
  ~ctx_has_dalloca ctx /\ eval_operand addr s = SOME slot /\
  op_prov G addr = NONE /\ op_taint tn addr = {} ==>
  ptr_inst_ok D 0 fuel ctx fn G tn
    (mk_inst id (if tr then TLOAD else SLOAD) [addr] [out]) s
Proof
  strip_tac >> Cases_on `tr` >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_read_ranges_def, source_memory_write_ranges_def,
       step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_read1_def, update_var_def]
QED

Theorem storage_address_load_path_ptr:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  eval_operand addr s = SOME slot /\
  op_prov G addr = NONE /\ op_taint tn addr = {} /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id (if tr then TLOAD else SLOAD) [addr] [out]) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id (if tr then TLOAD else SLOAD) [addr] [out])
      (update_var out (if tr then tload slot s else sload slot s) s))
    (step_taint (mk_inst id (if tr then TLOAD else SLOAD) [addr] [out]) s
      (update_var out (if tr then tload slot s else sload slot s) s) tn)
    (OK ((update_var out (if tr then tload slot s else sload slot s) s)
      with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn
     (mk_inst id (if tr then TLOAD else SLOAD) [addr] [out]) s` by
    (irule ptr_inst_ok_storage_address_load_ptr >> simp[] >> metis_tac[]) >>
  `step_inst_base (mk_inst id (if tr then TLOAD else SLOAD) [addr] [out]) s =
     OK (update_var out (if tr then tload slot s else sload slot s) s)` by
    (Cases_on `tr` >> simp[step_inst_base_def, mk_inst_def, exec_read1_def]) >>
  `~(update_var out (if tr then tload slot s else sload slot s) s).vs_halted` by
    simp[update_var_def] >>
  mp_tac (Q.INST [`lo` |-> `0`,
    `u` |-> `update_var out (if tr then tload slot s else sload slot s) s`,
    `i` |-> `mk_inst id (if tr then TLOAD else SLOAD) [addr] [out]`]
    straight_line_ptr_edge) >>
  Cases_on `tr` >> gvs[mk_inst_def, is_terminator_def] >> strip_tac >>
  drule (cj 2 gas_path_ptr_rules) >> simp[] >>
  disch_then irule >> irule (cj 1 gas_path_ptr_rules) >> simp[]
QED

Theorem storage_address_load_ghost_clean_ptr:
  eval_operand addr s = SOME slot /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} ==>
  op_taint (step_taint
    (mk_inst id (if tr then TLOAD else SLOAD) [addr] [out]) s
    (update_var out v s) tn) (Var out) = {}
Proof
  Cases_on `tr` >>
  simp[step_taint_def, set_var_taint_def, out_taint_def, op_taint_def,
       mk_inst_def, FLOOKUP_UPDATE]
QED

Theorem literal_slot_add_path_ptr:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ADD [Lit a; Lit b] [out]) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id ADD [Lit a; Lit b] [out])
      (update_var out (a + b) s))
    (step_taint (mk_inst id ADD [Lit a; Lit b] [out]) s
      (update_var out (a + b) s) tn)
    (OK ((update_var out (a + b) s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id ADD [Lit a; Lit b] [out]) s` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_read_ranges_def, source_memory_write_ranges_def,
       op_taint_def, step_inst_non_invoke] >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     pure_rewrite_tac[instruction_accessors, instruction_accfupds,
                     combinTheory.K_THM, opcode_case_def] >>
     simp[exec_pure2_def, eval_operand_def, update_var_def] >>
     gen_tac >> Cases_on `op` >> gvs[] >> metis_tac[]) >>
  `step_inst_base (mk_inst id ADD [Lit a; Lit b] [out]) s =
     OK (update_var out (a + b) s)` by
    simp[step_inst_base_def, mk_inst_def, exec_pure2_def, eval_operand_def] >>
  mp_tac (Q.INST [`lo` |-> `0`, `u` |-> `update_var out (a + b) s`,
    `i` |-> `mk_inst id ADD [Lit a; Lit b] [out]`] straight_line_ptr_edge) >>
  gvs[mk_inst_def, is_terminator_def] >> strip_tac >>
  drule (cj 2 gas_path_ptr_rules) >> simp[] >>
  disch_then irule >> irule (cj 1 gas_path_ptr_rules) >> simp[update_var_def]
QED
