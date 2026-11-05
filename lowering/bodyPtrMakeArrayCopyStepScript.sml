(* Raw copy steps permit tainted data, but never tainted addresses. *)
Theory bodyPtrMakeArrayCopyStep
Ancestors
  typedCopyPtr fragExecPtr fragGasSeqPtr fragGasPathPtr bodyPtrDefs venomInst
  venomExecSemantics venomState context ptrSafeRun ptrDiscipline memLocDefs codegenRel contextCodegenRel

Theorem ptr_inst_ok_mstore_raw:
  !D ctx fn G tn s id p v fuel.
    ptr_covers G tn p s 32 /\ ~ctx_has_dalloca ctx ==>
    ptr_inst_ok D 0 fuel ctx fn G tn
      (mk_inst id MSTORE [Var p; v] []) s
Proof
  rpt strip_tac >> gvs[ptr_covers_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, fixed_source_write_range_def,
       eval_operand_def] >>
  conj_tac >-
    (Cases_on `eval_operand v s` >> simp[] >>
     rpt strip_tac >> gvs[] >> simp[mem_write_ops_def] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_write2_def, eval_operand_def, AllCaseEqs(), mstore_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem mstore_raw_ptr_path:
  ptr_covers G tn dst s 32 /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id MSTORE [Var dst; value] []) /\
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id MSTORE [Var dst; value] [])
      (mstore (w2n a) w s))
    (step_taint (mk_inst id MSTORE [Var dst; value] []) s
      (mstore (w2n a) w s) tn)
    (OK ((mstore (w2n a) w s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id MSTORE [Var dst; value] [])
      (mstore (w2n a) w s))
    (step_taint (mk_inst id MSTORE [Var dst; value] []) s
      (mstore (w2n a) w s) tn)
    (OK ((mstore (w2n a) w s) with vs_inst_idx := SUC s.vs_inst_idx))` by
    (mp_tac (Q.INST [`i` |-> `mk_inst id MSTORE [Var dst; value] []`,
                     `lo` |-> `0`, `u` |-> `mstore (w2n (a:256 word)) w s`]
                    straight_line_ptr_edge) >>
     gvs[] >> simp[mk_inst_def, is_terminator_def, ptr_inst_ok_mstore_raw,
                  Once step_inst_base_def, exec_write2_def, eval_operand_def]) >>
  drule (cj 2 gas_path_ptr_rules) >>
  disch_then (qspec_then `0` mp_tac) >>
  simp[gas_path_ptr_rules] >> disch_then irule >>
  irule (cj 1 gas_path_ptr_rules) >> simp[mstore_def]
QED

Theorem ptr_inst_ok_external_load:
  (opc = SLOAD \/ opc = TLOAD \/ opc = DLOAD) /\
  op_taint tn src = {} /\ allocas_from 0 s /\ ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id opc [src] [tmp]) s
Proof
  strip_tac >> gvs[] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       fixed_source_write_range_def, step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_read1_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem external_load_ptr_path:
  (opc = SLOAD \/ opc = TLOAD \/ opc = DLOAD) /\
  op_taint tn src = {} /\ allocas_from 0 s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc [src] [tmp]) /\
  step_inst_base (mk_inst id opc [src] [tmp]) s = OK u ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id opc [src] [tmp]) u)
    (step_taint (mk_inst id opc [src] [tmp]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id opc [src] [tmp]) u)
    (step_taint (mk_inst id opc [src] [tmp]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))` by
    (mp_tac (Q.INST [`i` |-> `mk_inst id opc [src] [tmp]`, `lo` |-> `0`]
                    straight_line_ptr_edge) >>
     simp[ptr_inst_ok_external_load] >> gvs[mk_inst_def, is_terminator_def]) >>
  drule (cj 2 gas_path_ptr_rules) >>
  disch_then (qspec_then `0` mp_tac) >>
  simp[gas_path_ptr_rules] >> disch_then irule >>
  irule (cj 1 gas_path_ptr_rules) >>
  `step_inst 0 ctx (mk_inst id opc [src] [tmp]) s = OK u` by
    simp[step_inst_non_invoke, mk_inst_def] >>
  drule venomInstProofsTheory.step_preserves_halted >>
  gvs[mk_inst_def, is_terminator_def]
QED
