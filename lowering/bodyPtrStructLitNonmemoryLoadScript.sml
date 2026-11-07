(* Nonmemory word loads: safety is independent of output cleanliness. *)
Theory bodyPtrStructLitNonmemoryLoad
Ancestors
  bodyPtrStructLitMemoryUnwrap fragGasSeqPtr fragGasPathPtr ptrSafeRun
  ptrDiscipline venomExecSemantics venomInstProofs venomInst venomState list
  memLocDefs contextCodegenRel codegenRel accountsRelProps bodyPtrDefs

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

Theorem nonmemory_word_load_clean:
  MEM opc [SLOAD; TLOAD; CALLDATALOAD; DLOAD] /\
  eval_operand src s = SOME a /\
  (opc = SLOAD ==> key_taint tn.t_stor a = {}) /\
  (opc = TLOAD ==> key_taint tn.t_trans a = {}) ==>
  op_taint (step_taint (mk_inst id opc [src] [out]) s u tn)
    (Var out) = {}
Proof
  simp[MEM] >> strip_tac >> gvs[] >>
  simp[op_taint_def, step_taint_def, set_var_taint_def, out_taint_def,
       mk_inst_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem located_storage_base_key_clean:
  ptr_vv_ok cx t tv (LocatedValue t' p) es G tn s /\
  eval_operand p.ptr_operand s = SOME a /\
  evaluate_type (get_tenv cx) t = SOME ty /\
  0 < type_slot_size ty /\ p.ptr_location = LocStorage ==>
  key_taint tn.t_stor a = {}
Proof
  simp[ptr_vv_ok_def, key_taint_def, pred_setTheory.EXTENSION] >>
  rpt strip_tac >> simp[] >>
  spose_not_then strip_assume_tac >>
  first_x_assum (qspecl_then [`a`, `ty`, `a`, `x`] mp_tac) >>
  simp[] >> strip_tac >>
  drule (cj 1 dead_bytes_range) >> simp[]
QED

Theorem located_transient_base_key_clean:
  ptr_vv_ok cx t tv (LocatedValue t' p) es G tn s /\
  eval_operand p.ptr_operand s = SOME a /\
  evaluate_type (get_tenv cx) t = SOME ty /\
  0 < type_slot_size ty /\ p.ptr_location = LocTransient ==>
  key_taint tn.t_trans a = {}
Proof
  simp[ptr_vv_ok_def, key_taint_def, pred_setTheory.EXTENSION] >>
  rpt strip_tac >> simp[] >>
  spose_not_then strip_assume_tac >>
  first_x_assum (qspecl_then [`a`, `ty`, `a`, `x`] mp_tac) >>
  simp[] >> strip_tac >>
  drule (cj 1 dead_bytes_range) >> simp[]
QED

Theorem nonmemory_load_output_provenance:
  MEM opc [SLOAD; TLOAD; CALLDATALOAD; DLOAD] ==>
  op_prov (step_prov PG G (mk_inst id opc [src] [out]) u) (Var out) = NONE
Proof
  simp[MEM] >> strip_tac >> gvs[] >>
  irule step_prov_out_none >> simp[mk_inst_def] >>
  irule out_prov_other_none >> simp[mk_inst_def]
QED

Theorem nonmemory_word_load_ptr_val_ok:
  MEM opc [SLOAD; TLOAD; CALLDATALOAD; DLOAD] /\
  eval_operand src s = SOME a /\
  (opc = SLOAD ==> key_taint tn.t_stor a = {}) /\
  (opc = TLOAD ==> key_taint tn.t_trans a = {}) /\
  is_word_type t ==>
  ptr_val_ok cx t v (Var out)
    (step_prov PG G (mk_inst id opc [src] [out]) u)
    (step_taint (mk_inst id opc [src] [out]) s u tn) s'
Proof
  strip_tac >> simp[ptr_val_ok_def] >> conj_tac
  >- (irule nonmemory_word_load_clean >> simp[] >> metis_tac[]) >>
  irule nonmemory_load_output_provenance >> simp[]
QED
