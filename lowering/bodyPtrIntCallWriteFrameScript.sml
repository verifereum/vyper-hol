Theory bodyPtrIntCallWriteFrame
Ancestors bodyPtrIntCallConfinement ptrDiscipline pred_set arithmetic
  venomExecSemantics codegenRel memSafeRun contextCodegenRel list

Theorem intcall_access_write_outside:
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  intcall_prov_outside P PG G /\ (!i. i < lo ==> i NOTIN P) /\
  MEM (off,len) (source_memory_write_ranges inst s) /\
  off <= a /\ a < off + len ==> a NOTIN P
Proof
  rpt strip_tac >>
  Cases_on `lo < off + len`
  >- (fs[access_ok_def] >>
      `len <> 0` by decide_tac >>
      qpat_x_assum `!off len. MEM (off,len) (source_memory_write_ranges inst s) /\ _ ==> _` drule >>
      simp[] >> rpt strip_tac >>
      fs[intcall_prov_outside_def] >>
      qpat_x_assum `!x site. FLOOKUP G x = SOME site ==> _` drule >>
      simp[intcall_site_outside_def, DISJOINT_DEF, EXTENSION] >>
      disch_then (qspec_then `a` mp_tac) >> simp[] >> decide_tac) >>
  `a < lo` by decide_tac >> metis_tac[]
QED

(* Only these store opcodes omit value evaluation in written_taint. *)
Theorem intcall_store_ok_evaluates:
  (inst.inst_opcode = MSTORE \/ inst.inst_opcode = ISTORE) /\
  inst.inst_operands = [a; v] /\ step_inst fuel ctx inst s = OK t ==>
  (?off. eval_operand a s = SOME off) /\
  (?value. eval_operand v s = SOME value)
Proof
  strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_def, exec_write2_def,
      AllCaseEqs()]
QED

Theorem intcall_written_taint_range_ok:
  step_inst fuel ctx inst s = OK t /\
  (!op k. MEM op inst.inst_operands /\ k IN op_taint tn op ==> k < 32)
  ==> written_taint tn inst s SUBSET
      range_bytes (source_memory_write_ranges inst s)
Proof
  strip_tac >>
  Cases_on `inst.inst_operands` >- simp[written_taint_def] >>
  rename1 `inst.inst_operands = a::rest` >>
  Cases_on `rest` >- simp[written_taint_def] >>
  rename1 `inst.inst_operands = a::v::rest` >>
  Cases_on `rest`
  >- (Cases_on `inst.inst_opcode = MSTORE \/ inst.inst_opcode = ISTORE`
      >- (drule_all intcall_store_ok_evaluates >> strip_tac >>
          gvs[written_taint_def, source_memory_write_ranges_def,
              fixed_source_write_range_def, range_bytes_def, SUBSET_DEF] >>
          rpt strip_tac >> gvs[] >>
          first_x_assum (qspecl_then [`v`,`k`] mp_tac) >> simp[]) >>
      simp[written_taint_def]) >>
  rename1 `inst.inst_operands = a::v::n::rest` >>
  Cases_on `rest`
  >- (Cases_on `inst.inst_opcode = MCOPY` >>
      simp[written_taint_def] >>
      Cases_on `eval_operand a s` >> simp[] >>
      Cases_on `eval_operand v s` >> simp[] >>
      Cases_on `eval_operand n s` >>
      gvs[source_memory_write_ranges_def, sized_source_write_range_def,
          range_bytes_def, SUBSET_DEF] >> rpt strip_tac >> gvs[]) >>
  simp[written_taint_def]
QED

Theorem intcall_written_taint_outside_ok:
  step_inst fuel ctx inst s = OK t /\
  (!op k. MEM op inst.inst_operands /\ k IN op_taint tn op ==> k < 32) /\
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  intcall_prov_outside P PG G /\ (!i. i < lo ==> i NOTIN P)
  ==> written_taint tn inst s SUBSET COMPL P
Proof
  strip_tac >>
  drule_all intcall_written_taint_range_ok >>
  simp[SUBSET_DEF, range_bytes_def] >> strip_tac >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  metis_tac[intcall_access_write_outside, ADD_COMM]
QED

Theorem intcall_revert_forward_written_taint:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  revert_forward_at bb s.vs_inst_idx ==>
  written_taint tn inst s = {}
Proof
  strip_tac >> drule_all revert_forward_at_opcode >> strip_tac >>
  simp[written_taint_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[] >>
  Cases_on `t` >> simp[]
QED

Theorem intcall_in_revert_forward_written_taint:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  in_revert_forward fn s ==>
  written_taint tn inst s = {}
Proof
  strip_tac >> gvs[in_revert_forward_def] >>
  irule intcall_revert_forward_written_taint >>
  qexistsl [`bb`, `fn`] >> simp[]
QED

Theorem intcall_written_taint_outside_lookup:
  step_inst fuel ctx inst s = OK t /\
  (!op k. MEM op inst.inst_operands /\ k IN op_taint tn op ==> k < 32) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  access_ok lo G fn inst s /\
  intcall_prov_outside P PG G /\ (!i. i < lo ==> i NOTIN P) ==>
  written_taint tn inst s SUBSET COMPL P
Proof
  strip_tac >> Cases_on `in_revert_forward fn s`
  >- (drule_all intcall_in_revert_forward_written_taint >> simp[]) >>
  irule intcall_written_taint_outside_ok >> metis_tac[]
QED

Theorem intcall_written_taint_outside_zero:
  step_inst fuel ctx inst s = OK t /\
  (!op k. MEM op inst.inst_operands /\ k IN op_taint tn op ==> k < 32) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  access_ok 0 G fn inst s /\ intcall_prov_outside P PG G ==>
  written_taint tn inst s SUBSET COMPL P
Proof
  strip_tac >> irule intcall_written_taint_outside_lookup >>
  simp[] >> conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  qexistsl [`G`, `PG`, `bb`, `fn`, `0`] >> simp[]
QED
