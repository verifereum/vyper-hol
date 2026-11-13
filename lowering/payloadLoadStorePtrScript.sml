(* Payload words may be tainted: only addressing operands must be clean. *)
Theory payloadLoadStorePtr
Ancestors
  fragExecPtr stmtAppendStorageRunPtr ptrSafeRun ptrDiscipline
  venomExecSemantics venomInst venomState finite_map pred_set codegenRel
  venomInstProofs bodyPtrDefs memLocDefs contextCodegenRel

Theorem storage_load_payload_taint:
  eval_operand a s = SOME slot /\
  s'.vs_allocas = s.vs_allocas /\ s'.vs_fmp = s.vs_fmp ==>
  step_taint (mk_inst id (if tr then TLOAD else SLOAD) [a] [out]) s s' tn =
    tn with t_var := tn.t_var |+
      (out,key_taint (if tr then tn.t_trans else tn.t_stor) slot)
Proof
  strip_tac >>
  `new_site_bytes s s' = {}` by
    simp[new_site_bytes_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss] >>
  Cases_on `tr` >>
  gvs[step_taint_def, set_var_taint_def, mk_inst_def, out_taint_def,
      mem_taint_def, step_writes_def, source_memory_write_ranges_def,
      written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
      range_bytes_def, taint_component_equality, DRESTRICT_UNIV]
QED

Theorem ptr_inst_ok_mstore_payload:
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
  conj_tac >- (rpt strip_tac >> gvs[]) >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accessors, instruction_accfupds, opcode_case_def, combinTheory.K_THM] >>
  simp[exec_write2_def, eval_operand_def, AllCaseEqs(), mstore_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem immutable_load_payload_taint:
  eval_operand a s = SOME addr /\
  s'.vs_allocas = s.vs_allocas /\ s'.vs_fmp = s.vs_fmp ==>
  step_taint (mk_inst id (if ctor then ILOAD else DLOAD) [a] [out]) s s' tn =
    tn with t_var := tn.t_var |+
      (out,if ctor then mem_word_taint tn.t_mem (w2n addr) else {})
Proof
  strip_tac >>
  `new_site_bytes s s' = {}` by
    simp[new_site_bytes_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss] >>
  Cases_on `ctor` >>
  gvs[step_taint_def, set_var_taint_def, mk_inst_def, out_taint_def,
      mem_taint_def, step_writes_def, source_memory_write_ranges_def,
      written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
      range_bytes_def, taint_component_equality, DRESTRICT_UNIV]
QED

Theorem payload_load_provenance:
  MEM opc [SLOAD; TLOAD; DLOAD; ILOAD] ==>
  op_prov (step_prov PG G (mk_inst id opc [a] [out]) s') (Var out) = NONE
Proof
  simp[step_prov_def, out_prov_def, set_prov_def, mk_inst_def,
       op_prov_def, FLOOKUP_DRESTRICT] >> rpt strip_tac >>
  gvs[FLOOKUP_DRESTRICT]
QED

Theorem ptr_inst_ok_storage_load_payload:
  op_taint tn a = {} /\ ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst id (if tr then TLOAD else SLOAD) [a] [out]) s = OK s' /\
  s'.vs_requests = s.vs_requests ==>
  ptr_inst_ok D 0 fuel ctx fn G tn
    (mk_inst id (if tr then TLOAD else SLOAD) [a] [out]) s
Proof
  strip_tac >> irule append_scalar_inst_check >>
  Cases_on `tr` >> simp[] >> metis_tac[]
QED

Theorem ptr_inst_ok_immutable_load_payload:
  op_taint tn a = {} /\ ~ctx_has_dalloca ctx /\
  access_ok 0 G fn (mk_inst id (if ctor then ILOAD else DLOAD) [a] [out]) s /\
  step_inst_base (mk_inst id (if ctor then ILOAD else DLOAD) [a] [out]) s = OK s' /\
  s'.vs_requests = s.vs_requests ==>
  ptr_inst_ok D 0 fuel ctx fn G tn
    (mk_inst id (if ctor then ILOAD else DLOAD) [a] [out]) s
Proof
  strip_tac >> Cases_on `ctor` >>
  gvs[ptr_inst_ok_def, taint_ok_def, allocas_from_def, mk_inst_def,
      source_memory_read_ranges_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke] >> metis_tac[]
QED

Theorem mstore_payload_memory_taint:
  eval_operand a s = SOME addr /\ eval_operand v s = SOME value /\
  s'.vs_allocas = s.vs_allocas /\ s'.vs_fmp = s.vs_fmp ==>
  (step_taint (mk_inst id MSTORE [a;v] []) s s' tn).t_mem =
    (tn.t_mem DIFF {i | w2n addr <= i /\ i < w2n addr + 32}) UNION
    {w2n addr + k | k IN op_taint tn v}
Proof
  strip_tac >>
  `new_site_bytes s s' = {}` by
    simp[new_site_bytes_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss] >>
  simp[step_taint_def, mem_taint_def, written_taint_def, step_writes_def,
       source_memory_write_ranges_def, fixed_source_write_range_def,
       mk_inst_def, range_bytes_def]
QED

Theorem immutable_load_access:
  (ctor ==> ptr_covers G tn p s 32) ==>
  access_ok 0 G fn
    (mk_inst id (if ctor then ILOAD else DLOAD) [Var p] [out]) s
Proof
  Cases_on `ctor` >>
  simp[access_ok_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, mk_inst_def] >>
  strip_tac >> gvs[ptr_covers_def, eval_operand_def] >>
  rpt strip_tac >> gvs[] >> simp[mem_read_ops_def] >> metis_tac[]
QED

Theorem payload_step_safe:
  MEM opc [SLOAD; TLOAD; DLOAD; ILOAD; MSTORE] ==>
  (ptr_safe_step D lo fuel ctx fn PG G tn (mk_inst id opc ops outs) s <=>
   ptr_inst_ok D lo fuel ctx fn G tn (mk_inst id opc ops outs) s)
Proof
  strip_tac >> gvs[ptr_safe_step_def, mk_inst_def]
QED

Theorem payload_load_runtime_frame:
  MEM opc [SLOAD; TLOAD; DLOAD; ILOAD] /\
  step_inst_base (mk_inst id opc [a] [out]) s = OK t ==>
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp /\
  t.vs_alloca_next = s.vs_alloca_next /\ t.vs_requests = s.vs_requests /\
  t.vs_memory = s.vs_memory /\
  (!x. x <> out ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def, instruction_accessors,
                   instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[exec_read1_def] >>
  Cases_on `eval_operand a s` >> simp[] >> strip_tac >>
  gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem mstore_payload_runtime_frame:
  step_inst_base (mk_inst id MSTORE [a;v] []) s = OK t ==>
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp /\
  t.vs_alloca_next = s.vs_alloca_next /\ t.vs_requests = s.vs_requests /\
  (!x. lookup_var x t = lookup_var x s)
Proof
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def, instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_write2_def, AllCaseEqs(), mstore_def, lookup_var_def] >>
  rpt strip_tac >> gvs[]
QED
