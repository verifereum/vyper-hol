(* Exact taint transport for storage/transient word copies. Payload taint
   is allowed; only address and counter operands must remain clean. *)
Theory storageCopyBodyPtr
Ancestors
  storageCopyControlPtr ptrDiscipline ptrSafeRun codegenRel contextCodegenRel
  venomState venomInst finite_map pred_set words fragExecPtr memLocDefs

Theorem storage_copy_load_taint:
  eval_operand src s = SOME slot /\
  s'.vs_allocas = s.vs_allocas /\ s'.vs_fmp = s.vs_fmp ==>
  step_taint (mk_inst id (if tr then TLOAD else SLOAD) [src] [out]) s s' tn =
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

(* Byte offsets are unchanged, not endian-reversed. key_taint already
   intersects source taint with the 32-byte word interval. *)
Theorem storage_copy_store_written_taint:
  eval_operand dst s = SOME addr /\
  op_taint tn value = key_taint X slot ==>
  written_taint tn (mk_inst id MSTORE [dst;value] []) s =
    {w2n addr + r | r < 32 /\ (slot,r) IN X}
Proof
  simp[written_taint_def, mk_inst_def, key_taint_def]
QED

Theorem storage_copy_store_mem_taint:
  eval_operand dst s = SOME addr /\ eval_operand value s = SOME w /\
  op_taint tn value = key_taint X slot /\
  s'.vs_allocas = s.vs_allocas /\ s'.vs_fmp = s.vs_fmp ==>
  mem_taint tn (mk_inst id MSTORE [dst;value] []) s s' =
    (tn.t_mem DIFF {x | w2n addr <= x /\ x < w2n addr + 32}) UNION
    {w2n addr + r | r < 32 /\ (slot,r) IN X}
Proof
  strip_tac >>
  `new_site_bytes s s' = {}` by
    simp[new_site_bytes_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss] >>
  simp[mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       written_taint_def, key_taint_def,
       mk_inst_def, fixed_source_write_range_def, range_bytes_def] >>
  simp[EXTENSION]
QED

Theorem storage_copy_payload_byte_probe:
  key_taint {(17w:bytes32,7:num)} 17w = {7} /\
  written_taint (tn with t_var := tn.t_var |+ ("payload",{7}))
    (mk_inst 0 MSTORE [Lit 0w; Var "payload"] []) s = {7}
Proof
  simp[key_taint_def, written_taint_def, mk_inst_def, eval_operand_def,
       op_taint_def, FLOOKUP_UPDATE, EXTENSION]
QED

Theorem storage_copy_mstore_check:
  ptr_covers G tn p s 32 /\ ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn
    (mk_inst id MSTORE [Var p; value] []) s
Proof
  strip_tac >> gvs[bodyPtrDefsTheory.ptr_covers_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, fixed_source_write_range_def,
       eval_operand_def] >>
  conj_tac
  >- (Cases_on `eval_operand value s` >> simp[] >>
      rpt strip_tac >> gvs[] >> simp[mem_write_ops_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  simp[venomExecSemanticsTheory.step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[venomExecSemanticsTheory.step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds, opcode_case_def] >>
  simp[venomExecSemanticsTheory.exec_write2_def, eval_operand_def,
       AllCaseEqs(), mstore_def] >> rpt strip_tac >> gvs[]
QED
