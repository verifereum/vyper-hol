Theory bodyFullStoreSlotsStaticTransfer
Ancestors
  fragGasOriginPtr fragGasOrigin fragGasPathPtr ptrSafeRun ptrDiscipline
  gasEvents gasCount memSafeRun venomExecSemantics venomState venomInst
  contextCodegenRel codegenRel unitTransformDefs
  list finite_map arithmetic

Theorem slots_static_operand[local,simp]:
  eval_operand op (s with vs_call_ctx := (s.vs_call_ctx with cc_static := T)) =
  eval_operand op s
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def]
QED

Theorem slots_static_update_var[local,simp]:
  update_var x v (s with vs_call_ctx := (s.vs_call_ctx with cc_static := T)) =
  (update_var x v s) with vs_call_ctx :=
    ((update_var x v s).vs_call_ctx with cc_static := T)
Proof
  simp[update_var_def]
QED

Theorem slots_static_jump[local,simp]:
  jump_to lbl (s with vs_call_ctx := (s.vs_call_ctx with cc_static := T)) =
  (jump_to lbl s) with vs_call_ctx :=
    ((jump_to lbl s).vs_call_ctx with cc_static := T)
Proof
  simp[jump_to_def]
QED

Theorem slots_static_step_ok[local]:
  MEM inst.inst_opcode [ASSIGN; ADD; MUL; EQ; LT; ISZERO; SHR; MLOAD; JMP; JNZ] /\
  step_inst fuel ctx inst s = OK u ==>
  step_inst fuel ctx inst
    (s with vs_call_ctx := (s.vs_call_ctx with cc_static := T)) =
  OK (u with vs_call_ctx := (u.vs_call_ctx with cc_static := T))
Proof
  simp[MEM] >> strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_ASSIGN, step_inst_base_ADD,
      step_inst_base_MUL, step_inst_base_EQ, step_inst_base_LT,
      step_inst_base_ISZERO, step_inst_base_SHR, step_inst_base_MLOAD,
      step_inst_base_JMP, step_inst_base_JNZ,
      exec_pure1_def, exec_pure2_def, exec_read1_def, AllCaseEqs()] >>
  simp[mload_def]
QED

Theorem slots_static_phi[local,simp]:
  eval_one_phi (s with vs_call_ctx := (s.vs_call_ctx with cc_static := T)) inst =
  eval_one_phi s inst
Proof
  simp[eval_one_phi_def]
QED

Theorem slots_static_phis[local]:
  !insts s u. eval_phis s insts = OK u ==>
  eval_phis (s with vs_call_ctx := (s.vs_call_ctx with cc_static := T)) insts =
  OK (u with vs_call_ctx := (u.vs_call_ctx with cc_static := T))
Proof
  Induct >> simp[eval_phis_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> first_x_assum drule >> simp[]
QED

Theorem slots_static_ranges[local,simp]:
  MEM inst.inst_opcode [ASSIGN; ADD; MUL; EQ; LT; ISZERO; SHR; MLOAD; JMP; JNZ] ==>
  source_memory_read_ranges inst
    (s with vs_call_ctx := (s.vs_call_ctx with cc_static := T)) =
    source_memory_read_ranges inst s /\
  source_memory_write_ranges inst
    (s with vs_call_ctx := (s.vs_call_ctx with cc_static := T)) =
    source_memory_write_ranges inst s
Proof
  simp[MEM] >> strip_tac >>
  simp[source_memory_read_ranges_def, source_memory_write_ranges_def]
QED

Theorem slots_static_checks[local]:
  MEM inst.inst_opcode [ASSIGN; ADD; MUL; EQ; LT; ISZERO; SHR; MLOAD; JMP; JNZ] ==>
  (access_ok lo G fn inst
     (s with vs_call_ctx := (s.vs_call_ctx with cc_static := T)) =
   access_ok lo G fn inst s) /\
  (taint_ok fn tn inst
     (s with vs_call_ctx := (s.vs_call_ctx with cc_static := T)) =
   taint_ok fn tn inst s) /\
  (mem_safe_step fuel ctx inst
     (s with vs_call_ctx := (s.vs_call_ctx with cc_static := T)) =
   mem_safe_step fuel ctx inst s)
Proof
  strip_tac >>
  simp[access_ok_def, taint_ok_def, in_revert_forward_def, about_to_revert_def] >>
  gvs[MEM, mem_safe_step_non_invoke, inst_mem_below_frontier_def,
      inst_dload_in_section_def, source_memory_read_ranges_def,
      source_memory_write_ranges_def]
QED

Theorem slots_readonly_step_frame[local]:
  MEM inst.inst_opcode [ASSIGN; ADD; MUL; EQ; LT; ISZERO; SHR; MLOAD; JMP; JNZ] ==>
  (!u. step_inst fuel ctx inst s = OK u ==> u.vs_requests = s.vs_requests) /\
  (!u. step_inst fuel ctx inst s <> Halt u)
Proof
  simp[MEM] >> strip_tac >>
  simp[step_inst_non_invoke, step_inst_base_ASSIGN, step_inst_base_ADD,
       step_inst_base_MUL, step_inst_base_EQ, step_inst_base_LT,
       step_inst_base_ISZERO, step_inst_base_SHR, step_inst_base_MLOAD,
       step_inst_base_JMP, step_inst_base_JNZ,
       exec_pure1_def, exec_pure2_def, exec_read1_def, AllCaseEqs(),
       update_var_def, jump_to_def] >>
  rpt strip_tac >> gvs[update_var_def, jump_to_def]
QED

Theorem slots_static_ptr_safe[local]:
  MEM inst.inst_opcode [ASSIGN; ADD; MUL; EQ; LT; ISZERO; SHR; MLOAD; JMP; JNZ] /\
  ptr_safe_step D lo fuel ctx fn PG G tn inst s ==>
  ptr_safe_step D lo fuel ctx fn PG G tn inst
    (s with vs_call_ctx := (s.vs_call_ctx with cc_static := T))
Proof
  strip_tac >>
  drule slots_static_checks >> strip_tac >>
  drule slots_readonly_step_frame >> strip_tac >>
  qspec_then `s with vs_call_ctx := (s.vs_call_ctx with cc_static := T)`
    mp_tac (GEN_ALL slots_readonly_step_frame) >>
  simp[] >> strip_tac >>
  gvs[ptr_safe_step_def, ptr_inst_ok_def, allocas_from_def,
      allocas_below_fmp_def, MEM] >> metis_tac[prim_recTheory.LESS_REFL]
QED

Theorem slots_static_ghost[local]:
  MEM inst.inst_opcode [ASSIGN; ADD; MUL; EQ; LT; ISZERO; SHR; MLOAD; JMP; JNZ] /\
  step_inst fuel ctx inst s = OK u ==>
  ghost_step fuel ctx PG G tn inst
    (s with vs_call_ctx := (s.vs_call_ctx with cc_static := T)) =
  ghost_step fuel ctx PG G tn inst s
Proof
  strip_tac >> drule_all slots_static_step_ok >> strip_tac >>
  gvs[MEM, ghost_step_def, step_prov_def, out_prov_def,
      step_taint_def, adopt_reset_def, mem_taint_def, new_site_bytes_def,
      step_writes_def, written_taint_def, out_taint_def,
      store_taint_def, imm_taint_def, source_memory_write_ranges_def]
QED

Theorem slots_static_entry[local,simp]:
  entry_prov fn
    (s with vs_call_ctx := (s.vs_call_ctx with cc_static := T)) G =
    entry_prov fn s G /\
  entry_taint_vars fn
    (s with vs_call_ctx := (s.vs_call_ctx with cc_static := T)) tn =
    entry_taint_vars fn s tn
Proof
  simp[entry_prov_def, entry_taint_vars_def]
QED
