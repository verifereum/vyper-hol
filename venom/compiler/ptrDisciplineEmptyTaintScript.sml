Theory ptrDisciplineEmptyTaint
Ancestors
  ptrDiscipline venomExecSemantics venomMemProofs venomInstProofs1
  opcodeClass finite_map pred_set list

Definition var_taint_empty_def:
  var_taint_empty tv <=> !v m. FLOOKUP tv v = SOME m ==> m = {}
End

Definition taint_empty_def:
  taint_empty tn <=>
    tn.t_mem = {} /\ var_taint_empty tn.t_var /\
    tn.t_stor = {} /\ tn.t_trans = {} /\ tn.t_imm = {}
End

Definition allocation_free_opcode_def:
  allocation_free_opcode opc <=>
    opc <> ALLOCA /\ opc <> DALLOCA /\ opc <> SETFMP /\
    opc <> DRET /\ opc <> RETFMP
End

Theorem entry_taint_empty:
  taint_empty entry_taint
Proof
  simp[taint_empty_def, var_taint_empty_def, entry_taint_def]
QED

Theorem op_taint_empty:
  taint_empty tn ==> op_taint tn op = {}
Proof
  strip_tac >> Cases_on `op` >> simp[op_taint_def] >>
  gvs[taint_empty_def, var_taint_empty_def] >>
  CASE_TAC >> simp[] >> metis_tac[]
QED

Theorem shift_taint_empty:
  shift_taint opc k {} = {}
Proof
  simp[shift_taint_def, EXTENSION]
QED

Theorem out_taint_empty:
  taint_empty tn ==> out_taint tn inst s = {}
Proof
  strip_tac >>
  simp[out_taint_def, op_taint_empty, shift_taint_empty,
       mem_word_taint_def, key_taint_def] >>
  gvs[taint_empty_def] >>
  rpt CASE_TAC >> simp[shift_taint_empty, op_taint_empty,
    mem_word_taint_def, key_taint_def]
QED

Theorem written_taint_empty:
  taint_empty tn ==> written_taint tn inst s = {}
Proof
  strip_tac >>
  `tn.t_mem = {}` by gvs[taint_empty_def] >>
  namedCases_on `inst.inst_operands` ["", "a xs"] >>
  simp[written_taint_def] >>
  namedCases_on `xs` ["", "v ys"] >> simp[written_taint_def] >>
  namedCases_on `ys` ["", "sz zs"] >>
  simp[written_taint_def, op_taint_empty] >-
    (rpt (CASE_TAC >> simp[])) >>
  namedCases_on `zs` ["", "extra rest"] >>
  simp[written_taint_def, op_taint_empty] >>
  rpt (CASE_TAC >> simp[])
QED

Theorem set_var_taint_empty:
  var_taint_empty tv ==> var_taint_empty (set_var_taint tv outs {})
Proof
  strip_tac >> simp[set_var_taint_def] >> rpt CASE_TAC >>
  gvs[var_taint_empty_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem key_update_empty:
  key_update {} key {} = {}
Proof
  simp[key_update_def, EXTENSION]
QED

Theorem store_taint_empty:
  taint_empty tn ==> store_taint opc tn inst s {} = {}
Proof
  strip_tac >> simp[store_taint_def, op_taint_empty] >>
  rpt (CASE_TAC >> simp[key_update_empty])
QED

Theorem imm_taint_empty:
  taint_empty tn ==> imm_taint tn inst s = {}
Proof
  strip_tac >> `tn.t_imm = {}` by gvs[taint_empty_def] >>
  simp[imm_taint_def, op_taint_empty] >>
  rpt (CASE_TAC >> simp[key_update_empty])
QED

Theorem step_taint_empty:
  taint_empty tn /\ new_site_bytes s s' = {} ==>
  taint_empty (step_taint inst s s' tn)
Proof
  strip_tac >>
  simp[step_taint_def, taint_empty_def, mem_taint_def,
       written_taint_empty, out_taint_empty, set_var_taint_empty,
       store_taint_empty, imm_taint_empty, adopt_reset_def] >>
  gvs[taint_empty_def, set_var_taint_empty] >>
  `taint_empty tn` by simp[taint_empty_def] >>
  simp[store_taint_empty]
QED

Theorem phi_taint_empty:
  taint_empty tn ==> phi_taint prev tn inst = {}
Proof
  strip_tac >> Cases_on `prev` >> simp[phi_taint_def] >>
  CASE_TAC >> simp[op_taint_empty]
QED

Theorem phis_taint_empty:
  taint_empty tn ==> var_taint_empty (phis_taint prev tn insts)
Proof
  Induct_on `insts` >> simp[phis_taint_def] >-
    simp[taint_empty_def] >>
  strip_tac >> simp[phi_taint_empty] >>
  CASE_TAC >> gvs[taint_empty_def, set_var_taint_empty]
QED

Theorem entry_taint_vars_empty:
  taint_empty tn ==> taint_empty (entry_taint_vars fn s tn)
Proof
  strip_tac >> simp[entry_taint_vars_def] >> CASE_TAC >>
  simp[taint_empty_def, phis_taint_empty] >> gvs[taint_empty_def]
QED

Theorem new_site_bytes_unchanged:
  s'.vs_allocas = s.vs_allocas /\ s'.vs_fmp = s.vs_fmp ==>
  new_site_bytes s s' = {}
Proof
  simp[new_site_bytes_def, EXTENSION, FLOOKUP_DEF] >> metis_tac[]
QED

Theorem var_taint_empty_restrict:
  var_taint_empty tv ==> var_taint_empty (DRESTRICT tv dom)
Proof
  simp[var_taint_empty_def, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem taint_empty_variables:
  taint_empty tn /\ var_taint_empty tv ==>
  taint_empty (tn with t_var := tv)
Proof
  simp[taint_empty_def]
QED

Theorem var_taint_empty_fempty:
  var_taint_empty FEMPTY
Proof
  simp[var_taint_empty_def]
QED

Theorem merge_callee_state_allocas:
  (merge_callee_state caller callee).vs_allocas = caller.vs_allocas
Proof
  simp[merge_callee_state_def]
QED

Theorem allocation_free_step_allocas:
  inst.inst_opcode <> INVOKE /\ allocation_free_opcode inst.inst_opcode /\
  (step_inst fuel ctx inst s = OK s' \/
   step_inst fuel ctx inst s = Halt s' \/
   (?a. step_inst fuel ctx inst s = Abort a s') \/
   (?v. step_inst fuel ctx inst s = IntRet v s')) ==>
  s'.vs_allocas = s.vs_allocas
Proof
  strip_tac >> gvs[step_inst_non_invoke, allocation_free_opcode_def] >>
  metis_tac[step_inst_base_preserves_allocas]
QED

Theorem allocation_free_nonterminator_fmp_ok[local]:
  inst.inst_opcode <> INVOKE /\ allocation_free_opcode inst.inst_opcode /\
  ~is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK s' ==>
  s'.vs_fmp = s.vs_fmp
Proof
  strip_tac >> gvs[step_inst_non_invoke, allocation_free_opcode_def] >>
  `~is_alloca_op inst.inst_opcode` by
    (Cases_on `inst.inst_opcode` >> gvs[venomInstTheory.is_alloca_op_def]) >>
  drule_all step_inst_base_preserves_all >> simp[] >> metis_tac[]
QED

Theorem allocation_free_step_intret:
  inst.inst_opcode <> INVOKE /\ allocation_free_opcode inst.inst_opcode /\
  step_inst fuel ctx inst s = IntRet ret s' ==>
  s' = s /\ ret.iret_adopt_fmp = NONE
Proof
  strip_tac >> gvs[step_inst_non_invoke, allocation_free_opcode_def] >>
  drule step_inst_base_intret_opcodes >> strip_tac >> gvs[] >>
  gvs[step_inst_base_def, AllCaseEqs()]
QED

Theorem allocation_free_terminator_fmp_ok[local]:
  allocation_free_opcode inst.inst_opcode /\
  is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK s' ==>
  s'.vs_fmp = s.vs_fmp
Proof
  strip_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[venomInstTheory.is_terminator_def, allocation_free_opcode_def] >>
  gvs[step_inst_non_invoke] >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> asm_rewrite_tac[] >>
  simp[] >> strip_tac >> gvs[AllCaseEqs(), venomStateTheory.jump_to_def]
QED

Theorem allocation_free_step_fmp_halt:
  inst.inst_opcode <> INVOKE /\ step_inst fuel ctx inst s = Halt s' ==>
  s'.vs_fmp = s.vs_fmp
Proof
  strip_tac >> gvs[step_inst_non_invoke] >>
  drule step_inst_base_halt_opcodes >> strip_tac >>
  qpat_x_assum `step_inst_base inst s = Halt s'` mp_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> asm_rewrite_tac[] >>
  simp[] >> strip_tac >>
  gvs[AllCaseEqs(), extract_venom_result_def,
      venomStateTheory.halt_state_def, venomStateTheory.set_returndata_def]
QED

Theorem allocation_free_step_fmp_ok:
  inst.inst_opcode <> INVOKE /\ allocation_free_opcode inst.inst_opcode /\
  step_inst fuel ctx inst s = OK s' ==> s'.vs_fmp = s.vs_fmp
Proof
  metis_tac[allocation_free_nonterminator_fmp_ok,
            allocation_free_terminator_fmp_ok]
QED

Theorem allocation_free_step_new_site_bytes:
  inst.inst_opcode <> INVOKE /\ allocation_free_opcode inst.inst_opcode /\
  step_inst fuel ctx inst s = OK s' ==> new_site_bytes s s' = {}
Proof
  strip_tac >> irule new_site_bytes_unchanged >>
  metis_tac[allocation_free_step_fmp_ok, allocation_free_step_allocas]
QED

Theorem bind_outputs_allocation_frame:
  bind_outputs outs vals s = SOME s' ==>
  s'.vs_allocas = s.vs_allocas /\ s'.vs_fmp = s.vs_fmp
Proof
  strip_tac >> conj_tac >>
  irule bind_outputs_preserves >>
  simp[venomStateTheory.update_var_def] >> metis_tac[]
QED

Theorem ret_taint_empty:
  taint_empty tn ==> ret_taint tn inst s = {}
Proof
  strip_tac >> `tn.t_mem = {}` by gvs[taint_empty_def] >>
  simp[ret_taint_def] >> rpt (CASE_TAC >> simp[EXTENSION])
QED
