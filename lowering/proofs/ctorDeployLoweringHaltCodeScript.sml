(* A piece of deploy_unit_execution_correct (ctorDeployLowering):
   a run never changes the code or the labels. *)
Theory ctorDeployLoweringHaltCode
Ancestors
  fragExec venomState venomInst venomExecSemantics venomInstProofs1 calleeTransport opcodeClass

Theorem pack_dret_dynamic_code[local]:
  !cursor pairs s ptrs fc s'.
    pack_dret_dynamic cursor pairs s = (ptrs, fc, s') ==>
    s'.vs_code = s.vs_code /\ s'.vs_labels = s.vs_labels
Proof
  Induct_on `pairs` >> simp[] >>
  Cases >> rw[pack_dret_dynamic_def] >>
  pairarg_tac >> gvs[] >> first_x_assum drule >>
  simp[mcopy_def, write_memory_with_expansion_def]
QED

Theorem step_inst_base_term_code[local]:
  !inst s s'.
    is_terminator inst.inst_opcode /\
    (step_inst_base inst s = OK s' \/
     (?r. step_inst_base inst s = IntRet r s') \/
     step_inst_base inst s = Halt s') ==>
    s'.vs_code = s.vs_code /\ s'.vs_labels = s.vs_labels
Proof
  rpt gen_tac >> Cases_on `inst.inst_opcode` >> simp[is_terminator_def] >>
  strip_tac >> qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  qpat_assum `inst.inst_opcode = _` (fn eq =>
    PURE_ONCE_REWRITE_TAC
      [tryfind (fn th => MATCH_MP th eq)
         (CONJUNCTS step_inst_base_opcode_eqs)]) >>
  simp[AllCaseEqs(), jump_to_def, halt_state_def, set_returndata_def] >>
  rpt strip_tac >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac pack_dret_dynamic_code >> gvs[]
QED

Theorem step_inst_base_code[local]:
  (!inst s s'. step_inst_base inst s = OK s' ==>
     s'.vs_code = s.vs_code /\ s'.vs_labels = s.vs_labels) /\
  (!inst s r s'. step_inst_base inst s = IntRet r s' ==>
     s'.vs_code = s.vs_code /\ s'.vs_labels = s.vs_labels) /\
  (!inst s s'. step_inst_base inst s = Halt s' ==>
     s'.vs_code = s.vs_code /\ s'.vs_labels = s.vs_labels)
Proof
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (Cases_on `is_terminator inst.inst_opcode`
      >- (irule step_inst_base_term_code >> metis_tac[]) >>
      drule_all step_inst_base_preserves_all >> simp[])
  >- (`is_terminator inst.inst_opcode` by
        (drule step_inst_base_intret_opcodes >> rw[] >>
         simp[is_terminator_def]) >>
      irule step_inst_base_term_code >> metis_tac[]) >>
  `is_terminator inst.inst_opcode` by
    (drule step_inst_base_halt_opcodes >> rw[] >> simp[is_terminator_def]) >>
  irule step_inst_base_term_code >> metis_tac[]
QED

Theorem eval_phis_code[local]:
  !insts s s'. eval_phis s insts = OK s' ==>
               s'.vs_code = s.vs_code /\ s'.vs_labels = s.vs_labels
Proof
  Induct >> rw[eval_phis_def] >> gvs[AllCaseEqs(), update_var_def] >>
  res_tac
QED

Theorem bind_outputs_code[local]:
  bind_outputs outs vals s = SOME s' ==>
  s'.vs_code = s.vs_code /\ s'.vs_labels = s.vs_labels
Proof
  strip_tac >> conj_tac >>
  irule bind_outputs_preserves >> simp[update_var_def] >> metis_tac[]
QED

Theorem run_defs_code[local]:
  (!fuel ctx inst s.
     (!s'. step_inst fuel ctx inst s = OK s' ==>
           s'.vs_code = s.vs_code /\ s'.vs_labels = s.vs_labels) /\
     (!r s'. step_inst fuel ctx inst s = IntRet r s' ==>
           s'.vs_code = s.vs_code /\ s'.vs_labels = s.vs_labels) /\
     (!s'. step_inst fuel ctx inst s = Halt s' ==>
           s'.vs_code = s.vs_code /\ s'.vs_labels = s.vs_labels)) /\
  (!fuel ctx bb s.
     (!s'. exec_block fuel ctx bb s = OK s' ==>
           s'.vs_code = s.vs_code /\ s'.vs_labels = s.vs_labels) /\
     (!r s'. exec_block fuel ctx bb s = IntRet r s' ==>
           s'.vs_code = s.vs_code /\ s'.vs_labels = s.vs_labels) /\
     (!s'. exec_block fuel ctx bb s = Halt s' ==>
           s'.vs_code = s.vs_code /\ s'.vs_labels = s.vs_labels)) /\
  (!fuel ctx fn s.
     (!s'. run_blocks fuel ctx fn s = OK s' ==>
           s'.vs_code = s.vs_code /\ s'.vs_labels = s.vs_labels) /\
     (!r s'. run_blocks fuel ctx fn s = IntRet r s' ==>
           s'.vs_code = s.vs_code /\ s'.vs_labels = s.vs_labels) /\
     (!s'. run_blocks fuel ctx fn s = Halt s' ==>
           s'.vs_code = s.vs_code /\ s'.vs_labels = s.vs_labels))
Proof
  ho_match_mp_tac run_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "run"
QED

Resume run_defs_code[step]:
  rpt gen_tac >> strip_tac >> rpt conj_tac >> rpt gen_tac >>
  Cases_on `inst.inst_opcode = INVOKE` >>
  simp[Once step_inst_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  imp_res_tac step_inst_base_code >>
  imp_res_tac setup_callee_shared_fields >>
  imp_res_tac bind_outputs_code >> res_tac >>
  gvs[adopt_return_fmp_def] >> BasicProvers.every_case_tac >>
  gvs[merge_callee_state_def]
QED

Resume run_defs_code[block]:
  rpt gen_tac >> strip_tac >> rpt conj_tac >> rpt gen_tac >>
  simp[Once exec_block_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  res_tac >> gvs[]
QED

Resume run_defs_code[run]:
  rpt gen_tac >> strip_tac >> rpt conj_tac >> rpt gen_tac >>
  simp[Once run_blocks_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs >> gvs[] >>
  imp_res_tac eval_phis_code >> res_tac >> gvs[]
QED

Finalise run_defs_code

Theorem run_from_halt_code:
  !fuel ctx func s final.
    run_from fuel ctx func s = Halt final ==>
    final.vs_code = s.vs_code /\ final.vs_labels = s.vs_labels
Proof
  rpt gen_tac >> simp[run_from_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  imp_res_tac run_defs_code >> gvs[]
QED
