(* Label containment for symbolic steps reading fixed own-code bytes. *)
Theory asmOwnLabels
Ancestors
  asmSymOwnCode asmSplice asmSymSem asmSem

Theorem sym_step_own_labels_in:
  MEM inst p /\ sym_state_labels_in (asm_label_refs p) ss /\
  sym_step_own p env own inst ss = SymOK ss' ==>
  sym_state_labels_in (asm_label_refs p) ss'
Proof
  Cases_on `inst = AsmOp "CODESIZE"`
  >- (gvs[sym_step_own_def, sym_step_op_own_def] >>
      strip_tac >> irule sym_set_stack_labels_in >>
      qpat_assum `_ = SymOK ss'` (irule_at Any) >>
      gvs[sym_state_labels_in_def] >> metis_tac[]) >>
  Cases_on `inst = AsmOp "CODECOPY"`
  >- (gvs[sym_step_own_def, sym_step_op_own_def] >>
      rw[sym_codecopy_own_def, AllCaseEqs()] >>
      irule sym_lift_labels_in >>
      qpat_assum `_ = SymOK ss'` (irule_at Any) >>
      gvs[sym_state_labels_in_def] >> metis_tac[mem_labels_clear_lookup]) >>
  `sym_step_own p env own inst ss = sym_step p env inst ss`
    by (Cases_on `inst` >>
        gvs[sym_step_own_def, sym_step_op_own_def, sym_step_def]) >>
  metis_tac[sym_step_labels_in]
QED
