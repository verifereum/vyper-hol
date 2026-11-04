(* Exact equality outside the three control coordinates. *)
Theory simplifyCfgControl
Ancestors
  simplifyCfgSimTools o1PassLift stateFrame unitMemInv contextCodegenRel codegenRel
  venomState venomExecSemantics venomWf list

Definition scfg_ctrl_def:
  scfg_ctrl c p n (s:venom_state) =
    s with <|vs_current_bb := c; vs_prev_bb := p; vs_inst_idx := n|>
End

Definition scfg_payload_def:
  scfg_payload s t <=>
    t = scfg_ctrl t.vs_current_bb t.vs_prev_bb t.vs_inst_idx s
End

Theorem scfg_ctrl_same[simp]:
  scfg_ctrl s.vs_current_bb s.vs_prev_bb s.vs_inst_idx s = s
Proof
  simp[scfg_ctrl_def]
QED

Theorem scfg_ctrl_compose[simp]:
  scfg_ctrl c p n (scfg_ctrl c' p' n' s) = scfg_ctrl c p n s
Proof
  simp[scfg_ctrl_def]
QED

Theorem scfg_payload_refl[simp]:
  scfg_payload s s
Proof
  simp[scfg_payload_def]
QED

Theorem scfg_payload_ctrl[simp]:
  scfg_payload s (scfg_ctrl c p n s)
Proof
  simp[scfg_payload_def, scfg_ctrl_def]
QED

Theorem scfg_payload_sym:
  scfg_payload s t ==> scfg_payload t s
Proof
  simp[scfg_payload_def] >> strip_tac >>
  qpat_x_assum `t = _` SUBST1_TAC >> simp[scfg_ctrl_def]
QED

Theorem scfg_payload_trans:
  scfg_payload s t /\ scfg_payload t u ==> scfg_payload s u
Proof
  simp[scfg_payload_def] >> rpt strip_tac >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >> gvs[]
QED

Theorem scfg_payload_operand:
  scfg_payload s t ==> eval_operand op s = eval_operand op t
Proof
  simp[scfg_payload_def] >> strip_tac >>
  qpat_x_assum `t = _` SUBST1_TAC >>
  Cases_on `op` >> simp[scfg_ctrl_def, eval_operand_def, lookup_var_def]
QED

Theorem scfg_payload_operands:
  !ops s t. scfg_payload s t ==> eval_operands ops s = eval_operands ops t
Proof
  Induct >> simp[eval_operands_def] >> rpt strip_tac >>
  metis_tac[scfg_payload_operand]
QED

Theorem scfg_payload_frame:
  scfg_payload s t ==> execution_frame s = execution_frame t
Proof
  pure_rewrite_tac[scfg_payload_def] >> strip_tac >>
  qpat_x_assum `t = _` SUBST1_TAC >> simp[scfg_ctrl_def]
QED

Theorem scfg_payload_allocas:
  scfg_payload s t ==> s.vs_allocas = t.vs_allocas
Proof
  pure_rewrite_tac[scfg_payload_def] >> strip_tac >>
  qpat_x_assum `t = _` SUBST1_TAC >> simp[scfg_ctrl_def]
QED

Theorem scfg_payload_mem_corr:
  scfg_payload s t ==> mem_corr i s i t
Proof
  strip_tac >>
  `!op. eval_operand op s = eval_operand op t` by
    metis_tac[scfg_payload_operand] >>
  `!ops. eval_operands ops s = eval_operands ops t` by
    metis_tac[scfg_payload_operands] >>
  qpat_x_assum `scfg_payload _ _` mp_tac >>
  pure_rewrite_tac[scfg_payload_def] >> strip_tac >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  simp[mem_corr_def, inst_mem_ranges_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, memory_range_of_operands_def,
       dret_memory_read_ranges_def, fixed_source_write_range_def,
       sized_source_write_range_def, scfg_ctrl_def]
QED

Theorem scfg_payload_call_corr:
  inst_wf i /\ scfg_payload s t ==> call_corr i s i t
Proof
  strip_tac >> drule call_corr_refl >>
  drule scfg_payload_frame >>
  `!ops. eval_operands ops s = eval_operands ops t` by
    metis_tac[scfg_payload_operands] >>
  simp[call_corr_def]
QED
