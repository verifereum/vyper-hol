(* Advance the operational and ghost prefixes at the same emitted step. *)
Theory gasFocusLowerDloadActualInterior
Ancestors
  gasFocusLowerDloadCutGuards lowerDloadSafetyRelation lowerDloadSafetyKernel
  lowerDloadPtrPhaseNext lowerDloadPtrPhase lowerDloadPtrRel
  ptrDiscipline contextCodegenRel venomExecSemantics venomInst venomState list

Theorem ld_focus_actual_interior_next:
  ld_envelope q fn s s.vs_inst_idx X p /\ active_inst fn inst s /\
  t0.vs_inst_idx = p /\ ld_prefix C' gn X p h t0 t /\
  dload_prefix_match pfuel C' PH X h t0 H0 un0 t H un /\
  dload_control_match q fn gn s t inst X h /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) gn.fn_blocks) /\
  SUC h < LENGTH X /\ ti = EL h X /\ step_inst fuel C' ti t = OK v /\
  active_inst gn j (v with vs_inst_idx := SUC t.vs_inst_idx) ==>
  j = EL (SUC h) X /\
  ld_prefix C' gn X p (SUC h) t0 (v with vs_inst_idx := SUC t.vs_inst_idx) /\
  dload_prefix_match pfuel C' PH X (SUC h) t0 H0 un0
    (v with vs_inst_idx := SUC t.vs_inst_idx)
    (step_prov PH H ti v) (step_taint ti t v un) /\
  dload_control_match q fn gn s (v with vs_inst_idx := SUC t.vs_inst_idx)
    inst X (SUC h) /\
  (v with vs_inst_idx := SUC t.vs_inst_idx).vs_gas_readings = t0.vs_gas_readings
Proof
  strip_tac >> qpat_x_assum `ti = EL h X` SUBST_ALL_TAC >>
  drule dload_control_match_expansion >> strip_tac >>
  drule_all dload_supply_interior_shape >>
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  drule_all dload_expanded_step_blocks >> strip_tac >>
  drule_all dload_control_interior_next_fields >> strip_tac >>
  qpat_x_assum `j = EL (SUC h) X` SUBST_ALL_TAC >>
  `(EL h X).inst_opcode <> INVOKE` by fs[] >>
  `step_inst 0 C' (EL h X) t = OK v /\
   step_inst pfuel C' (EL h X) t = OK v` by fs[step_inst_non_invoke] >>
  drule_all ld_prefix_next >> strip_tac >>
  drule_all dload_prefix_extend >> strip_tac >>
  drule_all ld_expansion_prefix_readings >> simp[]
QED
