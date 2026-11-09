Theory lowerDloadPtrControlInversion
Ancestors lowerDloadPtrRel lowerDloadDefs venomInst venomExecSemantics
  venomState list

Theorem dload_supply_terminator_singleton[local]:
  lower_dload_inst_supply q i = (emitted,q') /\
  n < LENGTH emitted /\ is_terminator (EL n emitted).inst_opcode ==>
  n = 0 /\ emitted = [i]
Proof
  simp[lower_dload_inst_supply_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  gvs[is_terminator_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[AllCaseEqs(), is_terminator_def] >>
  `n = 0 \/ n = 1 \/ n = 2 \/ n = 3` by decide_tac >>
  gvs[is_terminator_def]
QED

Theorem dload_control_block_inversion:
  dload_control_match q f g s t i emitted n /\ j = EL n emitted /\
  is_terminator j.inst_opcode /\ step_inst fuel C' j t = OK t1 /\
  ~t1.vs_halted ==>
  n = 0 /\ emitted = [i] /\ j = i /\ MEM i.inst_opcode [JMP; JNZ; DJMP]
Proof
  strip_tac >> gvs[] >> drule dload_control_match_expansion >> strip_tac >>
  drule_all dload_supply_terminator_singleton >> strip_tac >> gvs[] >>
  Cases_on `i.inst_opcode` >> gvs[is_terminator_def] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> pairarg_tac >> gvs[]
QED

Theorem dload_control_next_source_guards:
  dload_control_match q f g s t i emitted n /\ j = EL n emitted /\
  ~is_terminator j.inst_opcode /\ j.inst_opcode <> INVOKE ==>
  ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE
Proof
  strip_tac >> drule dload_control_match_expansion >> strip_tac >>
  Cases_on `i.inst_opcode = DLOAD` >- simp[is_terminator_def] >>
  Cases_on `i.inst_opcode = DLOADBYTES` >- simp[is_terminator_def] >>
  `emitted = [i]` by
    (qpat_x_assum `lower_dload_inst_supply _ _ = _` mp_tac >>
     simp[lower_dload_inst_supply_def]) >>
  `n = 0` by gvs[] >> gvs[]
QED

val _ = if null (hyp dload_control_next_source_guards) then ()
        else raise Fail "next source guards: nonempty hypotheses";
