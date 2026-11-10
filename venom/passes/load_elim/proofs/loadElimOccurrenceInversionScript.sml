Theory loadElimOccurrenceInversion
Ancestors
  loadElimOccurrence venomExecSemantics list

Theorem le_occ_prefix_phi_semantics:
  le_occ_prefix C fn s0 (pre ++ PhiOcc bb u p :: suffix) i s ==>
  lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis u bb.bb_instructions = OK p
Proof
  strip_tac >> drule le_occ_prefix_valid >>
  simp[EVERY_APPEND, le_occ_valid_def]
QED

Theorem le_occ_prefix_phi_inversion_aux[local]:
  !C fn s0 es i s. le_occ_prefix C fn s0 es i s ==>
  !pre bb u p suffix. es = pre ++ PhiOcc bb u p :: suffix ==>
  (pre = [] /\ u = s0) \/
  (?front prev j t k.
    pre = front ++ [StepOcc prev t.vs_inst_idx k t u] /\
    le_occ_prefix C fn s0 front j t /\
    lookup_block t.vs_current_bb fn.fn_blocks = SOME prev /\
    t.vs_inst_idx < LENGTH prev.bb_instructions /\
    EL t.vs_inst_idx prev.bb_instructions = j /\
    is_terminator j.inst_opcode /\
    step_inst k C j t = OK u /\ ~u.vs_halted)
Proof
  ho_match_mp_tac le_occ_prefix_strongind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> Cases_on `pre` >> simp[])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[APPEND_EQ_APPEND] >> strip_tac
      >- (Cases_on `l` >> gvs[] >> metis_tac[]) >>
      Cases_on `l` >> gvs[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[APPEND_EQ_APPEND] >> strip_tac
  >- (Cases_on `l` >> gvs[] >> metis_tac[]) >>
  Cases_on `l` >> gvs[] >>
  Cases_on `t` >> gvs[]
QED

Theorem le_occ_prefix_phi_inversion:
  le_occ_prefix C fn s0 (pre ++ PhiOcc bb u p :: suffix) i s ==>
  (pre = [] /\ u = s0) \/
  (?front prev j t k.
    pre = front ++ [StepOcc prev t.vs_inst_idx k t u] /\
    le_occ_prefix C fn s0 front j t /\
    lookup_block t.vs_current_bb fn.fn_blocks = SOME prev /\
    t.vs_inst_idx < LENGTH prev.bb_instructions /\
    EL t.vs_inst_idx prev.bb_instructions = j /\
    is_terminator j.inst_opcode /\
    step_inst k C j t = OK u /\ ~u.vs_halted)
Proof
  metis_tac[le_occ_prefix_phi_inversion_aux]
QED
