Theory o1MakeSsaCallCleanup
Ancestors
  o1MakeSsaCallPaths o1MakeSsaFormats unitShapeDefs makeSsaDefs list
  fmpStepList

Theorem simplify_current_phi_prefix_parts_suffix:
  !pre rest.
  EVERY (\i. i.inst_opcode = PHI) pre /\
  EVERY (\i. i.inst_opcode <> PHI) rest ==>
  ?phis copies.
    simplify_current_phi_prefix_parts (pre ++ rest) = (phis,copies ++ rest) /\
    EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL)
      (phis ++ copies)
Proof
  Induct >- (Cases_on `rest` >> simp[simplify_current_phi_prefix_parts_def]) >>
  rpt gen_tac >> simp[] >> strip_tac >>
  first_x_assum (qspec_then `rest` mp_tac) >> simp[] >> strip_tac >>
  `((simplify_current_phi h).inst_opcode <> CALL /\
    (simplify_current_phi h).inst_opcode <> STATICCALL)` by
    (drule simplify_current_phi_classification >> simp[] >> strip_tac >> gvs[]) >>
  simp[simplify_current_phi_prefix_parts_def] >>
  Cases_on `(simplify_current_phi h).inst_opcode = PHI` >> simp[]
QED
