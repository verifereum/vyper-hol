Theory o1MakeSsaCallCleanup
Ancestors
  o1MakeSsaCallPaths o1MakeSsaFormats unitShapeDefs makeSsaDefs list
  fmpStepList simplifyCfgCallChecks

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

Theorem simplify_current_phi_prefix_calls_flagged:
  EVERY (\i. i.inst_opcode = PHI) pre /\
  EVERY (\i. i.inst_opcode <> PHI) rest ==>
  (calls_flagged env (simplify_current_phi_prefix (pre ++ rest)) =
   calls_flagged env (pre ++ rest))
Proof
  strip_tac >> drule_all simplify_current_phi_prefix_parts_suffix >> strip_tac >>
  `LENGTH (phis ++ copies ++ rest) <= LENGTH (MAP (\i. i.inst_id) (pre ++ rest))` by
    (drule simplify_current_phi_prefix_parts_length >> simp[]) >>
  simp[simplify_current_phi_prefix_def, mssa_calls_flagged_reassign_ids] >>
  `EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL) pre` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  `calls_flagged env ((phis ++ copies) ++ rest) = calls_flagged env rest` by
    metis_tac[calls_flagged_prefix_no_calls] >>
  gvs[calls_flagged_prefix_no_calls, APPEND_ASSOC] >>
  mp_tac (Q.SPECL [`phis ++ copies ++ rest`,
    `MAP (\i. i.inst_id) pre ++ MAP (\i. i.inst_id) rest`]
    (mssa_calls_flagged_reassign_ids |> Q.INST [`bbs` |-> `env`])) >>
  simp[calls_flagged_prefix_no_calls]
QED

Theorem mssa_list_prefix_split[local]:
  !xs. list_prefix P xs ==>
  ?pre rest. xs = pre ++ rest /\ EVERY P pre /\ EVERY (\i. ~P i) rest
Proof
  Induct >- (simp[] >> qexistsl_tac [`[]`,`[]`] >> simp[]) >>
  simp[list_prefix_def] >> rpt strip_tac >> Cases_on `P h`
  >- (first_x_assum drule >> strip_tac >>
      qexistsl_tac [`h::pre`,`rest`] >> simp[]) >>
  qexistsl_tac [`[]`,`h::xs`] >> simp[]
QED

Theorem simplify_current_phi_prefix_calls_flagged_list_prefix:
  list_prefix (\i. i.inst_opcode = PHI) insts ==>
  (calls_flagged env (simplify_current_phi_prefix insts) = calls_flagged env insts)
Proof
  strip_tac >> drule mssa_list_prefix_split >> strip_tac >> gvs[] >>
  irule simplify_current_phi_prefix_calls_flagged >> simp[]
QED

Theorem simplify_current_phi_block_calls_flagged:
  list_prefix (\i. i.inst_opcode = PHI) bb.bb_instructions ==>
  (calls_flagged env (simplify_current_phi_block bb).bb_instructions =
   calls_flagged env bb.bb_instructions)
Proof
  strip_tac >> simp[simplify_current_phi_block_def] >>
  Cases_on `bb.bb_instructions` >> simp[] >> IF_CASES_TAC >> simp[] >>
  irule simplify_current_phi_prefix_calls_flagged_list_prefix >> simp[]
QED

Theorem simplify_current_phis_if_calls_flagged:
  EVERY (\bb. list_prefix (\i. i.inst_opcode = PHI) bb.bb_instructions) bbs ==>
  (EVERY (\bb. calls_flagged env bb.bb_instructions)
     (simplify_current_phis_if enabled bbs) =
   EVERY (\bb. calls_flagged env bb.bb_instructions) bbs)
Proof
  strip_tac >> simp[simplify_current_phis_if_def, simplify_current_phis_def] >>
  Cases_on `enabled` >> simp[] >> IF_CASES_TAC >> simp[EVERY_MAP] >>
  gvs[EVERY_MEM] >>
  metis_tac[simplify_current_phi_block_calls_flagged]
QED
