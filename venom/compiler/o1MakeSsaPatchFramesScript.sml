Theory o1MakeSsaPatchFrames
Ancestors
  o1MakeSsaVisitRetention makeSsaDefs list
  venomExecProofs

Theorem patch_instruction_projection:
  (!i ops. i.inst_opcode = PHI ==>
    f (i with inst_operands := ops) = f i) ==>
  MAP f (MAP (\i. if i.inst_opcode <> PHI then i else
    i with inst_operands := update_current_phi_for_pred rs pred i.inst_operands) insts) =
  MAP f insts
Proof
  strip_tac >> simp[MAP_MAP_o, combinTheory.o_DEF] >>
  irule MAP_CONG >> simp[] >> rpt strip_tac >> IF_CASES_TAC >> gvs[]
QED

Theorem patch_lookup_projection:
  (!i ops. i.inst_opcode = PHI ==>
    f (i with inst_operands := ops) = f i) ==>
  !succs bbs q bb rs pred.
    lookup_block q bbs = SOME bb ==>
    ?out. lookup_block q (update_current_succ_phis rs pred bbs succs) = SOME out /\
      out.bb_label = bb.bb_label /\
      MAP f out.bb_instructions = MAP f bb.bb_instructions
Proof
  strip_tac >> Induct >> simp[update_current_succ_phis_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `lookup_block h bbs` >> simp[]
  >- (first_x_assum drule >> simp[update_current_succ_phis_def]) >>
  `x.bb_label = h` by metis_tac[lookup_block_label] >>
  qmatch_goalsub_abbrev_tac `FOLDL _ patched succs` >>
  `?mid. lookup_block q patched = SOME mid /\
    mid.bb_label = bb.bb_label /\
    MAP f mid.bb_instructions = MAP f bb.bb_instructions` by
    (simp[Abbr `patched`, retention_lookup_replace] >>
     Cases_on `q = h` >> gvs[] >> simp[patch_instruction_projection]) >>
  qpat_x_assum `!bbs q bb rs pred. _` drule >>
  disch_then (qspecl_then [`rs`,`pred`] mp_tac) >>
  simp[update_current_succ_phis_def] >> metis_tac[]
QED

Theorem patch_lookup_indexed_frame:
  lookup_block q bbs = SOME bb ==>
  ?out. lookup_block q (update_current_succ_phis rs pred bbs succs) = SOME out /\
    out.bb_label = bb.bb_label /\
    LENGTH out.bb_instructions = LENGTH bb.bb_instructions /\
    !i. i < LENGTH bb.bb_instructions ==>
      (EL i out.bb_instructions).inst_opcode = (EL i bb.bb_instructions).inst_opcode /\
      (EL i out.bb_instructions).inst_outputs = (EL i bb.bb_instructions).inst_outputs /\
      ((EL i bb.bb_instructions).inst_opcode <> PHI ==>
        EL i out.bb_instructions = EL i bb.bb_instructions)
Proof
  strip_tac >>
  qspec_then `\i. (i.inst_opcode, i.inst_outputs,
    if i.inst_opcode = PHI then NONE else SOME i)` mp_tac (Q.GEN `f` patch_lookup_projection) >>
  simp[] >> disch_then drule >>
  disch_then (qspecl_then [`succs`,`rs`,`pred`] strip_assume_tac) >>
  qexists `out` >> simp[] >>
  `LENGTH out.bb_instructions = LENGTH bb.bb_instructions` by
    metis_tac[LENGTH_MAP] >> simp[] >> rpt strip_tac >>
  qpat_x_assum `MAP _ _ = MAP _ _` (mp_tac o Q.AP_TERM `EL i`) >>
  simp[EL_MAP] >> rpt strip_tac >> gvs[]
QED
