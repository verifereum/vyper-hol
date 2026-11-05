Theory makeSsaCurrentEpochSplit
Ancestors makeSsaCurrentExecutionHistory makeSsaCurrentSemanticHistory
  venomExecSemantics venomInst venomState list

Theorem current_edge_header_batch:
  current_execution_edge fn ctx loc st phases next result after /\
  MEM (CurrentBatch h phis) phases ==>
  ?fuel bb post.
    loc = CurrentEntry (SUC fuel) /\ st.vs_current_bb = h /\
    lookup_block h fn.fn_blocks = SOME bb /\
    eval_phis st bb.bb_instructions = OK post /\
    phases = [CurrentBatch h
      (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions); CurrentControl] /\
    next = SOME (CurrentBody fuel bb) /\
    result = OK (post with vs_inst_idx := phi_prefix_length bb.bb_instructions) /\
    after = post with vs_inst_idx := phi_prefix_length bb.bb_instructions
Proof
  simp[current_execution_edge_cases] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem current_actual_prefix_last_header_dispatch:
  !loc st phases next result after.
  current_actual_prefix fn ctx loc st phases next result after ==>
  !h.
  (!phis. ~MEM (CurrentBatch h phis) phases) \/
  ?pre tail fuel before post bb.
    phases = pre ++ [CurrentBatch h
      (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions); CurrentControl] ++ tail /\
    current_actual_prefix fn ctx loc st pre
      (SOME (CurrentEntry (SUC fuel))) (OK before) before /\
    before.vs_current_bb = h /\ lookup_block h fn.fn_blocks = SOME bb /\
    eval_phis before bb.bb_instructions = OK post /\
    current_actual_prefix fn ctx (CurrentBody fuel bb)
      (post with vs_inst_idx := phi_prefix_length bb.bb_instructions)
      tail next result after /\
    (!phis. ~MEM (CurrentBatch h phis) tail)
Proof
  ho_match_mp_tac current_actual_prefix_strongind >> rpt strip_tac
  >- simp[]
  >- suspend "single"
  >- suspend "compose"
  >> simp[]
QED

Resume current_actual_prefix_last_header_dispatch[single]:
  Cases_on `!phis. ~MEM (CurrentBatch h phis) phases` >> simp[] >>
  gvs[] >> drule_all current_edge_header_batch >> strip_tac >> gvs[] >>
  qexistsl_tac [`[]`, `[]`, `fuel`, `st`, `post`] >>
  simp[current_actual_prefix_rules]
QED

Resume current_actual_prefix_last_header_dispatch[compose]:
  first_x_assum (qspec_then `h` strip_assume_tac)
  >- (Cases_on `!phis. ~MEM (CurrentBatch h phis) phases`
      >- (disj1_tac >> simp[MEM_APPEND]) >>
      gvs[] >> drule_all current_edge_header_batch >> strip_tac >> gvs[] >>
      qexistsl_tac [`[]`, `phases'`, `fuel`, `st`, `post`] >>
      simp[current_actual_prefix_rules]) >>
  disj2_tac >>
  qexistsl_tac [`phases ++ pre`, `tail`, `fuel`, `before`, `post`, `bb`] >>
  simp[APPEND_ASSOC] >>
  irule (cj 3 current_actual_prefix_rules) >> metis_tac[]
QED
Finalise current_actual_prefix_last_header_dispatch
