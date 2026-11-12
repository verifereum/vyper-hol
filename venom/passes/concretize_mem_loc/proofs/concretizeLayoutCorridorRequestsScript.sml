Theory concretizeLayoutCorridorRequests
Ancestors
  concretizeLayoutPhaseCorridor frameRankedTerminalCorridor
  frameTerminalCorridor frameRelocationValues concretizeLayoutLocalTerminals
  stepWriteFootprintForward
  venomExecSemantics venomState venomInst list arithmetic

(* Successful corridor instructions leave the external-call history alone. *)
Theorem corridor_step_ok_requests:
  (i.inst_opcode = ASSIGN \/ i.inst_opcode = RETURNDATACOPY) /\
  step_inst_base i s = OK p ==>
  p.vs_requests = s.vs_requests
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base i s = OK p` mp_tac >>
  simp[step_inst_base_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[update_var_def, write_memory_with_expansion_def, write_memory_def]
QED

Theorem corridor_revert_requests:
  i.inst_opcode = REVERT /\ step_inst_base i s = Abort a p ==>
  p.vs_requests = s.vs_requests
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base i s = Abort a p` mp_tac >>
  simp[step_inst_base_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

(* Each side of a ranked corridor preserves its own history.  No relation
   between the histories, or between their memory contents, is needed. *)
Theorem ranked_terminal_abort_requests:
  !n bb bb' s t fuel C a post.
  ranked_terminal_entry bb bb' n s t /\
  exec_block fuel C bb s = Abort a post ==>
  post.vs_requests = s.vs_requests
Proof
  Induct_on `n`
  >- (rpt strip_tac >>
      fs[ranked_terminal_entry_def, ranked_terminal_corridor_def] >>
      `step_inst_base i s = Abort a post` by
        (gvs[Once exec_block_def, step_inst_non_invoke,
             is_terminator_def, AllCaseEqs()]) >>
      metis_tac[corridor_revert_requests]) >>
  rpt strip_tac >>
  `?i. get_instruction bb s.vs_inst_idx = SOME i /\
       i.inst_opcode = ASSIGN` by
    (fs[ranked_terminal_entry_def, ranked_terminal_corridor_def] >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[] >> metis_tac[]) >>
  reverse (drule step_assign_cases >>
    disch_then (qspecl_then [`s`, `fuel`, `C`] strip_assume_tac))
  >- (gvs[] >>
      qpat_x_assum `exec_block fuel C bb s = Abort a post` mp_tac >>
      simp[Once exec_block_def]) >>
  rename1 `step_inst fuel C i s = OK p` >>
  `step_inst_base i s = OK p` by gvs[step_inst_non_invoke] >>
  drule_all ranked_terminal_entry_assign >> strip_tac >>
  `p.vs_requests = s.vs_requests` by metis_tac[corridor_step_ok_requests] >>
  `p.vs_inst_idx = s.vs_inst_idx` by
    (qpat_x_assum `step_inst_base i s = OK p` mp_tac >>
     simp[step_inst_base_def, AllCaseEqs()] >> rpt strip_tac >>
     gvs[update_var_def]) >>
  `exec_block fuel C bb (p with vs_inst_idx := SUC p.vs_inst_idx) =
    Abort a post` by
    (qpat_x_assum `exec_block fuel C bb s = Abort a post` mp_tac >>
     simp[Once exec_block_def, is_terminator_def]) >>
  first_x_assum drule >> disch_then drule >> simp[]
QED

Theorem ranked_terminal_entry_sym:
  ranked_terminal_entry bb bb' n s t ==>
  ranked_terminal_entry bb' bb n t s
Proof
  simp[ranked_terminal_entry_def, ranked_terminal_corridor_def,
       variable_domains_def] >> metis_tac[]
QED

(* Reuse the existing matching execution; attach the two independent
   history-preservation facts rather than redoing its simulation. *)
Theorem ranked_terminal_corridor_abort_requests:
  ranked_terminal_entry bb bb' n s t /\
  exec_block fuel C bb s = Abort a post ==>
  ?post'. exec_block fuel C' bb' t = Abort a post' /\
    dead_result_rel D (Abort a post) (Abort a post') /\
    post.vs_requests = s.vs_requests /\
    post'.vs_requests = t.vs_requests
Proof
  rpt strip_tac >>
  drule_all ranked_terminal_corridor_abort >>
  disch_then (qspecl_then [`D`, `C'`] strip_assume_tac) >>
  drule ranked_terminal_entry_sym >> strip_tac >>
  qexists `post'` >>
  metis_tac[ranked_terminal_abort_requests]
QED

val _ = export_theory();
