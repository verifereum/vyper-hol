Theory frameRankedTerminalCorridor
Ancestors frameTerminalCorridor frameRelocationValues frameFiniteExecution
  stepWriteFootprintForward
  concretizeLayoutLocalTerminals venomExecSemantics venomState venomInst
  list arithmetic

Definition ranked_terminal_corridor_def:
  ranked_terminal_corridor bb bb' k k' n <=>
    (?i. get_instruction bb (k+n) = SOME i /\
         get_instruction bb' (k'+n) = SOME i /\ i.inst_opcode = REVERT) /\
    (!d. d < n ==> ?i. get_instruction bb (k+d) = SOME i /\
         get_instruction bb' (k'+d) = SOME i /\ i.inst_opcode = ASSIGN)
End

Definition ranked_terminal_entry_def:
  ranked_terminal_entry bb bb' n s t <=>
    ranked_terminal_corridor bb bb' s.vs_inst_idx t.vs_inst_idx n /\
    variable_domains s t /\ s.vs_labels = t.vs_labels
End

Theorem ranked_terminal_corridor_advance:
  ranked_terminal_corridor bb bb' k k' (SUC n) ==>
  ranked_terminal_corridor bb bb' (SUC k) (SUC k') n
Proof
  simp[ranked_terminal_corridor_def, ADD_CLAUSES] >> rpt strip_tac >>
  first_x_assum (qspec_then `SUC d` mp_tac) >> simp[ADD_CLAUSES]
QED

Theorem ranked_terminal_corridor_abort:
  !n bb bb' s t fuel C C' a post.
  ranked_terminal_entry bb bb' n s t /\
  exec_block fuel C bb s = Abort a post ==>
  ?post'. exec_block fuel C' bb' t = Abort a post' /\
    dead_result_rel D (Abort a post) (Abort a post')
Proof
  Induct_on `n`
  >- (rpt strip_tac >>
      fs[ranked_terminal_entry_def, ranked_terminal_corridor_def] >>
      `step_inst_base i s = Abort a post` by
        (gvs[Once exec_block_def, step_inst_non_invoke,
             is_terminator_def, AllCaseEqs()]) >>
      drule_all concretize_revert_complete >>
      disch_then (qspec_then `D` strip_assume_tac) >>
      gvs[] >> qexists_tac `post'` >>
      simp[Once exec_block_def, step_inst_non_invoke]) >>
  rpt strip_tac >> fs[ranked_terminal_entry_def] >>
  `?i. get_instruction bb s.vs_inst_idx = SOME i /\
       get_instruction bb' t.vs_inst_idx = SOME i /\ i.inst_opcode = ASSIGN` by
    (fs[ranked_terminal_corridor_def] >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  reverse (drule step_assign_cases >>
    disch_then (qspecl_then [`s`, `fuel`, `C`] strip_assume_tac))
  >- (gvs[] >>
      qpat_x_assum `exec_block fuel C bb s = Abort a post` mp_tac >>
      simp[Once exec_block_def]) >>
  rename1 `step_inst fuel C i s = OK p` >>
  `step_inst_base i s = OK p` by gvs[step_inst_non_invoke] >>
  drule_all terminal_assign_progress >> strip_tac >>
  `exec_block fuel C bb (p with vs_inst_idx := SUC s.vs_inst_idx) = Abort a post` by
    (gvs[] >>
     qpat_x_assum `exec_block fuel C bb s = Abort a post` mp_tac >>
     simp[Once exec_block_def, is_terminator_def]) >>
  drule ranked_terminal_corridor_advance >> strip_tac >>
  gvs[] >> once_rewrite_tac[exec_block_def] >>
  simp[step_inst_non_invoke, is_terminator_def] >>
  first_x_assum irule >>
  qexistsl_tac [`C`, `bb`, `p with vs_inst_idx := SUC s.vs_inst_idx`] >>
  fs[ranked_terminal_entry_def, variable_domains_def, lookup_var_def]
QED

Theorem ranked_terminal_entry_revert:
  ranked_terminal_entry bb bb' 0 s t /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  step_inst_base i s = Abort a post ==>
  ?post'. get_instruction bb' t.vs_inst_idx = SOME i /\
    step_inst_base i t = Abort a post' /\
    dead_result_rel D (Abort a post) (Abort a post')
Proof
  rpt strip_tac >>
  `get_instruction bb' t.vs_inst_idx = SOME i /\ i.inst_opcode = REVERT` by
    (fs[ranked_terminal_entry_def, ranked_terminal_corridor_def] >> metis_tac[]) >>
  `variable_domains s t /\ s.vs_labels = t.vs_labels` by
    fs[ranked_terminal_entry_def] >>
  drule_all concretize_revert_complete >>
  disch_then (qspec_then `D` strip_assume_tac) >> metis_tac[]
QED

Theorem ranked_terminal_entry_assign:
  ranked_terminal_entry bb bb' (SUC n) s t /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  step_inst_base i s = OK p ==>
  ?q. get_instruction bb' t.vs_inst_idx = SOME i /\
    step_inst_base i t = OK q /\
    ranked_terminal_entry bb bb' n
      (p with vs_inst_idx := SUC p.vs_inst_idx)
      (q with vs_inst_idx := SUC q.vs_inst_idx)
Proof
  rpt strip_tac >>
  `get_instruction bb' t.vs_inst_idx = SOME i /\ i.inst_opcode = ASSIGN` by
    (fs[ranked_terminal_entry_def, ranked_terminal_corridor_def] >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[] >> metis_tac[]) >>
  fs[ranked_terminal_entry_def] >>
  drule_all terminal_assign_progress >> strip_tac >>
  drule ranked_terminal_corridor_advance >> strip_tac >>
  qexists `q` >>
  fs[ranked_terminal_entry_def, variable_domains_def, lookup_var_def]
QED

val _ = export_theory();
