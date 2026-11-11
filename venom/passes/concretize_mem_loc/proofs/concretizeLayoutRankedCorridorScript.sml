Theory concretizeLayoutRankedCorridor
Ancestors frameRankedTerminalCorridor frameTerminalCorridor
  concretizeLayoutBlockPairing concretizeStepStructure
  venomExecSemantics venomState venomInst frameRelocationValues list arithmetic

Theorem layout_ranked_corridor_produce:
  !n k k'. layout_block_pair positions bb bb' k k' /\
  ranked_terminal_corridor bb bb k k n ==>
  ranked_terminal_corridor bb bb' k k' n
Proof
  Induct_on `n`
  >- (simp[ranked_terminal_corridor_def] >> rpt strip_tac >>
      `get_instruction bb' k' = SOME i` by
        (drule layout_block_pair_lookup >> disch_then drule >>
         simp[concretize_positions_unchanged]) >>
      metis_tac[]) >>
  rpt strip_tac >>
  `?i. get_instruction bb k = SOME i /\ i.inst_opcode = ASSIGN` by
    (fs[ranked_terminal_corridor_def] >>
     qpat_x_assum `!d. d < SUC n ==> _` (qspec_then `0` mp_tac) >> simp[] >> metis_tac[]) >>
  `get_instruction bb' k' = SOME i` by
    (drule layout_block_pair_lookup >> disch_then drule >>
         simp[concretize_positions_unchanged]) >>
  `layout_block_pair positions bb bb' (SUC k) (SUC k')` by
    (drule_all layout_block_pair_advance >>
     simp[concretize_positions_unchanged, ADD1]) >>
  `ranked_terminal_corridor bb bb (SUC k) (SUC k) n` by
    metis_tac[ranked_terminal_corridor_advance] >>
  `ranked_terminal_corridor bb bb' (SUC k) (SUC k') n` by metis_tac[] >>
  qpat_x_assum `!k k'. _` kall_tac >>
  fs[ranked_terminal_corridor_def, ADD_CLAUSES] >>
  rpt strip_tac >> Cases_on `d` >> simp[ADD_CLAUSES] >>
  qpat_x_assum `!d. d < n ==> ?i. _ /\ get_instruction bb' _ = _ /\ _`
    (qspec_then `n'` mp_tac) >> simp[ADD_CLAUSES]
QED

Theorem layout_terminal_corridor_ranked:
  layout_block_pair positions bb bb' k k' /\ terminal_corridor bb bb k j ==>
  ranked_terminal_corridor bb bb' k k' (j-k)
Proof
  strip_tac >> irule layout_ranked_corridor_produce >>
  conj_tac >- metis_tac[] >>
  fs[terminal_corridor_def, ranked_terminal_corridor_def] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

(* RETURNDATACOPY preserves domains and labels on both sides.  Its
   administrative successors keep their own cursor, not a shared index. *)
Theorem layout_returncopy_ranked_entry:
  ranked_terminal_corridor bb bb' (SUC s.vs_inst_idx) (SUC t.vs_inst_idx) n /\
  variable_domains s t /\ s.vs_labels = t.vs_labels /\
  i.inst_opcode = RETURNDATACOPY /\
  step_inst_base i s = OK p /\ step_inst_base i t = OK q ==>
  ranked_terminal_entry bb bb' n
    (p with vs_inst_idx := SUC p.vs_inst_idx)
    (q with vs_inst_idx := SUC q.vs_inst_idx)
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base i s = OK p` mp_tac >>
  qpat_x_assum `step_inst_base i t = OK q` mp_tac >>
  simp[step_inst_base_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  gvs[ranked_terminal_entry_def, variable_domains_def,
    write_memory_with_expansion_def, write_memory_def, lookup_var_def]
QED

Theorem layout_returncopy_ranked_abort:
  ranked_terminal_corridor bb bb' (SUC s.vs_inst_idx) (SUC t.vs_inst_idx) n /\
  variable_domains s t /\ s.vs_labels = t.vs_labels /\
  i.inst_opcode = RETURNDATACOPY /\
  step_inst_base i s = OK p /\ step_inst_base i t = OK q /\
  exec_block fuel C bb (p with vs_inst_idx := SUC p.vs_inst_idx) = Abort a post ==>
  ?post'. exec_block fuel C' bb' (q with vs_inst_idx := SUC q.vs_inst_idx) =
    Abort a post' /\ dead_result_rel D (Abort a post) (Abort a post')
Proof
  strip_tac >> drule_all layout_returncopy_ranked_entry >> strip_tac >>
  drule_all ranked_terminal_corridor_abort >> simp[]
QED

val _ = export_theory();
