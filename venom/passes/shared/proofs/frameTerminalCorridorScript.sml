Theory frameTerminalCorridor
Ancestors frameRelocationOpaque frameRelocationValues frameIndexedCertificates
          frameFiniteExecution stepWriteFootprintForward
          concretizeLayoutLocalTerminals venomExecSemantics venomState venomInst
          list arithmetic

(* A block-local terminal corridor has no cross-state memory obligation.
   Its instructions are paired exactly, but their operand VALUES may differ. *)
Definition terminal_corridor_def:
  terminal_corridor bb bb' k j <=>
    k <= j /\
    (?i. get_instruction bb j = SOME i /\
         get_instruction bb' j = SOME i /\ i.inst_opcode = REVERT) /\
    (!n. k <= n /\ n < j ==>
       ?i. get_instruction bb n = SOME i /\
           get_instruction bb' n = SOME i /\ i.inst_opcode = ASSIGN)
End

Definition terminal_entry_def:
  terminal_entry bb bb' j s t <=>
    terminal_corridor bb bb' s.vs_inst_idx j /\
    s.vs_inst_idx = t.vs_inst_idx /\
    variable_domains s t /\ s.vs_labels = t.vs_labels
End

Theorem terminal_corridor_advance:
  terminal_corridor bb bb' k j /\ k < j ==>
  terminal_corridor bb bb' (SUC k) j
Proof
  simp[terminal_corridor_def] >> rpt strip_tac >>
  first_x_assum irule >> decide_tac
QED

(* This inversion/transport wrapper consumes a successful source step; the
   underlying definedness and domain preservation theorem is reused. *)
Theorem terminal_assign_progress:
  variable_domains s t /\ s.vs_labels = t.vs_labels /\
  i.inst_opcode = ASSIGN /\ step_inst_base i s = OK p ==>
  ?q. step_inst_base i t = OK q /\ variable_domains p q /\
      p.vs_labels = q.vs_labels /\
      p.vs_inst_idx = s.vs_inst_idx /\ q.vs_inst_idx = t.vs_inst_idx
Proof
  rpt strip_tac >>
  qpat_x_assum `step_inst_base i s = OK p` mp_tac >>
  simp[step_inst_base_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_all opaque_assign_definedness >> strip_tac >>
  qexists_tac `update_var out y t` >>
  simp[update_var_def]
QED

Theorem terminal_corridor_abort:
  !n bb bb' j s t fuel C C' a post.
  terminal_entry bb bb' j s t /\ j = s.vs_inst_idx + n /\
  exec_block fuel C bb s = Abort a post ==>
  ?post'. exec_block fuel C' bb' t = Abort a post' /\
    dead_result_rel D (Abort a post) (Abort a post')
Proof
  Induct_on `n`
  >- (rpt strip_tac >>
      fs[terminal_entry_def, terminal_corridor_def] >>
      `step_inst_base i s = Abort a post` by
        (gvs[Once exec_block_def, step_inst_non_invoke,
             is_terminator_def, AllCaseEqs()]) >>
      drule_all concretize_revert_complete >>
      disch_then (qspec_then `D` strip_assume_tac) >>
      gvs[] >> qexists_tac `post'` >>
      simp[Once exec_block_def, step_inst_non_invoke]) >>
  rpt strip_tac >>
  fs[terminal_entry_def] >>
  `s.vs_inst_idx < j` by decide_tac >>
  `?i. get_instruction bb s.vs_inst_idx = SOME i /\
       get_instruction bb' t.vs_inst_idx = SOME i /\ i.inst_opcode = ASSIGN` by
    (fs[terminal_corridor_def] >> metis_tac[]) >>
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
  `terminal_corridor bb bb' (SUC s.vs_inst_idx) j` by
    (irule terminal_corridor_advance >> simp[] >> metis_tac[]) >>
  gvs[] >>
  once_rewrite_tac[exec_block_def] >>
  simp[step_inst_non_invoke, is_terminator_def] >>
  first_x_assum irule >>
  qexistsl_tac [`C`, `bb`, `p with vs_inst_idx := SUC t.vs_inst_idx`] >>
  fs[variable_domains_def, lookup_var_def, ADD_CLAUSES]
QED

(* Step entry retains the preincrement cursor.  The administrative boundary
   below advances both sides only after successful ASSIGN execution. *)
Theorem terminal_entry_assign:
  terminal_entry bb bb' j s t /\ s.vs_inst_idx < j /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  step_inst_base i s = OK p ==>
  ?q. get_instruction bb' t.vs_inst_idx = SOME i /\
      step_inst_base i t = OK q /\ terminal_entry bb bb' j p q /\
      p.vs_inst_idx = s.vs_inst_idx /\ q.vs_inst_idx = t.vs_inst_idx
Proof
  rpt strip_tac >>
  `get_instruction bb' t.vs_inst_idx = SOME i /\ i.inst_opcode = ASSIGN` by
    (fs[terminal_entry_def, terminal_corridor_def] >>
     first_x_assum (qspec_then `s.vs_inst_idx` mp_tac) >> simp[] >>
     metis_tac[]) >>
  `variable_domains s t /\ s.vs_labels = t.vs_labels` by
    fs[terminal_entry_def] >>
  drule_all terminal_assign_progress >> strip_tac >>
  qexists_tac `q` >> gvs[terminal_entry_def]
QED

Theorem terminal_entry_increment:
  terminal_entry bb bb' j s t /\ s.vs_inst_idx < j ==>
  terminal_entry bb bb' j
    (s with vs_inst_idx := SUC s.vs_inst_idx)
    (t with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  simp[terminal_entry_def, variable_domains_def, lookup_var_def] >>
  rpt strip_tac >> gvs[] >> irule terminal_corridor_advance >> simp[]
QED

Theorem terminal_entry_revert:
  terminal_entry bb bb' s.vs_inst_idx s t /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  step_inst_base i s = Abort a post ==>
  ?post'. get_instruction bb' t.vs_inst_idx = SOME i /\
    step_inst_base i t = Abort a post' /\
    dead_result_rel D (Abort a post) (Abort a post')
Proof
  rpt strip_tac >>
  `get_instruction bb' t.vs_inst_idx = SOME i /\ i.inst_opcode = REVERT` by
    (fs[terminal_entry_def, terminal_corridor_def] >> metis_tac[]) >>
  `variable_domains s t /\ s.vs_labels = t.vs_labels` by
    fs[terminal_entry_def] >>
  drule_all concretize_revert_complete >>
  disch_then (qspec_then `D` strip_assume_tac) >> metis_tac[]
QED

Theorem terminal_entry_abort:
  terminal_entry bb bb' j s t /\ exec_block fuel C bb s = Abort a post ==>
  ?post'. exec_block fuel C' bb' t = Abort a post' /\
    dead_result_rel D (Abort a post) (Abort a post')
Proof
  rpt strip_tac >> irule terminal_corridor_abort >>
  qexistsl_tac [`C`, `bb`, `j`, `j - s.vs_inst_idx`, `s`] >>
  fs[terminal_entry_def, terminal_corridor_def]
QED

val _ = export_theory();
