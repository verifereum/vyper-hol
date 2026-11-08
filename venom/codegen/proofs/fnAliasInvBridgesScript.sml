Theory fnAliasInvBridges
Ancestors
  fnAliasInvPrefix venomExecProps venomExecSemantics venomInst list

(* Success supplies actual PARAM outcomes; no entry value shape is needed. *)
Theorem exec_block_param_prefix_success:
  !n j bb s fuel ctx t.
    j + n <= LENGTH bb.bb_instructions /\ s.vs_inst_idx = j /\
    (!k. k < n ==> is_param_opcode (EL (j+k) bb.bb_instructions).inst_opcode) /\
    exec_block fuel ctx bb s = OK t ==>
    ?u. u.vs_inst_idx = j+n /\ u.vs_labels = s.vs_labels /\
        exec_block fuel ctx bb u = OK t
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (qexists_tac `s` >> simp[]) >>
  `j < LENGTH bb.bb_instructions` by decide_tac >>
  `is_param_opcode (EL j bb.bb_instructions).inst_opcode` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `~is_terminator (EL j bb.bb_instructions).inst_opcode` by
    (Cases_on `(EL j bb.bb_instructions).inst_opcode` >>
     gvs[is_param_opcode_def, is_terminator_def]) >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  simp_tac std_ss [Once exec_block_def, get_instruction_def] >>
  qpat_assum `s.vs_inst_idx = j` (fn th => rewrite_tac[th]) >>
  qpat_assum `j < _` (fn th => rewrite_tac[th]) >>
  qpat_assum `~is_terminator _` (fn th => rewrite_tac[th]) >>
  simp_tac std_ss [AllCaseEqs()] >> strip_tac >>
  fs[NoAsms] >>
  `s''.vs_labels = s.vs_labels` by metis_tac[step_inst_preserves_labels_always] >>
  first_x_assum (drule_at (Pat `exec_block _ _ _ _ = _`)) >>
  simp[] >> impl_tac
  >- (rpt strip_tac >>
      first_x_assum (qspec_then `SUC k` mp_tac) >>
      simp[arithmeticTheory.ADD_CLAUSES, arithmeticTheory.ADD_SYM]) >>
  strip_tac >> qexists_tac `u` >>
  fs[arithmeticTheory.ADD_CLAUSES, arithmeticTheory.ADD_SYM]
QED
