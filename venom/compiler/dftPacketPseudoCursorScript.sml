Theory dftPacketPseudoCursor
Ancestors
  dftPacketPseudoAdvance dftRunRel dftIndexedExec venomInst venomState
  venomExecSemantics venomWfProps finite_map list rich_list

Theorem dft_packet_pseudo_cursor_split:
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
  bt.bb_instructions = ps ++ ys /\
  l <= k /\ k < LENGTH ps /\ s.vs_inst_idx = k /\
  FOLDR (dft_exec_cons f C) OK (DROP l (TAKE k ps)) s0 = OK s /\
  step_inst f C (EL k ps) s = OK u /\
  s1 = u with vs_inst_idx := SUC k /\
  get_instruction bt s1.vs_inst_idx = SOME i1 ==>
  SUC k <= LENGTH ps /\ s1.vs_inst_idx = SUC k /\
  (!g D gs. FOLDR (dft_exec_cons g D) OK
    (DROP l (TAKE (SUC k) ps)) (s0 with vs_gas_readings := gs) =
    OK (s1 with vs_gas_readings := gs)) /\
  (SUC k < LENGTH ps ==> i1 = EL (SUC k) ps) /\
  (SUC k = LENGTH ps ==> ys <> [] /\ i1 = HD ys /\
    !g D gs. FOLDR (dft_exec_cons g D) OK (DROP l ps)
      (s0 with vs_gas_readings := gs) = OK (s1 with vs_gas_readings := gs))
Proof
  strip_tac >>
  drule_all dft_packet_pseudo_prefix_advance >> strip_tac >>
  `SUC k <= LENGTH ps` by decide_tac >>
  gvs[get_instruction_def] >>
  conj_tac >- (strip_tac >> gvs[EL_APPEND1]) >>
  strip_tac >> gvs[EL_APPEND2] >>
  Cases_on `ys` >> gvs[]
QED

Theorem dft_packet_pseudo_initialized:
  bb.bb_instructions = ps ++ xs /\
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  EVERY inst_wf bb.bb_instructions /\
  bb.bb_label = s.vs_current_bb /\ strict_dom_vars_defined sf s /\
  (!i l. MEM i bb.bb_instructions /\ ~is_pseudo i.inst_opcode /\
    ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
    i.inst_opcode <> CODECOPY /\ MEM (Label l) i.inst_operands ==>
    l IN FDOM s.vs_labels) /\
  eval_phis s ps = OK sp /\
  FOLDR (dft_exec_cons fuel C) OK (DROP (phi_prefix_length ps) ps)
    (sp with vs_inst_idx := phi_prefix_length ps) = OK be ==>
  dft_remaining_inv sf bb xs be
Proof
  strip_tac >>
  `FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions = ps /\
   FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions = xs` by
    (`FILTER (\i. is_pseudo i.inst_opcode) ps = ps /\
      FILTER (\i. is_pseudo i.inst_opcode) xs = [] /\
      FILTER (\i. ~is_pseudo i.inst_opcode) ps = [] /\
      FILTER (\i. ~is_pseudo i.inst_opcode) xs = xs` by
       simp[FILTER_EQ_ID, FILTER_EQ_NIL] >>
     simp[FILTER_APPEND]) >>
  qpat_x_assum `FILTER (\i. ~is_pseudo i.inst_opcode) _ = xs`
    (SUBST1_TAC o SYM) >>
  irule dft_remaining_inv_initialized >>
  simp[] >> qexistsl_tac [`C`, `fuel`, `s`, `sp`] >> gvs[] >>
  first_assum ACCEPT_TAC
QED
