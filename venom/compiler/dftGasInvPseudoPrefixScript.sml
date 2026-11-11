Theory dftGasInvPseudoPrefix
Ancestors
  dftGasInvSSAProbe dftGasInvPrefixRun dftIndexedExec
  dftGasOracleDefs venomExecSemantics venomInst list

Theorem inv_pseudo_step:
  is_pseudo x.inst_opcode ==>
  ev_step orc p d f ctx x s = step_inst fuel ctx x s
Proof
  Cases_on `x.inst_opcode` >> simp[is_pseudo_def] >>
  simp[Once ev_step_def, Once step_inst_def]
QED

Theorem inv_pseudo_prefix_fold:
  !xs before s t.
    bb.bb_instructions = before ++ xs ++ after /\
    EVERY (\i. is_pseudo i.inst_opcode) xs /\
    s.vs_inst_idx = LENGTH before /\
    inv_ev_prefix orc p d ctx bb (LENGTH xs) s t ==>
    FOLDR (dft_exec_cons fuel ctx) OK xs s = OK t
Proof
  Induct >> simp[] >>
  rpt strip_tac >> fs[inv_ev_prefix_suc] >>
  `inst = h` by
    (gvs[get_instruction_def] >>
     qpat_x_assum `_ = inst` mp_tac >>
     simp[EL_APPEND_EQN]) >>
  `step_inst fuel ctx h s = OK u` by metis_tac[inv_pseudo_step] >>
  gvs[] >> simp[dft_exec_cons_def] >>
  first_x_assum irule >> simp[]
QED

Theorem inv_pseudo_prefix_drop:
  bb.bb_instructions = pseudos ++ normal /\
  EVERY (\i. is_pseudo i.inst_opcode) pseudos /\
  k <= LENGTH pseudos /\
  inv_ev_prefix orc p d ctx bb (LENGTH pseudos - k)
    (u with vs_inst_idx := k) t ==>
  FOLDR (dft_exec_cons fuel ctx) OK (DROP k pseudos)
    (u with vs_inst_idx := k) = OK t
Proof
  strip_tac >> irule inv_pseudo_prefix_fold >>
  conj_tac >- metis_tac[TAKE_DROP, EVERY_APPEND] >>
  simp[LENGTH_DROP] >> goal_assum (drule_at Any) >>
  qexistsl_tac [`normal`, `TAKE k pseudos`] >>
  simp[LENGTH_TAKE] >> metis_tac[TAKE_DROP, APPEND_ASSOC]
QED

Theorem inv_entry_oracle_residual_extension:
  wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  EVERY inst_wf bb.bb_instructions /\
  bb.bb_instructions = pseudos ++ normal /\
  EVERY (\i. is_pseudo i.inst_opcode) pseudos /\
  EVERY (\i. ~is_pseudo i.inst_opcode) normal /\
  fn_entry_label fn = SOME s.vs_current_bb /\ bb.bb_label = s.vs_current_bb /\
  ~s.vs_call_ctx.cc_static /\
  (!i l. MEM i bb.bb_instructions /\ ~is_pseudo i.inst_opcode /\
     ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
     i.inst_opcode <> CODECOPY /\ MEM (Label l) i.inst_operands ==>
     l IN FDOM s.vs_labels) /\
  eval_phis s bb.bb_instructions = OK u /\
  inv_ev_prefix orc p d ctx bb (LENGTH pseudos - phi_prefix_length pseudos)
    (u with vs_inst_idx := phi_prefix_length pseudos) t /\
  normal = pre ++ executed::post /\ pre ++ post = x::rest /\
  ~is_terminator executed.inst_opcode /\
  ev_step orc p d fuel ctx executed t = OK v /\
  inst_shape_ok x /\ ~is_terminator x.inst_opcode /\
  x.inst_opcode <> INVOKE /\ x.inst_opcode <> CODECOPY /\
  inv_memory_observation y.inst_opcode /\ ~dft_must_order x y ==>
  ?w. ev_step orc p d fuel ctx x
    (v with vs_inst_idx := SUC t.vs_inst_idx) = OK w
Proof
  strip_tac >>
  `FOLDR (dft_exec_cons fuel ctx) OK (DROP (phi_prefix_length pseudos) pseudos)
    (u with vs_inst_idx := phi_prefix_length pseudos) = OK t` by
    (irule inv_pseudo_prefix_drop >>
     simp[venomExecProofsTheory.phi_prefix_length_le] >>
     goal_assum (drule_at Any) >> simp[]) >>
  drule_all inv_entry_residual_extension >> simp[]
QED
