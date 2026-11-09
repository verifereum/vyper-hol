Theory frameFiniteControl
Ancestors frameFiniteExecution frameFiniteJointTrace contextCodegenRel
  venomInstProps venomExecProofs venomExecSemantics venomState venomInst list

Theorem finite_step_nonterminator_control:
  finite_step C i s (OK post) /\ ~is_terminator i.inst_opcode ==>
  post.vs_current_bb = s.vs_current_bb /\
  post.vs_inst_idx = s.vs_inst_idx /\ post.vs_prev_bb = s.vs_prev_bb
Proof
  strip_tac >> drule (cj 1 finite_execution_realizable) >> strip_tac >>
  `step_inst n C i s = OK post` by simp[] >>
  drule_all step_preserves_control_flow >> simp[]
QED

Theorem finite_block_entry_active:
  finite_block C bb s r /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
  ?i. get_instruction bb s.vs_inst_idx = SOME i /\ active_inst fn i s
Proof
  simp[Once finite_step_cases] >> rpt strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    (fs[lookup_block_def] >> drule venomExecProofsTheory.FIND_P >>
     drule venomExecProofsTheory.FIND_MEM >> simp[]) >>
  gvs[get_instruction_def, AllCaseEqs()] >>
  simp[active_inst_def] >> metis_tac[]
QED

(* A successful block ends at a real terminator.  Its pre-state retains
   the block label, even across successful calls in the block prefix. *)
Theorem finite_execution_block_endpoint:
  (!C i s r. finite_step C i s r ==> T) /\
  (!C bb s r. finite_block C bb s r ==> !post.
    r = OK post ==> ~post.vs_halted /\
    ?si i. si.vs_current_bb = s.vs_current_bb /\
      get_instruction bb si.vs_inst_idx = SOME i /\
      is_terminator i.inst_opcode /\ finite_step C i si (OK post)) /\
  (!C fn s r. finite_run C fn s r ==> T)
Proof
  ho_match_mp_tac finite_step_strongind >> simp[] >> rpt conj_tac
  >- (rpt strip_tac >> Cases_on `post.vs_halted` >> gvs[] >> metis_tac[])
  >- (rpt strip_tac >> gvs[] >>
      drule_all finite_step_nonterminator_control >> strip_tac >>
      qexistsl_tac [`si`, `i'`] >> simp[])
  >> rpt strip_tac >> gvs[]
QED

Theorem finite_block_ok_active_endpoint:
  finite_block C bb s (OK post) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
  ~post.vs_halted /\
  ?si i. active_inst fn i si /\ is_terminator i.inst_opcode /\
    finite_step C i si (OK post)
Proof
  strip_tac >> drule (cj 2 finite_execution_block_endpoint) >>
  simp[] >> strip_tac >> simp[] >>
  `lookup_block si.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = si.vs_current_bb` by
    (fs[lookup_block_def] >> drule venomExecProofsTheory.FIND_P >>
     drule venomExecProofsTheory.FIND_MEM >> simp[]) >>
  qexistsl_tac [`si`, `i`] >> simp[active_inst_def] >>
  gvs[get_instruction_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem finite_block_next_active:
  finite_step C i s (OK post) /\ ~is_terminator i.inst_opcode /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  finite_block C bb (post with vs_inst_idx := SUC s.vs_inst_idx) r ==>
  ?next. active_inst fn next (post with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> drule_all finite_step_nonterminator_control >> strip_tac >>
  drule finite_block_entry_active >> simp[] >> metis_tac[]
QED

val _ = export_theory();
