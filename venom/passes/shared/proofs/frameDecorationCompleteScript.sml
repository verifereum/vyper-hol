Theory frameDecorationComplete
Ancestors frameDecorationEntry frameDecoratedEndpoints frameFiniteControl frameFiniteJointDecoration
  frameFiniteJointTrace frameFiniteExecution frameJointTransition
  contextCodegenRel venomExecSemantics venomExecProofs venomState venomInst list arithmetic

Theorem decorated_success_consumable:
  decorated_step C i s (OK post) q n w qm d /\
  decoration_at fn i s q /\ ~is_terminator i.inst_opcode /\
  active_inst fn next (post with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?ev qn. decoration_consumes C i q post qm ev qn /\
    decoration_entry fn (post with vs_inst_idx := SUC s.vs_inst_idx) qn
Proof
  strip_tac >> Cases_on `i.inst_opcode = INVOKE`
  >- (drule decorated_step_pending_exit >>
      simp[pending_exit_def] >> strip_tac >>
      Cases_on `q` >> gvs[decoration_at_def, resume_pending_def] >>
      gvs[local_pending_def] >>
      drule (cj 1 finite_execution_realizable) >> strip_tac >>
      `step_inst n' C ri sr = IntRet ret send` by simp[] >>
      qexists_tac `SOME (OriginResume n' callee ri sr ret send post)` >>
      simp[decoration_consumes_def] >>
      irule_at (Pos hd) joint_transition_ret >>
      simp[decoration_entry_def, decoration_at_def, resume_pending_def,
           local_pending_def] >> metis_tac[])
  >> drule (cj 1 decorated_execution_frame) >> simp[] >> strip_tac >>
  drule (cj 1 decorated_execution_erases) >> strip_tac >>
  drule (cj 1 finite_execution_realizable) >> strip_tac >>
  `step_inst n' C i s = OK post` by simp[] >>
  Cases_on `q` >> gvs[decoration_at_def] >>
  qexists_tac `SOME (OriginOrdinary n' post)` >>
  simp[decoration_consumes_def] >>
  irule_at (Pos hd) joint_transition_next >>
  simp[decoration_entry_def, decoration_at_def] >> metis_tac[]
QED

Theorem finite_decoration_complete:
  (!C i s r. finite_step C i s r ==>
    !fn q n. decoration_at fn i s q /\ ALL_DISTINCT (fn_labels fn) /\
      EVERY (\f. ALL_DISTINCT (fn_labels f)) C.ctx_functions ==>
      ?w qe d. decorated_step C i s r q n w qe d) /\
  (!C bb s r. finite_block C bb s r ==>
    !fn q n. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      decoration_entry fn s q /\ ALL_DISTINCT (fn_labels fn) /\
      EVERY (\f. ALL_DISTINCT (fn_labels f)) C.ctx_functions ==>
      ?w qe d. decorated_block C bb s r q n w qe d) /\
  (!C fn s r. finite_run C fn s r ==>
    !q n p. enters_block fn s p /\ decoration_entry fn p q /\
      ALL_DISTINCT (fn_labels fn) /\
      EVERY (\f. ALL_DISTINCT (fn_labels f)) C.ctx_functions ==>
      ?w qe d. decorated_run C fn s r q n w qe d)
Proof
  ho_match_mp_tac finite_step_strongind >> rpt conj_tac
  >- suspend "base"
  >- suspend "call_return"
  >- suspend "call_exit"
  >- suspend "block_term"
  >- suspend "block_next"
  >- suspend "block_exit"
  >- suspend "run_next"
  >- suspend "run_halt"
  >> suspend "run_exit"
QED

Resume finite_decoration_complete[base]:
  rpt strip_tac >>
  qexistsl_tac [`[]`, `q`, `FiniteDecoration n n []`] >>
  irule decorated_step_base >> simp[] >> metis_tac[]
QED

Resume finite_decoration_complete[block_term]:
  rpt strip_tac >>
  drule_all decoration_entry_instruction >> strip_tac >>
  first_x_assum (qspecl_then [`fn`, `q`, `n`] mp_tac) >>
  simp[] >> strip_tac >>
  irule_at Any decorated_step_block_term >> metis_tac[]
QED

Resume finite_decoration_complete[call_return]:
  rpt strip_tac >>
  rename1 `decoration_at caller i s q` >>
  `ALL_DISTINCT (fn_labels fn)` by
    (qpat_x_assum `EVERY _ C.ctx_functions` mp_tac >>
     simp[EVERY_MEM] >> disch_then irule >>
     fs[lookup_function_def] >> metis_tac[venomExecProofsTheory.FIND_MEM]) >>
  drule finite_run_entry_active >> strip_tac >>
  `?qc. joint_transition C q NONE qc /\ decoration_entry fn p qc` by
    (Cases_on `q` >> gvs[decoration_at_def] >>
     irule_at (Pos hd) joint_transition_call >>
     simp[decoration_entry_def, decoration_at_def] >> metis_tac[]) >>
  first_x_assum (qspecl_then [`qc`, `n+1`, `p`] mp_tac) >>
  simp[] >> strip_tac >>
  irule_at Any decorated_step_invoke_return >> metis_tac[]
QED
Resume finite_decoration_complete[call_exit]:
  rpt strip_tac >>
  rename1 `decoration_at caller i s q` >>
  `ALL_DISTINCT (fn_labels fn)` by
    (qpat_x_assum `EVERY _ C.ctx_functions` mp_tac >>
     simp[EVERY_MEM] >> disch_then irule >>
     fs[lookup_function_def] >> metis_tac[venomExecProofsTheory.FIND_MEM]) >>
  drule finite_run_entry_active >> strip_tac >>
  `?qc. joint_transition C q NONE qc /\ decoration_entry fn p qc` by
    (Cases_on `q` >> gvs[decoration_at_def] >>
     irule_at (Pos hd) joint_transition_call >>
     simp[decoration_entry_def, decoration_at_def] >> metis_tac[]) >>
  first_x_assum (qspecl_then [`qc`, `n+1`, `p`] mp_tac) >>
  simp[] >> strip_tac >>
  irule_at Any decorated_step_invoke_exit >> metis_tac[]
QED
Resume finite_decoration_complete[block_next]:
  rpt strip_tac >>
  drule_all decoration_entry_instruction >> strip_tac >>
  qpat_x_assum `!fn q n. decoration_at _ _ _ _ /\ _ ==> _`
    (qspecl_then [`fn`, `q`, `n`] mp_tac) >> simp[] >> strip_tac >>
  drule_all finite_block_next_active >> strip_tac >>
  drule_all decorated_success_consumable >> strip_tac >>
  drule_all finite_step_nonterminator_control >> strip_tac >>
  first_x_assum (qspecl_then [`fn`, `qn`, `n+LENGTH w+1`] mp_tac) >>
  simp[] >> strip_tac >>
  irule_at Any decorated_step_block_next >>
  goal_assum (drule_at (Pos hd)) >>
  goal_assum (drule_at (Pos hd)) >>
  goal_assum (drule_at (Pos hd)) >> simp[] >> metis_tac[]
QED
Resume finite_decoration_complete[block_exit]:
  rpt strip_tac >>
  drule_all decoration_entry_instruction >> strip_tac >>
  first_x_assum (qspecl_then [`fn`, `q`, `n`] mp_tac) >>
  simp[] >> strip_tac >>
  irule_at Any decorated_step_block_exit >> metis_tac[]
QED
Resume finite_decoration_complete[run_next]:
  rpt strip_tac >>
  `p = phi with vs_inst_idx := phi_prefix_length bb.bb_instructions` by
    gvs[enters_block_def] >> gvs[] >>
  drule eval_phis_preserves_current_bb >> strip_tac >>
  qpat_x_assum `!fn q n. _`
    (qspecl_then [`fn`, `q`, `n`] mp_tac) >> simp[] >> strip_tac >>
  drule (cj 2 decorated_execution_ok_endpoint) >>
  fs[decoration_entry_def] >> disch_then drule >> strip_tac >>
  drule finite_run_entry_active >> strip_tac >>
  gvs[local_pending_def] >>
  drule (cj 1 finite_execution_realizable) >> strip_tac >>
  `step_inst n' C ti si = OK s''` by simp[] >>
  `?qn. joint_transition C
    (JointConfig stk PG G tn fn ti si oms om hs h)
    (SOME (OriginBlock n' s'')) qn /\ decoration_entry fn p qn` by
    (irule_at (Pos hd) joint_transition_block >>
     simp[decoration_entry_def, decoration_at_def] >> metis_tac[]) >>
  first_x_assum (qspecl_then [`qn`, `n+LENGTH w+1`, `p`] mp_tac) >>
  (impl_tac >- (fs[decoration_entry_def] >> metis_tac[])) >> strip_tac >>
  `decoration_entry fn
     (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) q` by
    (simp[decoration_entry_def] >> metis_tac[]) >>
  irule_at Any decorated_block_run_sequence >>
  goal_assum (drule_at (Pos hd)) >>
  goal_assum (drule_at (Pos hd)) >>
  goal_assum (drule_at (Pos hd)) >>
  goal_assum (drule_at (Pos hd)) >> simp[] >>
  rule_assum_tac (PURE_REWRITE_RULE [ADD_ASSOC]) >>
  pure_rewrite_tac[ADD_ASSOC] >> metis_tac[]
QED
Resume finite_decoration_complete[run_halt]:
  rpt strip_tac >>
  `p = phi with vs_inst_idx := phi_prefix_length bb.bb_instructions` by
    gvs[enters_block_def] >> gvs[] >>
  drule eval_phis_preserves_current_bb >> strip_tac >>
  first_x_assum (qspecl_then [`fn`, `q`, `n`] mp_tac) >>
  simp[] >> strip_tac >>
  irule_at Any decorated_step_run_halt >> metis_tac[]
QED
Resume finite_decoration_complete[run_exit]:
  rpt strip_tac >>
  `p = phi with vs_inst_idx := phi_prefix_length bb.bb_instructions` by
    gvs[enters_block_def] >> gvs[] >>
  drule eval_phis_preserves_current_bb >> strip_tac >>
  first_x_assum (qspecl_then [`fn`, `q`, `n`] mp_tac) >>
  simp[] >> strip_tac >>
  irule_at Any decorated_step_run_exit >> metis_tac[]
QED
Finalise finite_decoration_complete

val _ = export_theory();
