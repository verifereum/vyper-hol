Theory frameFiniteJointTrace
Ancestors frameFiniteExecution frameJointTrace frameJointTransition contextCodegenRel
  venomExecProofs venomExecSemantics venomState venomInst list

Theorem finite_run_entry_active:
  finite_run C fn post r ==>
  ?p inst'. enters_block fn post p /\ active_inst fn inst' p
Proof
  simp[Once finite_step_cases] >> strip_tac >>
  qpat_x_assum `finite_block _ _ _ _` mp_tac >>
  simp[Once finite_step_cases] >> strip_tac >>
  drule eval_phis_preserves_current_bb >> strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = post.vs_current_bb` by
    (fs[lookup_block_def] >>
     drule venomExecProofsTheory.FIND_P >>
     drule venomExecProofsTheory.FIND_MEM >> simp[]) >>
  simp[enters_block_def, active_inst_def] >>
  gvs[get_instruction_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem finite_joint_block_extension:
  joint_trace vs0 C q0 es qs
    (JointConfig stk PG G tn fn inst s oms om hs h) /\
  active_inst fn inst s /\ is_terminator inst.inst_opcode /\
  finite_step C inst s (OK post) /\ ~post.vs_halted /\
  finite_run C fn post r ==>
  ?fuel p inst' q'.
    enters_block fn post p /\ active_inst fn inst' p /\
    step_inst fuel C inst s = OK post /\
    joint_transition C (JointConfig stk PG G tn fn inst s oms om hs h)
      (SOME (OriginBlock fuel post)) q' /\
    q' = JointConfig stk PG (entry_prov fn post G)
      (entry_taint_vars fn post tn) fn inst' p oms (origin_entry fn post om) hs
      (h ++ [OriginBlock fuel post; OriginObserve
        (OriginSnapshot fn PG (entry_prov fn post G)
          (origin_entry fn post om) inst' p)]) /\
    joint_trace vs0 C q0 (es ++ [SOME (OriginBlock fuel post)]) (qs ++ [q']) q'
Proof
  strip_tac >> drule finite_run_entry_active >> strip_tac >>
  drule (cj 1 finite_execution_realizable) >> strip_tac >>
  `step_inst n C inst s = OK post` by simp[] >>
  qexistsl_tac [`n`, `p`, `inst'`] >> simp[] >>
  qmatch_goalsub_abbrev_tac `joint_transition C _ _ next` >>
  `joint_transition C (JointConfig stk PG G tn fn inst s oms om hs h)
      (SOME (OriginBlock n post)) next` by
    (simp[joint_transition_block_iff, Abbr `next`] >> metis_tac[]) >>
  simp[] >> metis_tac[joint_trace_snoc]
QED

val _ = export_theory();
