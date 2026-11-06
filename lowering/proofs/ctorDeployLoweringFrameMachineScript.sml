Theory ctorDeployLoweringFrameMachine
Ancestors
  vfmStepLength vfmRunWithinFrame vfmAccountFrame vfmHandleStep vfmRunCall
  vfmExecution vfmOperation vfmState vfmContext vfmSameFrame
Libs finite_mapLib

Theorem root_handle_preserves_length[local]:
  preserves_same_frame m /\ LENGTH s.contexts = 1 /\
  handle m handle_step s = (INL (),s') ==>
  LENGTH s'.contexts = 1
Proof
  rpt strip_tac >>
  `s.contexts <> []` by (strip_tac >> gvs[]) >>
  Cases_on `m s` >>
  `same_frame_rel s r` by
    metis_tac[preserves_same_frame_def] >>
  `LENGTH r.contexts = 1` by fs[same_frame_rel_def] >>
  Cases_on `q` >> gvs[handle_def] >>
  metis_tac[handle_step_preserves_length_1]
QED

Theorem root_noncall_step_length:
  wf_state s /\ LENGTH s.contexts = 1 /\
  (!op. FLOOKUP (FST (HD s.contexts)).msgParams.parsed
                   (FST (HD s.contexts)).pc = SOME op ==> ~is_call op) /\
  step s = (INL (),s') ==>
  LENGTH s'.contexts = 1
Proof
  rpt strip_tac >>
  `s.contexts <> []` by (strip_tac >> gvs[]) >>
  `step s = handle
     (case FLOOKUP (FST (HD s.contexts)).msgParams.parsed
                   (FST (HD s.contexts)).pc of
        NONE => if LENGTH (FST (HD s.contexts)).msgParams.code <=
                           (FST (HD s.contexts)).pc
                then step_inst Stop else step_inst Invalid
      | SOME op => ignore_bind (step_inst op) (inc_pc_or_jump op))
     handle_step s` by
    simp[IgnAsm `step s = _`, step_def, handle_def, bind_def,
         ignore_bind_def, get_current_context_def, return_def] >>
  qpat_x_assum `step s = (INL (),s')` mp_tac >>
  asm_rewrite_tac[] >> disch_tac >>
  Cases_on `FLOOKUP (FST (HD s.contexts)).msgParams.parsed
                   (FST (HD s.contexts)).pc` >> gvs[] >>
  irule root_handle_preserves_length >>
  goal_assum (drule_at Any) >> simp[] >>
  irule preserves_same_frame_ignore_bind >>
  simp[preserves_same_frame_step_inst_not_call,
       preserves_same_frame_inc_pc_or_jump]
QED

Theorem root_noncall_step_msgParams:
  wf_state s /\ LENGTH s.contexts = 1 /\
  (!op. FLOOKUP (FST (HD s.contexts)).msgParams.parsed
                   (FST (HD s.contexts)).pc = SOME op ==> ~is_call op) /\
  step s = (INL (),s') ==>
  (FST (HD s'.contexts)).msgParams = (FST (HD s.contexts)).msgParams
Proof
  strip_tac >>
  `LENGTH s'.contexts = 1` by metis_tac[root_noncall_step_length] >>
  drule step_same_frame_foreign >> simp[]
QED
