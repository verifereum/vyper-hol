Theory frameJointTaint
Ancestors frameJointDemand frameAllocationEffects frameJointTransition
  frameJointTrace frameOriginHistory ptrDiscipline list pred_set arithmetic

Definition joint_mem_taint_def:
  joint_mem_taint (JointConfig stk PG G tn fn inst s oms om hs h) = tn.t_mem
End

Theorem joint_transition_mem_taint:
  joint_transition C p ev q /\ byte IN joint_mem_taint p /\
  byte NOTIN joint_writes p ev ==> byte IN joint_mem_taint q
Proof
  simp[Once joint_transition_cases] >> rpt strip_tac >>
  gvs[joint_mem_taint_def, joint_writes_def, step_taint_def,
      mem_taint_def, entry_taint_vars_def] >>
  Cases_on `lookup_block s'.vs_current_bb fn.fn_blocks` >> gvs[]
QED

Theorem joint_trace_mem_taint:
  !j n. joint_trace vs0 C q0 es qs q /\ n <= j /\ j <= LENGTH es /\
  byte IN joint_mem_taint (EL n (q0::qs)) /\
  (!k. n <= k /\ k < j ==>
    byte NOTIN joint_writes (EL k (q0::qs)) (EL k es)) ==>
  byte IN joint_mem_taint (EL j (q0::qs))
Proof
  Induct >> rpt strip_tac >- gvs[] >>
  Cases_on `n = SUC j` >- gvs[] >>
  `n <= j /\ j < LENGTH es` by decide_tac >>
  `byte IN joint_mem_taint (EL j (q0::qs))` by
    (first_x_assum irule >> simp[] >> qexists_tac `n` >> simp[] >>
     rpt strip_tac >> first_x_assum irule >> simp[]) >>
  drule joint_trace_edge_at >> disch_then (qspec_then `j` mp_tac) >>
  simp[] >> strip_tac >> irule joint_transition_mem_taint >>
  goal_assum (drule_at (Pat `joint_transition _ _ _ _`)) >> simp[]
QED

Theorem joint_trace_fresh_alloca_tainted:
  joint_trace vs0 C q0 es qs q /\ c < j /\ j <= LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\ inst.inst_opcode = ALLOCA /\
  aid NOTIN FDOM s.vs_allocas /\ FLOOKUP post.vs_allocas aid = SOME (b,sz) /\
  b <= byte /\ byte < b + sz /\
  (!k. SUC c <= k /\ k < j ==>
    byte NOTIN joint_writes (EL k (q0::qs)) (EL k es)) ==>
  byte IN joint_mem_taint (EL j (q0::qs))
Proof
  strip_tac >>
  `c < LENGTH es` by decide_tac >>
  `byte IN joint_mem_taint (EL (SUC c) (q0::qs))` by
    (drule joint_trace_edge_at >> disch_then (qspec_then `c` mp_tac) >>
     simp[] >> strip_tac >>
     qpat_x_assum `joint_transition _ _ _ _` mp_tac >>
     simp[joint_transition_ordinary] >> strip_tac >>
     simp[joint_mem_taint_def] >> irule alloca_fresh_site_tainted >>
     simp[] >> goal_assum (drule_at (Pat `FLOOKUP _ _ = _`)) >> simp[]) >>
  irule joint_trace_mem_taint >>
  goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
  qexists_tac `SUC c` >> simp[]
QED

Theorem joint_trace_untainted_alloca_before:
  joint_trace vs0 C q0 es qs q /\ c < j /\ j <= LENGTH es /\ n <= j /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\ inst.inst_opcode = ALLOCA /\
  aid NOTIN FDOM s.vs_allocas /\ FLOOKUP post.vs_allocas aid = SOME (b,sz) /\
  b <= byte /\ byte < b + sz /\
  (!k. n <= k /\ k < j ==>
    byte NOTIN joint_writes (EL k (q0::qs)) (EL k es)) /\
  byte NOTIN joint_mem_taint (EL j (q0::qs)) ==> c < n
Proof
  strip_tac >> spose_not_then assume_tac >>
  `n <= c` by decide_tac >>
  `byte IN joint_mem_taint (EL j (q0::qs))` suffices_by simp[] >>
  irule joint_trace_fresh_alloca_tainted >>
  goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `EL _ (_::_) = _`)) >>
  goal_assum (drule_at (Pat `EL _ es = _`)) >>
  goal_assum (drule_at (Pat `FLOOKUP _ _ = _`)) >>
  simp[] >> rpt strip_tac >> first_x_assum irule >> simp[]
QED
