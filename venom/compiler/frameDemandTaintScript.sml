Theory frameDemandTaint
Ancestors frameDemandOwnership frameJointTaint frameJointTrace
  frameJointTransition frameActivationCache finite_map list arithmetic

Theorem joint_untainted_demand_cache:
  joint_trace vs0 C q0 es qs q /\ vs0.vs_allocas = FEMPTY /\
  n <= j /\ j <= LENGTH es /\
  activation_cache (EL j (q0::qs)) d owner aid (b,sz) /\
  b <= byte /\ byte < b + sz /\
  byte NOTIN joint_mem_taint (EL j (q0::qs)) /\
  (!k. n <= k /\ k < j ==>
    byte NOTIN joint_writes (EL k (q0::qs)) (EL k es)) ==>
  !k. n <= k /\ k <= j ==>
    d <= activation_depth (EL k (q0::qs)) /\
    activation_cache (EL k (q0::qs)) d owner aid (b,sz)
Proof
  strip_tac >> drule_all joint_cache_birth >> strip_tac >>
  `t < n` by
    (Cases_on `EL t (q0::qs)` >>
     gvs[allocation_birth_def] >>
     irule joint_trace_untainted_alloca_before >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `EL _ (_::_) = _`)) >>
     goal_assum (drule_at (Pat `EL _ es = _`)) >>
     goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
     qexistsl_tac [`byte`,`j`] >> simp[] >>
     gvs[FLOOKUP_DEF]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!i. t < i /\ i <= j ==> _` irule >> decide_tac
QED
