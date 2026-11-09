Theory frameDemandLastWrite
Ancestors frameDemandOwnership frameJointTaint frameJointTrace frameJointDemand
  frameActivationCache frameJointTransition finite_map list arithmetic

Theorem bounded_last_occurrence:
  !j:num. (?k. l <= k /\ k < j /\ P k) ==>
  ?m. l <= m /\ m < j /\ P m /\ (!k. m < k /\ k < j ==> ~P k)
Proof
  Induct >- simp[] >> strip_tac >>
  Cases_on `l <= j /\ P j`
  >- (qexists_tac `j` >> simp[] >> rpt strip_tac >> `F` by decide_tac) >>
  `?k. l <= k /\ k < j /\ P k` by
    (qexists_tac `k` >> simp[] >> Cases_on `k = j` >> gvs[] >> decide_tac) >>
  qpat_x_assum `(?k. _) ==> _` mp_tac >>
  (impl_tac >- metis_tac[]) >> strip_tac >> qexists_tac `m` >> simp[] >>
  rpt strip_tac >> `k'' <= j` by decide_tac >>
  Cases_on `k'' = j` >> gvs[] >> metis_tac[LESS_OR_EQ, LESS_EQ_TRANS]
QED

Theorem joint_untainted_cache_last_write:
  joint_trace vs0 C q0 es qs q /\ vs0.vs_allocas = FEMPTY /\ j <= LENGTH es /\
  activation_cache (EL j (q0::qs)) d owner aid (b,sz) /\
  b <= byte /\ byte < b + sz /\ byte NOTIN joint_mem_taint (EL j (q0::qs)) ==>
  ?t m. t < m /\ m < j /\
    allocation_birth C (EL t (q0::qs)) (EL t es) d owner aid (b,sz) /\
    byte IN joint_writes (EL m (q0::qs)) (EL m es) /\
    (!k. m < k /\ k < j ==> byte NOTIN joint_writes (EL k (q0::qs)) (EL k es)) /\
    (!k. t < k /\ k <= j ==> d <= activation_depth (EL k (q0::qs)) /\
      activation_cache (EL k (q0::qs)) d owner aid (b,sz))
Proof
  strip_tac >> drule_all joint_cache_birth >> strip_tac >>
  `?k. SUC t <= k /\ k < j /\ byte IN joint_writes (EL k (q0::qs)) (EL k es)` by
    (spose_not_then assume_tac >>
     `byte IN joint_mem_taint (EL j (q0::qs))` suffices_by simp[] >>
     qpat_x_assum `byte NOTIN joint_mem_taint _` kall_tac >>
     Cases_on `EL t (q0::qs)` >> gvs[allocation_birth_def] >>
     irule joint_trace_fresh_alloca_tainted >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `EL _ (_::_) = _`)) >>
     goal_assum (drule_at (Pat `EL _ es = _`)) >>
     goal_assum (drule_at (Pat `FLOOKUP _ _ = _`)) >>
     gvs[FLOOKUP_DEF]) >>
  `?m. SUC t <= m /\ m < j /\
    byte IN joint_writes (EL m (q0::qs)) (EL m es) /\
    (!k. m < k /\ k < j ==> byte NOTIN joint_writes (EL k (q0::qs)) (EL k es))` by
    (ho_match_mp_tac bounded_last_occurrence >> metis_tac[]) >>
  qexistsl_tac [`t`,`m`] >> simp[] >> decide_tac
QED
