(* Temporal observation adapter. positions assigns positions to static sites;
 * depth/owner/cache witnesses are kept separately from numerical addresses.
 * The last trace configuration supplies reads, not an extra event. *)
Theory frameRelocationBinding
Ancestors
  frameRelocationDemand frameDemandTaint frameJointDemand frameJointTaint
  frameJointRevert o1PassContract
  frameActivationCache frameJointTrace frameJointTransition ptrDiscipline
  finite_map list pred_set arithmetic

Definition joint_read_exempt_def:
  joint_read_exempt (JointConfig stk PG G tn fn inst s oms om hs h) <=>
    in_revert_forward fn s
End

Definition joint_observed_read_def:
  joint_observed_read q a <=>
    a IN joint_reads q /\ a NOTIN joint_mem_taint q /\ ~joint_read_exempt q
End

Definition relocation_pair_def:
  relocation_pair lo positions q a z <=>
    (a < lo /\ z = a) \/
    (lo <= a /\ ?d owner aid b sz.
      activation_cache q d owner aid (b,sz) /\ b <= a /\ a < b+sz /\
      z = positions owner aid + (a-b))
End

Definition joint_relocation_demand_def:
  joint_relocation_demand lo positions q0 es qs n a z <=>
    ?j. n <= j /\ j <= LENGTH es /\
      joint_observed_read (EL j (q0::qs)) a /\
      (!k. n <= k /\ k < j ==>
        a NOTIN joint_writes (EL k (q0::qs)) (EL k es)) /\
      relocation_pair lo positions (EL n (q0::qs)) a z /\
      relocation_pair lo positions (EL j (q0::qs)) a z
End

Theorem joint_relocation_demand_current:
  n <= LENGTH es /\ joint_observed_read (EL n (q0::qs)) a /\
  relocation_pair lo positions (EL n (q0::qs)) a z ==>
  joint_relocation_demand lo positions q0 es qs n a z
Proof
  rw[joint_relocation_demand_def] >> qexists_tac `n` >> simp[]
QED

Theorem joint_relocation_demand_retained:
  joint_trace vs0 C q0 es qs q /\ vs0.vs_allocas = FEMPTY /\
  joint_relocation_demand lo positions q0 es qs (SUC n) a z /\
  a NOTIN joint_writes (EL n (q0::qs)) (EL n es) ==>
  joint_relocation_demand lo positions q0 es qs n a z
Proof
  rw[joint_relocation_demand_def] >> qexists_tac `j` >>
  `n <= j` by decide_tac >> simp[] >>
  conj_tac >- (rpt strip_tac >> Cases_on `k = n` >> gvs[] >>
               first_x_assum irule >> decide_tac) >>
  qpat_x_assum `relocation_pair _ _ (EL j _) _ _` mp_tac >>
  simp[relocation_pair_def] >> strip_tac >- simp[] >>
  `activation_cache (EL n (q0::qs)) d owner aid (b,sz)` by
    (irule (cj 2 joint_untainted_demand_cache) >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `activation_cache _ _ _ _ _`)) >>
     qexists_tac `a` >> simp[] >> qexists_tac `n` >>
     gvs[joint_observed_read_def] >> rpt strip_tac >>
     Cases_on `k = n` >> gvs[] >> first_x_assum irule >> decide_tac) >>
  metis_tac[]
QED

Theorem joint_relocation_demand_empty_entry:
  q0 = JointConfig [] PG G tn fn inst s oms om hs h /\
  s.vs_allocas = FEMPTY /\
  joint_relocation_demand lo positions q0 es qs 0 a z ==> z = a
Proof
  rw[joint_relocation_demand_def] >>
  gvs[relocation_pair_def, activation_cache_def]
QED

(* Total byte observation, including the implicit zero tail. *)
Definition joint_memory_observation_def:
  joint_memory_observation (JointConfig stk PG G tn fn inst s oms om hs h) =
    (\a. read_byte a s.vs_memory)
End

Theorem joint_relocation_demand_initial_agreement:
  q0 = JointConfig [] PG G tn fn inst s oms om hs h /\
  s.vs_allocas = FEMPTY ==>
  demand_agree (joint_relocation_demand lo positions q0 es qs 0)
    (joint_memory_observation q0) (joint_memory_observation q0)
Proof
  strip_tac >> irule demand_agree_identity >> rpt strip_tac >>
  sym_tac >> irule joint_relocation_demand_empty_entry >> metis_tac[]
QED

Theorem joint_nonrevert_read_exempt:
  joint_nonrevert q <=> ~joint_read_exempt q
Proof
  Cases_on `q` >> simp[joint_nonrevert_def, joint_read_exempt_def]
QED

Theorem joint_relocation_demand_nonrevert:
  joint_trace vs0 C q0 es qs q /\ o1_ctx_shape C /\
  joint_relocation_demand lo positions q0 es qs n a z ==>
  ~joint_read_exempt (EL n (q0::qs))
Proof
  rw[joint_relocation_demand_def, joint_observed_read_def] >>
  rewrite_tac[GSYM joint_nonrevert_read_exempt] >>
  irule joint_trace_nonrevert_read_at >>
  goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
  qexistsl_tac [`a`, `j`] >> simp[joint_nonrevert_read_exempt]
QED

Theorem joint_relocation_demand_clean:
  joint_trace vs0 C q0 es qs q /\
  joint_relocation_demand lo positions q0 es qs n a z ==>
  a NOTIN joint_mem_taint (EL n (q0::qs))
Proof
  rw[joint_relocation_demand_def, joint_observed_read_def] >>
  spose_not_then assume_tac >>
  `a IN joint_mem_taint (EL j (q0::qs))` suffices_by simp[] >>
  irule joint_trace_mem_taint >>
  goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
  qexists_tac `n` >> simp[]
QED

Theorem joint_relocation_demand_fresh_excluded:
  joint_trace vs0 C q0 es qs q /\ c < LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\ inst.inst_opcode = ALLOCA /\
  aid NOTIN FDOM s.vs_allocas /\ FLOOKUP post.vs_allocas aid = SOME (b,sz) /\
  b <= a /\ a < b+sz ==>
  ~joint_relocation_demand lo positions q0 es qs (SUC c) a z
Proof
  strip_tac >> spose_not_then assume_tac >>
  gvs[joint_relocation_demand_def, joint_observed_read_def] >>
  `a IN joint_mem_taint (EL j (q0::qs))` suffices_by simp[] >>
  irule joint_trace_fresh_alloca_tainted >>
  goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `EL _ (_::_) = _`)) >>
  goal_assum (drule_at (Pat `EL _ es = _`)) >>
  goal_assum (drule_at (Pat `FLOOKUP _ _ = _`)) >> simp[]
QED
