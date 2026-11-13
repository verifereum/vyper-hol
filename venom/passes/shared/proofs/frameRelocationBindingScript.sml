(* Temporal observation adapter. positions assigns positions to static sites;
 * depth/owner/cache witnesses are kept separately from numerical addresses.
 * The last trace configuration supplies reads, not an extra event. *)
Theory frameRelocationBinding
Ancestors
  frameRelocationDemand frameDemandTaint frameJointDemand frameJointTaint
  frameJointRevert o1PassContract
  frameActivationCache frameJointTrace frameJointTransition ptrDiscipline
  frameReadOwnership frameRawProjection frameOriginHistory frameOriginReachable
  frameResolvedTrace ctxLookupAgree
  finite_map list pred_set arithmetic

Definition joint_read_exempt_def:
  joint_read_exempt (JointConfig stk PG G tn fn inst s oms om hs h) <=>
    in_revert_forward fn s
End

Definition joint_observed_read_def:
  joint_observed_read q a <=>
    a IN joint_reads q /\ a NOTIN joint_mem_taint q /\ ~joint_read_exempt q
End

(* The bottom of the dynamic (DALLOCA) region of the current frame. *)
Definition joint_initial_fmp_def:
  joint_initial_fmp (JointConfig stk PG G tn fn inst s oms om hs h) =
    w2n s.vs_initial_fmp
End

(* A dynamic byte is relocated to itself, provided no live cache reaches
   the dynamic region. *)
Definition relocation_pair_def:
  relocation_pair lo positions q a z <=>
    (a < lo /\ z = a) \/
    (lo <= a /\ ?d owner aid b sz.
      activation_cache q d owner aid (b,sz) /\ b <= a /\ a < b+sz /\
      z = positions owner aid + (a-b)) \/
    (lo <= a /\ joint_initial_fmp q <= a /\
     (!d owner aid b sz. activation_cache q d owner aid (b,sz) ==>
        b + sz <= joint_initial_fmp q) /\ z = a)
End

Theorem relocation_pair_static:
  a < lo ==> relocation_pair lo positions q a a
Proof
  simp[relocation_pair_def]
QED

Theorem relocation_pair_cached:
  activation_cache q d owner aid (b,sz) /\ lo <= a /\ b <= a /\ a < b+sz /\
  z = positions owner aid + (a-b) ==>
  relocation_pair lo positions q a z
Proof
  strip_tac >> rewrite_tac[relocation_pair_def] >> disj2_tac >> disj1_tac >>
  simp[] >> qexistsl_tac [`d`, `owner`, `aid`, `b`, `sz`] >> simp[]
QED

Theorem relocation_pair_dynamic:
  lo <= a /\ joint_initial_fmp q <= a /\
  (!d owner aid b sz. activation_cache q d owner aid (b,sz) ==>
     b + sz <= joint_initial_fmp q) ==>
  relocation_pair lo positions q a a
Proof
  strip_tac >> rewrite_tac[relocation_pair_def] >> disj2_tac >> disj2_tac >>
  simp[] >> metis_tac[]
QED

Theorem relocation_pair_static_eq:
  a < lo ==> (relocation_pair lo positions q a z <=> z = a)
Proof
  strip_tac >> `~(lo <= a)` by decide_tac >> fs[relocation_pair_def]
QED

(* With every byte at or above lo inside a live cache, the dynamic branch
   is unavailable. *)
Theorem relocation_pair_covered:
  relocation_pair lo positions q a z ==>
  (lo <= a ==> ?d owner aid b sz.
     activation_cache q d owner aid (b,sz) /\ b <= a /\ a < b + sz) ==>
  (a < lo /\ z = a) \/
  (lo <= a /\ ?d owner aid b sz.
     activation_cache q d owner aid (b,sz) /\ b <= a /\ a < b+sz /\
     z = positions owner aid + (a-b))
Proof
  rewrite_tac[relocation_pair_def] >> strip_tac
  >- simp[]
  >- (rpt strip_tac >> disj2_tac >> simp[] >>
      qexistsl_tac [`d`, `owner`, `aid`, `b`, `sz`] >> simp[]) >>
  rpt strip_tac >> `F` suffices_by simp[] >>
  `?d owner aid b sz. activation_cache q d owner aid (b,sz) /\
     b <= a /\ a < b + sz` by metis_tac[] >>
  `b + sz <= joint_initial_fmp q` by metis_tac[] >> decide_tac
QED

Definition joint_relocation_demand_def:
  joint_relocation_demand lo positions q0 es qs n a z <=>
    ?j. n <= j /\ j <= LENGTH es /\
      joint_observed_read (EL j (q0::qs)) a /\
      (!k. n <= k /\ k < j ==>
        a NOTIN joint_writes (EL k (q0::qs)) (EL k es)) /\
      (z = a \/ ?d owner aid b sz.
         activation_cache (EL n (q0::qs)) d owner aid (b,sz) /\
         b <= a /\ a < b+sz /\ z = positions owner aid + (a-b)) /\
      relocation_pair lo positions (EL j (q0::qs)) a z
End

Theorem joint_relocation_demand_current:
  n <= LENGTH es /\ joint_observed_read (EL n (q0::qs)) a /\
  relocation_pair lo positions (EL n (q0::qs)) a z ==>
  joint_relocation_demand lo positions q0 es qs n a z
Proof
  rw[joint_relocation_demand_def] >> qexists_tac `n` >> simp[] >>
  qpat_x_assum `relocation_pair _ _ _ _ _` mp_tac >>
  rewrite_tac[relocation_pair_def] >> strip_tac
  >- simp[]
  >- (disj2_tac >> metis_tac[]) >>
  simp[]
QED

Theorem joint_relocation_demand_retained:
  joint_trace vs0 C q0 es qs q /\ vs0.vs_allocas = FEMPTY /\
  joint_relocation_demand lo positions q0 es qs (SUC n) a z /\
  a NOTIN joint_writes (EL n (q0::qs)) (EL n es) ==>
  joint_relocation_demand lo positions q0 es qs n a z
Proof
  simp[joint_relocation_demand_def, PULL_EXISTS] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qexists_tac `j` >> `n <= j` by decide_tac >>
  `!k. n <= k /\ k < j ==> a NOTIN joint_writes (EL k (q0::qs)) (EL k es)` by
    (rpt strip_tac >> Cases_on `k = n` >> gvs[] >>
     first_x_assum irule >> decide_tac) >>
  asm_rewrite_tac[] >>
  qpat_x_assum `relocation_pair _ _ (EL j _) _ _` mp_tac >>
  rewrite_tac[relocation_pair_def] >> strip_tac >> asm_rewrite_tac[] >>
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
  rw[joint_relocation_demand_def] >> gvs[activation_cache_def]
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

Theorem joint_trace_reachable_at:
  joint_trace vs0 C q0 es qs q /\ k <= LENGTH es ==>
  joint_config_reachable vs0 C (EL k (q0::qs))
Proof
  strip_tac >>
  `LENGTH es = LENGTH qs` by metis_tac[joint_chain_length, joint_trace_def] >>
  drule joint_trace_prefix_reachable >> simp[EVERY_EL] >> strip_tac >>
  Cases_on `k` >> simp[] >> first_x_assum irule >> decide_tac
QED

(* Without DALLOCA every observed byte at or above lo lies in a live cache. *)
Theorem joint_observed_read_cached:
  joint_trace vs0 C q0 es qs q /\ vs0.vs_allocas = FEMPTY /\
  ptr_discipline lo C vs0 /\ ~ctx_has_dalloca C /\ j <= LENGTH es /\
  joint_observed_read (EL j (q0::qs)) a /\ lo <= a ==>
  ?d owner aid b sz. activation_cache (EL j (q0::qs)) d owner aid (b,sz) /\
    b <= a /\ a < b + sz
Proof
  strip_tac >>
  `?stk PG G tn fn inst s oms om hs h.
     EL j (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h` by
    (Cases_on `EL j (q0::qs)` >> simp[]) >>
  `a IN joint_reads (EL j (q0::qs)) /\ ~in_revert_forward fn s` by
    gvs[joint_observed_read_def, joint_read_exempt_def] >>
  drule_all joint_read_owner_birth_above >> strip_tac >>
  first_x_assum (qspec_then `j` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem joint_initial_fmp_trace:
  joint_trace vs0 C q0 es qs q /\ EVERY wf_function C.ctx_functions /\
  k <= LENGTH es ==>
  joint_initial_fmp (EL k (q0::qs)) = w2n vs0.vs_initial_fmp
Proof
  strip_tac >> drule_all joint_trace_reachable_at >> strip_tac >>
  `?stk PG G tn fn inst s oms om hs h.
     EL k (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h` by
    (Cases_on `EL k (q0::qs)` >> simp[]) >>
  fs[joint_initial_fmp_def] >>
  metis_tac[joint_config_raw, raw_reachable_initial_fmp]
QED

(* With DALLOCA every live cache, saved frames included, lies below the
   initial free memory pointer. *)
Theorem joint_cache_below_initial_fmp:
  joint_trace vs0 C q0 es qs q /\ EVERY wf_function C.ctx_functions /\
  ptr_discipline lo C vs0 /\ ctx_has_dalloca C /\ k <= LENGTH es /\
  activation_cache (EL k (q0::qs)) d owner aid (b,sz) ==>
  b + sz <= w2n vs0.vs_initial_fmp
Proof
  strip_tac >> drule_all joint_trace_reachable_at >> strip_tac >>
  Cases_on `EL k (q0::qs)` >> gvs[] >> metis_tac[frameDemandOwnershipTheory.joint_config_cache_below]
QED
