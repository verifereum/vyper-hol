Theory frameWriteOwnership
Ancestors
  frameReadOwnership frameActivationSeparation frameDemandOwnership
  frameJointDemand frameJointTransition ptrDiscipline memLocDefs
  finite_map list pred_set arithmetic

Theorem step_writes_source_subset:
  range_bytes (step_writes inst s post) SUBSET
    range_bytes (source_memory_write_ranges inst s)
Proof
  rw[step_writes_def] >>
  simp[SUBSET_DEF, range_bytes_def, MEM_MAP, pairTheory.EXISTS_PROD] >>
  rpt strip_tac >> gvs[] >>
  qexistsl_tac [`off`,`p_2`] >> simp[] >> gvs[MIN_DEF] >> decide_tac
QED

Theorem access_ok_write_site:
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\ lo <= byte /\
  byte IN range_bytes (source_memory_write_ranges inst s) ==>
  ?ops v b sz. mem_write_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
    FLOOKUP G v = SOME (b,sz) /\ b <= byte /\ byte < b + sz
Proof
  simp[access_ok_def, range_bytes_def] >> rpt strip_tac >>
  `len <> 0 /\ lo < off + len` by decide_tac >> gvs[] >>
  qpat_x_assum `!off len. MEM (off,len) (source_memory_write_ranges inst s) /\ _ ==> _`
    (qspecl_then [`off`,`len`] mp_tac) >> simp[] >>
  strip_tac >> qexistsl_tac [`ops`,`v`,`b`,`sz`] >> simp[]
QED

Theorem joint_writes_source_subset:
  joint_transition C
    (JointConfig stk PG G tn fn inst s oms om hs h) ev q' ==>
  joint_writes (JointConfig stk PG G tn fn inst s oms om hs h) ev SUBSET
    range_bytes (source_memory_write_ranges inst s)
Proof
  strip_tac >> drule joint_transition_label_cases >> strip_tac >>
  gvs[joint_writes_def]
  >- simp[step_writes_source_subset]
  >- simp[step_writes_source_subset] >>
  gvs[joint_transition_return] >> simp[step_writes_source_subset]
QED

Theorem joint_write_owner_identity:
  joint_config_reachable vs0 C
    (JointConfig stk PG G tn fn inst s oms om hs h) /\
  vs0.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  joint_transition C
    (JointConfig stk PG G tn fn inst s oms om hs h) ev q' /\
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  lo <= byte /\
  byte IN joint_writes (JointConfig stk PG G tn fn inst s oms om hs h) ev /\
  activation_cache (JointConfig stk PG G tn fn inst s oms om hs h)
    d owner aid (b,sz) /\ b <= byte /\ byte < b + sz ==>
  ?ops v. mem_write_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
    FLOOKUP G v = SOME (b,sz)
Proof
  strip_tac >>
  `byte IN range_bytes (source_memory_write_ranges inst s)` by
    (drule joint_writes_source_subset >> simp[SUBSET_DEF] >> metis_tac[]) >>
  drule_all access_ok_write_site >> strip_tac >>
  drule_all joint_provenance_activation_owner >> strip_tac >>
  `d = d' /\ owner = owner' /\ aid = aid' /\ b = b' /\ sz = sz'` by
    (irule joint_activation_cache_byte_unique >>
     (conj_tac >- (qexists_tac `byte` >> simp[])) >>
     goal_assum (drule_at (Pat `joint_config_reachable _ _ _`)) >>
     simp[]) >>
  gvs[] >> metis_tac[]
QED
