Theory frameReadOwnership
Ancestors
  concretizeLayoutCutSafe o1SafeUpto
  frameDemandOwnership frameJointDemand frameJointTrace frameOriginHistory
  frameOriginReachable frameJointTransition ptrDiscipline memLocDefs finite_map list pred_set

Theorem access_ok_read_site:
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\ lo <= byte /\
  byte IN range_bytes (source_memory_read_ranges inst s) ==>
  ?ops v b sz. mem_read_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
    FLOOKUP G v = SOME (b,sz) /\ b <= byte /\ byte < b + sz
Proof
  simp[access_ok_def, range_bytes_def] >> rpt strip_tac >>
  `len <> 0 /\ lo < off + len` by decide_tac >> gvs[] >>
  first_x_assum (qspecl_then [`off`,`len`] mp_tac) >> simp[] >>
  strip_tac >> qexistsl_tac [`ops`,`v`,`b`,`sz`] >> simp[]
QED

Theorem joint_read_owner_birth_upto:
  joint_trace vs0 ctx q0 es qs q /\ vs0.vs_allocas = FEMPTY /\
  ptr_discipline_upto lo ncut ctx vs0 /\ gas_cut ncut vs0 (joint_state q) /\ (ctx_has_dalloca ctx ==> byte < w2n vs0.vs_initial_fmp) /\ j <= LENGTH es /\
  EL j (q0::qs) = JointConfig stk PG G tn current inst s oms om hs h /\
  byte IN joint_reads (EL j (q0::qs)) ==>
  byte < lo \/ in_revert_forward current s \/
  ?ops v b sz d owner aid t.
    mem_read_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
    FLOOKUP G v = SOME (b,sz) /\ b <= byte /\ byte < b + sz /\
    t < j /\ allocation_birth ctx (EL t (q0::qs)) (EL t es) d owner aid (b,sz) /\
    (!i. t < i /\ i <= j ==>
      d <= activation_depth (EL i (q0::qs)) /\
      activation_cache (EL i (q0::qs)) d owner aid (b,sz))
Proof
  strip_tac >> Cases_on `byte < lo` >> simp[] >>
  Cases_on `in_revert_forward current s` >> simp[] >>
  `LENGTH es = LENGTH qs` by metis_tac[joint_trace_def, joint_chain_length] >>
  `joint_config_reachable vs0 ctx (EL j (q0::qs))` by
    (drule joint_trace_prefix_reachable >> strip_tac >>
     Cases_on `j` >> gvs[EVERY_EL] >>
     rename1 `SUC k <= LENGTH qs` >> `k < LENGTH qs` by decide_tac >> metis_tac[]) >>
  `frame_reachable vs0 ctx stk PG G tn current inst s` by
    (gvs[joint_config_reachable_def] >>
     drule joint_origin_history_erasure >> strip_tac >>
     metis_tac[origin_frame_erasure]) >>
  `gas_cut ncut vs0 s` by
    (drule_all trace_config_gas_cut >> gvs[joint_state_def]) >>
  `access_ok lo G current inst s` by metis_tac[ptr_discipline_upto_at] >>
  `byte IN range_bytes (source_memory_read_ranges inst s)` by
    gvs[joint_reads_def] >>
  `lo <= byte` by decide_tac >>
  drule_all access_ok_read_site >> strip_tac >>
  `(ctx_has_dalloca ctx ==> FST (b,sz) < w2n vs0.vs_initial_fmp)` by
    (simp[] >> strip_tac >> res_tac >> decide_tac) >>
  `(ctx_has_dalloca ctx ==>
     ptr_discipline_upto lo ncut ctx vs0 /\ gas_cut ncut vs0 s)` by simp[] >>
  drule_all joint_provenance_birth_upto >> strip_tac >>
  qexistsl_tac [`ops`,`v`,`b`,`sz`,`d`,`owner`,`aid`,`t`] >> simp[]
QED

Theorem joint_read_owner_birth:
  joint_trace vs0 ctx q0 es qs q /\ vs0.vs_allocas = FEMPTY /\
  ptr_discipline lo ctx vs0 /\ (ctx_has_dalloca ctx ==> byte < w2n vs0.vs_initial_fmp) /\ j <= LENGTH es /\
  EL j (q0::qs) = JointConfig stk PG G tn current inst s oms om hs h /\
  byte IN joint_reads (EL j (q0::qs)) ==>
  byte < lo \/ in_revert_forward current s \/
  ?ops v b sz d owner aid t.
    mem_read_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
    FLOOKUP G v = SOME (b,sz) /\ b <= byte /\ byte < b + sz /\
    t < j /\ allocation_birth ctx (EL t (q0::qs)) (EL t es) d owner aid (b,sz) /\
    (!i. t < i /\ i <= j ==>
      d <= activation_depth (EL i (q0::qs)) /\
      activation_cache (EL i (q0::qs)) d owner aid (b,sz))
Proof
  strip_tac >>
  mp_tac (Q.INST [`ncut` |-> `SUC (LENGTH vs0.vs_gas_readings)`]
    joint_read_owner_birth_upto) >>
  simp[ptr_discipline_upto_whole]
QED

Theorem joint_read_owner_birth_above_upto:
  joint_trace vs0 ctx q0 es qs q /\ vs0.vs_allocas = FEMPTY /\
  ptr_discipline_upto lo ncut ctx vs0 /\ gas_cut ncut vs0 (joint_state q) /\ (ctx_has_dalloca ctx ==> byte < w2n vs0.vs_initial_fmp) /\ j <= LENGTH es /\
  EL j (q0::qs) = JointConfig stk PG G tn current inst s oms om hs h /\
  byte IN joint_reads (EL j (q0::qs)) /\ lo <= byte /\
  ~in_revert_forward current s ==>
  ?ops v b sz d owner aid t.
    mem_read_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
    FLOOKUP G v = SOME (b,sz) /\ b <= byte /\ byte < b + sz /\
    t < j /\ allocation_birth ctx (EL t (q0::qs)) (EL t es) d owner aid (b,sz) /\
    (!i. t < i /\ i <= j ==>
      d <= activation_depth (EL i (q0::qs)) /\
      activation_cache (EL i (q0::qs)) d owner aid (b,sz))
Proof
  strip_tac >> drule_all joint_read_owner_birth_upto >> simp[]
QED

Theorem joint_read_owner_birth_above:
  joint_trace vs0 ctx q0 es qs q /\ vs0.vs_allocas = FEMPTY /\
  ptr_discipline lo ctx vs0 /\ (ctx_has_dalloca ctx ==> byte < w2n vs0.vs_initial_fmp) /\ j <= LENGTH es /\
  EL j (q0::qs) = JointConfig stk PG G tn current inst s oms om hs h /\
  byte IN joint_reads (EL j (q0::qs)) /\ lo <= byte /\
  ~in_revert_forward current s ==>
  ?ops v b sz d owner aid t.
    mem_read_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
    FLOOKUP G v = SOME (b,sz) /\ b <= byte /\ byte < b + sz /\
    t < j /\ allocation_birth ctx (EL t (q0::qs)) (EL t es) d owner aid (b,sz) /\
    (!i. t < i /\ i <= j ==>
      d <= activation_depth (EL i (q0::qs)) /\
      activation_cache (EL i (q0::qs)) d owner aid (b,sz))
Proof
  strip_tac >>
  mp_tac (Q.INST [`ncut` |-> `SUC (LENGTH vs0.vs_gas_readings)`]
    joint_read_owner_birth_above_upto) >>
  simp[ptr_discipline_upto_whole]
QED
