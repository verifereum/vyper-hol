Theory requestCutStaticFrontier
Ancestors
  jointRequestCut frameJointTransition frameJointTrace staticAbortDefs
  frameOriginHistory requestCutDftPrefixReach dftGasFromListTraceDefs dftGasOracleDefs
  venomExecSemantics venomState venomInst venomWf list arithmetic

(* Once a fixed native trace reaches a static interval, later reachable
   visits stay inside that interval. *)
Theorem request_cut_visit_before_static:
  EVERY wf_function C.ctx_functions /\ ALL_DISTINCT (fn_labels stopfn) /\
  joint_trace vs0 C q0 es qs
    (JointConfig stk PG G tn stopfn stopinst stop oms om hs hist) /\
  in_static_abort_prefix stopfn stop /\
  raw_reachable vs0 C fn inst s /\ ~in_static_abort_prefix fn s ==>
  ?n stk' PG' G' tn' oms' om' hs' hist'.
    n < LENGTH es /\
    EL n (q0::qs) = JointConfig stk' PG' G' tn' fn inst s oms' om' hs' hist'
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  dxrule raw_reachable_joint_trace >> strip_tac >>
  rename1 `joint_trace vs0 C r0 fs rs
    (JointConfig stk2 PG2 G2 tn2 fn inst s oms2 om2 hs2 hist2)` >>
  `EL (LENGTH es) (q0::qs) =
     JointConfig stk PG G tn stopfn stopinst stop oms om hs hist` by
    metis_tac[joint_trace_endpoint] >>
  `EL (LENGTH fs) (r0::rs) =
     JointConfig stk2 PG2 G2 tn2 fn inst s oms2 om2 hs2 hist2` by
    metis_tac[joint_trace_endpoint] >>
  Cases_on `LENGTH fs < LENGTH es`
  >- (mp_tac (Q.SPECL [`LENGTH (fs:origin_event option list)`, `r0`, `fs`, `rs`,
       `JointConfig stk2 PG2 G2 tn2 fn inst s oms2 om2 hs2 hist2`, `q0`, `es`, `qs`,
       `JointConfig stk PG G tn stopfn stopinst stop oms om hs hist`]
       cut_joint_trace_execution_agrees) >>
      impl_tac >- (simp[] >> decide_tac) >>
      Cases_on `EL (LENGTH fs) (q0::qs)` >> simp[] >> strip_tac >>
      qexists_tac `LENGTH fs` >> simp[] >> metis_tac[]) >>
  `LENGTH es <= LENGTH fs` by decide_tac >>
  mp_tac (Q.SPECL [`LENGTH (es:origin_event option list)`, `q0`, `es`, `qs`,
    `JointConfig stk PG G tn stopfn stopinst stop oms om hs hist`, `r0`, `fs`, `rs`,
    `JointConfig stk2 PG2 G2 tn2 fn inst s oms2 om2 hs2 hist2`]
    cut_joint_trace_execution_agrees) >>
  simp[] >>
  Cases_on `EL (LENGTH es) (r0::rs)` >> simp[] >>
  strip_tac >>
  rename1 `EL (LENGTH es) (r0::rs) =
    JointConfig mstk mPG mG mtn mfn mi mid moms mom mhs mh` >>
  fs[in_static_abort_prefix_def, static_abort_at_def] >>
  mp_tac (Q.SPECL [`LENGTH (fs:origin_event option list)`,
    `LENGTH (es:origin_event option list)`]
    (Q.INST [`q0` |-> `r0`, `es` |-> `fs`, `qs` |-> `rs`,
    `q` |-> `JointConfig stk2 PG2 G2 tn2 fn inst s oms2 om2 hs2 hist2`,
    `stk` |-> `mstk`, `PG` |-> `mPG`, `G` |-> `mG`, `tn` |-> `mtn`,
    `fn` |-> `mfn`, `inst` |-> `mi`, `s` |-> `mid`,
    `oms` |-> `moms`, `om` |-> `mom`, `hs` |-> `mhs`, `h` |-> `mh`,
    `r` |-> `j:num`]
    joint_trace_static_prefix)) >>
  impl_tac
  >- (simp[] >> metis_tac[]) >>
  simp[] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem request_cut_observed_cover_before_static:
  EVERY wf_function C8.ctx_functions /\ ALL_DISTINCT (fn_labels stopfn) /\
  joint_trace v C8 q0 evs qs
    (JointConfig stk PG G tn stopfn stopinst end8 oms om hs hist) /\
  in_static_abort_prefix stopfn end8 /\
  tr = trace_context N C8 v /\
  LENGTH evs < LENGTH tr /\
  obs = trace_gas (TAKE (LENGTH evs) tr) /\
  ALL_DISTINCT (MAP FST obs) /\
  (!h. h < LENGTH evs ==>
    ?p d f i t stk PG G tn oms om hs hist.
      EL h tr = ((p,d,i.inst_id),f,i,t) /\
      EL h (q0::qs) = JointConfig stk PG G tn f i t oms om hs hist) ==>
  !fn i s. raw_reachable v C8 fn i s /\ ~in_static_abort_prefix fn s ==>
    ?p d. ev_reachable
      (\key. case ALOOKUP (obs ++ filling) key of NONE => 0w | SOME w => w)
      v C8 p d fn i (s with vs_gas_readings := v.vs_gas_readings)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> rpt strip_tac >>
  drule_all request_cut_visit_before_static >> strip_tac >>
  qpat_x_assum `!h. h < LENGTH evs ==> _` drule >> strip_tac >>
  `n <= LENGTH evs /\ n < LENGTH tr` by decide_tac >>
  `?p d. EL n tr = ((p,d,i.inst_id),fn,i,s)` by metis_tac[joint_config_11] >>
  drule_all trace_context_observed_visit >> metis_tac[]
QED
