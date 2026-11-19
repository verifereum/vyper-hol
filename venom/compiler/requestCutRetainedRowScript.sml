Theory requestCutRetainedRow
Ancestors
  requestCutReplaySuffix o1ContractCfgNormJointCursors jointRequestCut
  frameJointTrace frameRawProjection stepWriteFootprintBase
  concretizeLayoutLocalReturn dftGasInvCrossingProbe dftGasFromListLookup
  stateFrame venomExecSemantics venomState venomInst venomWf list arithmetic

(* The paired cursors preserve the request count. An earlier C9 recording
   edge therefore cannot align with the stopped C8 endpoint once the
   stopped C9 endpoint has passed that request. *)
Theorem request_cut_cfg_retained_row:
  EVERY wf_function C8.ctx_functions /\ EVERY wf_function C9.ctx_functions /\
  joint_trace vs0 C8 q80 evs8 qs8
    (JointConfig stk8 PG8 G8 tn8 f8 i8 end8 oms8 om8 hs8 hist8) /\
  joint_trace vs0 C9 q90 evs9 qs9
    (JointConfig stk9 PG9 G9 tn9 f9 i9 end9 oms9 om9 hs9 hist9) /\
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 f8 i8 end8 oms8 om8 hs8 hist8)
    (JointConfig stk9 PG9 G9 tn9 f9 i9 end9 oms9 om9 hs9 hist9) /\
  (!h. h < LENGTH evs9 ==> align h <= LENGTH evs8 /\
    ?packet. cfg_norm_joint_cursors C8 C9 packet
      (EL (align h) (q80::qs8)) (EL h (q90::qs9))) /\
  LENGTH vs0.vs_requests <= k /\ k < LENGTH end9.vs_requests ==>
  ?h stk PG G tn f i s oms om hs hist fuel u g j t v.
    align h < LENGTH evs8 /\ h < LENGTH evs9 /\
    EL (align h) (q80::qs8) = JointConfig stk PG G tn f i s oms om hs hist /\
    inv_memory_observation i.inst_opcode /\ ~in_revert_forward f s /\
    raw_reachable vs0 C8 f i s /\ i.inst_opcode <> INVOKE /\
    LENGTH s.vs_requests = k /\ step_inst fuel C8 i s = OK u /\
    raw_reachable vs0 C9 g j t /\ j.inst_opcode <> INVOKE /\
    LENGTH t.vs_requests = k /\ step_inst fuel C9 j t = OK v /\
    k < LENGTH v.vs_requests /\ u.vs_requests = v.vs_requests /\
    s.vs_requests = t.vs_requests /\ s.vs_outcomes = t.vs_outcomes
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule cfg_norm_joint_cursor_execution_frame >> strip_tac >>
  `end8.vs_requests = end9.vs_requests` by
    (qpat_assum `execution_frame end8 = execution_frame end9`
       (mp_tac o Q.AP_TERM `\s. s.vs_requests`) >> simp[execution_frame_def]) >>
  drule_all (Q.INST [`ctx` |-> `C9`] joint_trace_request_crossing) >>
  disch_then (qx_choosel_then [`h`, `g`, `j`, `t`, `fuel`, `v`] strip_assume_tac) >>
  qpat_x_assum `!h. h < LENGTH evs9 ==> _` drule >> strip_tac >>
  drule_all (Q.INST [`ctx` |-> `C9`, `n` |-> `h`] joint_trace_edge_at) >>
  strip_tac >>
  namedCases_on `EL (align h) (q80::qs8)` ["stk PG G tn f i s oms om hs hist"] >>
  `LENGTH t.vs_requests < LENGTH v.vs_requests` by simp[] >>
  qpat_assum `EL h (q90::qs9) = _` SUBST_ALL_TAC >>
  qpat_assum `EL h evs9 = _` SUBST_ALL_TAC >>
  PairCases_on `packet` >>
  drule_all cfg_norm_joint_recording_step >> strip_tac >>
  rename1 `step_inst fuel C8 i s = OK u` >>
  `align h < LENGTH evs8` by
    (spose_not_then assume_tac >>
     `align h = LENGTH evs8` by decide_tac >>
     qpat_assum `joint_trace vs0 C8 _ _ _ _`
       (assume_tac o MATCH_MP joint_trace_endpoint) >>
     gvs[]) >>
  `raw_reachable vs0 C8 f i s` by
    (`align h <= LENGTH evs8` by decide_tac >>
     `joint_config_reachable vs0 C8 (EL (align h) (q80::qs8))` by
       metis_tac[joint_trace_reachable_at] >>
     qpat_assum `EL (align h) (q80::qs8) = _` (fn eq =>
       qpat_x_assum `joint_config_reachable vs0 C8 (EL (align h) (q80::qs8))`
         (mp_tac o PURE_REWRITE_RULE [eq])) >>
     metis_tac[joint_config_raw]) >>
  `MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]` by
    metis_tac[step_inst_request_outcomes] >>
  `wf_function f` by metis_tac[raw_reachable_wf] >>
  `ALL_DISTINCT (fn_labels f)` by fs[wf_function_def] >>
  `~in_revert_forward f s` by
    (irule active_inst_not_revert_forward >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `i` >> fs[MEM] >> metis_tac[raw_reachable_active]) >>
  qexistsl_tac [`h`, `stk`, `PG`, `G`, `tn`, `f`, `i`, `s`, `oms`,
    `om`, `hs`, `hist`, `fuel`, `u`, `g`, `j`, `t`, `v`] >>
  gvs[inv_memory_observation_def, MEM]
QED
