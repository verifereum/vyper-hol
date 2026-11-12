Theory frameRelocationStoreDemand
Ancestors frameRelocationBinding frameRelocationStoreTaint
  frameJointTrace frameJointTransition frameJointTaint venomExecSemantics
  ptrDiscipline venomInst words list pred_set arithmetic

Theorem joint_relocation_demand_mstore_lane_clean:
  joint_trace vs0 C q0 es qs q /\ c < LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\
  inst.inst_opcode = MSTORE /\ inst.inst_operands = [opd;opv] /\
  eval_operand opd s = SOME dst /\ eval_operand opv s = SOME value /\
  k < 32 /\
  joint_relocation_demand lo positions q0 es qs (SUC c) (w2n dst+k) z ==>
  k NOTIN op_taint tn opv
Proof
  strip_tac >>
  `w2n dst+k NOTIN joint_mem_taint (EL (SUC c) (q0::qs))` by
    (irule joint_relocation_demand_clean >> metis_tac[]) >>
  drule_all joint_trace_edge_at >> strip_tac >>
  qpat_x_assum `joint_transition _ _ _ _` mp_tac >>
  simp[joint_transition_ordinary] >> strip_tac >>
  `post = mstore (w2n dst) value s` by
    gvs[step_inst_non_invoke, step_inst_base_def, exec_write2_def] >>
  `w2n dst+k NOTIN (step_taint inst s post tn).t_mem` by
    gvs[joint_mem_taint_def] >>
  drule_all step_taint_mstore_mem >>
  disch_then (qspecl_then [`tn`, `w2n dst+k`] mp_tac) >> metis_tac[]
QED

Theorem joint_relocation_demand_mstore_address_clean:
  joint_trace vs0 C q0 es qs q /\ c < LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\
  inst.inst_opcode = MSTORE /\ inst.inst_operands = [opd;opv] /\
  eval_operand opd s = SOME dst /\ eval_operand opv s = SOME value /\
  w2n dst <= a /\ a < w2n dst+32 /\
  joint_relocation_demand lo positions q0 es qs (SUC c) a z ==>
  (a-w2n dst) NOTIN op_taint tn opv
Proof
  strip_tac >> irule joint_relocation_demand_mstore_lane_clean >>
  conj_tac >- decide_tac >>
  goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `EL _ (_::_) = _`)) >>
  goal_assum (drule_at (Pat `EL _ es = _`)) >>
  goal_assum (drule_at (Pat `inst.inst_operands = _`)) >>
  simp[] >> qexistsl_tac [`lo`, `positions`, `z`] >> simp[]
QED
