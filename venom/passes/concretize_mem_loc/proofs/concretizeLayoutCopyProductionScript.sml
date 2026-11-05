Theory concretizeLayoutCopyProduction
Ancestors concretizeLayoutStoreProduction frameRelocationBinding
  frameRelocationCopyTaint frameJointTrace frameJointTransition frameJointDemand
  ptrDiscipline venomState frameJointTaint

(* A demanded copy result is clean, so its simultaneous pre-state producer
   is clean. No corresponding fact is needed for tainted producer lanes. *)
Theorem joint_mcopy_demand_producer_clean:
  joint_trace vs0 C q0 es qs q /\ c < LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\
  inst.inst_opcode = MCOPY /\ inst.inst_operands = [opd;ops;opn] /\
  eval_operand opd s = SOME dst /\ eval_operand ops s = SOME src /\
  eval_operand opn s = SOME sz /\
  post = mcopy (w2n dst) (w2n src) (w2n sz) s /\
  joint_relocation_demand lo positions q0 es qs (SUC c) a z /\
  w2n dst <= a /\ a < w2n dst+w2n sz ==>
  w2n src+(a-w2n dst) NOTIN tn.t_mem
Proof
  strip_tac >>
  `a NOTIN joint_mem_taint (EL (SUC c) (q0::qs))` by
    (irule joint_relocation_demand_clean >> metis_tac[]) >>
  drule_all joint_trace_edge_at >> strip_tac >> gvs[] >>
  qpat_x_assum `joint_transition _ _ _ _` mp_tac >>
  simp[joint_transition_ordinary] >> strip_tac >>
  gvs[joint_mem_taint_def] >>
  `a IN (step_taint inst s (mcopy (w2n dst) (w2n src) (w2n sz) s) tn).t_mem <=>
   if w2n dst <= a /\ a < w2n dst+w2n sz then
     w2n src+(a-w2n dst) IN tn.t_mem else a IN tn.t_mem` by
    (irule step_taint_mcopy_mem >> simp[] >> metis_tac[]) >>
  gvs[]
QED

val _ = if null (hyp joint_mcopy_demand_producer_clean) then ()
        else raise Fail "copy producer cleanliness export has hypotheses";
