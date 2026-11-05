Theory concretizePtrWriteTransport
Ancestors concretizePtrComparisonTransport concretizePtrWriteFootprint
  concretizePtrValueTransport ptrDiscipline finite_map words arithmetic

Theorem ptr_mstore_transport_same_owner_exclusion:
  ptr_vars_transport births positions TG tn s t /\
  inst.inst_opcode = MSTORE /\ inst.inst_operands = [addr;value] /\
  ((?u. addr = Var u) \/ (?w. addr = Lit w)) /\
  ((?u. value = Var u) \/ (?w. value = Lit w)) /\
  eval_operand addr s = SOME x /\ eval_operand value s = SOME v /\
  op_prov TG addr = SOME (token,aid) /\
  FLOOKUP births (token,aid) = SOME (srcbase,sz) /\
  FLOOKUP positions (Allocation aid) = SOME (pos,sz) /\
  srcbase <= w2n x /\ w2n x + 32 <= srcbase + sz /\
  pos + sz < dimword(:256) /\ k < sz /\
  srcbase+k NOTIN range_bytes (step_writes inst s posts) ==>
  pos+k NOTIN range_bytes (step_writes inst t postt)
Proof
  strip_tac >>
  `?y. eval_operand addr t = SOME y /\
    ptr_value_transport births positions (SOME (token,aid))
      (op_taint tn addr) x y` by
    (drule ptr_vars_transport_eval >>
     disch_then (qspec_then `addr` mp_tac) >>
     simp[ptr_lookup_transport_some]) >>
  `?vt. eval_operand value t = SOME vt` by
    (drule ptr_vars_transport_eval >>
     disch_then (qspec_then `value` mp_tac) >>
     simp[ptr_lookup_transport_some] >> metis_tac[]) >>
  `y = x - n2w srcbase + n2w pos` by
    gvs[ptr_value_transport_def] >>
  `w2n y = pos + (w2n x - srcbase)` by
    (irule ptr_closed_relocation_value >> simp[] >>
     qexists_tac `sz` >> simp[] >> decide_tac) >>
  `!i. i IN range_bytes (step_writes inst s posts) <=>
       w2n x <= i /\ i < w2n x + 32` by
    (irule ptr_mstore_footprint_interval >> simp[] >> metis_tac[]) >>
  `!i. i IN range_bytes (step_writes inst t postt) <=>
       w2n y <= i /\ i < w2n y + 32` by
    (irule ptr_mstore_footprint_interval >> simp[] >> metis_tac[]) >>
  gvs[] >> decide_tac
QED

Theorem ptr_mstore_transport_fixed_exclusion:
  ptr_vars_transport births positions TG tn s t /\
  inst.inst_opcode = MSTORE /\ inst.inst_operands = [addr;value] /\
  ((?u. addr = Var u) \/ (?w. addr = Lit w)) /\
  ((?u. value = Var u) \/ (?w. value = Lit w)) /\
  eval_operand addr s = SOME x /\ eval_operand value s = SOME v /\
  op_prov TG addr = NONE /\ op_taint tn addr = {} /\
  w2n x + 32 <= lo /\ lo <= q ==>
  q NOTIN range_bytes (step_writes inst t postt)
Proof
  strip_tac >>
  `eval_operand addr t = SOME x` by
    (drule ptr_vars_transport_eval >>
     disch_then (qspec_then `addr` mp_tac) >>
     simp[ptr_lookup_transport_some, ptr_value_transport_scalar_empty]) >>
  `?vt. eval_operand value t = SOME vt` by
    (drule ptr_vars_transport_eval >>
     disch_then (qspec_then `value` mp_tac) >>
     simp[ptr_lookup_transport_some] >> metis_tac[]) >>
  `!i. i IN range_bytes (step_writes inst t postt) <=>
       w2n x <= i /\ i < w2n x + 32` by
    (irule ptr_mstore_footprint_interval >> simp[] >> metis_tac[]) >>
  simp[]
QED
