Theory concretizePtrWriteTransport
Ancestors concretizePtrComparisonTransport concretizePtrWriteFootprint
  concretizePtrValueTransport concretizePtrWriteClassification
  ptrDiscipline memLocDefs finite_map words arithmetic

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

Theorem ptr_write_transport_owner_containment:
  ptr_lookup_transport births positions (op_prov TG ops.iao_ofst)
    (op_taint tn ops.iao_ofst) (eval_operand ops.iao_ofst s) (eval_operand ops.iao_ofst t) /\
  ptr_lookup_transport births positions (op_prov TG sizeop)
    (op_taint tn sizeop) (eval_operand sizeop s) (eval_operand sizeop t) /\
  mem_write_ops inst = SOME ops /\ ops.iao_max_size = SOME sizeop /\
  ((?v. ops.iao_ofst = Var v) \/ (?w. ops.iao_ofst = Lit w)) /\
  ((?v. sizeop = Var v) \/ (?w. sizeop = Lit w)) /\
  eval_operand ops.iao_ofst s = SOME x /\ eval_operand sizeop s = SOME z /\
  op_prov TG ops.iao_ofst = SOME (token,aid) /\
  FLOOKUP births (token,aid) = SOME (srcbase,sz) /\
  FLOOKUP positions (Allocation aid) = SOME (pos,sz) /\
  op_prov TG sizeop = NONE /\ op_taint tn sizeop = {} /\
  srcbase <= w2n x /\ w2n x + w2n z <= srcbase + sz /\
  pos + sz < dimword(:256) ==>
  (w2n x - srcbase) + w2n z <= sz /\
  !q. q IN range_bytes (step_writes inst t post) ==>
    pos + (w2n x - srcbase) <= q /\
    q < pos + (w2n x - srcbase) + w2n z
Proof
  strip_tac >>
  `eval_operand sizeop t = SOME z` by
    (gvs[ptr_lookup_transport_some, ptr_value_transport_scalar_empty]) >>
  `?y. eval_operand ops.iao_ofst t = SOME y /\
    ptr_value_transport births positions (SOME (token,aid))
      (op_taint tn ops.iao_ofst) x y` by
    (gvs[ptr_lookup_transport_some]) >>
  `y = x - n2w srcbase + n2w pos` by
    gvs[ptr_value_transport_def] >>
  `w2n y = pos + (w2n x - srcbase)` by
    (irule ptr_closed_relocation_value >> simp[] >>
     qexists_tac `sz` >> simp[] >> decide_tac) >>
  conj_tac >- decide_tac >>
  `!q. q IN range_bytes (step_writes inst t post) ==>
    w2n y <= q /\ q < w2n y + w2n z` by
    (gen_tac >> strip_tac >> irule ptr_step_write_max_containment >>
     simp[] >> metis_tac[]) >>
  gvs[]
QED

Theorem ptr_write_transport_fixed_containment:
  ptr_lookup_transport births positions (op_prov TG ops.iao_ofst)
    (op_taint tn ops.iao_ofst) (eval_operand ops.iao_ofst s) (eval_operand ops.iao_ofst t) /\
  ptr_lookup_transport births positions (op_prov TG sizeop)
    (op_taint tn sizeop) (eval_operand sizeop s) (eval_operand sizeop t) /\
  mem_write_ops inst = SOME ops /\ ops.iao_max_size = SOME sizeop /\
  ((?v. ops.iao_ofst = Var v) \/ (?w. ops.iao_ofst = Lit w)) /\
  ((?v. sizeop = Var v) \/ (?w. sizeop = Lit w)) /\
  eval_operand ops.iao_ofst s = SOME x /\ eval_operand sizeop s = SOME z /\
  op_prov TG ops.iao_ofst = NONE /\ op_taint tn ops.iao_ofst = {} /\
  op_prov TG sizeop = NONE /\ op_taint tn sizeop = {} /\
  w2n x + w2n z <= lo ==>
  !q. q IN range_bytes (step_writes inst t post) ==> q < lo
Proof
  strip_tac >>
  `eval_operand sizeop t = SOME z` by
    (gvs[ptr_lookup_transport_some, ptr_value_transport_scalar_empty]) >>
  `eval_operand ops.iao_ofst t = SOME x` by
    (gvs[ptr_lookup_transport_some, ptr_value_transport_scalar_empty]) >>
  `!q. q IN range_bytes (step_writes inst t post) ==>
    w2n x <= q /\ q < w2n x + w2n z` by
    (gen_tac >> strip_tac >> irule ptr_step_write_max_containment >>
     simp[] >> metis_tac[]) >>
  gen_tac >> disch_tac >> first_x_assum drule >> decide_tac
QED
