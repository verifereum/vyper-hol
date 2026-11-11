Theory concretizePtrExactWriteTransport
Ancestors concretizePtrWriteTransport concretizePtrWriteClassification
  concretizePtrValueTransport concretizePtrComparisonTransport
  ptrDiscipline memLocDefs venomState words finite_map list pred_set arithmetic option pair


Theorem ptr_paired_source_write_range[local]:
  mem_write_ops inst = SOME ops /\ ops.iao_max_size = SOME sizeop /\
  eval_operand ops.iao_ofst s = SOME x /\ eval_operand ops.iao_ofst t = SOME y /\
  eval_operand sizeop s = SOME z /\ eval_operand sizeop t = SOME z /\
  (!op. IS_SOME (eval_operand op s) = IS_SOME (eval_operand op t)) ==>
  !len. (MEM (w2n x,len) (source_memory_write_ranges inst s) <=>
         MEM (w2n y,len) (source_memory_write_ranges inst t)) /\
    (!off. MEM (off,len) (source_memory_write_ranges inst s) ==> off = w2n x) /\
    (!off. MEM (off,len) (source_memory_write_ranges inst t) ==> off = w2n y)
Proof
  strip_tac >> gen_tac >>
  simp[ptr_source_write_classification, ptr_classified_write_range_def] >>
  Cases_on `inst.inst_opcode` >>
  gvs[mem_write_ops_def, eval_operand_def, AllCaseEqs()] >>
  metis_tac[IS_SOME_EXISTS]
QED

Theorem ptr_paired_write_intervals[local]:
  mem_write_ops inst = SOME ops /\ ops.iao_max_size = SOME sizeop /\
  eval_operand ops.iao_ofst s = SOME x /\ eval_operand ops.iao_ofst t = SOME y /\
  eval_operand sizeop s = SOME z /\ eval_operand sizeop t = SOME z /\
  (!op. IS_SOME (eval_operand op s) = IS_SOME (eval_operand op t)) /\
  (MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL] ==>
    LENGTH posts.vs_returndata = LENGTH postt.vs_returndata) ==>
  ?lens. (!q. q IN range_bytes (step_writes inst s posts) <=>
             ?len. MEM len lens /\ w2n x <= q /\ q < w2n x + len) /\
         (!q. q IN range_bytes (step_writes inst t postt) <=>
             ?len. MEM len lens /\ w2n y <= q /\ q < w2n y + len)
Proof
  strip_tac >> drule_all ptr_paired_source_write_range >> strip_tac >>
  qexists `MAP (\(off,len). if MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL]
    then MIN len (LENGTH posts.vs_returndata) else len)
    (source_memory_write_ranges inst s)` >>
  simp[ptr_step_write_range, MEM_MAP, EXISTS_PROD] >>
  conj_tac >> gen_tac >> eq_tac >> rpt strip_tac >>
  metis_tac[ADD_COMM]
QED

Theorem ptr_write_transport_owner_exact:
  ptr_lookup_transport births positions (op_prov TG ops.iao_ofst)
    (op_taint tn ops.iao_ofst) (eval_operand ops.iao_ofst s) (eval_operand ops.iao_ofst t) /\
  ptr_lookup_transport births positions (op_prov TG sizeop)
    (op_taint tn sizeop) (eval_operand sizeop s) (eval_operand sizeop t) /\
  (!op. IS_SOME (eval_operand op s) = IS_SOME (eval_operand op t)) /\
  s.vs_labels = t.vs_labels /\
  mem_write_ops inst = SOME ops /\ ops.iao_max_size = SOME sizeop /\
  eval_operand ops.iao_ofst s = SOME x /\ eval_operand sizeop s = SOME z /\
  op_prov TG ops.iao_ofst = SOME (token,aid) /\
  FLOOKUP births (token,aid) = SOME (b,sz) /\
  FLOOKUP positions (Allocation aid) = SOME (p,sz) /\
  op_prov TG sizeop = NONE /\ op_taint tn sizeop = {} /\
  b <= w2n x /\ w2n x + w2n z <= b + sz /\ p + sz < dimword(:256) /\
  (MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL] ==>
    LENGTH posts.vs_returndata = LENGTH postt.vs_returndata) ==>
  !k. k < sz ==>
    (b+k IN range_bytes (step_writes inst s posts) <=>
     p+k IN range_bytes (step_writes inst t postt))
Proof
  strip_tac >>
  `eval_operand sizeop t = SOME z` by
    (gvs[ptr_lookup_transport_some, ptr_value_transport_scalar_empty]) >>
  `?y. eval_operand ops.iao_ofst t = SOME y /\
    ptr_value_transport births positions (SOME (token,aid))
      (op_taint tn ops.iao_ofst) x y` by
    (gvs[ptr_lookup_transport_some]) >>
  `y = x - n2w b + n2w p` by gvs[ptr_value_transport_def] >>
  `w2n y = p + (w2n x - b)` by
    (irule ptr_closed_relocation_value >> simp[] >>
     qexists `sz` >> simp[] >> decide_tac) >>
  drule_all ptr_paired_write_intervals >> strip_tac >>
  rpt strip_tac >>
  `!len. (w2n x <= b+k /\ b+k < w2n x+len) <=>
    (w2n y <= p+k /\ p+k < w2n y+len)` by (gen_tac >> decide_tac) >>
  metis_tac[]
QED

Theorem ptr_write_transport_fixed_exact:
  ptr_lookup_transport births positions (op_prov TG ops.iao_ofst)
    (op_taint tn ops.iao_ofst) (eval_operand ops.iao_ofst s) (eval_operand ops.iao_ofst t) /\
  ptr_lookup_transport births positions (op_prov TG sizeop)
    (op_taint tn sizeop) (eval_operand sizeop s) (eval_operand sizeop t) /\
  (!op. IS_SOME (eval_operand op s) = IS_SOME (eval_operand op t)) /\
  s.vs_labels = t.vs_labels /\
  mem_write_ops inst = SOME ops /\ ops.iao_max_size = SOME sizeop /\
  eval_operand ops.iao_ofst s = SOME x /\ eval_operand sizeop s = SOME z /\
  op_prov TG ops.iao_ofst = NONE /\ op_taint tn ops.iao_ofst = {} /\
  op_prov TG sizeop = NONE /\ op_taint tn sizeop = {} /\
  (MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL] ==>
    LENGTH posts.vs_returndata = LENGTH postt.vs_returndata) ==>
  range_bytes (step_writes inst s posts) = range_bytes (step_writes inst t postt)
Proof
  strip_tac >>
  `eval_operand sizeop t = SOME z` by
    (gvs[ptr_lookup_transport_some, ptr_value_transport_scalar_empty]) >>
  `eval_operand ops.iao_ofst t = SOME x` by
    (gvs[ptr_lookup_transport_some, ptr_value_transport_scalar_empty]) >>
  drule_all ptr_paired_write_intervals >> strip_tac >>
  simp[EXTENSION] >> metis_tac[]
QED
