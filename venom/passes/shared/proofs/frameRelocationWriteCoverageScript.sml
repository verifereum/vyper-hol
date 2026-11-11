Theory frameRelocationWriteCoverage
Ancestors
  frameRelocationBinding frameJointDemand codegenRel ptrDiscipline
  venomInst venomState words list pred_set arithmetic

(* Both operands must evaluate: footprints account for successful stores. *)
Theorem step_writes_store:
  ((inst.inst_opcode = MSTORE /\ len = 32) \/
   (inst.inst_opcode = MSTORE8 /\ len = 1)) /\
  inst.inst_operands = [opd; opv] /\
  eval_operand opd s = SOME dst /\ eval_operand opv s = SOME value ==>
  step_writes inst s post = [(w2n dst,len)]
Proof
  strip_tac >>
  gvs[step_writes_def, source_memory_write_ranges_def,
      fixed_source_write_range_def]
QED

Theorem relocation_pair_range:
  ((off + len <= lo /\ offT = off) \/
   (?d owner aid b sz.
     activation_cache q d owner aid (b,sz) /\ lo <= b /\ b <= off /\
     off + len <= b + sz /\ offT = positions owner aid + (off-b))) ==>
  !i. i < len ==> relocation_pair lo positions q (off+i) (offT+i)
Proof
  strip_tac >> rpt strip_tac
  >- (simp[relocation_pair_def] >> decide_tac) >>
  simp[relocation_pair_def] >>
  qexistsl_tac [`d`, `owner`, `aid`, `b`, `sz`] >> simp[] >> decide_tac
QED

(* Operational footprints in both directions, with identical byte offsets.
 * Address geometry is explicit; discovery of the cache witness is upstream. *)
Theorem joint_store_write_correspondence:
  q = JointConfig stk PG G tn fn inst s oms om hs h /\
  ev = SOME (OriginOrdinary fuel post) /\
  ((inst.inst_opcode = MSTORE /\ len = 32) \/
   (inst.inst_opcode = MSTORE8 /\ len = 1)) /\
  inst.inst_operands = [opd;opv] /\
  eval_operand opd s = SOME dst /\ eval_operand opv s = SOME value /\
  eval_operand opd t = SOME dstT /\ eval_operand opv t = SOME valueT /\
  ((w2n dst + len <= lo /\ w2n dstT = w2n dst) \/
   (?d owner aid b sz.
     activation_cache q d owner aid (b,sz) /\ lo <= b /\ b <= w2n dst /\
     w2n dst + len <= b + sz /\
     w2n dstT = positions owner aid + (w2n dst-b))) ==>
  (!i. i < len ==>
    w2n dst+i IN joint_writes q ev /\
    w2n dstT+i IN range_bytes (step_writes inst t postT) /\
    relocation_pair lo positions q (w2n dst+i) (w2n dstT+i)) /\
  (!z. z IN range_bytes (step_writes inst t postT) ==> ?a.
    a IN joint_writes q ev /\ relocation_pair lo positions q a z /\
    a-w2n dst = z-w2n dstT)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `step_writes inst s post = [(w2n dst,len)]` by
    (irule step_writes_store >> metis_tac[]) >>
  `step_writes inst t postT = [(w2n dstT,len)]` by
    (irule step_writes_store >> metis_tac[]) >>
  `!i. i < len ==> relocation_pair lo positions q (w2n dst+i) (w2n dstT+i)` by
    (rpt strip_tac >> irule relocation_pair_range >> metis_tac[]) >>
  `joint_writes q ev = range_bytes [(w2n dst,len)]` by
    gvs[joint_writes_ordinary] >>
  simp[range_bytes_def] >>
  rpt strip_tac >> qexists_tac `w2n dst + (z-w2n dstT)` >>
  `z = w2n dstT + (z-w2n dstT)` by decide_tac >>
  `z-w2n dstT < len` by decide_tac >>
  qpat_x_assum `!i. i < len ==> _` (qspec_then `z-w2n dstT` mp_tac) >>
  gvs[]
QED
