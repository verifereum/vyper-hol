Theory frameRelocationStoreTaint
Ancestors frameRelocationTaintOrder frameRelocationStoreSteps
  frameRelocationCopyTaint frameRelocationMemory ptrDiscipline
  codegenRel venomState venomExecSemantics finite_map pred_set words

Theorem step_taint_mstore_mem:
  inst.inst_opcode = MSTORE /\ inst.inst_operands = [opd;opv] /\
  eval_operand opd s = SOME dst /\ eval_operand opv s = SOME value /\
  s' = mstore (w2n dst) value s ==>
  (a IN (step_taint inst s s' tn).t_mem <=>
   (a IN tn.t_mem /\ ~(w2n dst <= a /\ a < w2n dst+32)) \/
   ?k. k IN op_taint tn opv /\ a = w2n dst+k)
Proof
  strip_tac >>
  `new_site_bytes s s' = {}` by
    (irule new_site_bytes_unchanged >>
     simp[mstore_def, write_memory_with_expansion_def]) >>
  simp[step_taint_def, mem_taint_def, step_writes_def,
       source_memory_write_ranges_def, written_taint_def, range_bytes_def,
       fixed_source_write_range_def] >> metis_tac[]
QED

Theorem relocation_taint_le_mstore:
  inst.inst_opcode = MSTORE /\ inst.inst_operands = [opd;opv] /\
  eval_operand opd s = SOME dst /\ eval_operand opv s = SOME value /\
  eval_operand opd t = SOME dstT /\ eval_operand opv t = SOME valueT /\
  s' = mstore (w2n dst) value s /\ t' = mstore (w2n dstT) valueT t /\
  relocation_taint_le R tn un /\ op_taint un opv SUBSET {k | k < 32} /\
  (!a b. next a b /\ w2n dst <= a /\ a < w2n dst+32 ==>
    w2n dstT <= b /\ b < w2n dstT+32 /\ a-w2n dst = b-w2n dstT) /\
  (!a b. next a b /\ ~(w2n dst <= a /\ a < w2n dst+32) ==>
    R a b /\ ~(w2n dstT <= b /\ b < w2n dstT+32)) ==>
  relocation_taint_le next (step_taint inst s s' tn)
    (step_taint inst t t' un)
Proof
  strip_tac >>
  `op_taint un opv SUBSET op_taint tn opv` by
    (Cases_on `opv` >> gvs[relocation_taint_le_def, op_taint_def]) >>
  `demand_taint next (step_taint inst s s' tn).t_mem
     (step_taint inst t t' un).t_mem` by
    (simp[demand_taint_def] >> rpt gen_tac >> strip_tac >>
     `!i. i IN (step_taint inst s s' tn).t_mem <=>
       (i IN tn.t_mem /\ ~(w2n dst <= i /\ i < w2n dst+32)) \/
       ?k. k IN op_taint tn opv /\ i = w2n dst+k` by
       (gen_tac >> irule step_taint_mstore_mem >> metis_tac[]) >>
     `!i. i IN (step_taint inst t t' un).t_mem <=>
       (i IN un.t_mem /\ ~(w2n dstT <= i /\ i < w2n dstT+32)) \/
       ?k. k IN op_taint un opv /\ i = w2n dstT+k` by
       (gen_tac >> irule step_taint_mstore_mem >> metis_tac[]) >>
     qpat_x_assum `!a b. next a b /\ _ /\ _ ==> _`
       (qspecl_then [`a`,`b`] mp_tac) >>
     qpat_x_assum `!a b. next a b /\ ~_ ==> _`
       (qspecl_then [`a`,`b`] mp_tac) >>
     Cases_on `w2n dst <= a /\ a < w2n dst+32`
     >- (simp[] >> rpt strip_tac >>
         gvs[relocation_taint_le_def, demand_taint_def, SUBSET_DEF] >>
         disj2_tac >> qexists_tac `a-w2n dst` >>
         conj_tac >- metis_tac[] >> decide_tac) >>
     simp[] >> rpt strip_tac >>
     gvs[relocation_taint_le_def, demand_taint_def, SUBSET_DEF] >>
     metis_tac[arithmeticTheory.ADD_COMM, arithmeticTheory.ADD_SUB]) >>
  gvs[relocation_taint_le_def] >>
  simp[step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
       out_taint_def, op_taint_def] >>
  irule set_var_taint_subset >> simp[] >> gvs[op_taint_def]
QED

Theorem relocation_taint_le_mstore8:
  inst.inst_opcode = MSTORE8 /\ inst.inst_operands = [opd;opv] /\
  eval_operand opd s = SOME dst /\ eval_operand opv s = SOME value /\
  eval_operand opd t = SOME dstT /\ eval_operand opv t = SOME valueT /\
  s' = mstore8 (w2n dst) value s /\ t' = mstore8 (w2n dstT) valueT t /\
  relocation_taint_le R tn un /\
  (!a b. next a b /\ w2n dst <= a /\ a < w2n dst+1 ==>
    w2n dstT <= b /\ b < w2n dstT+1 /\ a-w2n dst = b-w2n dstT) /\
  (!a b. next a b /\ ~(w2n dst <= a /\ a < w2n dst+1) ==>
    R a b /\ ~(w2n dstT <= b /\ b < w2n dstT+1)) ==>
  relocation_taint_le next (step_taint inst s s' tn)
    (step_taint inst t t' un)
Proof
  strip_tac >>
  `new_site_bytes s s' = {}` by
    (irule new_site_bytes_unchanged >>
     simp[mstore8_def, write_memory_with_expansion_def]) >>
  `new_site_bytes t t' = {}` by
    (irule new_site_bytes_unchanged >>
     simp[mstore8_def, write_memory_with_expansion_def]) >>
  gvs[relocation_taint_le_def] >>
  simp[relocation_taint_le_def, step_taint_def, store_taint_def,
       adopt_reset_def, imm_taint_def, mem_taint_def, step_writes_def,
       source_memory_write_ranges_def, fixed_source_write_range_def,
       written_taint_def, range_bytes_def, out_taint_def, op_taint_def] >>
  conj_tac
  >- (simp[demand_taint_def] >> rpt gen_tac >> strip_tac >>
      qpat_x_assum `!a b. next a b /\ _ /\ _ ==> _`
        (qspecl_then [`a`,`b`] mp_tac) >>
      qpat_x_assum `!a b. next a b /\ (_ \/ _) ==> _`
        (qspecl_then [`a`,`b`] mp_tac) >>
      Cases_on `w2n dst <= a /\ a < w2n dst+1` >>
      gvs[demand_taint_def] >> metis_tac[]) >>
  irule set_var_taint_subset >> simp[] >> gvs[op_taint_def]
QED
