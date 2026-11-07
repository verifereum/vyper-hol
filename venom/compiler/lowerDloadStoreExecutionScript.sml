Theory lowerDloadStoreExecution
Ancestors
  lowerDloadRelocation lowerDloadOperand venomExecSemantics ptrDiscipline codegenRel
  venomMemProps regularCallEmitSim regularMemorySim venomState
  arithmetic words list pred_set finite_map

Theorem ld_mstore_read_byte[local]:
  read_memory a 1 (mstore p v s) =
    if p <= a /\ a < p+32 then [EL (a-p) (word_to_bytes v T)]
    else read_memory a 1 s
Proof
  simp[mstore_eq_write_mem, read_memory_def, venom_returndata_read_byte,
       GENLIST, read_byte_write_memory_with_expansion] >>
  IF_CASES_TAC >> simp[]
QED

Theorem ld_mstore_taint[local]:
  i.inst_opcode = MSTORE /\ i.inst_operands = [dst; value] /\
  eval_operand dst s = SOME p /\ eval_operand value s = SOME v ==>
  (step_taint i s (mstore (w2n p) v s) tn).t_mem =
    (tn.t_mem DIFF {a | w2n p <= a /\ a < w2n p+32}) UNION
    {w2n p+k | k IN op_taint tn value}
Proof
  strip_tac >>
  simp[step_taint_def, mem_taint_def, new_site_bytes_def,
       mstore_eq_write_mem, write_memory_with_expansion_def,
       step_writes_def, source_memory_write_ranges_def,
       range_bytes_def, written_taint_def, FLOOKUP_DEF, fixed_source_write_range_def] >>
  SET_TAC[]
QED

Theorem ld_mstore_masked[local]:
  Ms SUBSET count 32 /\ Mt SUBSET count 32 /\ ld_mask_word Ms Mt v w /\
  ld_byte_rel R Ts Tt (\a. read_memory a 1 s) (\b. read_memory b 1 t) /\
  (!a b. R a b ==> ((p <= a /\ a < p+32) <=> (q <= b /\ b < q+32))) /\
  (!a b. R a b /\ p <= a /\ a < p+32 ==> a-p = b-q) ==>
  ld_byte_rel R
    ((Ts DIFF {a | p <= a /\ a < p+32}) UNION {p+k | k IN Ms})
    ((Tt DIFF {b | q <= b /\ b < q+32}) UNION {q+k | k IN Mt})
    (\a. read_memory a 1 (mstore p v s))
    (\b. read_memory b 1 (mstore q w t))
Proof
  simp[ld_byte_rel_def, ld_mask_word_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  Cases_on `p <= a /\ a < p+32`
  >- (`q <= b /\ b < q+32` by metis_tac[] >>
      `a-p = b-q` by metis_tac[] >>
      `a = p+(a-p) /\ b = q+(b-q) /\ a-p < 32` by decide_tac >>
      `(!k. a = k+p <=> k = a-p) /\ (!k. b = k+q <=> k = b-q)` by decide_tac >>
      simp[ld_mstore_read_byte] >> fs[SUBSET_DEF]) >>
  `~(q <= b /\ b < q+32)` by metis_tac[] >>
  `~(?k. a = k+p /\ k IN Ms)` by
    (strip_tac >>
     `k < 32` by (qpat_x_assum `Ms SUBSET _` mp_tac >> simp[SUBSET_DEF] >> metis_tac[]) >>
     decide_tac) >>
  `~(?k. b = k+q /\ k IN Mt)` by
    (strip_tac >>
     `k < 32` by (qpat_x_assum `Mt SUBSET count 32` mp_tac >> simp[SUBSET_DEF] >> metis_tac[]) >>
     decide_tac) >>
  simp[ld_mstore_read_byte] >> metis_tac[]
QED

Theorem ld_mstore_memory_backward:
  i.inst_opcode = MSTORE /\ i.inst_operands = [dst; value] /\ i.inst_outputs = [] /\
  eval_operand dst s = SOME x /\ eval_operand dst t = SOME y /\
  eval_operand value s = SOME v /\ eval_operand value t = SOME w /\
  op_taint tn value SUBSET count 32 /\ op_taint un value SUBSET count 32 /\
  ld_mask_word (op_taint tn value) (op_taint un value) v w /\
  ld_byte_rel R tn.t_mem un.t_mem (\a. read_memory a 1 s) (\b. read_memory b 1 t) /\
  (!a b. R a b ==> ((w2n x <= a /\ a < w2n x+32) <=>
                       (w2n y <= b /\ b < w2n y+32))) /\
  (!a b. R a b /\ w2n x <= a /\ a < w2n x+32 ==> a-w2n x = b-w2n y) /\
  step_inst fuel ctx i t = OK t' ==>
  ?s'. step_inst fuel ctx i s = OK s' /\
    ld_byte_rel R (step_taint i s s' tn).t_mem (step_taint i t t' un).t_mem
      (\a. read_memory a 1 s') (\b. read_memory b 1 t')
Proof
  strip_tac >>
  `!u. step_inst fuel ctx i u =
    exec_write2 (\addr val st. mstore (w2n addr) val st) i u` by
    (gen_tac >> simp[step_inst_non_invoke] >>
     pure_once_rewrite_tac[step_inst_base_def] >>
     qpat_assum `i.inst_opcode = MSTORE` (fn th => pure_rewrite_tac[th]) >> simp[]) >>
  qpat_x_assum `step_inst fuel ctx i t = OK t'` mp_tac >>
  asm_rewrite_tac[exec_write2_def] >> strip_tac >>
  qexists_tac `mstore (w2n x) v s` >>
  simp[exec_write2_def] >> gvs[] >>
  drule_all ld_mstore_taint >> strip_tac >>
  qpat_x_assum `eval_operand dst t = SOME y` kall_tac >>
  drule_all ld_mstore_taint >> strip_tac >>
  drule_all ld_mstore_masked >> simp[]
QED
