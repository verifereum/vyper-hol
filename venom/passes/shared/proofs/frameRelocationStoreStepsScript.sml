Theory frameRelocationStoreSteps
Ancestors frameRelocationCopySteps frameRelocationDemand frameRelocationLocal
  regularCallEmitSim venomState venomExecSemantics venomInst byte words

Theorem demand_agree_write_memory:
  demand_agree R (\a. read_byte a s.vs_memory) (\b. read_byte b t.vs_memory) /\
  (!a b. next a b /\ d <= a /\ a < d + LENGTH xs ==>
    e <= b /\ b < e + LENGTH ys /\ EL (a-d) xs = EL (b-e) ys) /\
  (!a b. next a b /\ ~(d <= a /\ a < d + LENGTH xs) ==>
    R a b /\ ~(e <= b /\ b < e + LENGTH ys)) ==>
  demand_agree next
    (\a. read_byte a (write_memory_with_expansion d xs s).vs_memory)
    (\b. read_byte b (write_memory_with_expansion e ys t).vs_memory)
Proof
  strip_tac >> irule demand_agree_producer_update >>
  qexistsl_tac [`R`, `\a. EL (a-d) xs`, `\b. EL (b-e) ys`,
    `\a. read_byte a s.vs_memory`, `\b. read_byte b t.vs_memory`,
    `\a. d <= a /\ a < d + LENGTH xs`,
    `\b. e <= b /\ b < e + LENGTH ys`] >>
  simp[read_byte_write_memory_with_expansion] >>
  gvs[demand_agree_def] >> metis_tac[]
QED

Theorem local_rel_write_memory:
  local_rel P ptr B R Obs s t /\
  (!a b. next a b /\ d <= a /\ a < d + LENGTH xs ==>
    e <= b /\ b < e + LENGTH ys /\ EL (a-d) xs = EL (b-e) ys) /\
  (!a b. next a b /\ ~(d <= a /\ a < d + LENGTH xs) ==>
    R a b /\ ~(e <= b /\ b < e + LENGTH ys)) /\
  Obs (write_memory_with_expansion d xs s)
      (write_memory_with_expansion e ys t) ==>
  local_rel P ptr B next Obs
    (write_memory_with_expansion d xs s)
    (write_memory_with_expansion e ys t)
Proof
  strip_tac >> irule local_rel_memory_frame >>
  conj_tac >- simp[] >> conj_tac
  >- (irule demand_agree_write_memory >> metis_tac[local_rel_demand]) >>
  qexistsl_tac [`R`, `s`, `t`] >> simp[write_memory_with_expansion_def]
QED

Theorem mstore8_as_write_memory:
  mstore8 d v s = write_memory_with_expansion d [(w2w v):word8] s
Proof
  simp[mstore8_def, write_memory_with_expansion_def]
QED

Theorem local_rel_mstore_step:
  inst.inst_opcode = MSTORE /\ inst.inst_operands = [opd;opv] /\
  eval_operand opd s = SOME dst /\ eval_operand opv s = SOME value /\
  eval_operand opd t = SOME dstT /\ eval_operand opv t = SOME valueT /\
  local_rel P ptr B R Obs s t /\
  (!a b. next a b /\ w2n dst <= a /\ a < w2n dst + 32 ==>
    w2n dstT <= b /\ b < w2n dstT + 32 /\
    EL (a-w2n dst) (word_to_bytes value T) =
    EL (b-w2n dstT) (word_to_bytes valueT T)) /\
  (!a b. next a b /\ ~(w2n dst <= a /\ a < w2n dst + 32) ==>
    R a b /\ ~(w2n dstT <= b /\ b < w2n dstT + 32)) /\
  Obs (mstore (w2n dst) value s) (mstore (w2n dstT) valueT t) ==>
  ?s' t'. step_inst_base inst s = OK s' /\ step_inst_base inst t = OK t' /\
    local_rel P ptr B next Obs s' t'
Proof
  strip_tac >>
  qexistsl_tac [`mstore (w2n dst) value s`, `mstore (w2n dstT) valueT t`] >>
  simp[step_inst_base_def, exec_write2_def] >>
  `local_rel P ptr B next Obs
     (write_memory_with_expansion (w2n dst) (word_to_bytes value T) s)
     (write_memory_with_expansion (w2n dstT) (word_to_bytes valueT T) t)`
    suffices_by simp[mstore_def, write_memory_with_expansion_def,
                     LENGTH_word_to_bytes] >>
  irule local_rel_write_memory >>
  simp[LENGTH_word_to_bytes] >>
  conj_tac >- metis_tac[] >> conj_tac
  >- gvs[mstore_def, write_memory_with_expansion_def, LENGTH_word_to_bytes] >>
  qexists_tac `R` >> metis_tac[]
QED

Theorem local_rel_mstore8_step:
  inst.inst_opcode = MSTORE8 /\ inst.inst_operands = [opd;opv] /\
  eval_operand opd s = SOME dst /\ eval_operand opv s = SOME value /\
  eval_operand opd t = SOME dstT /\ eval_operand opv t = SOME valueT /\
  local_rel P ptr B R Obs s t /\
  (!a b. next a b /\ w2n dst <= a /\ a < w2n dst + 1 ==>
    w2n dstT <= b /\ b < w2n dstT + 1 /\
    EL (a-w2n dst) [(w2w value):word8] =
    EL (b-w2n dstT) [(w2w valueT):word8]) /\
  (!a b. next a b /\ ~(w2n dst <= a /\ a < w2n dst + 1) ==>
    R a b /\ ~(w2n dstT <= b /\ b < w2n dstT + 1)) /\
  Obs (mstore8 (w2n dst) value s) (mstore8 (w2n dstT) valueT t) ==>
  ?s' t'. step_inst_base inst s = OK s' /\ step_inst_base inst t = OK t' /\
    local_rel P ptr B next Obs s' t'
Proof
  strip_tac >>
  qexistsl_tac [`mstore8 (w2n dst) value s`, `mstore8 (w2n dstT) valueT t`] >>
  simp[step_inst_base_def, exec_write2_def] >>
  rewrite_tac[mstore8_as_write_memory] >> irule local_rel_write_memory >>
  simp[GSYM mstore8_as_write_memory] >> metis_tac[]
QED
