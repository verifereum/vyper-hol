Theory frameRelocationLoadSteps
Ancestors frameRelocationLocal frameRelocationDemand frameRelocationGuardedValues
  codegenRel ptrDiscipline venomMemProps venomState venomExecSemantics venomInst byte words
  list rich_list

Theorem mload_byte_lane:
  b < 32 ==>
  EL b (word_to_bytes (mload d s) T) = read_byte (d+b) s.vs_memory
Proof
  strip_tac >> simp[mload_def] >>
  `LENGTH (TAKE 32 (DROP d s.vs_memory ++ REPLICATE 32 0w)) = 32` by
    simp[LENGTH_TAKE_EQ] >>
  simp[word_bytes_roundtrip_256, EL_TAKE, EL_APPEND_EQN,
       LENGTH_DROP, EL_DROP, EL_REPLICATE, read_byte_def] >>
  Cases_on `d+b < LENGTH s.vs_memory` >> simp[]
QED

Theorem demand_agree_mload:
  demand_agree R (\a. read_byte a s.vs_memory) (\b. read_byte b t.vs_memory) /\
  (!i. i < 32 /\ i NOTIN mask ==> R (d+i) (e+i)) ==>
  word_agree_except mask (mload d s) (mload e t)
Proof
  simp[word_agree_except_def] >> rpt strip_tac >>
  simp[mload_byte_lane] >> gvs[demand_agree_def] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem local_rel_mload_step:
  inst.inst_opcode = MLOAD /\ inst.inst_operands = [opd] /\
  inst.inst_outputs = [v] /\
  eval_operand opd s = SOME dst /\ eval_operand opd t = SOME dstT /\
  local_rel P ptr B R Obs s t /\
  (!u. u <> v ==> (P' u ==> P u) /\
    (!x y. ptr u x y ==> ptr' u x y) /\
    (!x y. B u x y ==> B' u x y)) /\
  (!i. i < 32 /\ i NOTIN mask ==> R (w2n dst+i) (w2n dstT+i)) /\
  (P' v ==> mask = {}) /\
  (!x y. word_agree_except mask x y ==> ptr' v x y /\ B' v x y) /\
  Obs (update_var v (mload (w2n dst) s) s)
      (update_var v (mload (w2n dstT) t) t) ==>
  ?s' t'. step_inst_base inst s = OK s' /\ step_inst_base inst t = OK t' /\
    local_rel P' ptr' B' R Obs s' t'
Proof
  strip_tac >>
  `word_agree_except mask (mload (w2n dst) s) (mload (w2n dstT) t)` by
    (irule demand_agree_mload >> metis_tac[local_rel_demand]) >>
  qexistsl_tac [`update_var v (mload (w2n dst) s) s`,
               `update_var v (mload (w2n dstT) t) t`] >>
  simp[step_inst_base_def, exec_read1_def] >>
  irule local_rel_update >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[word_agree_except_empty]
QED
