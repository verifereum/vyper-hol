Theory concretizePtrLoadTransport
Ancestors concretizePtrAffineTransport concretizePtrValueTransport
  ptrDiscipline venomMemProps venomState venomExecSemantics codegenRel
  list rich_list words finite_map pred_set

Theorem ptr_mload_byte[local]:
  k < 32 ==> EL k (word_to_bytes (mload off s) T) =
    read_byte (off + k) s.vs_memory
Proof
  strip_tac >>
  simp[mload_def, word_bytes_roundtrip_256, LENGTH_TAKE_EQ,
       read_byte_def, EL_TAKE, EL_APPEND_EQN, EL_DROP] >>
  Cases_on `off + k < LENGTH s.vs_memory` >> gvs[] >>
  irule EL_REPLICATE >> decide_tac
QED

Theorem ptr_mload_masked_value:
  (!k. k < 32 /\ off + k NOTIN M ==>
    read_byte (off+k) s.vs_memory = read_byte (pos+k) t.vs_memory) ==>
  word_agree_except (mem_word_taint M off) (mload off s) (mload pos t)
Proof
  simp[word_agree_except_def, mem_word_taint_def, ptr_mload_byte] >>
  metis_tac[]
QED

Theorem ptr_mload_transport:
  inst.inst_opcode = MLOAD /\ inst.inst_operands = [op] /\
  inst.inst_outputs = [out] /\
  ((?v. op = Var v) \/ (?w. op = Lit w)) /\
  ptr_vars_transport births positions TG tn s t /\
  eval_operand op s = SOME x /\ eval_operand op t = SOME y /\
  (!k. k < 32 /\ w2n x + k NOTIN tn.t_mem ==>
    read_byte (w2n x+k) s.vs_memory = read_byte (w2n y+k) t.vs_memory) /\
  step_inst fuel C inst s = OK s' ==>
  ?t'. step_inst fuel C' inst t = OK t' /\
    ptr_vars_transport births positions (step_prov PT TG inst s')
      (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  `word_agree_except (mem_word_taint tn.t_mem (w2n x))
    (mload (w2n x) s) (mload (w2n y) t)` by
    (irule ptr_mload_masked_value >> simp[]) >>
  gvs[Once run_defs, step_inst_base_def, exec_read1_def,
      eval_operands_def, AllCaseEqs()] >>
  qexists_tac `update_var out (mload (w2n y) t) t` >>
  simp[Once run_defs, step_inst_base_def, exec_read1_def,
       eval_operands_def] >>
  simp[step_prov_def, out_prov_def] >>
  irule ptr_vars_transport_update >>
  rpt (goal_assum (drule_at Any)) >>
  simp[step_taint_def, out_taint_def, ptr_value_transport_def] >>
  qexists_tac `mem_word_taint tn.t_mem (w2n x)` >> simp[]
QED

Theorem ptr_mload_transport_back:
  inst.inst_opcode = MLOAD /\ inst.inst_operands = [op] /\
  inst.inst_outputs = [out] /\
  ((?v. op = Var v) \/ (?w. op = Lit w)) /\
  ptr_vars_transport births positions TG tn s t /\
  eval_operand op s = SOME x /\ eval_operand op t = SOME y /\
  (!k. k < 32 /\ w2n x + k NOTIN tn.t_mem ==>
    read_byte (w2n x+k) s.vs_memory = read_byte (w2n y+k) t.vs_memory) /\
  step_inst fuel C' inst t = OK t' ==>
  ?s'. step_inst fuel C inst s = OK s' /\
    ptr_vars_transport births positions (step_prov PT TG inst s')
      (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  `word_agree_except (mem_word_taint tn.t_mem (w2n x))
    (mload (w2n x) s) (mload (w2n y) t)` by
    (irule ptr_mload_masked_value >> simp[]) >>
  gvs[Once run_defs, step_inst_base_def, exec_read1_def,
      eval_operands_def, AllCaseEqs()] >>
  qexists_tac `update_var out (mload (w2n x) s) s` >>
  simp[Once run_defs, step_inst_base_def, exec_read1_def, eval_operands_def] >>
  simp[step_prov_def, out_prov_def] >>
  irule ptr_vars_transport_update >>
  rpt (goal_assum (drule_at Any)) >>
  simp[step_taint_def, out_taint_def, ptr_value_transport_def] >>
  qexists_tac `mem_word_taint tn.t_mem (w2n x)` >> simp[]
QED
