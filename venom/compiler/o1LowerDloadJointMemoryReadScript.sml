(* Source-indexed masked memory reads. *)
Theory o1LowerDloadJointMemoryRead
Ancestors
  o1LowerDloadMemoryConsumer o1LowerDloadJointShift
  o1LowerDloadRelocationKernel o1LowerDloadEnvironment o1LowerDloadOccurrence
  ptrDiscipline venomState venomExecSemantics list rich_list byte words
  finite_map pred_set vfmTypes codegenRel

Theorem ld_mload_masked_bytes:
  (!k. k < 32 /\ k NOTIN m ==>
    read_byte (a+k) s.vs_memory = read_byte (b+k) t.vs_memory) ==>
  word_agree_except m (mload a s) (mload b t)
Proof
  strip_tac >> simp[word_agree_except_def, mload_def] >> rpt strip_tac >>
  simp[word_to_bytes_def, EL_word_to_bytes_aux,
    get_byte_word_of_bytes_be, LENGTH_TAKE_EQ, first_byte_at_0w, dimword_def] >>
  simp[EL_TAKE, EL_APPEND_EQN, EL_DROP, EL_REPLICATE] >>
  first_x_assum (qspec_then `b'` mp_tac) >> simp[read_byte_def] >>
  Cases_on `a+b' < LENGTH s.vs_memory` >>
  Cases_on `b+b' < LENGTH t.vs_memory` >> simp[]
QED

Theorem ld_mload_site_masked:
  ld_memory_agree sites lo mask s.vs_memory t.vs_memory /\
  FLOOKUP sites id = SOME (b,c,z) /\ j+32 <= z ==>
  word_agree_except (mem_word_taint mask (b+j)) (mload (b+j) s) (mload (c+j) t)
Proof
  strip_tac >> irule ld_mload_masked_bytes >> rpt strip_tac >>
  `b+j+k NOTIN mask` by gvs[mem_word_taint_def] >>
  simp[GSYM arithmeticTheory.ADD_ASSOC] >>
  irule ld_memory_agree_site_byte >>
  qexistsl_tac [`id`, `lo`, `mask`, `sites`, `z`] >>
  rewrite_tac[arithmeticTheory.ADD_ASSOC] >> simp[]
QED

Theorem ld_step_mload_masked_transfer:
  ld_env_agree sites fn H tn s t /\
  ld_memory_agree sites lo tn.t_mem s.vs_memory t.vs_memory /\
  FLOOKUP sites id = SOME (b,c,z) /\ j+32 <= z /\
  b+j < dimword (:256) /\ c+j < dimword (:256) /\
  inst.inst_opcode = MLOAD /\ inst.inst_operands = [p] /\ inst.inst_outputs = [out] /\
  eval_operand p s = SOME (n2w (b+j)) /\
  eval_operand p t = SOME (n2w (c+j)) ==>
  step_inst fuel C inst s = OK (update_var out (mload (b+j) s) s) /\
  step_inst fuel C' inst t = OK (update_var out (mload (c+j) t) t) /\
  ld_env_agree sites fn
    (occurrence_step a0 HP H inst (update_var out (mload (b+j) s) s))
    (step_taint inst s (update_var out (mload (b+j) s) s) tn)
    (update_var out (mload (b+j) s) s) (update_var out (mload (c+j) t) t)
Proof
  strip_tac >> conj_tac >- (irule ld_step_mload >> metis_tac[]) >>
  conj_tac >- (irule ld_step_mload >> metis_tac[]) >>
  irule ld_env_masked_update >> simp[] >>
  conj_tac >- simp[occurrence_out_def, out_prov_def] >>
  simp[out_taint_def] >> irule ld_mload_site_masked >> metis_tac[]
QED
