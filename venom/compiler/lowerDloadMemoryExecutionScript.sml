Theory lowerDloadMemoryExecution
Ancestors
  lowerDloadPairedBoundary venomExecSemantics lowerDloadRelocation lowerDloadOperand
  ptrDiscipline venomMemProps venomState lowerDloadOwnership arithmetic list rich_list pred_set

Theorem ld_mload_byte[local]:
  k < 32 ==>
  [EL k (word_to_bytes (mload a s) T)] = read_memory (a+k) 1 s
Proof
  strip_tac >>
  `word_to_bytes (mload a s) T =
    TAKE 32 (DROP a s.vs_memory ++ REPLICATE 32 0w)` by
    (simp[mload_def] >> irule word_bytes_roundtrip_256 >>
     simp[LENGTH_TAKE_EQ]) >>
  simp[read_memory_def, EL_TAKE, EL_APPEND_EQN, EL_DROP,
       LENGTH_DROP, EL_REPLICATE] >>
  Cases_on `a+k < LENGTH s.vs_memory` >>
  simp[DROP_EQ_NIL, TAKE1, HD_DROP, HD_APPEND_NOT_NIL] >>
  `DROP (a+k) s.vs_memory = []` by (simp[DROP_EQ_NIL] >> decide_tac) >>
  simp[] >> EVAL_TAC
QED

Theorem ld_mload_masked:
  ld_byte_rel R Ts Tt (\a. read_memory a 1 s) (\b. read_memory b 1 t) /\
  (!k. k < 32 ==> R (a+k) (b+k)) ==>
  ld_mask_word (mem_word_taint Ts a) (mem_word_taint Tt b)
    (mload a s) (mload b t)
Proof
  simp[ld_byte_rel_def] >> strip_tac >>
  simp[ld_mask_word_def, mem_word_taint_def, SUBSET_DEF] >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  `read_memory (a+k) 1 s = read_memory (b+k) 1 t` by metis_tac[] >>
  metis_tac[ld_mload_byte, CONS_11]
QED

Theorem ld_owned_mload_backward:
  i.inst_opcode = MLOAD /\ i.inst_operands = [op] /\
  i.inst_outputs = [out] /\
  ld_owned_vars V E AG AH tn un s t /\
  (!v. op = Var v ==> v IN V) /\ op_taint tn op = {} /\
  ld_byte_rel R tn.t_mem un.t_mem
    (\a. read_memory a 1 s) (\b. read_memory b 1 t) /\
  (!x y k. eval_operand op s = SOME x /\ eval_operand op t = SOME y /\
     k < 32 ==> R (w2n x+k) (w2n y+k)) /\
  step_inst fuel ctx i t = OK t' ==>
  ?s'. step_inst fuel ctx i s = OK s' /\
    ld_owned_vars V E (ld_step_prov AP AG L i) (ld_step_prov AQ AH M i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
Proof
  strip_tac >>
  `!u. step_inst fuel ctx i u =
    exec_read1 (\addr st. mload (w2n addr) st) i u` by
    (gen_tac >> simp[step_inst_non_invoke] >>
     pure_once_rewrite_tac[step_inst_base_def] >>
     qpat_assum `i.inst_opcode = MLOAD` (fn th => pure_rewrite_tac[th]) >> simp[]) >>
  qpat_x_assum `step_inst fuel ctx i t = OK t'` mp_tac >>
  asm_rewrite_tac[exec_read1_def] >>
  Cases_on `eval_operand op t` >> simp[] >> strip_tac >>
  rename1 `eval_operand op t = SOME y` >>
  `eval_operand op s <> NONE` by (drule_all ld_owned_operand_defined >> simp[]) >>
  Cases_on `eval_operand op s` >> gvs[] >>
  rename1 `eval_operand op s = SOME a` >>
  `ld_owned_value E NONE NONE (mem_word_taint tn.t_mem (w2n a))
    (mem_word_taint un.t_mem (w2n y)) (mload (w2n a) s) (mload (w2n y) t)` by
    (simp[ld_owned_value_def] >> irule ld_mload_masked >>
     qexists_tac `R` >> simp[ADD_COMM]) >>
  drule_all ld_owned_vars_update >>
  disch_then (qspec_then `out` mp_tac) >>
  simp[ld_step_prov_def, ld_out_prov_def] >>
  simp[ld_owned_vars_def, step_taint_def, out_taint_def, op_taint_def]
QED
