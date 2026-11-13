Theory lowerDloadMemoryExecution
Ancestors
  lowerDloadPairedBoundary venomExecSemantics lowerDloadRelocation lowerDloadOperand
  lowerDloadAccessClassification lowerDloadLifetime contextCodegenRel memLocDefs
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

Theorem ld_owned_mload_live_range:
  i.inst_opcode = MLOAD /\ i.inst_operands = [op] /\
  ld_owned_vars V E AG AH tn un s t /\
  (!v. op = Var v ==> v IN V) /\ op_taint tn op = {} /\
  access_ok lo (ld_erase AG) fn i s /\ ~in_revert_forward fn s /\
  eval_operand op s = SOME x /\ eval_operand op t = SOME y /\
  (!v owner bs sz. FLOOKUP AG v = SOME(owner,(bs,sz)) ==>
    owner IN live /\ bs+sz < dimword(:256)) /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    bt+sz < dimword(:256)) /\
  (!a. a < lo ==> R a a) /\
  (!a b. ld_site_bytes E live a b ==> R a b) ==>
  !k. k < 32 ==> R (w2n x+k) (w2n y+k)
Proof
  strip_tac >>
  `MEM (w2n x,32) (source_memory_read_ranges i s)` by
    simp[source_memory_read_ranges_def] >>
  drule ld_access_read_classification >>
  disch_then (qspecl_then [`w2n x`,`32`] mp_tac) >>
  simp[] >> strip_tac
  >- (`op_prov (ld_erase AG) op = NONE` by
        (qpat_x_assum `!ops. mem_read_ops i = SOME ops ==> _` mp_tac >>
         simp[mem_read_ops_def]) >>
      `ld_op_prov AG op = NONE` by
        (Cases_on `op` >> gvs[op_prov_def, ld_op_prov_def, ld_erase_lookup,
                                optionTheory.OPTION_MAP_EQ_NONE]) >>
      drule_all ld_owned_operand_clean >> strip_tac >>
      `x = y` by metis_tac[optionTheory.SOME_11] >> gvs[] >>
      rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  gvs[mem_read_ops_def] >>
  `owner IN live /\ bs+sz < dimword(:256)` by metis_tac[] >>
  `!bt. ld_site_entry E owner bs bt sz ==> bt+sz < dimword(:256)` by metis_tac[] >>
  `0 < (32:num)` by simp[] >>
  drule_all ld_owned_address_transport >> strip_tac >>
  rpt strip_tac >>
  qpat_x_assum `!a b. ld_site_bytes E live a b ==> R a b` irule >>
  simp[ld_site_bytes_def] >>
  qexistsl_tac [`owner`,`bs`,`bt`,`sz`,`w2n x-bs+k`] >>
  simp[] >> decide_tac
QED

Theorem ld_owned_mload_range:
  i.inst_opcode = MLOAD /\ i.inst_operands = [op] /\
  ld_owned_vars V E AG AH tn un s t /\
  (!v. op = Var v ==> v IN V) /\ op_taint tn op = {} /\
  access_ok lo (ld_erase AG) fn i s /\ ~in_revert_forward fn s /\
  eval_operand op s = SOME x /\ eval_operand op t = SOME y /\
  (!v owner bs sz. FLOOKUP AG v = SOME(owner,(bs,sz)) ==>
    owner IN live /\ bs+sz < dimword(:256)) /\
  (!owner bs bt sz. ld_site_entry E owner bs bt sz ==>
    bt+sz < dimword(:256)) /\
  (!a. a < lo ==> R a a) /\
  (!a b. ld_site_bytes E live a b ==> R a b) ==>
  !k. k < 32 ==> R (w2n x+k) (w2n y+k)
Proof
  strip_tac >>
  `!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    bt+sz < dimword(:256)` by metis_tac[] >>
  rpt strip_tac >> irule ld_owned_mload_live_range >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem ld_owned_mload_access_backward:
  i.inst_opcode = MLOAD /\ i.inst_operands = [op] /\
  i.inst_outputs = [out] /\
  ld_owned_vars V E AG AH tn un s t /\
  (!v. op = Var v ==> v IN V) /\ op_taint tn op = {} /\
  access_ok lo (ld_erase AG) fn i s /\ ~in_revert_forward fn s /\
  (!v owner bs sz. FLOOKUP AG v = SOME(owner,(bs,sz)) ==>
    owner IN live /\ bs+sz < dimword(:256)) /\
  (!owner bs bt sz. ld_site_entry E owner bs bt sz ==>
    bt+sz < dimword(:256)) /\
  (!a. a < lo ==> R a a) /\
  (!a b. ld_site_bytes E live a b ==> R a b) /\
  ld_byte_rel R tn.t_mem un.t_mem
    (\a. read_memory a 1 s) (\b. read_memory b 1 t) /\
  step_inst fuel ctx i t = OK t' ==>
  ?s'. step_inst fuel ctx i s = OK s' /\
    ld_owned_vars V E (ld_step_prov AP AG L i) (ld_step_prov AQ AH M i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
Proof
  strip_tac >> irule ld_owned_mload_backward >>
  simp[] >> qexists_tac `R` >> simp[] >>
  rpt strip_tac >>
  drule_all ld_owned_mload_range >> simp[]
QED

Theorem ld_mstore8_execution_backward:
  i.inst_opcode = MSTORE8 /\ i.inst_operands = [dst;value] /\
  eval_operand dst s = SOME p /\ eval_operand value s = SOME v /\
  eval_operand dst t = SOME q /\ eval_operand value t = SOME w /\
  step_inst fuelT CT i t = OK t' ==>
  step_inst fuelS CS i s = OK (mstore8 (w2n p) v s) /\
  t' = mstore8 (w2n q) w t
Proof
  strip_tac >>
  qpat_x_assum `step_inst fuelT CT i t = OK t'` mp_tac >>
  simp[step_inst_non_invoke] >>
  asm_rewrite_tac[step_inst_base_def, venomInstTheory.opcode_case_def, exec_write2_def] >>
  simp[]
QED

Theorem ld_mcopy_execution_backward:
  i.inst_opcode = MCOPY /\ i.inst_operands = [dst;src;sz] /\
  eval_operand dst s = SOME p /\ eval_operand src s = SOME r /\
  eval_operand sz s = SOME n /\
  eval_operand dst t = SOME q /\ eval_operand src t = SOME u /\
  eval_operand sz t = SOME n /\ step_inst fuelT CT i t = OK t' ==>
  step_inst fuelS CS i s = OK (mcopy (w2n p) (w2n r) (w2n n) s) /\
  t' = mcopy (w2n q) (w2n u) (w2n n) t
Proof
  strip_tac >>
  qpat_x_assum `step_inst fuelT CT i t = OK t'` mp_tac >>
  simp[step_inst_non_invoke] >>
  asm_rewrite_tac[step_inst_base_def, venomInstTheory.opcode_case_def] >> simp[]
QED

Theorem ld_mstore8_memory_restore:
  (mstore8 p v s with vs_memory := s.vs_memory) = s
Proof
  simp[mstore8_def, write_memory_with_expansion_def,
       expand_memory_def, write_memory_def]
QED

Theorem ld_mcopy_memory_restore:
  (mcopy p r n s with vs_memory := s.vs_memory) = s
Proof
  simp[mcopy_def, write_memory_with_expansion_def,
       expand_memory_def, write_memory_def]
QED
