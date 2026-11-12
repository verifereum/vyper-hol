Theory lowerDloadImmutableWrite
Ancestors
  lowerDloadSharedState lowerDloadMaskedStorage
  venomExecSemantics venomState venomInst ptrDiscipline list words pred_set finite_map

Theorem ld_istore_backward:
  i.inst_opcode = ISTORE /\ i.inst_operands = [a;v] /\
  eval_operand a s = SOME off /\ eval_operand a t = SOME off /\
  eval_operand v s = SOME x /\ eval_operand v t = SOME y /\
  step_inst fuelT CT i t = OK t' ==>
  ?s'. step_inst fuelS CS i s = OK s' /\
    s' = istore (w2n off) x s /\ t' = istore (w2n off) y t
Proof
  strip_tac >>
  qpat_x_assum `step_inst fuelT CT i t = OK t'` mp_tac >>
  simp[Once step_inst_non_invoke, SimpLHS] >>
  asm_rewrite_tac[step_inst_base_def, opcode_case_def] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  simp[Once step_inst_non_invoke] >>
  asm_rewrite_tac[step_inst_base_def, opcode_case_def] >> simp[]
QED

Theorem ld_shared_istore:
  ld_shared_state tn un s t /\ word_agree_except (m INTER count 32) x y /\
  n SUBSET m ==>
  ld_shared_state (tn with t_imm := key_update tn.t_imm off m)
    (un with t_imm := key_update un.t_imm off n)
    (istore off x s) (istore off y t)
Proof
  strip_tac >>
  `key_update un.t_imm off n SUBSET key_update tn.t_imm off m` by
    (irule ld_key_update_mono >> gvs[ld_shared_state_def]) >>
  gvs[ld_shared_state_def] >>
  simp[istore_def, mstore_def, write_memory_with_expansion_def,
       write_memory_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `q = off` >>
  gvs[ld_key_taint_update, key_taint_def, word_agree_except_def] >>
  gvs[key_update_def, FAPPLY_FUPDATE_THM] >> metis_tac[]
QED

Theorem ld_shared_istore_backward:
  i.inst_opcode = ISTORE /\ i.inst_operands = [a;v] /\
  eval_operand a s = SOME off /\ eval_operand a t = SOME off /\
  eval_operand v s = SOME x /\ eval_operand v t = SOME y /\
  ld_shared_state tn un s t /\
  word_agree_except (op_taint tn v INTER count 32) x y /\
  op_taint un v SUBSET op_taint tn v /\
  step_inst fuelT CT i t = OK t' ==>
  ?s'. step_inst fuelS CS i s = OK s' /\
    ld_shared_state (step_taint i s s' tn) (step_taint i t t' un) s' t'
Proof
  strip_tac >>
  `?s'. step_inst fuelS CS i s = OK s' /\
    s' = istore (w2n off) x s /\ t' = istore (w2n off) y t` by
    (irule ld_istore_backward >> simp[] >> metis_tac[]) >>
  gvs[] >>
  drule_all ld_shared_istore >>
  disch_then (qspec_then `w2n off` mp_tac) >>
  simp[step_taint_def, imm_taint_def, store_taint_def, adopt_reset_def,
       ld_shared_state_def]
QED
