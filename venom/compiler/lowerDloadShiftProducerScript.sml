Theory lowerDloadShiftProducer
Ancestors
  lowerDloadOrdinaryExecution lowerDloadProvenanceSupport
  lowerDloadReachableDiscipline lowerDloadOperand ptrDiscipline
  words pred_set list venomInst venomExecSemantics venomState
  lowerDloadPairedBoundary lowerDloadOwnership lowerDloadReachableScalarExecution
  pointerConfinedDefs contextCodegenRel o1PassContract


Theorem ld_shift_taint_mono:
  mt SUBSET ms ==> shift_taint opc k mt SUBSET shift_taint opc k ms
Proof
  Cases_on `opc = SHL` >> simp[shift_taint_def, SUBSET_DEF] >>
  rpt strip_tac >> Cases_on `opc = SAR` >>
  Cases_on `0 IN mt` >> Cases_on `0 IN ms` >> gvs[] >> metis_tac[]
QED

Theorem ld_mask_word_shift:
  ld_mask_word ms mt x (y:bytes32) ==>
  ld_mask_word (shift_taint SHL k ms) (shift_taint SHL k mt)
    (word_lsl x k) (word_lsl y k) /\
  ld_mask_word (shift_taint SHR k ms) (shift_taint SHR k mt)
    (word_lsr x k) (word_lsr y k) /\
  ld_mask_word (shift_taint SAR k ms) (shift_taint SAR k mt)
    (word_asr x k) (word_asr y k)
Proof
  simp[ld_mask_word_def, GSYM word_agree_except_def] >>
  strip_tac >> rpt conj_tac
  >- (irule ld_shift_taint_mono >> simp[])
  >- (irule word_agree_except_shl >> simp[])
  >- (irule ld_shift_taint_mono >> simp[])
  >- (irule word_agree_except_shr >> simp[])
  >- (irule ld_shift_taint_mono >> simp[]) >>
  irule word_agree_except_sar >> simp[]
QED

Theorem ld_owned_shift_backward:
  MEM i.inst_opcode [SHL;SHR;SAR] /\
  i.inst_operands = [n;v] /\ i.inst_outputs = [out] /\
  ld_owned_vars V E AG AH tn un s t /\
  (!x. n = Var x \/ v = Var x ==> x IN V) /\
  ld_op_prov AG n = NONE /\ ld_op_prov AG v = NONE /\
  op_taint tn n = {} /\ step_inst fuelT CT i t = OK t' ==>
  ?s'. step_inst fuelS CS i s = OK s' /\
    ld_owned_vars V E (ld_step_prov AP AG L i) (ld_step_prov BP AH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
Proof
  strip_tac >>
  `eval_operand n s = eval_operand n t` by metis_tac[ld_owned_operand_clean] >>
  `eval_operand v s = NONE <=> eval_operand v t = NONE` by
    metis_tac[ld_owned_operand_defined] >>
  qpat_x_assum `step_inst fuelT CT i t = OK t'` mp_tac >>
  qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >> strip_tac >>
  simp[Once step_inst_non_invoke, SimpLHS] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  qpat_assum `i.inst_opcode = _` (fn th => pure_rewrite_tac[th]) >>
  simp[exec_pure2_def, SimpLHS] >>
  namedCases_on `eval_operand n t` ["", "amount"] >>
  namedCases_on `eval_operand v t` ["", "target"] >> simp[] >>
  strip_tac >>
  `?source. eval_operand v s = SOME source` by
    (Cases_on `eval_operand v s` >> gvs[]) >>
  `ld_owned_value E NONE (ld_op_prov AH n) {} (op_taint un n) amount amount` by
    metis_tac[ld_owned_operand_value] >>
  `ld_owned_value E NONE (ld_op_prov AH v)
    (op_taint tn v) (op_taint un v) source target` by
    metis_tac[ld_owned_operand_value] >>
  `ld_op_prov AH n = NONE /\ op_taint un n = {} /\
   ld_op_prov AH v = NONE /\ ld_mask_word (op_taint tn v) (op_taint un v) source target` by
    gvs[ld_owned_value_def, ld_mask_word_def] >>
  simp[Once step_inst_non_invoke] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  qpat_assum `i.inst_opcode = _` (fn th => pure_rewrite_tac[th]) >>
  simp[exec_pure2_def] >>
  `ld_mask_word (shift_taint SHL (w2n amount) (op_taint tn v))
      (shift_taint SHL (w2n amount) (op_taint un v))
      (word_lsl source (w2n amount)) (word_lsl target (w2n amount)) /\
   ld_mask_word (shift_taint SHR (w2n amount) (op_taint tn v))
      (shift_taint SHR (w2n amount) (op_taint un v))
      (word_lsr source (w2n amount)) (word_lsr target (w2n amount)) /\
   ld_mask_word (shift_taint SAR (w2n amount) (op_taint tn v))
      (shift_taint SAR (w2n amount) (op_taint un v))
      (word_asr source (w2n amount)) (word_asr target (w2n amount))` by
     (irule ld_mask_word_shift >> simp[]) >>
  qpat_x_assum `_ = t'` (SUBST_ALL_TAC o SYM) >>
  qmatch_goalsub_abbrev_tac `update_var out rs s` >>
  qmatch_goalsub_abbrev_tac `update_var out rt t` >>
  `ld_owned_value E NONE NONE
     (shift_taint i.inst_opcode (w2n amount) (op_taint tn v))
     (shift_taint i.inst_opcode (w2n amount) (op_taint un v)) rs rt` by
    simp[ld_owned_value_def, Abbr `rs`, Abbr `rt`] >>
  drule_all ld_owned_vars_update >>
  disch_then (qspec_then `out` mp_tac) >>
  simp[ld_step_prov_def, ld_out_prov_def, step_taint_def, out_taint_def,
       ld_owned_vars_def, op_taint_def]
QED

Theorem ld_annotated_shift_backward:
  (!f. MEM f ctx.ctx_functions ==> fn_ptr_ok P f) /\
  ptr_discipline lo ctx vs0 /\
  ld_annotated_reachable vs0 ctx astk k L AP AG tn fn i s /\
  MEM i.inst_opcode [SHL;SHR;SAR] /\
  i.inst_operands = [n;v] /\ i.inst_outputs = [out] /\
  ld_owned_vars V E AG AH tn un s t /\
  (!x. n = Var x \/ v = Var x ==> x IN V) /\
  step_inst fuelT CT i t = OK t' ==>
  ?s'. step_inst fuelS ctx i s = OK s' /\
    ld_owned_vars V E (ld_step_prov AP AG L i) (ld_step_prov BP AH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
Proof
  strip_tac >>
  `MEM i.inst_opcode [MUL;Div;Mod;SDIV;SMOD;Exp;ADDMOD;MULMOD;
    SLT;SGT;ISZERO;AND;OR;XOR;NOT;SHL;SHR;SAR]` by fs[MEM] >>
  `!op. MEM op i.inst_operands ==> ld_op_prov AG op = NONE` by
    (rpt strip_tac >> drule_all ld_annotated_pure_scalar_prov >> simp[]) >>
  `taint_ok fn tn i s` by metis_tac[ld_annotated_taint_ok] >>
  `op_taint tn n = {}` by metis_tac[ld_taint_shift_amount_clean] >>
  irule ld_owned_shift_backward >> simp[] >> metis_tac[MEM]
QED
