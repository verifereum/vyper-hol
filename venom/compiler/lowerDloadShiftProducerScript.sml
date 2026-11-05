Theory lowerDloadShiftProducer
Ancestors
  lowerDloadOrdinaryExecution lowerDloadProvenanceSupport
  lowerDloadReachableDiscipline lowerDloadOperand ptrDiscipline
  words pred_set list venomInst venomExecSemantics venomState
  lowerDloadPairedBoundary lowerDloadOwnership lowerDloadReachableScalarExecution
  pointerConfinedDefs contextCodegenRel o1PassContract
  lowerDloadVariableTransport lowerDloadMaskBounds lowerDloadParamProducer
  lowerDloadOpaqueExecution lowerDloadTargetGeometry lowerDloadAllocation
  memLocDefs finite_map codegenRel


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

Theorem ld_shift_update:
  MEM i.inst_opcode [SHL;SHR;SAR] /\
  i.inst_outputs = [out] /\ step_inst fuel C i s = OK s' ==>
  ?w. s' = update_var out w s
Proof
  strip_tac >>
  qpat_x_assum `step_inst fuel C i s = OK s'` mp_tac >>
  qpat_x_assum `MEM i.inst_opcode _` mp_tac >>
  simp[MEM] >> strip_tac >>
  simp[Once step_inst_non_invoke, SimpLHS] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  qpat_assum `i.inst_opcode = _` (fn th => pure_rewrite_tac[th]) >>
  simp[exec_pure2_def, SimpLHS] >>
  strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem ld_shift_taint_nonvar:
  MEM i.inst_opcode [SHL;SHR;SAR] /\
  i.inst_outputs = [out] /\ step_inst fuel C i s = OK s' ==>
  (step_taint i s s' tn).t_mem = tn.t_mem /\
  (step_taint i s s' tn).t_stor = tn.t_stor /\
  (step_taint i s s' tn).t_trans = tn.t_trans /\
  (step_taint i s s' tn).t_imm = tn.t_imm
Proof
  strip_tac >> drule_all ld_shift_update >> strip_tac >> gvs[] >>
  simp[step_taint_def, mem_taint_def, new_site_bytes_def,
    written_taint_def, step_writes_def, source_memory_write_ranges_def,
    store_taint_def, imm_taint_def, adopt_reset_def, update_var_def,
    range_bytes_def, EXTENSION, FLOOKUP_DEF] >>
  simp[SF CONJ_ss] >>
  namedCases_on `i.inst_operands` ["", "a ops1"] >> simp[] >>
  namedCases_on `ops1` ["", "b ops2"] >> simp[] >>
  namedCases_on `ops2` ["", "c ops3"] >> simp[] >>
  Cases_on `ops3` >> simp[]
QED

Theorem ld_shift_certificate_backward:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\ opaque_use_ok fn /\
  MEM i.inst_opcode [SHL;SHR;SAR] /\
  i.inst_operands = [n;v] /\ i.inst_outputs = [out] /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  LENGTH AP = LENGTH s.vs_params /\ LENGTH BP = LENGTH t.vs_params /\
  LENGTH s.vs_params = LENGTH t.vs_params /\
  (!q. q < LENGTH s.vs_params ==>
    ld_owned_value E (EL q AP) (EL q BP) {} {}
      (EL q s.vs_params) (EL q t.vs_params)) /\
  ld_frame_embedding E L H s t /\
  LIST_REL (ld_owned_selection E) AP BP /\
  (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v)) /\
  ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E AG BH tn un s t /\
  (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  ld_alloc_account keys d A s t /\
  ld_frame_bound t.vs_alloca_next H BP BH /\
  ld_stack_bound t.vs_alloca_next gstk /\ lo <= t.vs_alloca_next /\
  (!owner bs sz. ld_live astk L AP AG (owner,(bs,sz)) ==>
    owner IN live /\ lo <= bs) /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    lo <= bs /\ lo <= bt /\ bs+sz <= s.vs_alloca_next /\
    bt+sz <= t.vs_alloca_next) /\
  (!owner other bs bt sz cs ct cz.
    owner IN live /\ other IN live /\ owner <> other /\
    ld_site_entry E owner bs bt sz /\ ld_site_entry E other cs ct cz ==>
    (bs+sz <= cs \/ cs+cz <= bs) /\ (bt+sz <= ct \/ ct+cz <= bt)) /\
  ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
    tn.t_mem un.t_mem (\a. read_memory a 1 s) (\b. read_memory b 1 t) /\
  (!v. op_taint tn (Var v) SUBSET count 32) /\
  (!v. op_taint un (Var v) SUBSET count 32) /\
  un.t_stor SUBSET tn.t_stor /\ un.t_trans SUBSET tn.t_trans /\
  un.t_imm SUBSET tn.t_imm /\
  step_inst fuelT CT i t = OK t' ==>
  ?s'. step_inst fuelS CS i s = OK s' /\
    ld_frame_embedding E L H s' t' /\
    LIST_REL (ld_owned_selection E) AP BP /\
    (!v. ld_owned_selection E (FLOOKUP (ld_step_prov AP AG L i) v)
      (FLOOKUP (ld_step_prov BP BH H i) v)) /\
    ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E
      (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t' /\
    (!v. v IN V ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE)) /\
    ld_alloc_account keys d A s' t' /\
    ld_frame_bound t'.vs_alloca_next H BP (ld_step_prov BP BH H i) /\
    ld_stack_bound t'.vs_alloca_next gstk /\ lo <= t'.vs_alloca_next /\
    (!owner bs sz. ld_live astk L AP (ld_step_prov AP AG L i) (owner,(bs,sz)) ==>
      owner IN live /\ lo <= bs) /\
    (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
      lo <= bs /\ lo <= bt /\ bs+sz <= s'.vs_alloca_next /\
      bt+sz <= t'.vs_alloca_next) /\
    (!owner other bs bt sz cs ct cz.
      owner IN live /\ other IN live /\ owner <> other /\
      ld_site_entry E owner bs bt sz /\ ld_site_entry E other cs ct cz ==>
      (bs+sz <= cs \/ cs+cz <= bs) /\ (bt+sz <= ct \/ ct+cz <= bt)) /\
    ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
      (step_taint i s s' tn).t_mem (step_taint i t t' un).t_mem
      (\a. read_memory a 1 s') (\b. read_memory b 1 t') /\
    (!v. op_taint (step_taint i s s' tn) (Var v) SUBSET count 32) /\
    (!v. op_taint (step_taint i t t' un) (Var v) SUBSET count 32) /\
    (step_taint i t t' un).t_stor SUBSET (step_taint i s s' tn).t_stor /\
    (step_taint i t t' un).t_trans SUBSET (step_taint i s s' tn).t_trans /\
    (step_taint i t t' un).t_imm SUBSET (step_taint i s s' tn).t_imm /\
    LENGTH AP = LENGTH s'.vs_params /\ LENGTH BP = LENGTH t'.vs_params /\
    LENGTH s'.vs_params = LENGTH t'.vs_params /\
    (!q. q < LENGTH s'.vs_params ==>
      ld_owned_value E (EL q AP) (EL q BP) {} {}
        (EL q s'.vs_params) (EL q t'.vs_params)) /\
    (s' with vs_vars := s.vs_vars) = s /\
    (t' with vs_vars := t.vs_vars) = t
Proof
  strip_tac >>
  `MEM i (fn_insts fn)` by
    (drule ld_annotated_active_inst >>
     simp[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `!x. n = Var x \/ v = Var x ==> x IN {v | v IN V /\ ~retpc_var fn v}` by
    (rpt strip_tac >> simp[] >>
     irule ld_retpc_observable_operand >> simp[] >> qexists_tac `i` >>
     qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >>
     strip_tac >> simp[] >> metis_tac[MEM]) >>
  `?s'. step_inst fuelS CS i s = OK s' /\
    ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E
      (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'` by
    (drule_all ld_annotated_shift_backward >> simp[]) >>
  qexists_tac `s'` >>
  `?w. s' = update_var out w s` by metis_tac[ld_shift_update] >>
  `?w. t' = update_var out w t` by metis_tac[ld_shift_update] >>
  `!v. v IN V ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE)` by
    (simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >> metis_tac[lookup_var_def]) >>
  `!v. ld_owned_selection E (FLOOKUP (ld_step_prov AP AG L i) v)
      (FLOOKUP (ld_step_prov BP BH H i) v)` by
    (`ld_step_prov AP AG L i = ld_set_prov AG [out] NONE /\
      ld_step_prov BP BH H i = ld_set_prov BH [out] NONE` by
       (qpat_x_assum `MEM i.inst_opcode [SHL;SHR;SAR]` mp_tac >>
        simp[MEM] >> strip_tac >> simp[ld_step_prov_def, ld_out_prov_def]) >>
     simp[] >> irule ld_owned_set_selection >> simp[ld_owned_selection_def]) >>
  `ld_frame_bound t.vs_alloca_next H BP (ld_step_prov BP BH H i)` by
    (irule ld_frame_bound_step >> simp[]) >>
  `!owner bs sz. ld_live astk L AP (ld_step_prov AP AG L i) (owner,(bs,sz)) ==>
      owner IN live /\ lo <= bs` by metis_tac[ld_live_step_prov] >>
  `s' with vs_vars := s.vs_vars = s` by simp[ld_update_var_restore] >>
  `t' with vs_vars := t.vs_vars = t` by simp[ld_update_var_restore] >>
  `ld_frame_embedding E L H s' t'` by metis_tac[ld_frame_embedding_vars_transport] >>
  `ld_alloc_account keys d A s' t'` by metis_tac[ld_alloc_account_vars_transport] >>
  `ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
    tn.t_mem un.t_mem (\a. read_memory a 1 s') (\b. read_memory b 1 t')` by
    metis_tac[ld_byte_rel_vars_transport] >>
  `(step_taint i s s' tn).t_mem = tn.t_mem /\
   (step_taint i s s' tn).t_stor = tn.t_stor /\
   (step_taint i s s' tn).t_trans = tn.t_trans /\
   (step_taint i s s' tn).t_imm = tn.t_imm /\
   (step_taint i t t' un).t_mem = un.t_mem /\
   (step_taint i t t' un).t_stor = un.t_stor /\
   (step_taint i t t' un).t_trans = un.t_trans /\
   (step_taint i t t' un).t_imm = un.t_imm` by
    metis_tac[ld_shift_taint_nonvar] >>
  qpat_x_assum `s' = update_var out w s` kall_tac >>
  qpat_x_assum `t' = update_var out w' t` kall_tac >>
  simp[ld_step_taint_bound] >>
  dxrule ld_vars_restore_normalize >> disch_then SUBST_ALL_TAC >>
  dxrule ld_vars_restore_normalize >> disch_then SUBST_ALL_TAC >>
  simp[] >> rpt conj_tac >> fs[]
QED
