Theory lowerDloadOrdinaryExecution
Ancestors
  lowerDloadPairedBoundary lowerDloadOwnership ptrDiscipline
  venomExecSemantics venomState execEquivParamBase lowerDloadControlPosition
  lowerDloadDefs o1ContractLowerDload lowerDloadOperand finite_map

Theorem ld_owned_assign_backward:
  i.inst_opcode = ASSIGN /\ i.inst_operands = [op] /\ i.inst_outputs = [out] /\
  ld_owned_vars V E AG AH tn un s t /\ (!v. op = Var v ==> v IN V) /\
  step_inst fuelT CT i t = OK t' ==>
  ?x y s'. eval_operand op s = SOME x /\ eval_operand op t = SOME y /\
    s' = update_var out x s /\ t' = update_var out y t /\
    step_inst fuelS CS i s = OK s' /\
    ld_owned_vars V E (ld_step_prov AP AG L i) (ld_step_prov AQ AH M i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
Proof
  strip_tac >>
  qpat_x_assum `step_inst fuelT CT i t = OK t'` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def] >>
  Cases_on `eval_operand op t` >> simp[] >> strip_tac >>
  `eval_operand op s = NONE <=> eval_operand op t = NONE` by
    metis_tac[ld_owned_operand_defined] >>
  Cases_on `eval_operand op s` >> gvs[] >>
  drule_all ld_owned_operand_value >> strip_tac >>
  drule_all ld_owned_vars_update >>
  disch_then (qspec_then `out` mp_tac) >>
  Cases_on `ld_op_prov AG op` >> Cases_on `ld_op_prov AH op` >>
  simp[ld_step_prov_def, ld_out_prov_def, ld_first_prov_def,
       step_taint_def, out_taint_def, ld_owned_vars_def, op_taint_def]
QED

Theorem ld_owned_phis_backward:
  !ins s t t' AG AH tn un.
    ld_owned_vars V E AG AH tn un s t /\
    s.vs_prev_bb = t.vs_prev_bb /\
    (!i v. MEM i ins /\ MEM (Var v) i.inst_operands ==> v IN V) /\
    eval_phis t ins = OK t' ==>
    ?s'. eval_phis s ins = OK s' /\
      ld_owned_vars V E
        (ld_phis_prov s.vs_prev_bb AG ins)
        (ld_phis_prov t.vs_prev_bb AH ins)
        (tn with t_var := phis_taint s.vs_prev_bb tn ins)
        (un with t_var := phis_taint t.vs_prev_bb un ins) s' t'
Proof
  Induct >> rpt gen_tac >> simp[eval_phis_def, ld_phis_prov_def, phis_taint_def]
  >- simp[ld_owned_vars_def, op_taint_def] >>
  strip_tac >> Cases_on `h.inst_opcode = PHI` >> gvs[]
  >- (gvs[eval_one_phi_def, AllCaseEqs()] >>
      rename1 `eval_operand op t = SOME y` >>
      `!v. op = Var v ==> v IN V` by
        metis_tac[execEquivParamBaseTheory.resolve_phi_MEM] >>
      `eval_operand op s = NONE <=> eval_operand op t = NONE` by
        metis_tac[ld_owned_operand_defined] >>
      Cases_on `eval_operand op s` >> gvs[] >>
      drule_all ld_owned_operand_value >> strip_tac >>
      first_x_assum (qspecl_then [`s`, `t`] mp_tac) >>
      disch_then drule >>
      disch_then (qspec_then `s''` mp_tac) >>
      simp[] >> impl_tac >- metis_tac[] >>
      strip_tac >>
      qexists_tac `update_var out x s'` >>
      conj_tac >- metis_tac[] >>
      drule_all ld_owned_vars_update >>
      disch_then (qspec_then `out` mp_tac) >>
      simp[ld_phi_prov_def, phi_taint_def]) >>
  gvs[ld_owned_vars_def, op_taint_def]
QED

Theorem ld_lowered_phis_annotations:
  !ins a outs b prev AG tn.
    lower_dload_insts_supply a ins = (outs,b) ==>
    ld_phis_prov prev AG outs = ld_phis_prov prev AG ins /\
    phis_taint prev tn outs = phis_taint prev tn ins
Proof
  Induct >- simp[lower_dload_insts_supply_def, ld_phis_prov_def, phis_taint_def] >>
  rpt gen_tac >>
  Cases_on `lower_dload_inst_supply a h` >>
  Cases_on `lower_dload_insts_supply r ins` >>
  simp[lower_dload_insts_supply_def] >> strip_tac >> gvs[] >>
  Cases_on `h.inst_opcode = PHI`
  >- (`lower_dload_inst_supply a h = ([h],a)` by
        (irule lower_dload_inst_supply_special >> simp[]) >>
      gvs[] >> first_x_assum drule >>
      disch_then (qspecl_then [`prev`, `AG`, `tn`] strip_assume_tac) >>
      simp[ld_phis_prov_def, phis_taint_def]) >>
  `q <> []` by metis_tac[lower_dload_inst_supply_nonempty] >>
  `MEM (HD q) q` by (Cases_on `q` >> gvs[]) >>
  `(HD q).inst_opcode <> PHI` by
    metis_tac[lower_dload_inst_supply_control] >>
  Cases_on `q` >> gvs[ld_phis_prov_def, phis_taint_def]
QED

Theorem ld_owned_lowered_block_phis_backward:
  lower_dload_block_supply a bb = (bb',b) /\
  ld_owned_vars V E AG AH tn un s t /\
  s.vs_prev_bb = t.vs_prev_bb /\
  (!i v. MEM i bb.bb_instructions /\ MEM (Var v) i.inst_operands ==> v IN V) /\
  eval_phis t bb'.bb_instructions = OK t' ==>
  ?s'. eval_phis s bb.bb_instructions = OK s' /\
    ld_owned_vars V E
      (ld_phis_prov s.vs_prev_bb AG bb.bb_instructions)
      (ld_phis_prov t.vs_prev_bb AH bb'.bb_instructions)
      (tn with t_var := phis_taint s.vs_prev_bb tn bb.bb_instructions)
      (un with t_var := phis_taint t.vs_prev_bb un bb'.bb_instructions) s' t'
Proof
  strip_tac >>
  `eval_phis t bb.bb_instructions = OK t'` by
    metis_tac[lower_dload_block_supply_phis] >>
  `?a1. lower_dload_insts_supply a bb.bb_instructions = (bb'.bb_instructions,a1)` by
    gvs[lower_dload_block_supply_def, AllCaseEqs()] >>
  drule ld_lowered_phis_annotations >>
  disch_then (qspecl_then [`t.vs_prev_bb`, `AH`, `un`] strip_assume_tac) >>
  drule_all ld_owned_phis_backward >> gvs[]
QED

Theorem ld_owned_offset_cases_backward:
  i.inst_operands = [a;b] /\ i.inst_outputs = [out] /\
  ld_owned_vars V E AG AH tn un s t /\
  (!v. a = Var v \/ b = Var v ==> v IN V) /\
  op_taint tn a = {} /\ op_taint tn b = {} /\
  (((i.inst_opcode = ADD \/ i.inst_opcode = SUB) /\ ld_op_prov AG b = NONE) \/
   (i.inst_opcode = ADD /\ ld_op_prov AG a = NONE)) /\
  step_inst fuelT CT i t = OK t' ==>
  ?s'. step_inst fuelS CS i s = OK s' /\
    ld_owned_vars V E (ld_step_prov AP AG L i) (ld_step_prov AQ AH M i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
Proof
  rpt strip_tac >>
  `eval_operand a s = NONE <=> eval_operand a t = NONE` by
    (irule ld_owned_operand_defined >> simp[] >> metis_tac[]) >>
  `eval_operand b s = NONE <=> eval_operand b t = NONE` by
    (irule ld_owned_operand_defined >> simp[] >> metis_tac[]) >>
  qpat_x_assum `step_inst fuelT CT i t = OK t'` mp_tac >>
  simp[Once step_inst_non_invoke, SimpLHS] >>
  simp[Once step_inst_base_def, SimpLHS] >>
  simp[exec_pure2_def, SimpLHS] >>
  Cases_on `eval_operand a t` >> Cases_on `eval_operand b t` >> simp[] >>
  strip_tac >> Cases_on `eval_operand a s` >> Cases_on `eval_operand b s` >> gvs[] >>
  `ld_owned_value E (ld_op_prov AG a) (ld_op_prov AH a)
      {} (op_taint un a) x'' x` by metis_tac[ld_owned_operand_value] >>
  `ld_owned_value E (ld_op_prov AG b) (ld_op_prov AH b)
      {} (op_taint un b) x''' x'` by metis_tac[ld_owned_operand_value] >>
  simp[Once step_inst_non_invoke] >>
  simp[Once step_inst_base_def] >>
  simp[exec_pure2_def] >>
  `!ps pt Mt u v. ld_owned_value E ps pt {} Mt u v ==> Mt = {}` by
    (qx_gen_tac `ps` >> Cases_on `ps`
     >- simp[ld_owned_value_def, ld_mask_word_def] >>
     rename1 `ld_owned_value E (SOME site)` >>
     PairCases_on `site` >> simp[ld_owned_value_def] >> metis_tac[]) >>
  `op_taint un a = {} /\ op_taint un b = {}` by metis_tac[] >>
  `!pt u v. ld_owned_value E NONE pt {} {} u v ==> pt = NONE /\ u = v` by
    (simp[ld_owned_value_def] >> metis_tac[ld_mask_word_clean]) >>
  qmatch_goalsub_abbrev_tac `update_var out sx s` >>
  qmatch_goalsub_abbrev_tac `update_var out tx t` >>
  `ld_owned_value E (ld_first_prov AG [a;b]) (ld_first_prov AH [a;b])
      {} {} sx tx` by
    (`ld_op_prov AG a = NONE ==> ld_op_prov AH a = NONE /\ x'' = x` by
       metis_tac[] >>
     `ld_op_prov AG b = NONE ==> ld_op_prov AH b = NONE /\ x''' = x'` by
       metis_tac[] >>
     Cases_on `ld_op_prov AG a` >> Cases_on `ld_op_prov AH a` >>
     Cases_on `ld_op_prov AG b` >> Cases_on `ld_op_prov AH b` >>
     gvs[ld_first_prov_def, Abbr `sx`, Abbr `tx`] >>
     metis_tac[ld_owned_value_offset_add, ld_owned_value_offset_sub,
               wordsTheory.WORD_ADD_COMM]) >>
  drule_all ld_owned_vars_update >>
  disch_then (qspec_then `out` mp_tac) >>
  simp[ld_step_prov_def, ld_out_prov_def, step_taint_def, out_taint_def,
       ld_owned_vars_def, op_taint_def, Abbr `sx`, Abbr `tx`]
QED

Theorem ld_owned_offset_backward:
  (i.inst_opcode = ADD \/ i.inst_opcode = SUB) /\
  i.inst_operands = [a;b] /\ i.inst_outputs = [out] /\
  ld_owned_vars V E AG AH tn un s t /\
  (!v. a = Var v \/ b = Var v ==> v IN V) /\
  ld_op_prov AG b = NONE /\ op_taint tn a = {} /\ op_taint tn b = {} /\
  step_inst fuelT CT i t = OK t' ==>
  ?s'. step_inst fuelS CS i s = OK s' /\
    ld_owned_vars V E (ld_step_prov AP AG L i) (ld_step_prov AQ AH M i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
Proof
  metis_tac[ld_owned_offset_cases_backward]
QED

Theorem ld_owned_scalar_left_add_backward:
  i.inst_opcode = ADD /\
  i.inst_operands = [a;b] /\ i.inst_outputs = [out] /\
  ld_owned_vars V E AG AH tn un s t /\
  (!v. a = Var v \/ b = Var v ==> v IN V) /\
  ld_op_prov AG a = NONE /\ op_taint tn a = {} /\ op_taint tn b = {} /\
  step_inst fuelT CT i t = OK t' ==>
  ?s'. step_inst fuelS CS i s = OK s' /\
    ld_owned_vars V E (ld_step_prov AP AG L i) (ld_step_prov AQ AH M i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
Proof
  metis_tac[ld_owned_offset_cases_backward]
QED

Theorem ld_owned_pure_scalar_backward:
  MEM i.inst_opcode [ADD; SUB; MUL; Div; Mod; SDIV; SMOD; Exp;
    ADDMOD; MULMOD; EQ; LT; GT; SLT; SGT; ISZERO; AND; OR; XOR; NOT; SHL; SHR; SAR] /\
  i.inst_outputs = [out] /\ ld_owned_vars V E AG AH tn un s t /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  (!op. MEM op i.inst_operands ==> ld_op_prov AG op = NONE /\ op_taint tn op = {}) /\
  step_inst fuelT CT i t = OK t' ==>
  ?s'. step_inst fuelS CS i s = OK s' /\
    ld_owned_vars V E (ld_step_prov AP AG L i) (ld_step_prov AQ AH M i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
Proof
  strip_tac >>
  `!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> irule ld_owned_operand_clean >> simp[] >> metis_tac[]) >>
  `!op w. MEM op i.inst_operands /\ eval_operand op t = SOME w ==>
      ld_op_prov AH op = NONE /\ op_taint un op = {}` by
    (rpt strip_tac >>
     `ld_owned_value E (ld_op_prov AG op) (ld_op_prov AH op)
        (op_taint tn op) (op_taint un op) w w` by
       (irule ld_owned_operand_value >> simp[] >> metis_tac[]) >>
     gvs[ld_owned_value_def, ld_mask_word_def]) >>
  qpat_x_assum `step_inst fuelT CT i t = OK t'` mp_tac >>
  qpat_x_assum `MEM i.inst_opcode _` mp_tac >>
  simp[listTheory.MEM] >> strip_tac >>
  simp[Once step_inst_non_invoke, SimpLHS] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  qpat_assum `i.inst_opcode = _` (fn th => pure_rewrite_tac[th]) >>
  simp[SimpLHS] >>
  simp[exec_pure1_def, exec_pure2_def, exec_pure3_def, SimpLHS] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  simp[Once step_inst_non_invoke] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  qpat_assum `i.inst_opcode = _` (fn th => pure_rewrite_tac[th]) >>
  simp[exec_pure1_def, exec_pure2_def, exec_pure3_def] >>
  qmatch_goalsub_abbrev_tac `update_var out result s` >>
  `ld_owned_value E NONE NONE {} {} result result` by
    simp[ld_owned_value_def, ld_mask_word_def] >>
  drule_all ld_owned_vars_update >>
  disch_then (qspec_then `out` mp_tac) >>
  simp[ld_step_prov_def, ld_out_prov_def, ld_first_prov_def,
       step_taint_def, out_taint_def] >>
  simp[shift_taint_def] >>
  simp[ld_owned_vars_def, op_taint_def]
QED

Theorem ld_owned_compare_backward:
  MEM i.inst_opcode [EQ; LT; GT] /\
  i.inst_operands = [a;b] /\ i.inst_outputs = [out] /\
  ld_owned_vars V E AG AH tn un s t /\
  (!v. a = Var v \/ b = Var v ==> v IN V) /\
  eval_operand a s = SOME x /\ eval_operand b s = SOME y /\
  ld_op_prov AG a = SOME(owner,(bs,sz)) /\
  ld_op_prov AG b = SOME(owner,(bs,sz)) /\
  op_taint tn a = {} /\ op_taint tn b = {} /\
  ld_site_entry E owner bs bt sz /\ 0 < sz /\
  bs <= w2n x /\ w2n x <= bs+sz /\ bs <= w2n y /\ w2n y <= bs+sz /\
  bs+sz < dimword(:256) /\ bt+sz < dimword(:256) /\
  step_inst fuelT CT i t = OK t' ==>
  ?s'. step_inst fuelS CS i s = OK s' /\
    ld_owned_vars V E (ld_step_prov AP AG L i) (ld_step_prov AQ AH M i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
Proof
  strip_tac >>
  qpat_x_assum `step_inst fuelT CT i t = OK t'` mp_tac >>
  qpat_x_assum `MEM i.inst_opcode _` mp_tac >>
  simp[listTheory.MEM] >> strip_tac >>
  simp[Once step_inst_non_invoke, SimpLHS] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  qpat_assum `i.inst_opcode = _` (fn th => pure_rewrite_tac[th]) >>
  simp[exec_pure2_def, SimpLHS] >>
  Cases_on `eval_operand a t` >> Cases_on `eval_operand b t` >> simp[] >>
  strip_tac >>
  `ld_owned_value E (SOME(owner,(bs,sz))) (ld_op_prov AH a)
      {} (op_taint un a) x x'` by metis_tac[ld_owned_operand_value] >>
  `ld_owned_value E (SOME(owner,(bs,sz))) (ld_op_prov AH b)
      {} (op_taint un b) y x''` by metis_tac[ld_owned_operand_value] >>
  `(x <+ y <=> x' <+ x'') /\ (y <+ x <=> x'' <+ x') /\
    (x = y <=> x' = x'')` by
      (irule ld_owned_value_compare >> metis_tac[]) >>
  gvs[wordsTheory.WORD_LO] >>
  simp[Once step_inst_non_invoke] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  qpat_assum `i.inst_opcode = _` (fn th => pure_rewrite_tac[th]) >>
  simp[exec_pure2_def] >>
  simp[arithmeticTheory.GREATER_DEF] >>
  qmatch_goalsub_abbrev_tac `update_var out result s` >>
  `ld_owned_value E NONE NONE {} {} result result` by
    simp[ld_owned_value_def, ld_mask_word_def] >>
  drule_all ld_owned_vars_update >>
  disch_then (qspec_then `out` mp_tac) >>
  simp[ld_step_prov_def, ld_out_prov_def, step_taint_def, out_taint_def,
       ld_owned_vars_def, op_taint_def]
QED
