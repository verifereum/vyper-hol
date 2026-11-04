Theory algebraicOptOutputShapeProofs
Ancestors
  algebraicOptDefs venomInst
Libs
  listTheory

Theorem ao_handle_offset_projection:
  (ao_handle_offset_inst inst).inst_id = inst.inst_id /\
  (ao_handle_offset_inst inst).inst_outputs = inst.inst_outputs
Proof
  simp[ao_handle_offset_inst_def] >> rpt (CASE_TAC >> gvs[])
QED

Theorem ao_resolve_iszero_projection[simp]:
  (ao_resolve_iszero_inst targets inst).inst_id = inst.inst_id /\
  (ao_resolve_iszero_inst targets inst).inst_outputs = inst.inst_outputs
Proof
  simp[ao_resolve_iszero_inst_def]
QED

Theorem ao_pre_flip_projection:
  (ao_pre_flip_inst inst).inst_id = inst.inst_id /\
  (ao_pre_flip_inst inst).inst_outputs = inst.inst_outputs
Proof
  simp[ao_pre_flip_inst_def] >> rpt (CASE_TAC >> gvs[])
QED

Theorem ao_post_flip_projection:
  (ao_post_flip_inst inst).inst_id = inst.inst_id /\
  (ao_post_flip_inst inst).inst_outputs = inst.inst_outputs
Proof
  simp[ao_post_flip_inst_def] >> rpt (CASE_TAC >> gvs[])
QED

Theorem ao_opt_shift_projection:
  MAP (\i. (i.inst_id,i.inst_outputs)) (ao_opt_shift inst) =
  [(inst.inst_id,inst.inst_outputs)]
Proof
  simp[ao_opt_shift_def] >> rpt (CASE_TAC >> gvs[])
QED

Theorem ao_opt_signextend_projection:
  MAP (\i. (i.inst_id,i.inst_outputs)) (ao_opt_signextend ra lbl idx inst) =
  [(inst.inst_id,inst.inst_outputs)]
Proof
  Cases_on `inst.inst_operands` >- simp[ao_opt_signextend_def] >>
  Cases_on `t` >- simp[ao_opt_signextend_def] >>
  Cases_on `t'` >- (
    Cases_on `h` >> simp[ao_opt_signextend_def] >>
    rpt (IF_CASES_TAC >> simp[])) >>
  simp[ao_opt_signextend_def]
QED

Theorem ao_opt_exp_projection:
  MAP (\i. (i.inst_id,i.inst_outputs)) (ao_opt_exp inst) =
  [(inst.inst_id,inst.inst_outputs)]
Proof
  Cases_on `inst.inst_operands` >- simp[ao_opt_exp_def] >>
  Cases_on `t` >- simp[ao_opt_exp_def] >>
  Cases_on `t'` >> simp[ao_opt_exp_def] >>
  rpt (IF_CASES_TAC >> simp[])
QED

Theorem ao_opt_addsub_projection:
  MAP (\i. (i.inst_id,i.inst_outputs)) (ao_opt_addsub inst) =
  [(inst.inst_id,inst.inst_outputs)]
Proof
  Cases_on `inst.inst_operands` >- simp[ao_opt_addsub_def] >>
  Cases_on `t` >- simp[ao_opt_addsub_def] >>
  Cases_on `t'` >> simp[ao_opt_addsub_def] >>
  rpt (IF_CASES_TAC >> simp[])
QED

Theorem ao_opt_and_projection:
  MAP (\i. (i.inst_id,i.inst_outputs)) (ao_opt_and inst) =
  [(inst.inst_id,inst.inst_outputs)]
Proof
  simp[ao_opt_and_def] >> rpt (CASE_TAC >> gvs[])
QED

Theorem ao_opt_muldiv_projection:
  MAP (\i. (i.inst_id,i.inst_outputs)) (ao_opt_muldiv inst) =
  [(inst.inst_id,inst.inst_outputs)]
Proof
  Cases_on `inst.inst_operands` >- simp[ao_opt_muldiv_def] >>
  Cases_on `t` >- simp[ao_opt_muldiv_def] >>
  Cases_on `t'` >- (
    Cases_on `h'` >> simp[ao_opt_muldiv_def] >>
    rpt (IF_CASES_TAC >> simp[])) >>
  simp[ao_opt_muldiv_def]
QED

Theorem ao_opt_or_projection:
  MAP (\i. (i.inst_id,i.inst_outputs)) (ao_opt_or dfg inst) =
  [(inst.inst_id,inst.inst_outputs)]
Proof
  simp[ao_opt_or_def] >> rpt (CASE_TAC >> gvs[])
QED

Theorem ao_opt_producer_projection:
  ao_opt_producer dfg inst = SOME outs ==>
  MAP (\i. (i.inst_id,i.inst_outputs)) outs =
  [(inst.inst_id,inst.inst_outputs)]
Proof
  Cases_on `inst.inst_opcode = BALANCE`
  >- (Cases_on `inst.inst_operands` >- (simp[ao_opt_producer_def] >> strip_tac >> gvs[]) >>
      Cases_on `t`
      >- (Cases_on `h` >> simp[ao_opt_producer_def] >>
          rpt (CASE_TAC >> gvs[]) >> strip_tac >> gvs[]) >>
      simp[ao_opt_producer_def] >> strip_tac >> gvs[]) >>
  Cases_on `inst.inst_opcode = EXTCODESIZE`
  >- (simp[ao_opt_producer_def] >> strip_tac >> gvs[]) >>
  Cases_on `inst.inst_opcode = SIGNEXTEND`
  >- (Cases_on `inst.inst_operands` >- simp[ao_opt_producer_def] >>
      Cases_on `t` >- (Cases_on `h` >> simp[ao_opt_producer_def]) >>
      Cases_on `t'`
      >- (Cases_on `h` >> simp[ao_opt_producer_def] >>
          Cases_on `h'` >> simp[] >>
          rename1 `dfg_get_def dfg v` >>
          Cases_on `dfg_get_def dfg v` >> simp[] >>
          rename1 `producer.inst_opcode` >>
          Cases_on `producer.inst_opcode = SIGNEXTEND` >> simp[] >>
          Cases_on `producer.inst_operands` >> simp[] >>
          Cases_on `t` >- (Cases_on `h` >> simp[]) >>
          Cases_on `t'` >> simp[] >>
          Cases_on `h` >> simp[] >>
          strip_tac >> gvs[]) >>
      Cases_on `h` >> simp[ao_opt_producer_def]) >>
  simp[ao_opt_producer_def]
QED

Theorem ao_opt_eq_projection:
  fr "xor" = fr "not" ==>
  MAP (\i. (i.inst_id,i.inst_outputs)) (ao_opt_eq dfg fr inst) IN
  {[(inst.inst_id,inst.inst_outputs)];
   [(FST (fr "not"),[SND (fr "not")]);(inst.inst_id,inst.inst_outputs)]}
Proof
  strip_tac >>
  Cases_on `inst.inst_operands` >- simp[ao_opt_eq_def] >>
  Cases_on `t` >- simp[ao_opt_eq_def] >>
  Cases_on `t'` >- (
    Cases_on `fr "not"` >>
    simp[ao_opt_eq_def] >> rpt (IF_CASES_TAC >> simp[])) >>
  simp[ao_opt_eq_def]
QED

Theorem ao_cmp_prefer_iz_zero_projection:
  MAP (\i. (i.inst_id,i.inst_outputs)) (ao_cmp_prefer_iz_zero fr op inst) =
  [(FST (fr "iz"),[SND (fr "iz")]);(inst.inst_id,inst.inst_outputs)]
Proof
  Cases_on `fr "iz"` >> simp[ao_cmp_prefer_iz_zero_def]
QED

Theorem ao_cmp_prefer_iz_max_projection:
  MAP (\i. (i.inst_id,i.inst_outputs)) (ao_cmp_prefer_iz_max fr op inst) =
  [(FST (fr "not"),[SND (fr "not")]);
   (FST (fr "iz"),[SND (fr "iz")]);(inst.inst_id,inst.inst_outputs)]
Proof
  Cases_on `fr "iz"` >> Cases_on `fr "not"` >>
  simp[ao_cmp_prefer_iz_max_def]
QED

Theorem ao_cmp_prefer_iz_general_projection:
  MAP (\i. (i.inst_id,i.inst_outputs)) (ao_cmp_prefer_iz_general fr op1 op2 inst) =
  [(FST (fr "xor"),[SND (fr "xor")]);
   (FST (fr "iz"),[SND (fr "iz")]);(inst.inst_id,inst.inst_outputs)]
Proof
  Cases_on `fr "iz"` >> Cases_on `fr "xor"` >>
  simp[ao_cmp_prefer_iz_general_def]
QED

Theorem ao_opt_comparator_projection:
  fr "xor" = fr "not" ==>
  MAP (\i. (i.inst_id,i.inst_outputs)) (ao_opt_comparator dfg ra lbl idx fr inst) IN
  {[(inst.inst_id,inst.inst_outputs)];
   [(FST (fr "not"),[SND (fr "not")]);(inst.inst_id,inst.inst_outputs)];
   [(FST (fr "iz"),[SND (fr "iz")]);(inst.inst_id,inst.inst_outputs)];
   [(FST (fr "not"),[SND (fr "not")]);
    (FST (fr "iz"),[SND (fr "iz")]);(inst.inst_id,inst.inst_outputs)]}
Proof
  strip_tac >>
  Cases_on `inst.inst_operands` >- simp[ao_opt_comparator_def] >>
  Cases_on `t` >- simp[ao_opt_comparator_def] >>
  Cases_on `t'` >> simp[ao_opt_comparator_def] >>
  Cases_on `h = h'` >> simp[] >>
  Cases_on `ao_opt_cmp_range ra lbl idx inst
    (inst.inst_opcode = GT \/ inst.inst_opcode = SGT)
    (inst.inst_opcode = SGT \/ inst.inst_opcode = SLT)` >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  rpt (IF_CASES_TAC >> simp[ao_cmp_prefer_iz_zero_projection,
    ao_cmp_prefer_iz_max_projection, ao_cmp_prefer_iz_general_projection]) >>
  Cases_on `fr "not"` >> Cases_on `fr "iz"` >> gvs[]
QED

Theorem ao_peephole_inst_projection:
  fr "xor" = fr "not" ==>
  MAP (\i. (i.inst_id,i.inst_outputs)) (ao_peephole_inst dfg ra lbl idx fr inst) IN
  {[(inst.inst_id,inst.inst_outputs)];
   [(FST (fr "not"),[SND (fr "not")]);(inst.inst_id,inst.inst_outputs)];
   [(FST (fr "iz"),[SND (fr "iz")]);(inst.inst_id,inst.inst_outputs)];
   [(FST (fr "not"),[SND (fr "not")]);
    (FST (fr "iz"),[SND (fr "iz")]);(inst.inst_id,inst.inst_outputs)]}
Proof
  strip_tac >> pure_rewrite_tac[ao_peephole_inst_def, LET_THM] >> BETA_TAC >>
  rpt IF_CASES_TAC >>
  pure_rewrite_tac[ao_opt_shift_projection,
    ao_opt_signextend_projection, ao_opt_exp_projection,
    ao_opt_addsub_projection, ao_opt_and_projection,
    ao_opt_muldiv_projection, ao_opt_or_projection] >>
  simp[]
  >~ [`ao_opt_eq dfg fr inst`] >- (
    drule ao_opt_eq_projection >> simp[] >> metis_tac[])
  >> drule ao_opt_comparator_projection >> simp[]
QED
Theorem ao_transform_inst_projection:
  fr "xor" = fr "not" ==>
  MAP (\i. (i.inst_id,i.inst_outputs)) (ao_transform_inst dfg ra lbl idx targets fr inst) IN
  {[(inst.inst_id,inst.inst_outputs)];
   [(FST (fr "not"),[SND (fr "not")]);(inst.inst_id,inst.inst_outputs)];
   [(FST (fr "iz"),[SND (fr "iz")]);(inst.inst_id,inst.inst_outputs)];
   [(FST (fr "not"),[SND (fr "not")]);
    (FST (fr "iz"),[SND (fr "iz")]);(inst.inst_id,inst.inst_outputs)]}
Proof
  strip_tac >> pure_rewrite_tac[ao_transform_inst_def, LET_THM] >> BETA_TAC >>
  rpt IF_CASES_TAC
  >- gvs[ao_resolve_iszero_projection]
  >- gvs[ao_resolve_iszero_projection] >>
  Cases_on `ao_opt_producer dfg (ao_resolve_iszero_inst targets inst)` >>
  asm_rewrite_tac[optionTheory.option_case_def, MAP_MAP_o, combinTheory.o_DEF] >> BETA_TAC >>
  pure_rewrite_tac[ao_post_flip_projection]
  >- (drule ao_peephole_inst_projection >>
      disch_then (qspecl_then [`ra`,`lbl`,`ao_pre_flip_inst (ao_resolve_iszero_inst targets inst)`,
        `idx`,`dfg`] mp_tac) >>
      simp[ao_pre_flip_projection, ao_resolve_iszero_projection])
  >> drule ao_opt_producer_projection >>
  simp[ao_resolve_iszero_projection] >> strip_tac >>
  gvs[ao_post_flip_projection]
QED
