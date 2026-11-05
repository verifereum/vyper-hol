Theory algebraicOptShapeProofs
Ancestors
  algebraicOptDefs venomInst
Libs
  listTheory pred_setTheory

Theorem ao_handle_offset_inst_shape:
  (ao_handle_offset_inst inst).inst_id = inst.inst_id /\
  (ao_handle_offset_inst inst).inst_outputs = inst.inst_outputs /\
  inst_uses (ao_handle_offset_inst inst) = inst_uses inst /\
  is_terminator (ao_handle_offset_inst inst).inst_opcode =
    is_terminator inst.inst_opcode /\
  ((ao_handle_offset_inst inst).inst_opcode = PHI <=> inst.inst_opcode = PHI)
Proof
  Cases_on `inst.inst_opcode = ADD` >>
  simp[ao_handle_offset_inst_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `h` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `h` >> simp[] >>
  Cases_on `t'` >>
  gvs[inst_uses_def, operand_vars_def, operand_var_def, is_terminator_def]
QED

Theorem ao_resolve_iszero_inst_fields:
  (ao_resolve_iszero_inst targets inst).inst_id = inst.inst_id /\
  (ao_resolve_iszero_inst targets inst).inst_outputs = inst.inst_outputs /\
  (ao_resolve_iszero_inst targets inst).inst_opcode = inst.inst_opcode /\
  LENGTH (ao_resolve_iszero_inst targets inst).inst_operands =
    LENGTH inst.inst_operands
Proof
  simp[ao_resolve_iszero_inst_def]
QED

Theorem ao_pre_flip_inst_shape:
  (ao_pre_flip_inst inst).inst_id = inst.inst_id /\
  (ao_pre_flip_inst inst).inst_outputs = inst.inst_outputs /\
  (ao_pre_flip_inst inst).inst_opcode = inst.inst_opcode /\
  set (inst_uses (ao_pre_flip_inst inst)) = set (inst_uses inst) /\
  LENGTH (ao_pre_flip_inst inst).inst_operands = LENGTH inst.inst_operands /\
  ((is_terminator inst.inst_opcode \/ inst.inst_opcode = PHI) ==>
    ao_pre_flip_inst inst = inst)
Proof
  Cases_on `inst.inst_operands` >> simp[ao_pre_flip_inst_def] >>
  Cases_on `t` >> simp[ao_pre_flip_inst_def] >>
  Cases_on `t'` >> simp[ao_pre_flip_inst_def] >>
  IF_CASES_TAC >> gvs[inst_uses_def, is_terminator_def] >>
  Cases_on `h` >> Cases_on `h'` >>
  gvs[operand_vars_def, operand_var_def, EXTENSION, DISJ_COMM]
QED

Theorem ao_post_flip_inst_shape:
  (ao_post_flip_inst inst).inst_id = inst.inst_id /\
  (ao_post_flip_inst inst).inst_outputs = inst.inst_outputs /\
  (ao_post_flip_inst inst).inst_opcode = inst.inst_opcode /\
  set (inst_uses (ao_post_flip_inst inst)) = set (inst_uses inst) /\
  LENGTH (ao_post_flip_inst inst).inst_operands = LENGTH inst.inst_operands /\
  ((is_terminator inst.inst_opcode \/ inst.inst_opcode = PHI) ==>
    ao_post_flip_inst inst = inst)
Proof
  Cases_on `inst.inst_operands` >> simp[ao_post_flip_inst_def] >>
  Cases_on `t` >> simp[ao_post_flip_inst_def] >>
  Cases_on `t'` >> simp[ao_post_flip_inst_def] >>
  IF_CASES_TAC >> gvs[inst_uses_def, is_terminator_def] >>
  Cases_on `h` >> Cases_on `h'` >>
  gvs[operand_vars_def, operand_var_def, EXTENSION, DISJ_COMM]
QED

Theorem ao_opt_producer_shape:
  ao_opt_producer dfg inst = SOME outs ==>
  ?out. outs = [out] /\
    out.inst_id = inst.inst_id /\ out.inst_outputs = inst.inst_outputs /\
    set (inst_uses out) SUBSET set (inst_uses inst) /\
    is_terminator out.inst_opcode = is_terminator inst.inst_opcode /\
    (out.inst_opcode = PHI <=> inst.inst_opcode = PHI) /\
    ((out.inst_opcode = ISZERO \/ out.inst_opcode = ASSERT) ==> out = inst)
Proof
  simp[ao_opt_producer_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  gvs[inst_uses_def, operand_vars_def, operand_var_def,
      is_terminator_def, SUBSET_DEF]
QED

(* The layout records exactly which instructions own the old outputs and
   which optional slots own the allocated outputs.  Opcode arithmetic and
   operand evaluation are deliberately outside this syntactic interface. *)
Definition ao_rewrite_layout_def:
  ao_rewrite_layout inst fr outs <=>
    MAP (\i. (i.inst_id,i.inst_outputs)) outs =
      [(inst.inst_id,inst.inst_outputs)] \/
    MAP (\i. (i.inst_id,i.inst_outputs)) outs =
      [(FST (fr "not"),[SND (fr "not")]);
       (inst.inst_id,inst.inst_outputs)] \/
    MAP (\i. (i.inst_id,i.inst_outputs)) outs =
      [(FST (fr "iz"),[SND (fr "iz")]);
       (inst.inst_id,inst.inst_outputs)] \/
    MAP (\i. (i.inst_id,i.inst_outputs)) outs =
      [(FST (fr "not"),[SND (fr "not")]);
       (FST (fr "iz"),[SND (fr "iz")]);
       (inst.inst_id,inst.inst_outputs)]
End

Theorem ao_rewrite_layout_singleton[simp]:
  ao_rewrite_layout inst fr [out] <=>
    out.inst_id = inst.inst_id /\ out.inst_outputs = inst.inst_outputs
Proof
  simp[ao_rewrite_layout_def, EQ_SYM_EQ]
QED

Theorem ao_simple_peephole_layout:
  ao_rewrite_layout inst fr (ao_opt_shift inst) /\
  ao_rewrite_layout inst fr (ao_opt_signextend ra lbl idx inst) /\
  ao_rewrite_layout inst fr (ao_opt_exp inst) /\
  ao_rewrite_layout inst fr (ao_opt_addsub inst) /\
  ao_rewrite_layout inst fr (ao_opt_and inst) /\
  ao_rewrite_layout inst fr (ao_opt_muldiv inst) /\
  ao_rewrite_layout inst fr (ao_opt_or dfg inst)
Proof
  Cases_on `inst.inst_operands` >>
  simp[ao_opt_shift_def, ao_opt_signextend_def, ao_opt_exp_def,
       ao_opt_addsub_def, ao_opt_and_def, ao_opt_muldiv_def, ao_opt_or_def,
       ao_rewrite_layout_def] >>
  Cases_on `t` >>
  simp[ao_opt_shift_def, ao_opt_signextend_def, ao_opt_exp_def,
       ao_opt_addsub_def, ao_opt_and_def, ao_opt_muldiv_def, ao_opt_or_def,
       ao_rewrite_layout_def] >>
  Cases_on `t'` >>
  simp[ao_opt_shift_def, ao_opt_signextend_def, ao_opt_exp_def,
       ao_opt_addsub_def, ao_opt_and_def, ao_opt_muldiv_def, ao_opt_or_def,
       ao_rewrite_layout_def] >>
  Cases_on `h` >> Cases_on `h'` >> simp[] >>
  rpt conj_tac >> rpt (IF_CASES_TAC >> simp[ao_rewrite_layout_def])
QED

Theorem ao_opt_eq_layout:
  fr "xor" = fr "not" ==>
  ao_rewrite_layout inst fr (ao_opt_eq dfg fr inst)
Proof
  strip_tac >>
  Cases_on `inst.inst_operands` >> simp[ao_opt_eq_def, ao_rewrite_layout_def] >>
  Cases_on `t` >> simp[ao_opt_eq_def, ao_rewrite_layout_def] >>
  Cases_on `t'` >> simp[ao_opt_eq_def, ao_rewrite_layout_def] >>
  rpt (IF_CASES_TAC >> simp[ao_rewrite_layout_def]) >>
  Cases_on `fr "not"` >> gvs[ao_rewrite_layout_def]
QED

Theorem ao_cmp_prefer_iz_layout:
  fr "xor" = fr "not" ==>
  ao_rewrite_layout inst fr (ao_cmp_prefer_iz_zero fr op1 inst) /\
  ao_rewrite_layout inst fr (ao_cmp_prefer_iz_max fr op1 inst) /\
  ao_rewrite_layout inst fr (ao_cmp_prefer_iz_general fr op1 op2 inst)
Proof
  strip_tac >> Cases_on `fr "not"` >> Cases_on `fr "iz"` >>
  gvs[ao_cmp_prefer_iz_zero_def, ao_cmp_prefer_iz_max_def,
      ao_cmp_prefer_iz_general_def, ao_rewrite_layout_def]
QED

Theorem ao_opt_comparator_layout:
  fr "xor" = fr "not" ==>
  ao_rewrite_layout inst fr (ao_opt_comparator dfg ra lbl idx fr inst)
Proof
  strip_tac >>
  Cases_on `inst.inst_operands` >> simp[ao_opt_comparator_def] >>
  Cases_on `t` >> simp[ao_opt_comparator_def] >>
  Cases_on `t'` >> simp[ao_opt_comparator_def] >>
  Cases_on `h = h'` >> simp[] >>
  Cases_on `ao_opt_cmp_range ra lbl idx inst
    (inst.inst_opcode = GT \/ inst.inst_opcode = SGT)
    (inst.inst_opcode = SGT \/ inst.inst_opcode = SLT)` >> simp[] >>
  pairarg_tac >> simp[] >>
  rpt (IF_CASES_TAC >> simp[ao_cmp_prefer_iz_layout]) >>
  Cases_on `fr "not"` >> Cases_on `fr "iz"` >>
  gvs[ao_rewrite_layout_def]
QED

Theorem ao_peephole_inst_layout:
  fr "xor" = fr "not" ==>
  ao_rewrite_layout inst fr (ao_peephole_inst dfg ra lbl idx fr inst)
Proof
  strip_tac >> simp[ao_peephole_inst_def] >>
  rpt (IF_CASES_TAC >>
    simp[ao_simple_peephole_layout, ao_opt_eq_layout, ao_opt_comparator_layout])
QED

Theorem ao_rewrite_layout_post_flip:
  ao_rewrite_layout inst fr outs ==>
  ao_rewrite_layout inst fr (MAP ao_post_flip_inst outs)
Proof
  `MAP (\i. (i.inst_id,i.inst_outputs)) (MAP ao_post_flip_inst outs) =
   MAP (\i. (i.inst_id,i.inst_outputs)) outs` by
    (simp[MAP_MAP_o, combinTheory.o_DEF, ao_post_flip_inst_shape]) >>
  pure_rewrite_tac[ao_rewrite_layout_def] >> asm_rewrite_tac[]
QED

Theorem ao_rewrite_layout_source:
  inst1.inst_id = inst.inst_id /\ inst1.inst_outputs = inst.inst_outputs ==>
  (ao_rewrite_layout inst1 fr outs <=> ao_rewrite_layout inst fr outs)
Proof
  strip_tac >> pure_rewrite_tac[ao_rewrite_layout_def] >> asm_rewrite_tac[]
QED

Theorem ao_transform_inst_layout:
  fr "xor" = fr "not" ==>
  ao_rewrite_layout inst fr
    (ao_transform_inst dfg ra lbl idx targets fr inst)
Proof
  strip_tac >>
  `!outs. ao_rewrite_layout (ao_resolve_iszero_inst targets inst) fr outs =
          ao_rewrite_layout inst fr outs` by
    (rpt strip_tac >> irule ao_rewrite_layout_source >>
     simp[ao_resolve_iszero_inst_fields]) >>
  simp[ao_transform_inst_def] >>
  qabbrev_tac `inst0 = ao_resolve_iszero_inst targets inst` >>
  `!outs. ao_rewrite_layout inst fr outs = ao_rewrite_layout inst0 fr outs`
    by metis_tac[] >>
  pop_assum (fn th => pure_once_rewrite_tac[th]) >>
  qpat_x_assum `!outs. _` kall_tac >>
  rpt (IF_CASES_TAC >> simp[]) >>
  Cases_on `ao_opt_producer dfg inst0`
  >- (simp[] >> irule ao_rewrite_layout_post_flip >>
      `ao_rewrite_layout (ao_pre_flip_inst inst0) fr
         (ao_peephole_inst dfg ra lbl idx fr (ao_pre_flip_inst inst0))` by
        simp[ao_peephole_inst_layout] >>
      metis_tac[ao_rewrite_layout_source, ao_pre_flip_inst_shape]) >>
  simp[] >> irule ao_rewrite_layout_post_flip >>
  drule ao_opt_producer_shape >> strip_tac >> gvs[]
QED
