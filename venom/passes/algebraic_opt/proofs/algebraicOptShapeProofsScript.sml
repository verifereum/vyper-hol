Theory algebraicOptShapeProofs
Ancestors
  algebraicOptDefs venomInst algebraicOptSupplyProofs irSupply
  venomWf venomState stackPlanTypes list pred_set

Theorem ao_handle_offset_inst_shape:
  (ao_handle_offset_inst inst).inst_id = inst.inst_id /\
  (ao_handle_offset_inst inst).inst_outputs = inst.inst_outputs /\
  inst_uses (ao_handle_offset_inst inst) = inst_uses inst /\
  is_terminator (ao_handle_offset_inst inst).inst_opcode =
    is_terminator inst.inst_opcode /\
  ((ao_handle_offset_inst inst).inst_opcode = PHI <=> inst.inst_opcode = PHI) /\
  get_successors (ao_handle_offset_inst inst) = get_successors inst
Proof
  Cases_on `inst.inst_opcode = ADD` >>
  simp[ao_handle_offset_inst_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `h` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `h` >> simp[] >>
  Cases_on `t'` >>
  gvs[inst_uses_def, operand_vars_def, operand_var_def, is_terminator_def,
      get_successors_def]
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

Theorem ao_rewrite_layout_distinct_ids:
  ao_rewrite_layout inst fr outs /\
  FST (fr "not") <> FST (fr "iz") /\
  FST (fr "not") <> inst.inst_id /\ FST (fr "iz") <> inst.inst_id ==>
  ALL_DISTINCT (MAP (\i. i.inst_id) outs)
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP FST (MAP (\i. (i.inst_id,i.inst_outputs)) outs))`
    suffices_by simp[MAP_MAP_o, combinTheory.o_DEF] >>
  gvs[ao_rewrite_layout_def]
QED

Theorem ao_rewrite_layout_distinct_outputs:
  ao_rewrite_layout inst fr outs /\ ALL_DISTINCT inst.inst_outputs /\
  SND (fr "not") <> SND (fr "iz") /\
  ~MEM (SND (fr "not")) inst.inst_outputs /\
  ~MEM (SND (fr "iz")) inst.inst_outputs ==>
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) outs))
Proof
  strip_tac >>
  `ALL_DISTINCT (FLAT (MAP SND (MAP (\i. (i.inst_id,i.inst_outputs)) outs)))`
    suffices_by simp[MAP_MAP_o, combinTheory.o_DEF] >>
  gvs[ao_rewrite_layout_def]
QED

Theorem ao_rewrite_layout_ids:
  ao_rewrite_layout inst fr outs ==>
  set (MAP (\i. i.inst_id) outs) SUBSET
    {inst.inst_id; FST (fr "not"); FST (fr "iz")}
Proof
  strip_tac >>
  `set (MAP FST (MAP (\i. (i.inst_id,i.inst_outputs)) outs)) SUBSET
    {inst.inst_id; FST (fr "not"); FST (fr "iz")}`
    suffices_by simp[MAP_MAP_o, combinTheory.o_DEF] >>
  gvs[ao_rewrite_layout_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem ao_rewrite_layout_outputs:
  ao_rewrite_layout inst fr outs ==>
  set (FLAT (MAP (\i. i.inst_outputs) outs)) SUBSET
    (set inst.inst_outputs UNION {SND (fr "not"); SND (fr "iz")})
Proof
  strip_tac >>
  `set (FLAT (MAP SND (MAP (\i. (i.inst_id,i.inst_outputs)) outs))) SUBSET
    (set inst.inst_outputs UNION {SND (fr "not"); SND (fr "iz")})`
    suffices_by simp[MAP_MAP_o, combinTheory.o_DEF] >>
  gvs[ao_rewrite_layout_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem ao_transform_inst_supply_distinct:
  ir_supply_inst_ok s /\ ao_alloc_fresh s = (fr,s1) /\
  MEM inst.inst_id s.irs_used_inst_ids /\
  set inst.inst_outputs SUBSET set s.irs_used_vars /\
  ALL_DISTINCT inst.inst_outputs ==>
  ALL_DISTINCT (MAP (\i. i.inst_id)
    (ao_transform_inst dfg ra lbl idx targets fr inst)) /\
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs)
    (ao_transform_inst dfg ra lbl idx targets fr inst)))
Proof
  strip_tac >>
  drule ao_alloc_fresh_tags >>
  disch_then (qspec_then `"not"` mp_tac) >> simp[] >> strip_tac >>
  drule ao_alloc_fresh_tags >>
  disch_then (qspec_then `"xor"` mp_tac) >> simp[] >> strip_tac >>
  drule_all ao_alloc_fresh_contract >> strip_tac >>
  `ao_rewrite_layout inst fr
    (ao_transform_inst dfg ra lbl idx targets fr inst)` by
      simp[ao_transform_inst_layout] >>
  `~MEM (SND (fr "not")) inst.inst_outputs /\
   ~MEM (SND (fr "iz")) inst.inst_outputs` by
    (gvs[SUBSET_DEF] >> metis_tac[]) >>
  conj_tac
  >- (irule ao_rewrite_layout_distinct_ids >>
      qexistsl [`fr`,`inst`] >> gvs[] >> metis_tac[]) >>
  irule ao_rewrite_layout_distinct_outputs >>
  qexistsl [`fr`,`inst`] >> gvs[]
QED

Theorem ao_resolve_iszero_op_support:
  set (venomInst$operand_vars [op]) SUBSET V /\
  (!v chain p. ALOOKUP targets v = SOME chain /\ MEM p chain ==>
     set (venomInst$operand_vars [p]) SUBSET V) ==>
  set (venomInst$operand_vars [ao_resolve_iszero_op targets opc op]) SUBSET V
Proof
  strip_tac >> Cases_on `op` >>
  simp[ao_resolve_iszero_op_def] >>
  Cases_on `ALOOKUP targets s` >> simp[] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  first_x_assum irule >> metis_tac[MEM_EL]
QED

Theorem ao_operand_support:
  set (venomInst$operand_vars ops) SUBSET V <=>
  !op. MEM op ops ==> set (venomInst$operand_vars [op]) SUBSET V
Proof
  Induct_on `ops`
  >- simp[venomInstTheory.operand_vars_def, SUBSET_DEF] >>
  gen_tac >>
  simp[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `venomInst$operand_var h` >>
  simp[venomInstTheory.operand_vars_def, SUBSET_DEF] >>
  qpat_x_assum `_ <=> _` mp_tac >>
  simp[venomInstTheory.operand_vars_def, SUBSET_DEF,
       DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem ao_resolve_iszero_inst_support:
  set (inst_uses inst) SUBSET V /\
  (!v chain op. ALOOKUP targets v = SOME chain /\ MEM op chain ==>
     set (venomInst$operand_vars [op]) SUBSET V) ==>
  set (inst_uses (ao_resolve_iszero_inst targets inst)) SUBSET V
Proof
  simp[inst_uses_def, ao_resolve_iszero_inst_def] >>
  pure_once_rewrite_tac[ao_operand_support] >>
  simp[MEM_MAP] >> rpt strip_tac >> gvs[] >>
  irule ao_resolve_iszero_op_support >> metis_tac[]
QED

Theorem ao_simple_peephole_support:
  (MEM out (ao_opt_shift inst) \/
   MEM out (ao_opt_signextend ra lbl idx inst) \/
   MEM out (ao_opt_exp inst) \/
   MEM out (ao_opt_addsub inst) \/
   MEM out (ao_opt_and inst) \/
   MEM out (ao_opt_muldiv inst) \/
   MEM out (ao_opt_or dfg inst)) ==>
  set (inst_uses out) SUBSET set (inst_uses inst)
Proof
  pure_rewrite_tac[DISJ_IMP_THM] >> rpt conj_tac >>
  Cases_on `inst.inst_operands` >>
  simp[ao_opt_shift_def, ao_opt_signextend_def, ao_opt_exp_def,
       ao_opt_addsub_def, ao_opt_and_def, ao_opt_muldiv_def, ao_opt_or_def] >>
  Cases_on `t` >>
  simp[ao_opt_shift_def, ao_opt_signextend_def, ao_opt_exp_def,
       ao_opt_addsub_def, ao_opt_and_def, ao_opt_muldiv_def, ao_opt_or_def] >>
  Cases_on `t'` >>
  simp[ao_opt_shift_def, ao_opt_signextend_def, ao_opt_exp_def,
       ao_opt_addsub_def, ao_opt_and_def, ao_opt_muldiv_def, ao_opt_or_def] >>
  Cases_on `h` >> Cases_on `h'` >> simp[] >>
  rpt (IF_CASES_TAC >> simp[]) >> strip_tac >>
  gvs[inst_uses_def, venomInstTheory.operand_vars_def,
      venomInstTheory.operand_var_def, SUBSET_DEF]
QED

Theorem ao_opt_eq_support:
  fr "xor" = fr "not" /\ MEM out (ao_opt_eq dfg fr inst) ==>
  set (inst_uses out) SUBSET
    (set (inst_uses inst) UNION {SND (fr "not"); SND (fr "iz")})
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac mp_tac) >>
  Cases_on `inst.inst_operands` >> simp[ao_opt_eq_def] >>
  Cases_on `t` >> simp[ao_opt_eq_def] >>
  Cases_on `t'` >> simp[ao_opt_eq_def] >>
  Cases_on `fr "not"` >> gvs[] >>
  Cases_on `h` >> Cases_on `h'` >>
  rpt (IF_CASES_TAC >> simp[]) >> strip_tac >> gvs[] >>
  gvs[inst_uses_def, venomInstTheory.operand_vars_def,
      venomInstTheory.operand_var_def, SUBSET_DEF]
QED

Theorem ao_opt_cmp_range_support:
  ao_opt_cmp_range ra lbl idx inst is_gt signed = SOME op ==>
  venomInst$operand_vars [op] = []
Proof
  simp[ao_opt_cmp_range_def] >> rpt strip_tac >>
  gvs[AllCaseEqs(), venomInstTheory.operand_vars_def,
      venomInstTheory.operand_var_def]
QED

Theorem ao_cmp_prefer_iz_support:
  !fr op1 op2 inst. fr "xor" = fr "not" ==>
  !out.
  (MEM out (ao_cmp_prefer_iz_zero fr op1 inst) \/
   MEM out (ao_cmp_prefer_iz_max fr op1 inst) \/
   MEM out (ao_cmp_prefer_iz_general fr op1 op2 inst)) ==>
  set (inst_uses out) SUBSET
    (set (venomInst$operand_vars [op1;op2]) UNION
     {SND (fr "not"); SND (fr "iz")})
Proof
  rpt gen_tac >> strip_tac >> Cases_on `fr "not"` >> Cases_on `fr "iz"` >>
  simp[ao_cmp_prefer_iz_zero_def, ao_cmp_prefer_iz_max_def,
       ao_cmp_prefer_iz_general_def] >> rpt strip_tac >> gvs[] >>
  Cases_on `op1` >> Cases_on `op2` >>
  gvs[inst_uses_def, venomInstTheory.operand_vars_def,
      venomInstTheory.operand_var_def, SUBSET_DEF]
QED

Theorem ao_opt_comparator_support:
  fr "xor" = fr "not" ==>
  !out. MEM out (ao_opt_comparator dfg ra lbl idx fr inst) ==>
  set (inst_uses out) SUBSET
    (set (inst_uses inst) UNION {SND (fr "not"); SND (fr "iz")})
Proof
  strip_tac >>
  Cases_on `inst.inst_operands` >> simp[ao_opt_comparator_def] >>
  Cases_on `t` >> simp[ao_opt_comparator_def] >>
  Cases_on `t'` >> simp[ao_opt_comparator_def] >>
  Cases_on `h = h'`
  >- (simp[inst_uses_def, venomInstTheory.operand_vars_def,
           venomInstTheory.operand_var_def, SUBSET_DEF]) >>
  simp[] >>
  Cases_on `ao_opt_cmp_range ra lbl idx inst
    (inst.inst_opcode = GT \/ inst.inst_opcode = SGT)
    (inst.inst_opcode = SGT \/ inst.inst_opcode = SLT)`
  >- (qspecl_then [`fr`,`h`,`h'`,`inst`] mp_tac ao_cmp_prefer_iz_support >>
      simp[] >> strip_tac >>
      simp[] >> pairarg_tac >> simp[] >>
      rpt (IF_CASES_TAC >> simp[]) >>
      Cases_on `fr "not"` >> Cases_on `fr "iz"` >> simp[] >>
      Cases_on `h` >> Cases_on `h'` >>
      rpt strip_tac >> gvs[] >>
      gvs[inst_uses_def, venomInstTheory.operand_vars_def,
          venomInstTheory.operand_var_def, SUBSET_DEF] >> metis_tac[]) >>
  drule ao_opt_cmp_range_support >> strip_tac >>
  simp[inst_uses_def, SUBSET_DEF]
QED

Theorem ao_peephole_inst_support:
  fr "xor" = fr "not" ==>
  !out. MEM out (ao_peephole_inst dfg ra lbl idx fr inst) ==>
  set (inst_uses out) SUBSET
    (set (inst_uses inst) UNION {SND (fr "not"); SND (fr "iz")})
Proof
  strip_tac >> simp[ao_peephole_inst_def] >>
  rpt (IF_CASES_TAC >> simp[]) >> rpt strip_tac
  >~ [`MEM out (ao_opt_eq dfg fr inst)`]
  >- (irule ao_opt_eq_support >> simp[] >> qexists_tac `dfg` >> simp[]) 
  >~ [`MEM out (ao_opt_comparator dfg ra lbl idx fr inst)`]
  >- (irule ao_opt_comparator_support >> simp[] >>
      qexistsl_tac [`dfg`,`idx`,`lbl`,`ra`] >> simp[]) >>
  irule SUBSET_TRANS >> qexists_tac `set (inst_uses inst)` >>
  simp[] >> irule ao_simple_peephole_support >>
  qexistsl_tac [`dfg`,`idx`,`lbl`,`ra`] >> simp[]
QED

Theorem ao_transform_inst_support:
  fr "xor" = fr "not" /\ set (inst_uses inst) SUBSET V /\
  (!v chain op. ALOOKUP targets v = SOME chain /\ MEM op chain ==>
     set (venomInst$operand_vars [op]) SUBSET V) ==>
  !out. MEM out (ao_transform_inst dfg ra lbl idx targets fr inst) ==>
  set (inst_uses out) SUBSET (V UNION {SND (fr "not"); SND (fr "iz")})
Proof
  strip_tac >>
  `set (inst_uses (ao_resolve_iszero_inst targets inst)) SUBSET V`
    by (irule ao_resolve_iszero_inst_support >> metis_tac[]) >>
  simp[ao_transform_inst_def] >>
  qabbrev_tac `inst0 = ao_resolve_iszero_inst targets inst` >>
  `set (inst_uses inst0) SUBSET (V UNION {SND (fr "not"); SND (fr "iz")})`
    by (simp[SUBSET_DEF] >> metis_tac[SUBSET_DEF]) >>
  rpt (IF_CASES_TAC >> simp[]) >>
  Cases_on `ao_opt_producer dfg inst0`
  >- (simp[MEM_MAP] >> rpt strip_tac >> gvs[] >>
      simp[ao_post_flip_inst_shape] >>
      irule SUBSET_TRANS >>
      qexists_tac `set (inst_uses (ao_pre_flip_inst inst0)) UNION
                     {SND (fr "not"); SND (fr "iz")}` >>
      conj_tac
      >- (irule ao_peephole_inst_support >> simp[] >>
          qexistsl_tac [`dfg`,`idx`,`lbl`,`ra`] >> simp[]) >>
      gvs[ao_pre_flip_inst_shape, SUBSET_DEF] >> metis_tac[]) >>
  drule ao_opt_producer_shape >> strip_tac >> gvs[] >>
  simp[ao_post_flip_inst_shape] >> metis_tac[SUBSET_TRANS, SUBSET_UNION]
QED

Theorem ao_resolve_iszero_op_label:
  (!v chain op. ALOOKUP targets v = SOME chain /\ MEM op chain ==>
     ~is_label_operand op) ==>
  get_label (ao_resolve_iszero_op targets opc op) = get_label op
Proof
  strip_tac >> Cases_on `op` >> simp[ao_resolve_iszero_op_def] >>
  Cases_on `ALOOKUP targets s` >> simp[] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  qmatch_goalsub_abbrev_tac `EL k x` >>
  `k < LENGTH x` by gvs[Abbr `k`] >>
  `~is_label_operand (EL k x)` by
    (first_x_assum irule >> metis_tac[MEM_EL]) >>
  Cases_on `EL k x` >>
  gvs[stackPlanTypesTheory.is_label_operand_def, get_label_def]
QED

Theorem ao_resolve_iszero_inst_labels:
  (!v chain op. ALOOKUP targets v = SOME chain /\ MEM op chain ==>
     ~is_label_operand op) ==>
  MAP get_label (ao_resolve_iszero_inst targets inst).inst_operands =
  MAP get_label inst.inst_operands
Proof
  strip_tac >> simp[ao_resolve_iszero_inst_def, MAP_MAP_o,
                    combinTheory.o_DEF] >>
  irule MAP_CONG >> simp[] >> rpt strip_tac >>
  irule ao_resolve_iszero_op_label >> metis_tac[]
QED

Theorem ao_resolve_iszero_inst_successors:
  (!v chain op. ALOOKUP targets v = SOME chain /\ MEM op chain ==>
     ~is_label_operand op) ==>
  get_successors (ao_resolve_iszero_inst targets inst) = get_successors inst
Proof
  strip_tac >> drule ao_resolve_iszero_inst_labels >>
  simp[get_successors_def, ao_resolve_iszero_inst_fields]
QED

Theorem ao_simple_peephole_unary:
  LENGTH inst.inst_outputs = 1 /\
  inst.inst_opcode <> ISZERO /\ inst.inst_opcode <> ASSERT ==>
  !out.
    (MEM out (ao_opt_shift inst) \/
     MEM out (ao_opt_signextend ra lbl idx inst) \/
     MEM out (ao_opt_exp inst) \/
     MEM out (ao_opt_addsub inst) \/
     MEM out (ao_opt_and inst) \/
     MEM out (ao_opt_muldiv inst) \/
     MEM out (ao_opt_or dfg inst)) ==>
    (out.inst_opcode = ISZERO ==>
      LENGTH out.inst_operands = 1 /\ LENGTH out.inst_outputs = 1) /\
    out.inst_opcode <> ASSERT
Proof
  strip_tac >> gen_tac >>
  pure_rewrite_tac[DISJ_IMP_THM] >> rpt conj_tac >>
  Cases_on `inst.inst_operands` >>
  simp[ao_opt_shift_def, ao_opt_signextend_def, ao_opt_exp_def,
       ao_opt_addsub_def, ao_opt_and_def, ao_opt_muldiv_def, ao_opt_or_def] >>
  Cases_on `t` >>
  simp[ao_opt_shift_def, ao_opt_signextend_def, ao_opt_exp_def,
       ao_opt_addsub_def, ao_opt_and_def, ao_opt_muldiv_def, ao_opt_or_def] >>
  Cases_on `t'` >>
  simp[ao_opt_shift_def, ao_opt_signextend_def, ao_opt_exp_def,
       ao_opt_addsub_def, ao_opt_and_def, ao_opt_muldiv_def, ao_opt_or_def] >>
  Cases_on `h` >> Cases_on `h'` >> simp[] >>
  rpt (IF_CASES_TAC >> simp[]) >> rpt strip_tac >> gvs[]
QED

Theorem ao_opt_eq_unary:
  LENGTH inst.inst_outputs = 1 /\
  inst.inst_opcode <> ISZERO /\ inst.inst_opcode <> ASSERT ==>
  !out. MEM out (ao_opt_eq dfg fr inst) ==>
    (out.inst_opcode = ISZERO ==>
      LENGTH out.inst_operands = 1 /\ LENGTH out.inst_outputs = 1) /\
    out.inst_opcode <> ASSERT
Proof
  strip_tac >> gen_tac >>
  Cases_on `inst.inst_operands` >> simp[ao_opt_eq_def] >>
  Cases_on `t` >> simp[ao_opt_eq_def] >>
  Cases_on `t'` >> simp[ao_opt_eq_def] >>
  Cases_on `fr "not"` >> Cases_on `fr "xor"` >>
  rpt (IF_CASES_TAC >> simp[]) >> rpt strip_tac >> gvs[]
QED

Theorem ao_cmp_prefer_iz_unary:
  LENGTH inst.inst_outputs = 1 ==>
  !out.
    (MEM out (ao_cmp_prefer_iz_zero fr op1 inst) \/
     MEM out (ao_cmp_prefer_iz_max fr op1 inst) \/
     MEM out (ao_cmp_prefer_iz_general fr op1 op2 inst)) ==>
    (out.inst_opcode = ISZERO ==>
      LENGTH out.inst_operands = 1 /\ LENGTH out.inst_outputs = 1) /\
    out.inst_opcode <> ASSERT
Proof
  strip_tac >> Cases_on `fr "not"` >> Cases_on `fr "xor"` >>
  Cases_on `fr "iz"` >>
  simp[ao_cmp_prefer_iz_zero_def, ao_cmp_prefer_iz_max_def,
       ao_cmp_prefer_iz_general_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem ao_opt_comparator_unary:
  LENGTH inst.inst_outputs = 1 /\
  inst.inst_opcode <> ISZERO /\ inst.inst_opcode <> ASSERT ==>
  !out. MEM out (ao_opt_comparator dfg ra lbl idx fr inst) ==>
    (out.inst_opcode = ISZERO ==>
      LENGTH out.inst_operands = 1 /\ LENGTH out.inst_outputs = 1) /\
    out.inst_opcode <> ASSERT
Proof
  strip_tac >> gen_tac >>
  `!op1 op2 out.
    (MEM out (ao_cmp_prefer_iz_zero fr op1 inst) \/
     MEM out (ao_cmp_prefer_iz_max fr op1 inst) \/
     MEM out (ao_cmp_prefer_iz_general fr op1 op2 inst)) ==>
    (out.inst_opcode = ISZERO ==>
      LENGTH out.inst_operands = 1 /\ LENGTH out.inst_outputs = 1) /\
    out.inst_opcode <> ASSERT` by metis_tac[ao_cmp_prefer_iz_unary] >>
  Cases_on `inst.inst_operands` >> simp[ao_opt_comparator_def] >>
  Cases_on `t` >> simp[ao_opt_comparator_def] >>
  Cases_on `t'` >> simp[ao_opt_comparator_def] >>
  Cases_on `h = h'` >> simp[] >>
  Cases_on `ao_opt_cmp_range ra lbl idx inst
    (inst.inst_opcode = GT \/ inst.inst_opcode = SGT)
    (inst.inst_opcode = SGT \/ inst.inst_opcode = SLT)` >> simp[] >>
  pairarg_tac >> simp[] >>
  Cases_on `fr "not"` >> Cases_on `fr "iz"` >>
  rpt (IF_CASES_TAC >> simp[]) >> rpt strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem ao_peephole_inst_unary:
  !source inst. inst_wf source /\ inst.inst_opcode = source.inst_opcode /\
  LENGTH inst.inst_outputs = LENGTH source.inst_outputs /\
  LENGTH inst.inst_operands = LENGTH source.inst_operands ==>
  !out. MEM out (ao_peephole_inst dfg ra lbl idx fr inst) ==>
    (out.inst_opcode = ISZERO ==>
      LENGTH out.inst_operands = 1 /\ LENGTH out.inst_outputs = 1) /\
    (out.inst_opcode = ASSERT ==> LENGTH out.inst_operands = 1)
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  Cases_on `source.inst_opcode` >>
  gvs[inst_wf_def] >> simp[ao_peephole_inst_def] >>
  rpt (IF_CASES_TAC >> simp[]) >> rpt strip_tac >> gvs[] >>
  `inst.inst_opcode <> ISZERO /\ inst.inst_opcode <> ASSERT` by simp[] >>
  metis_tac[ao_simple_peephole_unary, ao_opt_eq_unary,
            ao_opt_comparator_unary]
QED

Theorem ao_inst_wf_unary:
  inst_wf inst ==>
    (inst.inst_opcode = ISZERO ==>
      LENGTH inst.inst_operands = 1 /\ LENGTH inst.inst_outputs = 1) /\
    (inst.inst_opcode = ASSERT ==> LENGTH inst.inst_operands = 1)
Proof
  Cases_on `inst.inst_opcode` >> simp[inst_wf_def]
QED

Theorem ao_transform_inst_unary:
  inst_wf inst ==>
  !out. MEM out (ao_transform_inst dfg ra lbl idx targets fr inst) ==>
    (out.inst_opcode = ISZERO ==>
      LENGTH out.inst_operands = 1 /\ LENGTH out.inst_outputs = 1) /\
    (out.inst_opcode = ASSERT ==> LENGTH out.inst_operands = 1)
Proof
  strip_tac >> gen_tac >>
  drule ao_inst_wf_unary >> strip_tac >>
  simp[ao_transform_inst_def] >>
  qabbrev_tac `inst0 = ao_resolve_iszero_inst targets inst` >>
  `inst0.inst_opcode = inst.inst_opcode /\
   inst0.inst_outputs = inst.inst_outputs /\
   LENGTH inst0.inst_operands = LENGTH inst.inst_operands` by
    simp[Abbr `inst0`, ao_resolve_iszero_inst_fields] >>
  Cases_on `inst0.inst_outputs = []`
  >- (simp[] >> rpt strip_tac >> gvs[]) >>
  Cases_on `inst0.inst_opcode = ASSIGN \/ inst0.inst_opcode = PHI \/
            inst0.inst_opcode = PARAM`
  >- (simp[] >> rpt strip_tac >> gvs[]) >>
  simp[] >> Cases_on `ao_opt_producer dfg inst0`
  >- (simp[MEM_MAP] >> rpt strip_tac >> gvs[] >>
      `!out. MEM out (ao_peephole_inst dfg ra lbl idx fr
                       (ao_pre_flip_inst inst0)) ==>
        (out.inst_opcode = ISZERO ==>
          LENGTH out.inst_operands = 1 /\ LENGTH out.inst_outputs = 1) /\
        (out.inst_opcode = ASSERT ==> LENGTH out.inst_operands = 1)` by
        (match_mp_tac ao_peephole_inst_unary >> qexists_tac `inst` >>
         simp[ao_pre_flip_inst_shape]) >>
      gvs[ao_post_flip_inst_shape] >> metis_tac[]) >>
  simp[MEM_MAP] >> rpt strip_tac >> gvs[] >>
  drule ao_opt_producer_shape >> strip_tac >> gvs[] >>
  gvs[ao_post_flip_inst_shape] >> metis_tac[]
QED

Theorem ao_simple_peephole_control:
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> PHI ==>
  !outs.
    (outs = ao_opt_shift inst \/
     outs = ao_opt_signextend ra lbl idx inst \/
     outs = ao_opt_exp inst \/ outs = ao_opt_addsub inst \/
     outs = ao_opt_and inst \/ outs = ao_opt_muldiv inst \/
     outs = ao_opt_or dfg inst) ==>
    outs <> [] /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> PHI) outs
Proof
  strip_tac >> gen_tac >>
  pure_rewrite_tac[DISJ_IMP_THM] >> rpt conj_tac >>
  Cases_on `inst.inst_operands` >>
  simp[ao_opt_shift_def, ao_opt_signextend_def, ao_opt_exp_def,
       ao_opt_addsub_def, ao_opt_and_def, ao_opt_muldiv_def, ao_opt_or_def] >>
  Cases_on `t` >>
  simp[ao_opt_shift_def, ao_opt_signextend_def, ao_opt_exp_def,
       ao_opt_addsub_def, ao_opt_and_def, ao_opt_muldiv_def, ao_opt_or_def] >>
  Cases_on `t'` >>
  simp[ao_opt_shift_def, ao_opt_signextend_def, ao_opt_exp_def,
       ao_opt_addsub_def, ao_opt_and_def, ao_opt_muldiv_def, ao_opt_or_def] >>
  Cases_on `h` >> Cases_on `h'` >> simp[] >>
  rpt (IF_CASES_TAC >> simp[]) >> rpt strip_tac >> gvs[is_terminator_def]
QED

Theorem ao_opt_eq_control:
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> PHI ==>
  ao_opt_eq dfg fr inst <> [] /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> PHI)
    (ao_opt_eq dfg fr inst)
Proof
  strip_tac >>
  Cases_on `inst.inst_operands` >> simp[ao_opt_eq_def] >>
  Cases_on `t` >> simp[ao_opt_eq_def] >>
  Cases_on `t'` >> simp[ao_opt_eq_def] >>
  Cases_on `fr "not"` >> Cases_on `fr "xor"` >>
  rpt (IF_CASES_TAC >> simp[is_terminator_def])
QED

Theorem ao_opt_comparator_control:
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> PHI ==>
  ao_opt_comparator dfg ra lbl idx fr inst <> [] /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> PHI)
    (ao_opt_comparator dfg ra lbl idx fr inst)
Proof
  strip_tac >>
  Cases_on `inst.inst_operands` >> simp[ao_opt_comparator_def] >>
  Cases_on `t` >> simp[ao_opt_comparator_def] >>
  Cases_on `t'` >> simp[ao_opt_comparator_def] >>
  Cases_on `h = h'` >> simp[is_terminator_def] >>
  Cases_on `ao_opt_cmp_range ra lbl idx inst
    (inst.inst_opcode = GT \/ inst.inst_opcode = SGT)
    (inst.inst_opcode = SGT \/ inst.inst_opcode = SLT)` >>
  simp[is_terminator_def] >> pairarg_tac >> simp[] >>
  Cases_on `fr "not"` >> Cases_on `fr "xor"` >> Cases_on `fr "iz"` >>
  rpt (IF_CASES_TAC >> simp[ao_cmp_prefer_iz_zero_def,
       ao_cmp_prefer_iz_max_def, ao_cmp_prefer_iz_general_def,
       is_terminator_def])
QED

Theorem ao_peephole_inst_control:
  ao_peephole_inst dfg ra lbl idx fr inst <> [] /\
  ((is_terminator inst.inst_opcode \/ inst.inst_opcode = PHI) ==>
    ao_peephole_inst dfg ra lbl idx fr inst = [inst]) /\
  ((~is_terminator inst.inst_opcode /\ inst.inst_opcode <> PHI) ==>
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> PHI)
      (ao_peephole_inst dfg ra lbl idx fr inst))
Proof
  Cases_on `inst.inst_outputs = []`
  >- simp[ao_peephole_inst_def] >>
  Cases_on `inst.inst_opcode` >> simp[ao_peephole_inst_def, is_terminator_def] >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> PHI` by
    simp[is_terminator_def] >>
  metis_tac[ao_simple_peephole_control, ao_opt_eq_control,
            ao_opt_comparator_control]
QED

Theorem ao_transform_inst_control_owner:
  is_terminator inst.inst_opcode \/ inst.inst_opcode = PHI ==>
  ao_transform_inst dfg ra lbl idx targets fr inst =
    [ao_resolve_iszero_inst targets inst]
Proof
  Cases_on `inst.inst_opcode` >> simp[is_terminator_def] >>
  simp[ao_transform_inst_def, ao_resolve_iszero_inst_fields,
       ao_opt_producer_def, ao_pre_flip_inst_shape,
       ao_peephole_inst_def, ao_post_flip_inst_shape, is_terminator_def]
QED

Theorem ao_transform_inst_noncontrol:
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> PHI ==>
  ao_transform_inst dfg ra lbl idx targets fr inst <> [] /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> PHI)
    (ao_transform_inst dfg ra lbl idx targets fr inst)
Proof
  strip_tac >> simp[ao_transform_inst_def] >>
  qabbrev_tac `inst0 = ao_resolve_iszero_inst targets inst` >>
  `~is_terminator inst0.inst_opcode /\ inst0.inst_opcode <> PHI` by
    simp[Abbr `inst0`, ao_resolve_iszero_inst_fields] >>
  Cases_on `inst0.inst_outputs = []` >- simp[] >>
  Cases_on `inst0.inst_opcode = ASSIGN \/ inst0.inst_opcode = PHI \/
            inst0.inst_opcode = PARAM` >- simp[] >>
  simp[] >> Cases_on `ao_opt_producer dfg inst0`
  >- (simp[] >>
      `ao_peephole_inst dfg ra lbl idx fr (ao_pre_flip_inst inst0) <> [] /\
       EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> PHI)
         (ao_peephole_inst dfg ra lbl idx fr (ao_pre_flip_inst inst0))` by
        metis_tac[ao_peephole_inst_control, ao_pre_flip_inst_shape] >>
      simp[EVERY_MAP, combinTheory.o_DEF, ao_post_flip_inst_shape]) >>
  simp[] >> drule ao_opt_producer_shape >> strip_tac >>
  gvs[ao_post_flip_inst_shape]
QED

Theorem ao_transform_inst_nonempty:
  ao_transform_inst dfg ra lbl idx targets fr inst <> []
Proof
  Cases_on `is_terminator inst.inst_opcode \/ inst.inst_opcode = PHI`
  >- (gvs[] >> simp[ao_transform_inst_control_owner]) >>
  metis_tac[ao_transform_inst_noncontrol]
QED

Theorem ao_transform_inst_control:
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> PHI)
    (FRONT (ao_transform_inst dfg ra lbl idx targets fr inst)) /\
  is_terminator (LAST (ao_transform_inst dfg ra lbl idx targets fr inst)).inst_opcode =
    is_terminator inst.inst_opcode /\
  ((LAST (ao_transform_inst dfg ra lbl idx targets fr inst)).inst_opcode = PHI <=>
    inst.inst_opcode = PHI)
Proof
  Cases_on `is_terminator inst.inst_opcode \/ inst.inst_opcode = PHI`
  >- (gvs[] >> simp[ao_transform_inst_control_owner, ao_resolve_iszero_inst_fields]) >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> PHI` by gvs[] >>
  `ao_transform_inst dfg ra lbl idx targets fr inst <> [] /\
   EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> PHI)
     (ao_transform_inst dfg ra lbl idx targets fr inst)` by
    metis_tac[ao_transform_inst_noncontrol] >>
  gvs[EVERY_MEM] >> conj_tac
  >- metis_tac[rich_listTheory.MEM_FRONT_NOT_NIL] >>
  metis_tac[rich_listTheory.MEM_LAST_NOT_NIL]
QED

Theorem ao_transform_inst_successors:
  (!v chain op. ALOOKUP targets v = SOME chain /\ MEM op chain ==>
     ~is_label_operand op) ==>
  get_successors (LAST (ao_transform_inst dfg ra lbl idx targets fr inst)) =
    get_successors inst
Proof
  strip_tac >>
  Cases_on `is_terminator inst.inst_opcode \/ inst.inst_opcode = PHI`
  >- (gvs[] >> simp[ao_transform_inst_control_owner] >>
      metis_tac[ao_resolve_iszero_inst_successors]) >>
  `is_terminator
     (LAST (ao_transform_inst dfg ra lbl idx targets fr inst)).inst_opcode =
   is_terminator inst.inst_opcode` by metis_tac[ao_transform_inst_control] >>
  gvs[get_successors_def]
QED

Theorem ao_handle_offset_inst_labels:
  inst_ir_labels (ao_handle_offset_inst inst) = inst_ir_labels inst
Proof
  Cases_on `inst.inst_opcode = ADD` >> simp[ao_handle_offset_inst_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `h` >> simp[] >> Cases_on `t` >> simp[] >>
  Cases_on `h` >> simp[] >> Cases_on `t'` >>
  simp[inst_ir_labels_def, operand_ir_labels_def]
QED

Theorem ao_flip_inst_labels:
  set (inst_ir_labels (ao_pre_flip_inst inst)) = set (inst_ir_labels inst) /\
  set (inst_ir_labels (ao_post_flip_inst inst)) = set (inst_ir_labels inst)
Proof
  Cases_on `inst.inst_operands` >>
  simp[ao_pre_flip_inst_def, ao_post_flip_inst_def] >>
  Cases_on `t` >> simp[ao_pre_flip_inst_def, ao_post_flip_inst_def] >>
  Cases_on `t'` >> simp[ao_pre_flip_inst_def, ao_post_flip_inst_def] >>
  rpt (IF_CASES_TAC >> gvs[]) >> Cases_on `h` >> Cases_on `h'` >>
  simp[inst_ir_labels_def, operand_ir_labels_def, EXTENSION, DISJ_COMM]
QED

Theorem ao_opt_producer_labels:
  ao_opt_producer dfg inst = SOME outs ==>
  !out. MEM out outs ==> set (inst_ir_labels out) SUBSET set (inst_ir_labels inst)
Proof
  simp[ao_opt_producer_def] >> rpt strip_tac >> gvs[AllCaseEqs()] >>
  simp[inst_ir_labels_def, operand_ir_labels_def]
QED

Theorem ao_simple_peephole_labels:
  (MEM out (ao_opt_shift inst) \/
   MEM out (ao_opt_signextend ra lbl idx inst) \/
   MEM out (ao_opt_exp inst) \/ MEM out (ao_opt_addsub inst) \/
   MEM out (ao_opt_and inst) \/ MEM out (ao_opt_muldiv inst) \/
   MEM out (ao_opt_or dfg inst)) ==>
  set (inst_ir_labels out) SUBSET set (inst_ir_labels inst)
Proof
  pure_rewrite_tac[DISJ_IMP_THM] >> rpt conj_tac >>
  Cases_on `inst.inst_operands` >>
  simp[ao_opt_shift_def, ao_opt_signextend_def, ao_opt_exp_def,
       ao_opt_addsub_def, ao_opt_and_def, ao_opt_muldiv_def, ao_opt_or_def] >>
  Cases_on `t` >>
  simp[ao_opt_shift_def, ao_opt_signextend_def, ao_opt_exp_def,
       ao_opt_addsub_def, ao_opt_and_def, ao_opt_muldiv_def, ao_opt_or_def] >>
  Cases_on `t'` >>
  simp[ao_opt_shift_def, ao_opt_signextend_def, ao_opt_exp_def,
       ao_opt_addsub_def, ao_opt_and_def, ao_opt_muldiv_def, ao_opt_or_def] >>
  Cases_on `h` >> Cases_on `h'` >> simp[] >>
  rpt (IF_CASES_TAC >> simp[]) >> strip_tac >>
  gvs[inst_ir_labels_def, operand_ir_labels_def, SUBSET_DEF]
QED

Theorem ao_opt_eq_labels:
  MEM out (ao_opt_eq dfg fr inst) ==>
  set (inst_ir_labels out) SUBSET set (inst_ir_labels inst)
Proof
  Cases_on `inst.inst_operands` >> simp[ao_opt_eq_def] >>
  Cases_on `t` >> simp[ao_opt_eq_def] >>
  Cases_on `t'` >> simp[ao_opt_eq_def] >>
  Cases_on `fr "not"` >> Cases_on `fr "xor"` >>
  Cases_on `h` >> Cases_on `h'` >>
  rpt (IF_CASES_TAC >> simp[]) >> strip_tac >>
  gvs[inst_ir_labels_def, operand_ir_labels_def, SUBSET_DEF]
QED

Theorem ao_opt_cmp_range_labels:
  ao_opt_cmp_range ra lbl idx inst is_gt signed = SOME op ==>
  operand_ir_labels [op] = []
Proof
  simp[ao_opt_cmp_range_def] >> rpt strip_tac >>
  gvs[AllCaseEqs(), operand_ir_labels_def]
QED

Theorem ao_cmp_prefer_iz_labels:
  !fr op1 op2 inst out.
  (MEM out (ao_cmp_prefer_iz_zero fr op1 inst) \/
   MEM out (ao_cmp_prefer_iz_max fr op1 inst) \/
   MEM out (ao_cmp_prefer_iz_general fr op1 op2 inst)) ==>
  set (inst_ir_labels out) SUBSET set (operand_ir_labels [op1;op2])
Proof
  rpt gen_tac >> Cases_on `fr "not"` >> Cases_on `fr "xor"` >>
  Cases_on `fr "iz"` >>
  simp[ao_cmp_prefer_iz_zero_def, ao_cmp_prefer_iz_max_def,
       ao_cmp_prefer_iz_general_def] >> rpt strip_tac >> gvs[] >>
  Cases_on `op1` >> Cases_on `op2` >>
  gvs[inst_ir_labels_def, operand_ir_labels_def, SUBSET_DEF]
QED

Theorem ao_opt_comparator_labels:
  !out. MEM out (ao_opt_comparator dfg ra lbl idx fr inst) ==>
  set (inst_ir_labels out) SUBSET set (inst_ir_labels inst)
Proof
  Cases_on `inst.inst_operands` >> simp[ao_opt_comparator_def] >>
  Cases_on `t` >> simp[ao_opt_comparator_def] >>
  Cases_on `t'` >> simp[ao_opt_comparator_def] >>
  Cases_on `h = h'`
  >- simp[inst_ir_labels_def, operand_ir_labels_def] >>
  simp[] >>
  Cases_on `ao_opt_cmp_range ra lbl idx inst
    (inst.inst_opcode = GT \/ inst.inst_opcode = SGT)
    (inst.inst_opcode = SGT \/ inst.inst_opcode = SLT)`
  >- (qspecl_then [`fr`,`h`,`h'`,`inst`] mp_tac ao_cmp_prefer_iz_labels >>
      simp[] >> strip_tac >> simp[] >> pairarg_tac >> simp[] >>
      rpt (IF_CASES_TAC >> simp[]) >>
      Cases_on `fr "not"` >> Cases_on `fr "iz"` >> simp[] >>
      Cases_on `h` >> Cases_on `h'` >> rpt strip_tac >> gvs[] >>
      fs[inst_ir_labels_def, operand_ir_labels_def, SUBSET_DEF] >> metis_tac[]) >>
  drule ao_opt_cmp_range_labels >> strip_tac >>
  simp[inst_ir_labels_def, SUBSET_DEF]
QED

Theorem ao_peephole_inst_labels:
  !out. MEM out (ao_peephole_inst dfg ra lbl idx fr inst) ==>
  set (inst_ir_labels out) SUBSET set (inst_ir_labels inst)
Proof
  simp[ao_peephole_inst_def] >>
  rpt (IF_CASES_TAC >> simp[]) >> rpt strip_tac
  >~ [`MEM out (ao_opt_eq dfg fr inst)`]
  >- (irule ao_opt_eq_labels >> qexists_tac `dfg` >> qexists_tac `fr` >> simp[])
  >~ [`MEM out (ao_opt_comparator dfg ra lbl idx fr inst)`]
  >- (irule ao_opt_comparator_labels >>
      qexistsl_tac [`dfg`,`fr`,`idx`,`lbl`,`ra`] >> simp[]) >>
  irule ao_simple_peephole_labels >>
  qexistsl_tac [`dfg`,`idx`,`lbl`,`ra`] >> simp[]
QED

Theorem ao_resolve_iszero_inst_ir_labels:
  (!v chain op. ALOOKUP targets v = SOME chain /\ MEM op chain ==>
     ~is_label_operand op) ==>
  set (inst_ir_labels (ao_resolve_iszero_inst targets inst)) SUBSET
    set (inst_ir_labels inst)
Proof
  strip_tac >> simp[inst_ir_labels_def, SUBSET_DEF,
    MEM_operand_ir_labels, ao_resolve_iszero_inst_def, MEM_MAP] >>
  rpt strip_tac >>
  `get_label (ao_resolve_iszero_op targets inst.inst_opcode y) = get_label y` by
    metis_tac[ao_resolve_iszero_op_label] >>
  `get_label y = SOME x` by metis_tac[get_label_def] >>
  Cases_on `y` >> gvs[get_label_def]
QED

Theorem ao_transform_inst_labels:
  (!v chain op. ALOOKUP targets v = SOME chain /\ MEM op chain ==>
     ~is_label_operand op) ==>
  !out. MEM out (ao_transform_inst dfg ra lbl idx targets fr inst) ==>
    set (inst_ir_labels out) SUBSET set (inst_ir_labels inst)
Proof
  strip_tac >>
  `set (inst_ir_labels (ao_resolve_iszero_inst targets inst)) SUBSET
    set (inst_ir_labels inst)` by
    (irule ao_resolve_iszero_inst_ir_labels >> metis_tac[]) >>
  simp[ao_transform_inst_def] >>
  qabbrev_tac `inst0 = ao_resolve_iszero_inst targets inst` >>
  rpt (IF_CASES_TAC >> simp[]) >>
  Cases_on `ao_opt_producer dfg inst0`
  >- (simp[MEM_MAP] >> rpt strip_tac >> gvs[] >>
      simp[ao_flip_inst_labels] >>
      metis_tac[ao_peephole_inst_labels, ao_flip_inst_labels, SUBSET_TRANS]) >>
  drule ao_opt_producer_labels >> strip_tac >>
  simp[MEM_MAP] >> rpt strip_tac >> gvs[] >>
  simp[ao_flip_inst_labels] >> metis_tac[SUBSET_TRANS]
QED

Theorem ao_transform_inst_residual_singleton:
  !inst dfg ra lbl idx targets fr.
  ~MEM inst.inst_opcode
    [SHL; SHR; SAR; SIGNEXTEND; Exp; ADD; SUB; XOR; AND; MUL;
     Div; SDIV; Mod; SMOD; OR; EQ; GT; LT; SGT; SLT; ISZERO; BALANCE; EXTCODESIZE] ==>
  ao_transform_inst dfg ra lbl idx targets fr inst =
    [ao_resolve_iszero_inst targets inst]
Proof
  rpt gen_tac >> Cases_on `inst.inst_opcode` >> simp[MEM] >>
  simp[ao_transform_inst_def, ao_resolve_iszero_inst_fields,
       ao_opt_producer_def, ao_pre_flip_inst_shape,
       ao_peephole_inst_def, ao_post_flip_inst_shape] >>
  Cases_on `(ao_resolve_iszero_inst targets inst).inst_operands` >>
  simp[ao_pre_flip_inst_def, ao_post_flip_inst_def, ao_resolve_iszero_inst_fields] >>
  Cases_on `t` >>
  simp[ao_pre_flip_inst_def, ao_post_flip_inst_def, ao_resolve_iszero_inst_fields] >>
  Cases_on `t'` >>
  simp[ao_pre_flip_inst_def, ao_post_flip_inst_def, ao_resolve_iszero_inst_fields]
QED
