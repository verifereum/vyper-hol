Theory algebraicOptWfProofs
Ancestors
  algebraicOptDefs passSharedDefs venomInst venomWf venomFnScheduleRunner unitShapeDefs
  dfgAnalysisProps

Theorem ao_handle_offset_inst_structure:
  (ao_handle_offset_inst inst).inst_id = inst.inst_id /\
  ((ao_handle_offset_inst inst).inst_opcode = PHI <=> inst.inst_opcode = PHI) /\
  (is_terminator (ao_handle_offset_inst inst).inst_opcode =
   is_terminator inst.inst_opcode) /\
  (get_successors (ao_handle_offset_inst inst) = get_successors inst)
Proof
  Cases_on `inst.inst_opcode = ADD`
  >- (Cases_on `inst.inst_operands` >- simp[ao_handle_offset_inst_def] >>
      rename1 `inst.inst_operands = a::xs` >>
      Cases_on `a` >> simp[ao_handle_offset_inst_def] >>
      Cases_on `xs` >- simp[] >>
      rename1 `inst.inst_operands = Label l::b::ys` >>
      Cases_on `b` >> simp[] >>
      Cases_on `ys` >> simp[is_terminator_def, get_successors_def]) >>
  simp[ao_handle_offset_inst_def]
QED

Theorem ao_pre_flip_inst_structure:
  (ao_pre_flip_inst inst).inst_id = inst.inst_id /\
  (ao_pre_flip_inst inst).inst_opcode = inst.inst_opcode
Proof
  simp[ao_pre_flip_inst_def] >> rpt (CASE_TAC >> gvs[])
QED

Theorem ao_post_flip_inst_structure:
  (ao_post_flip_inst inst).inst_id = inst.inst_id /\
  (ao_post_flip_inst inst).inst_opcode = inst.inst_opcode
Proof
  simp[ao_post_flip_inst_def] >> rpt (CASE_TAC >> gvs[])
QED

Theorem ao_opt_shift_structure:
  LENGTH (ao_opt_shift inst) = 1 /\
  EVERY (\i. i.inst_id = inst.inst_id /\
    (i.inst_opcode = inst.inst_opcode \/ i.inst_opcode = ASSIGN))
    (ao_opt_shift inst)
Proof
  simp[ao_opt_shift_def] >> rpt (CASE_TAC >> gvs[])
QED

Theorem ao_opt_signextend_structure:
  LENGTH (ao_opt_signextend ra lbl idx inst) = 1 /\
  EVERY (\i. i.inst_id = inst.inst_id /\
    (i.inst_opcode = inst.inst_opcode \/ i.inst_opcode = ASSIGN))
    (ao_opt_signextend ra lbl idx inst)
Proof
  Cases_on `inst.inst_operands`
  >- simp[ao_opt_signextend_def] >>
  rename1 `inst.inst_operands = a::xs` >>
  Cases_on `xs`
  >- simp[ao_opt_signextend_def] >>
  rename1 `inst.inst_operands = a::b::ys` >>
  Cases_on `ys`
  >- (Cases_on `a` >>
      asm_simp_tac (srw_ss()) [ao_opt_signextend_def, LET_THM] >>
      IF_CASES_TAC >- asm_simp_tac (srw_ss()) [] >>
      IF_CASES_TAC >- (IF_CASES_TAC
        >- (IF_CASES_TAC >> asm_simp_tac (srw_ss()) []) >>
        asm_simp_tac (srw_ss()) []) >>
      asm_simp_tac (srw_ss()) []) >>
  simp[ao_opt_signextend_def]
QED

Theorem ao_opt_exp_structure:
  LENGTH (ao_opt_exp inst) = 1 /\
  EVERY (\i. i.inst_id = inst.inst_id /\
    (i.inst_opcode = inst.inst_opcode \/ MEM i.inst_opcode [ASSIGN; ISZERO]))
    (ao_opt_exp inst)
Proof
  Cases_on `inst.inst_operands` >- simp[ao_opt_exp_def] >>
  rename1 `inst.inst_operands = a::xs` >>
  Cases_on `xs` >- simp[ao_opt_exp_def] >>
  rename1 `inst.inst_operands = a::b::ys` >>
  Cases_on `ys`
  >- (simp[ao_opt_exp_def] >>
      IF_CASES_TAC >- simp[] >>
      IF_CASES_TAC >- simp[] >>
      IF_CASES_TAC >- simp[] >>
      IF_CASES_TAC >> simp[]) >>
  simp[ao_opt_exp_def]
QED

Theorem ao_opt_addsub_structure:
  LENGTH (ao_opt_addsub inst) = 1 /\
  EVERY (\i. i.inst_id = inst.inst_id /\
    (i.inst_opcode = inst.inst_opcode \/ MEM i.inst_opcode [ASSIGN; NOT]))
    (ao_opt_addsub inst)
Proof
  Cases_on `inst.inst_operands` >- simp[ao_opt_addsub_def] >>
  rename1 `inst.inst_operands = a::xs` >>
  Cases_on `xs` >- simp[ao_opt_addsub_def] >>
  rename1 `inst.inst_operands = a::b::ys` >>
  Cases_on `ys`
  >- (simp[ao_opt_addsub_def] >>
      IF_CASES_TAC >- simp[] >>
      IF_CASES_TAC >- simp[] >>
      IF_CASES_TAC >- simp[] >>
      IF_CASES_TAC >> simp[]) >>
  simp[ao_opt_addsub_def]
QED

Theorem ao_opt_and_structure:
  LENGTH (ao_opt_and inst) = 1 /\
  EVERY (\i. i.inst_id = inst.inst_id /\
    (i.inst_opcode = inst.inst_opcode \/ i.inst_opcode = ASSIGN))
    (ao_opt_and inst)
Proof
  simp[ao_opt_and_def] >> rpt (CASE_TAC >> gvs[])
QED

Theorem ao_opt_muldiv_structure:
  LENGTH (ao_opt_muldiv inst) = 1 /\
  EVERY (\i. i.inst_id = inst.inst_id /\
    (i.inst_opcode = inst.inst_opcode \/ MEM i.inst_opcode [ASSIGN; AND; SHR; SHL]))
    (ao_opt_muldiv inst)
Proof
  Cases_on `inst.inst_operands` >- simp[ao_opt_muldiv_def] >>
  rename1 `inst.inst_operands = a::xs` >>
  Cases_on `xs` >- simp[ao_opt_muldiv_def] >>
  rename1 `inst.inst_operands = a::b::ys` >>
  Cases_on `ys`
  >- (simp[ao_opt_muldiv_def] >>
      IF_CASES_TAC >- simp[] >>
      IF_CASES_TAC >- simp[] >>
      IF_CASES_TAC >- simp[] >>
      Cases_on `b` >> simp[] >>
      IF_CASES_TAC >- (IF_CASES_TAC >- simp[] >>
        IF_CASES_TAC >- simp[] >> IF_CASES_TAC >> simp[]) >>
      simp[]) >>
  simp[ao_opt_muldiv_def]
QED

Theorem ao_opt_or_structure:
  LENGTH (ao_opt_or dfg inst) = 1 /\
  EVERY (\i. i.inst_id = inst.inst_id /\
    (i.inst_opcode = inst.inst_opcode \/ i.inst_opcode = ASSIGN))
    (ao_opt_or dfg inst)
Proof
  simp[ao_opt_or_def] >> rpt (CASE_TAC >> gvs[])
QED

Theorem ao_opt_producer_structure:
  ao_opt_producer dfg inst = SOME result ==>
  LENGTH result = 1 /\
  EVERY (\i. i.inst_id = inst.inst_id /\
    (i.inst_opcode = inst.inst_opcode \/ MEM i.inst_opcode [ASSIGN; SELFBALANCE]))
    result
Proof
  qid_spec_tac `result` >>
  Cases_on `inst.inst_opcode = BALANCE`
  >- (Cases_on `inst.inst_operands` >> simp[ao_opt_producer_def] >>
      rename1 `inst.inst_operands = a::xs` >>
      Cases_on `xs` >> simp[] >>
      Cases_on `a` >> simp[] >>
      CASE_TAC >> simp[] >> IF_CASES_TAC >> simp[] >>
      rpt strip_tac >> gvs[]) >>
  Cases_on `inst.inst_opcode = EXTCODESIZE`
  >- simp[ao_opt_producer_def] >>
  Cases_on `inst.inst_opcode = SIGNEXTEND`
  >- (Cases_on `inst.inst_operands` >> simp[ao_opt_producer_def] >>
      rename1 `inst.inst_operands = a::xs` >>
      Cases_on `a` >> simp[] >>
      Cases_on `xs` >> simp[] >>
      rename1 `inst.inst_operands = Lit w::b::ys` >>
      Cases_on `ys` >> simp[] >>
      Cases_on `b` >> simp[] >>
      CASE_TAC >> simp[] >>
      rename1 `dfg_get_def dfg v = SOME producer` >>
      Cases_on `producer.inst_opcode = SIGNEXTEND` >> simp[] >>
      Cases_on `producer.inst_operands` >> simp[] >>
      rename1 `producer.inst_operands = a::xs` >>
      Cases_on `a` >> simp[] >>
      Cases_on `xs` >> simp[] >>
      rename1 `producer.inst_operands = Lit k::b::ys` >>
      Cases_on `ys` >> simp[] >>
      IF_CASES_TAC >> simp[] >> rpt strip_tac >> gvs[]) >>
  simp[ao_opt_producer_def]
QED

Theorem ao_opt_eq_structure:
  MEM (MAP (\i. (i.inst_id, i.inst_opcode)) (ao_opt_eq dfg fr inst))
    [[(inst.inst_id, inst.inst_opcode)];
     [(inst.inst_id, ASSIGN)]; [(inst.inst_id, ISZERO)];
     [(FST (fr "not"), NOT); (inst.inst_id, ISZERO)];
     [(FST (fr "xor"), XOR); (inst.inst_id, ISZERO)]]
Proof
  Cases_on `inst.inst_operands` >- simp[ao_opt_eq_def] >>
  rename1 `inst.inst_operands = a::xs` >>
  Cases_on `xs` >- simp[ao_opt_eq_def] >>
  rename1 `inst.inst_operands = a::b::ys` >>
  Cases_on `ys`
  >- (simp[ao_opt_eq_def] >>
      IF_CASES_TAC >- simp[] >>
      IF_CASES_TAC >- simp[] >>
      IF_CASES_TAC >- (pairarg_tac >> gvs[]) >>
      IF_CASES_TAC >- (pairarg_tac >> gvs[]) >> simp[]) >>
  simp[ao_opt_eq_def]
QED

Theorem ao_opt_comparator_structure:
  LENGTH inst.inst_operands = 2 ==>
  MEM (MAP (\i. (i.inst_id, i.inst_opcode))
      (ao_opt_comparator dfg ra lbl idx fr inst))
    [[(inst.inst_id, inst.inst_opcode)];
     [(inst.inst_id, ASSIGN)]; [(inst.inst_id, ISZERO)]; [(inst.inst_id, EQ)];
     [(FST (fr "not"), NOT); (inst.inst_id, ISZERO)];
     [(FST (fr "iz"), ISZERO); (inst.inst_id, ISZERO)];
     [(FST (fr "not"), NOT); (FST (fr "iz"), ISZERO); (inst.inst_id, ISZERO)];
     [(FST (fr "xor"), XOR); (FST (fr "iz"), ISZERO); (inst.inst_id, ISZERO)]]
Proof
  strip_tac >>
  Cases_on `inst.inst_operands` >- gvs[] >>
  rename1 `inst.inst_operands = a::xs` >>
  Cases_on `xs` >- gvs[] >>
  rename1 `inst.inst_operands = a::b::ys` >>
  Cases_on `ys`
  >- (simp[ao_opt_comparator_def] >>
      IF_CASES_TAC >- simp[] >>
      Cases_on `ao_opt_cmp_range ra lbl idx inst
        (inst.inst_opcode = GT \/ inst.inst_opcode = SGT)
        (inst.inst_opcode = SGT \/ inst.inst_opcode = SLT)` >> simp[] >>
      pairarg_tac >> simp[] >>
      IF_CASES_TAC >- simp[] >>
      IF_CASES_TAC >- simp[] >>
      IF_CASES_TAC
      >- (IF_CASES_TAC >- simp[] >>
          IF_CASES_TAC >- (pairarg_tac >> gvs[]) >> simp[]) >>
      IF_CASES_TAC
      >- (Cases_on `b` >> gvs[is_lit_op_def] >>
          IF_CASES_TAC
          >- (simp[ao_cmp_prefer_iz_zero_def] >> pairarg_tac >> gvs[]) >>
          IF_CASES_TAC
          >- (simp[ao_cmp_prefer_iz_max_def] >>
              pairarg_tac >> gvs[] >> pairarg_tac >> gvs[]) >>
          simp[ao_cmp_prefer_iz_general_def] >>
          pairarg_tac >> gvs[] >> pairarg_tac >> gvs[]) >>
      IF_CASES_TAC >- (pairarg_tac >> gvs[]) >> simp[]) >>
  gvs[]
QED

Theorem ao_inst_wf_comparator_arity:
  inst_wf inst /\ MEM inst.inst_opcode [GT; LT; SGT; SLT] ==>
  LENGTH inst.inst_operands = 2
Proof
  simp[] >> strip_tac >> gvs[inst_wf_def]
QED

Theorem ao_resolve_iszero_inst_structure:
  (ao_resolve_iszero_inst targets inst).inst_id = inst.inst_id /\
  (ao_resolve_iszero_inst targets inst).inst_opcode = inst.inst_opcode /\
  (ao_resolve_iszero_inst targets inst).inst_outputs = inst.inst_outputs /\
  LENGTH (ao_resolve_iszero_inst targets inst).inst_operands = LENGTH inst.inst_operands
Proof
  simp[ao_resolve_iszero_inst_def]
QED

Theorem ao_pre_flip_inst_arity:
  LENGTH (ao_pre_flip_inst inst).inst_operands = LENGTH inst.inst_operands
Proof
  simp[ao_pre_flip_inst_def] >> rpt (CASE_TAC >> gvs[])
QED

Theorem ao_peephole_inst_nonempty:
  (MEM inst.inst_opcode [GT; LT; SGT; SLT] ==>
   LENGTH inst.inst_operands = 2) ==>
  ao_peephole_inst dfg ra lbl idx fr inst <> []
Proof
  strip_tac >> simp[ao_peephole_inst_def] >>
  IF_CASES_TAC >- simp[] >>
  IF_CASES_TAC >- simp[] >>
  IF_CASES_TAC >- (spose_not_then assume_tac >>
      mp_tac ao_opt_shift_structure >> simp[]) >>
  IF_CASES_TAC >- (spose_not_then assume_tac >>
      `LENGTH (ao_opt_signextend ra lbl idx inst) = 1`
        by metis_tac[ao_opt_signextend_structure] >> gvs[]) >>
  IF_CASES_TAC >- (spose_not_then assume_tac >>
      mp_tac ao_opt_exp_structure >> simp[]) >>
  IF_CASES_TAC >- (spose_not_then assume_tac >>
      mp_tac ao_opt_addsub_structure >> simp[]) >>
  IF_CASES_TAC >- (spose_not_then assume_tac >>
      mp_tac ao_opt_and_structure >> simp[]) >>
  IF_CASES_TAC >- (spose_not_then assume_tac >>
      mp_tac ao_opt_muldiv_structure >> simp[]) >>
  IF_CASES_TAC >- (spose_not_then assume_tac >>
      `LENGTH (ao_opt_or dfg inst) = 1`
        by metis_tac[ao_opt_or_structure] >> gvs[]) >>
  IF_CASES_TAC
  >- (mp_tac ao_opt_eq_structure >>
      Cases_on `ao_opt_eq dfg fr inst = []` >> gvs[]) >>
  IF_CASES_TAC
  >- (`LENGTH inst.inst_operands = 2` by gvs[] >>
      drule ao_opt_comparator_structure >>
      Cases_on `ao_opt_comparator dfg ra lbl idx fr inst = []` >> gvs[] >>
      qexistsl [`ra`, `lbl`, `idx`, `fr`, `dfg`] >> gvs[]) >>
  simp[]
QED

Theorem ao_transform_inst_nonempty:
  inst_wf inst ==>
  ao_transform_inst dfg ra lbl idx targets fr inst <> []
Proof
  strip_tac >> simp[ao_transform_inst_def] >>
  IF_CASES_TAC >- simp[] >>
  IF_CASES_TAC >- simp[] >>
  Cases_on `ao_opt_producer dfg (ao_resolve_iszero_inst targets inst)` >> simp[]
  >- (irule ao_peephole_inst_nonempty >>
      simp[ao_pre_flip_inst_structure, ao_pre_flip_inst_arity,
           ao_resolve_iszero_inst_structure] >>
      strip_tac >> irule ao_inst_wf_comparator_arity >> simp[]) >>
  drule ao_opt_producer_structure >>
  Cases_on `x = []` >> simp[]
QED

Theorem ao_singleton_projection[local]:
  LENGTH (xs:instruction list) = 1 ==>
  (MAP (f:instruction -> num) xs = [a] <=> EVERY (\x. f x = a) xs)
Proof
  Cases_on `xs` >> simp[] >> metis_tac[]
QED

Theorem ao_peephole_inst_ids:
  (MEM inst.inst_opcode [GT; LT; SGT; SLT] ==>
   LENGTH inst.inst_operands = 2) ==>
  MEM (MAP (\i. i.inst_id) (ao_peephole_inst dfg ra lbl idx fr inst))
    [[inst.inst_id]; [FST (fr "not"); inst.inst_id];
     [FST (fr "xor"); inst.inst_id]; [FST (fr "iz"); inst.inst_id];
     [FST (fr "not"); FST (fr "iz"); inst.inst_id];
     [FST (fr "xor"); FST (fr "iz"); inst.inst_id]]
Proof
  strip_tac >> pure_rewrite_tac [ao_peephole_inst_def, LET_THM, listTheory.MEM] >>
  BETA_TAC >>
  IF_CASES_TAC >- simp[] >>
  IF_CASES_TAC >- simp[] >>
  IF_CASES_TAC >- (mp_tac ao_opt_shift_structure >> strip_tac >>
    drule ao_singleton_projection >>
    disch_then (mp_tac o Q.ISPECL [`(\i. i.inst_id)`, `inst.inst_id`]) >>
    disch_tac >> disj1_tac >>
    asm_simp_tac (srw_ss()) [] >>
    gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  IF_CASES_TAC >- (mp_tac ao_opt_signextend_structure >> strip_tac >>
    drule ao_singleton_projection >>
    disch_then (mp_tac o Q.ISPECL [`(\i. i.inst_id)`, `inst.inst_id`]) >>
    disch_tac >> disj1_tac >>
    asm_simp_tac (srw_ss()) [] >>
    gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  IF_CASES_TAC >- (mp_tac ao_opt_exp_structure >> strip_tac >>
    drule ao_singleton_projection >>
    disch_then (mp_tac o Q.ISPECL [`(\i. i.inst_id)`, `inst.inst_id`]) >>
    disch_tac >> disj1_tac >>
    asm_simp_tac (srw_ss()) [] >>
    gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  IF_CASES_TAC >- (mp_tac ao_opt_addsub_structure >> strip_tac >>
    drule ao_singleton_projection >>
    disch_then (mp_tac o Q.ISPECL [`(\i. i.inst_id)`, `inst.inst_id`]) >>
    disch_tac >> disj1_tac >>
    asm_simp_tac (srw_ss()) [] >>
    gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  IF_CASES_TAC >- (mp_tac ao_opt_and_structure >> strip_tac >>
    drule ao_singleton_projection >>
    disch_then (mp_tac o Q.ISPECL [`(\i. i.inst_id)`, `inst.inst_id`]) >>
    disch_tac >> disj1_tac >>
    asm_simp_tac (srw_ss()) [] >>
    gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  IF_CASES_TAC >- (mp_tac ao_opt_muldiv_structure >> strip_tac >>
    drule ao_singleton_projection >>
    disch_then (mp_tac o Q.ISPECL [`(\i. i.inst_id)`, `inst.inst_id`]) >>
    disch_tac >> disj1_tac >>
    asm_simp_tac (srw_ss()) [] >>
    gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  IF_CASES_TAC >- (mp_tac ao_opt_or_structure >> strip_tac >>
    drule ao_singleton_projection >>
    disch_then (mp_tac o Q.ISPECL [`(\i. i.inst_id)`, `inst.inst_id`]) >>
    disch_tac >> disj1_tac >>
    asm_simp_tac (srw_ss()) [] >>
    gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  IF_CASES_TAC >- (mp_tac ao_opt_eq_structure >>
    simp[] >> rpt strip_tac >> gvs[listTheory.MAP_EQ_CONS, listTheory.MAP_EQ_NIL]) >>
  IF_CASES_TAC >- (`LENGTH inst.inst_operands = 2` by gvs[] >>
    drule ao_opt_comparator_structure >>
    disch_then (qspecl_then [`ra`, `lbl`, `idx`, `fr`, `dfg`] mp_tac) >>
    simp[] >> rpt strip_tac >> gvs[listTheory.MAP_EQ_CONS, listTheory.MAP_EQ_NIL]) >>
  simp[]
QED

Theorem ao_peephole_inst_classification:
  (MEM inst.inst_opcode [GT; LT; SGT; SLT] ==>
   LENGTH inst.inst_operands = 2) ==>
  EVERY (\i. i.inst_opcode = inst.inst_opcode \/
    MEM i.inst_opcode [ASSIGN; ISZERO; NOT; AND; SHR; SHL; EQ; XOR])
    (ao_peephole_inst dfg ra lbl idx fr inst)
Proof
  strip_tac >> simp[ao_peephole_inst_def] >>
  IF_CASES_TAC >- simp[] >>
  IF_CASES_TAC >- simp[] >>
  IF_CASES_TAC >- (mp_tac ao_opt_shift_structure >>
    simp[listTheory.EVERY_MEM] >> metis_tac[]) >>
  IF_CASES_TAC >- (mp_tac ao_opt_signextend_structure >>
    simp[listTheory.EVERY_MEM] >> metis_tac[]) >>
  IF_CASES_TAC >- (mp_tac ao_opt_exp_structure >>
    simp[listTheory.EVERY_MEM] >> metis_tac[]) >>
  IF_CASES_TAC >- (mp_tac ao_opt_addsub_structure >>
    simp[listTheory.EVERY_MEM] >> metis_tac[]) >>
  IF_CASES_TAC >- (mp_tac ao_opt_and_structure >>
    simp[listTheory.EVERY_MEM] >> metis_tac[]) >>
  IF_CASES_TAC >- (mp_tac ao_opt_muldiv_structure >>
    simp[listTheory.EVERY_MEM] >> metis_tac[]) >>
  IF_CASES_TAC >- (mp_tac ao_opt_or_structure >>
    simp[listTheory.EVERY_MEM] >> metis_tac[]) >>
  IF_CASES_TAC >- (mp_tac ao_opt_eq_structure >>
    simp[] >> rpt strip_tac >> gvs[listTheory.MAP_EQ_CONS, listTheory.MAP_EQ_NIL]) >>
  IF_CASES_TAC >- (`LENGTH inst.inst_operands = 2` by gvs[] >>
    drule ao_opt_comparator_structure >>
    disch_then (qspecl_then [`ra`, `lbl`, `idx`, `fr`, `dfg`] mp_tac) >>
    simp[] >> rpt strip_tac >> gvs[listTheory.MAP_EQ_CONS, listTheory.MAP_EQ_NIL]) >>
  simp[]
QED

Theorem ao_transform_inst_ids:
  inst_wf inst ==>
  MEM (MAP (\i. i.inst_id) (ao_transform_inst dfg ra lbl idx targets fr inst))
    [[inst.inst_id]; [FST (fr "not"); inst.inst_id];
     [FST (fr "xor"); inst.inst_id]; [FST (fr "iz"); inst.inst_id];
     [FST (fr "not"); FST (fr "iz"); inst.inst_id];
     [FST (fr "xor"); FST (fr "iz"); inst.inst_id]]
Proof
  strip_tac >> simp[ao_transform_inst_def] >>
  IF_CASES_TAC >- simp[ao_resolve_iszero_inst_structure] >>
  IF_CASES_TAC >- simp[ao_resolve_iszero_inst_structure] >>
  Cases_on `ao_opt_producer dfg (ao_resolve_iszero_inst targets inst)` >> simp[]
  >- (`MEM (ao_pre_flip_inst (ao_resolve_iszero_inst targets inst)).inst_opcode
          [GT; LT; SGT; SLT] ==>
        LENGTH (ao_pre_flip_inst (ao_resolve_iszero_inst targets inst)).inst_operands = 2`
        by (simp[ao_pre_flip_inst_structure, ao_pre_flip_inst_arity,
                 ao_resolve_iszero_inst_structure] >>
            strip_tac >> irule ao_inst_wf_comparator_arity >> simp[]) >>
      mp_tac (Q.INST [`inst` |-> `ao_pre_flip_inst (ao_resolve_iszero_inst targets inst)`]
        ao_peephole_inst_ids) >>
      simp[listTheory.MAP_MAP_o, combinTheory.o_DEF,
           ao_post_flip_inst_structure, ao_pre_flip_inst_structure,
           ao_resolve_iszero_inst_structure] >>
      rpt strip_tac >> gvs[ao_post_flip_inst_structure]) >>
  drule ao_opt_producer_structure >> strip_tac >>
  Cases_on `x` >> gvs[] >>
  gvs[ao_post_flip_inst_structure, ao_resolve_iszero_inst_structure]
QED

Theorem ao_transform_inst_classification:
  inst_wf inst ==>
  EVERY (\i. i.inst_opcode = inst.inst_opcode \/
    MEM i.inst_opcode [ASSIGN; ISZERO; NOT; AND; SHR; SHL; EQ; XOR; SELFBALANCE])
    (ao_transform_inst dfg ra lbl idx targets fr inst)
Proof
  strip_tac >> simp[ao_transform_inst_def] >>
  IF_CASES_TAC >- simp[ao_resolve_iszero_inst_structure] >>
  IF_CASES_TAC >- simp[ao_resolve_iszero_inst_structure] >>
  Cases_on `ao_opt_producer dfg (ao_resolve_iszero_inst targets inst)` >> simp[]
  >- (`MEM (ao_pre_flip_inst (ao_resolve_iszero_inst targets inst)).inst_opcode
          [GT; LT; SGT; SLT] ==>
        LENGTH (ao_pre_flip_inst (ao_resolve_iszero_inst targets inst)).inst_operands = 2`
        by (simp[ao_pre_flip_inst_structure, ao_pre_flip_inst_arity,
                 ao_resolve_iszero_inst_structure] >>
            strip_tac >> irule ao_inst_wf_comparator_arity >> simp[]) >>
      drule ao_peephole_inst_classification >>
      disch_then (qspecl_then [`ra`, `lbl`, `idx`, `fr`, `dfg`] mp_tac) >>
      simp[listTheory.EVERY_MAP, listTheory.EVERY_MEM,
           ao_post_flip_inst_structure, ao_pre_flip_inst_structure,
           ao_resolve_iszero_inst_structure] >> metis_tac[]) >>
  drule ao_opt_producer_structure >>
  simp[listTheory.EVERY_MAP, listTheory.EVERY_MEM,
       ao_post_flip_inst_structure, ao_resolve_iszero_inst_structure] >>
  metis_tac[]
QED

Theorem ao_transform_inst_nonphi:
  inst_wf inst /\ inst.inst_opcode <> PHI ==>
  EVERY (\i. i.inst_opcode <> PHI)
    (ao_transform_inst dfg ra lbl idx targets fr inst)
Proof
  strip_tac >> drule ao_transform_inst_classification >>
  disch_then (qspecl_then [`targets`, `ra`, `lbl`, `idx`, `fr`, `dfg`] mp_tac) >>
  simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >> gvs[]
QED

Theorem ao_transform_inst_nonterminator:
  inst_wf inst /\ ~is_terminator inst.inst_opcode ==>
  EVERY (\i. ~is_terminator i.inst_opcode)
    (ao_transform_inst dfg ra lbl idx targets fr inst)
Proof
  strip_tac >> drule ao_transform_inst_classification >>
  disch_then (qspecl_then [`targets`, `ra`, `lbl`, `idx`, `fr`, `dfg`] mp_tac) >>
  simp[listTheory.EVERY_MEM] >> disch_tac >> gen_tac >> disch_tac >>
  qpat_x_assum `!i. MEM i _ ==> _` (qspec_then `i` mp_tac) >>
  simp[] >> strip_tac >> gvs[is_terminator_def]
QED

Theorem ao_transform_inst_phi:
  inst.inst_opcode = PHI ==>
  ao_transform_inst dfg ra lbl idx targets fr inst =
    [ao_resolve_iszero_inst targets inst]
Proof
  simp[ao_transform_inst_def, ao_resolve_iszero_inst_structure]
QED

Theorem ao_transform_inst_no_outputs:
  inst.inst_outputs = [] ==>
  ao_transform_inst dfg ra lbl idx targets fr inst =
    [ao_resolve_iszero_inst targets inst]
Proof
  simp[ao_transform_inst_def, ao_resolve_iszero_inst_structure]
QED

Theorem ao_inst_wf_terminator_outputs:
  inst_wf inst /\ is_terminator inst.inst_opcode ==>
  inst.inst_outputs = []
Proof
  Cases_on `inst.inst_opcode` >> simp[is_terminator_def, inst_wf_def] >>
  metis_tac[]
QED

Theorem ao_transform_inst_terminator:
  inst_wf inst /\ is_terminator inst.inst_opcode ==>
  ao_transform_inst dfg ra lbl idx targets fr inst =
    [ao_resolve_iszero_inst targets inst]
Proof
  strip_tac >> irule ao_transform_inst_no_outputs >>
  irule ao_inst_wf_terminator_outputs >> simp[]
QED

Theorem ao_iszero_label_positions:
  label_positions_ok inst /\ inst.inst_opcode = ISZERO ==>
  EVERY (\op. get_label op = NONE) inst.inst_operands
Proof
  simp[label_positions_ok_def] >> strip_tac >>
  gvs[listTheory.EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> Cases_on `op` >>
  simp[stackPlanTypesTheory.is_label_operand_def, venomStateTheory.get_label_def]
QED

Theorem ao_label_free_lookup[local]:
  EVERY (\p. EVERY (\op. get_label op = NONE) (SND p)) targets /\
  ALOOKUP targets v = SOME ops ==>
  EVERY (\op. get_label op = NONE) ops
Proof
  Induct_on `targets` >> simp[] >>
  gen_tac >> PairCases_on `h` >> simp[] >>
  Cases_on `h0 = v` >> simp[] >> metis_tac[]
QED

Theorem ao_resolve_iszero_op_label:
  EVERY (\p. EVERY (\op. get_label op = NONE) (SND p)) targets ==>
  get_label (ao_resolve_iszero_op targets opc op) = get_label op
Proof
  strip_tac >> Cases_on `op` >>
  simp[ao_resolve_iszero_op_def, venomStateTheory.get_label_def] >>
  rename1 `ALOOKUP targets v` >>
  Cases_on `ALOOKUP targets v` >> simp[venomStateTheory.get_label_def] >>
  IF_CASES_TAC >- simp[venomStateTheory.get_label_def] >>
  IF_CASES_TAC >> simp[venomStateTheory.get_label_def] >>
  drule_all ao_label_free_lookup >>
  simp[listTheory.EVERY_EL] >> strip_tac >>
  first_x_assum irule >> simp[]
QED

Theorem ao_resolve_iszero_inst_labels:
  EVERY (\p. EVERY (\op. get_label op = NONE) (SND p)) targets ==>
  MAP get_label (ao_resolve_iszero_inst targets inst).inst_operands =
  MAP get_label inst.inst_operands
Proof
  strip_tac >> simp[ao_resolve_iszero_inst_def, listTheory.MAP_MAP_o,
    combinTheory.o_DEF] >>
  irule listTheory.MAP_CONG >> simp[] >> rpt strip_tac >>
  irule ao_resolve_iszero_op_label >> simp[]
QED

Theorem ao_resolve_iszero_inst_successors:
  EVERY (\p. EVERY (\op. get_label op = NONE) (SND p)) targets ==>
  get_successors (ao_resolve_iszero_inst targets inst) = get_successors inst
Proof
  strip_tac >> simp[get_successors_def, ao_resolve_iszero_inst_structure,
    ao_resolve_iszero_inst_labels]
QED

Theorem ao_transform_inst_terminator_successors:
  inst_wf inst /\ is_terminator inst.inst_opcode /\
  EVERY (\p. EVERY (\op. get_label op = NONE) (SND p)) targets ==>
  MAP get_successors (ao_transform_inst dfg ra lbl idx targets fr inst) =
    [get_successors inst]
Proof
  strip_tac >> drule_all ao_transform_inst_terminator >>
  disch_then (qspecl_then [`targets`, `ra`, `lbl`, `idx`, `fr`, `dfg`] mp_tac) >>
  simp[] >> disch_then SUBST1_TAC >>
  simp[ao_resolve_iszero_inst_successors]
QED

Theorem ao_compute_iszero_step_label_free:
  EVERY (\p. EVERY (\op. get_label op = NONE) (SND p)) targets /\
  (inst.inst_opcode = ISZERO ==>
   EVERY (\op. get_label op = NONE) inst.inst_operands) ==>
  EVERY (\p. EVERY (\op. get_label op = NONE) (SND p))
    (ao_compute_iszero_step targets inst)
Proof
  strip_tac >> Cases_on `inst.inst_opcode = ISZERO`
  >- (Cases_on `inst.inst_operands` >> simp[ao_compute_iszero_step_def] >>
      rename1 `inst.inst_operands = inp::rest` >>
      Cases_on `rest` >> simp[] >>
      Cases_on `inst.inst_outputs` >> simp[] >>
      rename1 `inst.inst_outputs = out::outs` >>
      Cases_on `outs` >> simp[] >>
      gvs[] >> Cases_on `inp` >>
      simp[venomStateTheory.get_label_def] >>
      CASE_TAC >> simp[listTheory.EVERY_SNOC, venomStateTheory.get_label_def] >>
      drule_all ao_label_free_lookup >> simp[]) >>
  simp[ao_compute_iszero_step_def]
QED

Theorem ao_compute_iszero_fold_label_free:
  EVERY (\p. EVERY (\op. get_label op = NONE) (SND p)) targets /\
  EVERY (\inst. inst.inst_opcode = ISZERO ==>
    EVERY (\op. get_label op = NONE) inst.inst_operands) insts ==>
  EVERY (\p. EVERY (\op. get_label op = NONE) (SND p))
    (FOLDL ao_compute_iszero_step targets insts)
Proof
  qid_spec_tac `targets` >> Induct_on `insts` >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> simp[] >>
  irule ao_compute_iszero_step_label_free >> simp[]
QED

Theorem ao_compute_fn_iszero_targets_label_free:
  EVERY label_positions_ok (fn_insts fn) ==>
  EVERY (\p. EVERY (\op. get_label op = NONE) (SND p))
    (ao_compute_fn_iszero_targets fn)
Proof
  strip_tac >> simp[ao_compute_fn_iszero_targets_def, ao_compute_iszero_targets_def] >>
  irule ao_compute_iszero_fold_label_free >> simp[] >>
  rewrite_tac[listTheory.EVERY_MEM] >> rpt strip_tac >>
  rename1 `MEM inst (fn_insts fn)` >>
  `label_positions_ok inst` by (gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  BETA_TAC >> strip_tac >> drule_all ao_iszero_label_positions >>
  simp[listTheory.EVERY_MEM]
QED

Theorem ao_handle_offset_iszero:
  (ao_handle_offset_inst inst).inst_opcode = ISZERO ==>
  ao_handle_offset_inst inst = inst /\ inst.inst_opcode = ISZERO
Proof
  Cases_on `inst.inst_opcode = ADD`
  >- (Cases_on `inst.inst_operands` >> simp[ao_handle_offset_inst_def] >>
      rename1 `inst.inst_operands = a::xs` >>
      Cases_on `a` >> simp[] >> Cases_on `xs` >> simp[] >>
      rename1 `inst.inst_operands = Label l::b::ys` >>
      Cases_on `b` >> simp[] >> Cases_on `ys` >> simp[]) >>
  simp[ao_handle_offset_inst_def]
QED

Theorem ao_offset_iszero_inputs:
  EVERY label_positions_ok insts ==>
  EVERY (\inst. inst.inst_opcode = ISZERO ==>
    EVERY (\op. get_label op = NONE) inst.inst_operands)
    (MAP ao_handle_offset_inst insts)
Proof
  strip_tac >> simp[listTheory.EVERY_MAP] >>
  gvs[listTheory.EVERY_MEM] >> rpt strip_tac >>
  drule ao_handle_offset_iszero >> strip_tac >> gvs[] >>
  rename1 `MEM inst insts` >>
  `label_positions_ok inst` by metis_tac[] >>
  drule_all ao_iszero_label_positions >> simp[listTheory.EVERY_MEM]
QED

Theorem ao_offset_blocks_iszero_inputs:
  EVERY label_positions_ok (fn_insts_blocks bbs) ==>
  EVERY (\inst. inst.inst_opcode = ISZERO ==>
    EVERY (\op. get_label op = NONE) inst.inst_operands)
    (fn_insts_blocks
      (MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) bbs))
Proof
  Induct_on `bbs` >> simp[fn_insts_blocks_def] >>
  metis_tac[ao_offset_iszero_inputs]
QED

Theorem ao_offset_fn_iszero_targets_label_free:
  EVERY label_positions_ok (fn_insts fn) ==>
  EVERY (\p. EVERY (\op. get_label op = NONE) (SND p))
    (ao_compute_fn_iszero_targets
      (fn with fn_blocks :=
        MAP (\bb. bb with bb_instructions :=
          MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks))
Proof
  strip_tac >>
  simp[ao_compute_fn_iszero_targets_def, ao_compute_iszero_targets_def] >>
  irule ao_compute_iszero_fold_label_free >> simp[fn_insts_def] >>
  irule ao_offset_blocks_iszero_inputs >> gvs[fn_insts_def]
QED

Theorem ao_alloc_fresh_ids:
  ao_alloc_fresh s = (fr, s') ==>
  FST (fr "not") = s.irs_next_inst /\
  FST (fr "xor") = s.irs_next_inst /\
  FST (fr "iz") = SUC s.irs_next_inst /\
  s'.irs_next_inst = s.irs_next_inst + 2
Proof
  simp[ao_alloc_fresh_def, irSupplyTheory.fresh_inst_id_def,
       irSupplyTheory.fresh_ir_var_def] >>
  rpt CASE_TAC >> simp[] >> strip_tac >> gvs[]
QED

Theorem ao_transform_inst_fresh_ids:
  inst_wf inst /\ inst.inst_id < s.irs_next_inst /\
  ao_alloc_fresh s = (fr, s') ==>
  ALL_DISTINCT (MAP (\i. i.inst_id)
    (ao_transform_inst dfg ra lbl idx targets fr inst)) /\
  EVERY (\id. id < s'.irs_next_inst)
    (MAP (\i. i.inst_id) (ao_transform_inst dfg ra lbl idx targets fr inst)) /\
  (!id. MEM id (MAP (\i. i.inst_id)
    (ao_transform_inst dfg ra lbl idx targets fr inst)) ==>
    id = inst.inst_id \/ s.irs_next_inst <= id)
Proof
  strip_tac >> drule ao_alloc_fresh_ids >> strip_tac >>
  mp_tac ao_transform_inst_ids >>
  simp[] >> strip_tac >> gvs[]
QED

Theorem ao_transform_insts_supply_frontier:
  ao_transform_insts_supply dfg ra lbl targets s idx insts = (outs, s') ==>
  s'.irs_next_inst = s.irs_next_inst + 2 * LENGTH insts
Proof
  map_every qid_spec_tac [`s'`, `outs`, `idx`, `s`] >>
  Induct_on `insts` >> simp[ao_transform_insts_supply_def] >>
  rpt gen_tac >>
  Cases_on `ao_alloc_fresh s` >>
  Cases_on `ao_transform_insts_supply dfg ra lbl targets r (SUC idx) insts` >>
  simp[] >> strip_tac >> gvs[] >>
  drule ao_alloc_fresh_ids >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem ao_transform_inst_supply_id_origin:
  inst_wf inst /\ ao_alloc_fresh s = (fr,s') /\
  MEM id (MAP (\i. i.inst_id)
    (ao_transform_inst dfg ra lbl idx targets fr inst)) ==>
  id = inst.inst_id \/ s.irs_next_inst <= id
Proof
  strip_tac >> drule ao_alloc_fresh_ids >> strip_tac >>
  mp_tac ao_transform_inst_ids >>
  simp[] >> strip_tac >> gvs[]
QED

Theorem ao_transform_insts_supply_id_origin:
  EVERY inst_wf insts /\
  ao_transform_insts_supply dfg ra lbl targets s idx insts = (outs, s') ==>
  !id. MEM id (MAP (\i. i.inst_id) outs) ==>
    MEM id (MAP (\i. i.inst_id) insts) \/ s.irs_next_inst <= id
Proof
  map_every qid_spec_tac [`s'`, `outs`, `idx`, `s`] >>
  Induct_on `insts` >> simp[ao_transform_insts_supply_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `ao_alloc_fresh s` >>
  Cases_on `ao_transform_insts_supply dfg ra lbl targets r (SUC idx) insts` >>
  gvs[] >> gen_tac >> strip_tac
  >- metis_tac[ao_transform_inst_supply_id_origin] >>
  first_x_assum drule >> disch_then (qspec_then `id` mp_tac) >>
  simp[] >> strip_tac >- simp[] >>
  drule ao_alloc_fresh_ids >> strip_tac >> gvs[] >>
  disj2_tac >> decide_tac
QED

val _ = List.app (fn th =>
  if null (hyp th) then () else raise Fail "residual hypotheses in AO boundary")
  [ao_singleton_projection, ao_peephole_inst_ids, ao_transform_inst_ids,
   ao_alloc_fresh_ids, ao_transform_inst_fresh_ids,
   ao_transform_insts_supply_frontier, ao_transform_inst_supply_id_origin,
   ao_transform_insts_supply_id_origin];

Theorem ao_transform_insts_supply_bound:
  EVERY inst_wf insts /\
  EVERY (\i. i.inst_id < s.irs_next_inst) insts /\
  ao_transform_insts_supply dfg ra lbl targets s idx insts = (outs, s') ==>
  EVERY (\i. i.inst_id < s'.irs_next_inst) outs
Proof
  map_every qid_spec_tac [`s'`, `outs`, `idx`, `s`] >>
  Induct_on `insts` >> simp[ao_transform_insts_supply_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `ao_alloc_fresh s` >>
  Cases_on `ao_transform_insts_supply dfg ra lbl targets r (SUC idx) insts` >>
  gvs[] >>
  drule ao_alloc_fresh_ids >> strip_tac >>
  `EVERY (\i. i.inst_id < r.irs_next_inst) insts` by
    (gvs[listTheory.EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> simp[]) >>
  `EVERY (\i. i.inst_id < r''.irs_next_inst) q'` by metis_tac[] >>
  `EVERY (\i. i.inst_id < r.irs_next_inst)
    (ao_transform_inst dfg ra lbl idx targets q h)` by
    (mp_tac (Q.INST [`inst` |-> `h`, `fr` |-> `q`, `s'` |-> `r`]
       ao_transform_inst_fresh_ids) >> simp[listTheory.EVERY_MAP]) >>
  drule ao_transform_insts_supply_frontier >> strip_tac >>
  gvs[listTheory.EVERY_MEM] >> rpt strip_tac >>
  qpat_x_assum `!i. MEM i (ao_transform_inst _ _ _ _ _ _ _) ==> _`
    drule >> simp[]
QED

Theorem ao_transform_insts_supply_distinct:
  EVERY inst_wf insts /\
  ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\
  EVERY (\i. i.inst_id < s.irs_next_inst) insts /\
  ao_transform_insts_supply dfg ra lbl targets s idx insts = (outs, s') ==>
  ALL_DISTINCT (MAP (\i. i.inst_id) outs)
Proof
  map_every qid_spec_tac [`s'`, `outs`, `idx`, `s`] >>
  Induct_on `insts` >> simp[ao_transform_insts_supply_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `ao_alloc_fresh s` >>
  Cases_on `ao_transform_insts_supply dfg ra lbl targets r (SUC idx) insts` >>
  gvs[] >> drule ao_alloc_fresh_ids >> strip_tac >>
  `EVERY (\i. i.inst_id < r.irs_next_inst) insts` by
    (gvs[listTheory.EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> simp[]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) q')` by metis_tac[] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id)
     (ao_transform_inst dfg ra lbl idx targets q h)) /\
   EVERY (\id. id < r.irs_next_inst)
     (MAP (\i. i.inst_id) (ao_transform_inst dfg ra lbl idx targets q h))`
    by (mp_tac (Q.INST [`inst` |-> `h`, `fr` |-> `q`, `s'` |-> `r`]
      ao_transform_inst_fresh_ids) >> simp[]) >>
  simp[listTheory.ALL_DISTINCT_APPEND] >>
  gen_tac >> strip_tac >> strip_tac >>
  `MEM e (MAP (\i. i.inst_id) insts) \/ r.irs_next_inst <= e`
    by metis_tac[ao_transform_insts_supply_id_origin] >>
  `e = h.inst_id \/ s.irs_next_inst <= e`
    by metis_tac[ao_transform_inst_supply_id_origin] >>
  gvs[listTheory.EVERY_MEM, listTheory.MEM_MAP] >>
  metis_tac[arithmeticTheory.NOT_LESS, arithmeticTheory.LESS_TRANS]
QED

Theorem ao_transform_blocks_supply_frontier:
  ao_transform_blocks_supply dfg ra targets s bbs = (bbs', s') ==>
  s'.irs_next_inst = s.irs_next_inst + 2 * LENGTH (fn_insts_blocks bbs)
Proof
  map_every qid_spec_tac [`s'`, `bbs'`, `s`] >>
  Induct_on `bbs` >> simp[ao_transform_blocks_supply_def, fn_insts_blocks_def] >>
  rpt gen_tac >>
  simp[ao_transform_block_supply_def] >>
  Cases_on `ao_transform_insts_supply dfg ra h.bb_label targets s 0 h.bb_instructions` >>
  Cases_on `ao_transform_blocks_supply dfg ra targets r bbs` >>
  simp[] >> strip_tac >> gvs[] >>
  drule ao_transform_insts_supply_frontier >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem ao_transform_blocks_supply_id_origin:
  EVERY inst_wf (fn_insts_blocks bbs) /\
  ao_transform_blocks_supply dfg ra targets s bbs = (bbs', s') ==>
  !id. MEM id (MAP (\i. i.inst_id) (fn_insts_blocks bbs')) ==>
    MEM id (MAP (\i. i.inst_id) (fn_insts_blocks bbs)) \/ s.irs_next_inst <= id
Proof
  map_every qid_spec_tac [`s'`, `bbs'`, `s`] >>
  Induct_on `bbs` >> simp[ao_transform_blocks_supply_def, fn_insts_blocks_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[ao_transform_block_supply_def, pairTheory.pair_case_eq] >>
  simp[fn_insts_blocks_def] >> rpt strip_tac
  >- metis_tac[ao_transform_insts_supply_id_origin] >>
  first_x_assum drule >> disch_then (qspec_then `id` mp_tac) >>
  simp[] >> strip_tac >- simp[] >>
  drule ao_transform_insts_supply_frontier >> strip_tac >> gvs[] >>
  disj2_tac >> decide_tac
QED

Theorem ao_transform_blocks_supply_bound:
  EVERY inst_wf (fn_insts_blocks bbs) /\
  EVERY (\i. i.inst_id < s.irs_next_inst) (fn_insts_blocks bbs) /\
  ao_transform_blocks_supply dfg ra targets s bbs = (bbs', s') ==>
  EVERY (\i. i.inst_id < s'.irs_next_inst) (fn_insts_blocks bbs')
Proof
  map_every qid_spec_tac [`s'`, `bbs'`, `s`] >>
  Induct_on `bbs` >> simp[ao_transform_blocks_supply_def, fn_insts_blocks_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[ao_transform_block_supply_def, pairTheory.pair_case_eq] >>
  drule ao_transform_insts_supply_frontier >> strip_tac >>
  `EVERY (\i. i.inst_id < s1.irs_next_inst) (fn_insts_blocks bbs)` by
    (gvs[listTheory.EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> simp[]) >>
  `EVERY (\i. i.inst_id < s'.irs_next_inst) (fn_insts_blocks bbs'')`
    by metis_tac[] >>
  `EVERY (\i. i.inst_id < s1.irs_next_inst) insts`
    by metis_tac[ao_transform_insts_supply_bound] >>
  drule ao_transform_blocks_supply_frontier >> strip_tac >>
  gvs[fn_insts_blocks_def, listTheory.EVERY_MEM] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem ao_transform_blocks_supply_distinct:
  EVERY inst_wf (fn_insts_blocks bbs) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts_blocks bbs)) /\
  EVERY (\i. i.inst_id < s.irs_next_inst) (fn_insts_blocks bbs) /\
  ao_transform_blocks_supply dfg ra targets s bbs = (bbs', s') ==>
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts_blocks bbs'))
Proof
  map_every qid_spec_tac [`s'`, `bbs'`, `s`] >>
  Induct_on `bbs` >> simp[ao_transform_blocks_supply_def, fn_insts_blocks_def,
    listTheory.ALL_DISTINCT_APPEND] >>
  rpt gen_tac >> strip_tac >>
  gvs[ao_transform_block_supply_def, pairTheory.pair_case_eq] >>
  drule ao_transform_insts_supply_frontier >> strip_tac >>
  `EVERY (\i. i.inst_id < s1.irs_next_inst) (fn_insts_blocks bbs)` by
    (gvs[listTheory.EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> simp[]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts_blocks bbs''))`
    by metis_tac[] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) insts)`
    by metis_tac[ao_transform_insts_supply_distinct] >>
  `EVERY (\i. i.inst_id < s1.irs_next_inst) insts`
    by metis_tac[ao_transform_insts_supply_bound] >>
  simp[fn_insts_blocks_def, listTheory.ALL_DISTINCT_APPEND] >>
  gen_tac >> strip_tac >> strip_tac >>
  `MEM e (MAP (\i. i.inst_id) (fn_insts_blocks bbs)) \/ s1.irs_next_inst <= e`
    by metis_tac[ao_transform_blocks_supply_id_origin] >>
  `MEM e (MAP (\i. i.inst_id) h.bb_instructions) \/ s.irs_next_inst <= e`
    by metis_tac[ao_transform_insts_supply_id_origin] >>
  gvs[listTheory.EVERY_MEM, listTheory.MEM_MAP] >>
  metis_tac[arithmeticTheory.NOT_LESS, arithmeticTheory.LESS_TRANS]
QED

Theorem ao_transform_insts_supply_last:
  EVERY inst_wf insts /\ insts <> [] /\
  is_terminator (LAST insts).inst_opcode /\
  ao_transform_insts_supply dfg ra lbl targets s idx insts = (outs, s') ==>
  outs <> [] /\ LAST outs = ao_resolve_iszero_inst targets (LAST insts)
Proof
  map_every qid_spec_tac [`s'`, `outs`, `idx`, `s`] >>
  Induct_on `insts` >> simp[ao_transform_insts_supply_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `ao_alloc_fresh s` >>
  Cases_on `insts = []`
  >- (gvs[ao_transform_insts_supply_def] >>
      `ao_transform_inst dfg ra lbl idx targets q h =
        [ao_resolve_iszero_inst targets h]`
        by (irule ao_transform_inst_terminator >> simp[]) >> gvs[]) >>
  Cases_on `ao_transform_insts_supply dfg ra lbl targets r (SUC idx) insts` >>
  gvs[listTheory.LAST_DEF] >>
  `q' <> [] /\ LAST q' = ao_resolve_iszero_inst targets (LAST insts)`
    by metis_tac[] >>
  Cases_on `q'` >> gvs[listTheory.LAST_APPEND_CONS]
QED

Theorem ao_transform_block_supply_label:
  ao_transform_block_supply dfg ra targets s bb = (bb', s') ==>
  bb'.bb_label = bb.bb_label
Proof
  simp[ao_transform_block_supply_def, pairTheory.pair_case_eq] >>
  rpt strip_tac >> gvs[]
QED

Theorem ao_transform_block_supply_successors:
  EVERY inst_wf bb.bb_instructions /\ bb_well_formed bb /\
  EVERY (\p. EVERY (\op. get_label op = NONE) (SND p)) targets /\
  ao_transform_block_supply dfg ra targets s bb = (bb', s') ==>
  bb_succs bb' = bb_succs bb
Proof
  simp[ao_transform_block_supply_def, pairTheory.pair_case_eq] >>
  rpt strip_tac >> gvs[bb_well_formed_def] >>
  drule_all ao_transform_insts_supply_last >> strip_tac >>
  simp[bb_succs_def] >>
  Cases_on `bb.bb_instructions` >> gvs[] >>
  Cases_on `insts` >> gvs[ao_resolve_iszero_inst_successors]
QED

Theorem ao_transform_blocks_supply_labels:
  ao_transform_blocks_supply dfg ra targets s bbs = (bbs', s') ==>
  MAP (\bb. bb.bb_label) bbs' = MAP (\bb. bb.bb_label) bbs
Proof
  map_every qid_spec_tac [`s'`, `bbs'`, `s`] >>
  Induct_on `bbs` >> simp[ao_transform_blocks_supply_def] >>
  rpt gen_tac >>
  Cases_on `ao_transform_block_supply dfg ra targets s h` >>
  Cases_on `ao_transform_blocks_supply dfg ra targets r bbs` >>
  simp[] >> strip_tac >> gvs[] >>
  drule ao_transform_block_supply_label >> strip_tac >> simp[] >>
  first_x_assum irule >> simp[] >> goal_assum drule
QED

Theorem ao_transform_blocks_supply_successors:
  EVERY inst_wf (fn_insts_blocks bbs) /\ EVERY bb_well_formed bbs /\
  EVERY (\p. EVERY (\op. get_label op = NONE) (SND p)) targets /\
  ao_transform_blocks_supply dfg ra targets s bbs = (bbs', s') ==>
  MAP bb_succs bbs' = MAP bb_succs bbs
Proof
  map_every qid_spec_tac [`s'`, `bbs'`, `s`] >>
  Induct_on `bbs` >> simp[ao_transform_blocks_supply_def, fn_insts_blocks_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `ao_transform_block_supply dfg ra targets s h` >>
  Cases_on `ao_transform_blocks_supply dfg ra targets r bbs` >>
  gvs[] >>
  `bb_succs q = bb_succs h` by metis_tac[ao_transform_block_supply_successors] >>
  simp[] >> first_x_assum irule >> simp[] >> goal_assum drule
QED

Theorem ao_bb_cons_well_formed:
  tail <> [] ==>
  (bb_well_formed (bb with bb_instructions := h::tail) <=>
   bb_well_formed (bb with bb_instructions := tail) /\
   ~is_terminator h.inst_opcode /\
   (h.inst_opcode = PHI \/ EVERY (\i. i.inst_opcode <> PHI) tail))
Proof
  strip_tac >> simp[bb_well_formed_def, listTheory.LAST_DEF] >>
  eq_tac
  >- (strip_tac >> rpt conj_tac
      >- simp[]
      >- (rpt strip_tac >>
          qpat_x_assum `!i. _ ==> i = _`
            (qspec_then `SUC i` mp_tac) >> simp[])
      >- (rpt strip_tac >>
          first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[])
      >- (strip_tac >>
          qpat_x_assum `!i. _ ==> i = _` (qspec_then `0` mp_tac) >>
          Cases_on `tail` >> gvs[]) >>
      Cases_on `h.inst_opcode = PHI` >> simp[listTheory.EVERY_EL] >>
      rpt strip_tac >>
      qpat_x_assum `!i j. _` (qspecl_then [`0`, `SUC n`] mp_tac) >> simp[]) >>
  strip_tac >>
  (simp[] >> conj_tac
   >- (gen_tac >> Cases_on `i` >> simp[] >> rpt strip_tac >> gvs[] >>
       qpat_x_assum `!i. _ ==> i = _` (qspec_then `n` mp_tac) >>
       Cases_on `tail` >> gvs[]) >>
   rpt gen_tac >> Cases_on `i` >> Cases_on `j` >> simp[] >>
   rpt strip_tac >> gvs[listTheory.EVERY_EL] >> metis_tac[])
QED

Theorem ao_bb_prefix_well_formed:
  bb_well_formed (bb with bb_instructions := tail) /\
  EVERY (\i. ~is_terminator i.inst_opcode) pre /\
  (EVERY (\i. i.inst_opcode = PHI) pre \/
   EVERY (\i. i.inst_opcode <> PHI) (pre ++ tail)) ==>
  bb_well_formed (bb with bb_instructions := pre ++ tail)
Proof
  Induct_on `pre` >> simp[] >> rpt strip_tac >>
  `tail <> []` by gvs[bb_well_formed_def] >>
  `bb_well_formed (bb with bb_instructions := pre ++ tail)`
    by (first_x_assum irule >> simp[]) >>
  `pre ++ tail <> []` by simp[] >>
  simp[ao_bb_cons_well_formed] >> gvs[]
QED

Theorem ao_transform_insts_supply_nonphi:
  EVERY inst_wf insts /\ EVERY (\i. i.inst_opcode <> PHI) insts /\
  ao_transform_insts_supply dfg ra lbl targets s idx insts = (outs,s') ==>
  EVERY (\i. i.inst_opcode <> PHI) outs
Proof
  map_every qid_spec_tac [`s'`, `outs`, `idx`, `s`] >>
  Induct_on `insts` >> simp[ao_transform_insts_supply_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[pairTheory.pair_case_eq] >>
  simp[] >> conj_tac
  >- (irule ao_transform_inst_nonphi >> simp[]) >>
  first_x_assum irule >> simp[] >> goal_assum drule
QED

Theorem ao_transform_insts_supply_well_formed:
  EVERY inst_wf insts /\ bb_well_formed (bb with bb_instructions := insts) /\
  ao_transform_insts_supply dfg ra lbl targets s idx insts = (outs,s') ==>
  bb_well_formed (bb with bb_instructions := outs)
Proof
  map_every qid_spec_tac [`s'`, `outs`, `idx`, `s`] >>
  Induct_on `insts`
  >- simp[bb_well_formed_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `ao_alloc_fresh s` >>
  Cases_on `insts = []`
  >- (gvs[ao_transform_insts_supply_def, bb_well_formed_def] >>
      `ao_transform_inst dfg ra lbl idx targets q h =
        [ao_resolve_iszero_inst targets h]`
        by (irule ao_transform_inst_terminator >> simp[]) >>
      gvs[bb_well_formed_def, ao_resolve_iszero_inst_structure]) >>
  gvs[ao_bb_cons_well_formed, ao_transform_insts_supply_def,
      pairTheory.pair_case_eq] >>
  (`bb_well_formed (bb with bb_instructions := outs')` by metis_tac[] >>
   irule ao_bb_prefix_well_formed >> simp[] >>
   conj_tac
   >- (irule ao_transform_inst_nonterminator >> simp[]) >>
   Cases_on `h.inst_opcode = PHI` >>
   gvs[ao_transform_inst_phi, ao_resolve_iszero_inst_structure] >>
   metis_tac[ao_transform_inst_nonphi, ao_transform_insts_supply_nonphi])
QED

Theorem ao_transform_block_supply_well_formed:
  EVERY inst_wf bb.bb_instructions /\ bb_well_formed bb /\
  ao_transform_block_supply dfg ra targets s bb = (bb',s') ==>
  bb_well_formed bb'
Proof
  simp[ao_transform_block_supply_def, pairTheory.pair_case_eq] >>
  rpt strip_tac >> gvs[] >>
  irule ao_transform_insts_supply_well_formed >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem ao_transform_blocks_supply_well_formed:
  EVERY inst_wf (fn_insts_blocks bbs) /\ EVERY bb_well_formed bbs /\
  ao_transform_blocks_supply dfg ra targets s bbs = (bbs',s') ==>
  EVERY bb_well_formed bbs'
Proof
  map_every qid_spec_tac [`s'`, `bbs'`, `s`] >>
  Induct_on `bbs` >> simp[ao_transform_blocks_supply_def, fn_insts_blocks_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `ao_transform_block_supply dfg ra targets s h` >>
  Cases_on `ao_transform_blocks_supply dfg ra targets r bbs` >>
  gvs[] >> conj_tac
  >- metis_tac[ao_transform_block_supply_well_formed] >>
  first_x_assum irule >> simp[] >> goal_assum drule
QED

val _ = List.app (fn th =>
  if null (hyp th) then () else raise Fail "residual hypotheses in AO lifting")
  [ao_transform_insts_supply_bound, ao_transform_insts_supply_distinct,
   ao_transform_blocks_supply_frontier, ao_transform_blocks_supply_id_origin,
   ao_transform_blocks_supply_bound, ao_transform_blocks_supply_distinct,
   ao_transform_insts_supply_last, ao_transform_block_supply_label,
   ao_transform_block_supply_successors, ao_transform_blocks_supply_labels,
   ao_transform_blocks_supply_successors,
   ao_bb_cons_well_formed, ao_bb_prefix_well_formed,
   ao_transform_insts_supply_nonphi, ao_transform_insts_supply_well_formed,
   ao_transform_block_supply_well_formed, ao_transform_blocks_supply_well_formed];

Theorem ao_flip_comparison_comparator:
  is_comparator opc ==> is_comparator (flip_comparison_opcode opc)
Proof
  Cases_on `opc` >> simp[is_comparator_def, flip_comparison_opcode_def]
QED

Theorem ao_cmp_flip_scan_provenance:
  EVERY (\i. MEM i (fn_insts fn)) insts /\
  ao_cmp_flip_scan (dfg_build_function fn) insts = (flips,removes,inserts) ==>
  EVERY (\(id,opc,w,op).
    is_comparator opc /\
    ?i. MEM i (fn_insts fn) /\ i.inst_id = id /\ is_comparator i.inst_opcode) flips /\
  EVERY (\id. ?i. MEM i (fn_insts fn) /\ i.inst_id = id /\
                  i.inst_opcode = ISZERO) removes /\
  EVERY (\(id,v,c). ?i. MEM i (fn_insts fn) /\ i.inst_id = id /\
                        i.inst_opcode = ASSERT) inserts
Proof
  map_every qid_spec_tac [`inserts`, `removes`, `flips`] >>
  Induct_on `insts`
  >- simp[ao_cmp_flip_scan_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `ao_cmp_flip_scan (dfg_build_function fn) insts` >>
  PairCases_on `r` >>
  gvs[] >>
  gvs[Once ao_cmp_flip_scan_def, AllCaseEqs()] >>
  pairarg_tac >> gvs[AllCaseEqs()] >>
  `MEM (HD (dfg_get_uses (dfg_build_function fn) out_var)) (fn_insts fn)` by
    (irule (cj 1 dfg_build_function_uses_sound) >>
     qexists `out_var` >>
     Cases_on `dfg_get_uses (dfg_build_function fn) out_var` >> gvs[]) >>
  simp[ao_flip_comparison_comparator] >> metis_tac[]
QED

Theorem ao_fn_inst_ids_distinct_alt:
  fn_inst_ids_distinct fn <=> ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))
Proof
  `!bbs. MAP (\i. i.inst_id) (fn_insts_blocks bbs) =
    FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs)` by
    (Induct >> simp[fn_insts_blocks_def]) >>
  simp[fn_inst_ids_distinct_def, fn_insts_def]
QED

Theorem ao_fn_inst_id_injective:
  fn_inst_ids_distinct fn /\ MEM x (fn_insts fn) /\ MEM y (fn_insts fn) /\
  x.inst_id = y.inst_id ==> x = y
Proof
  simp[ao_fn_inst_ids_distinct_alt, fn_insts_def] >> strip_tac >>
  gvs[listTheory.MEM_EL] >>
  `n < LENGTH (MAP (\i. i.inst_id) (fn_insts_blocks fn.fn_blocks)) /\
   n' < LENGTH (MAP (\i. i.inst_id) (fn_insts_blocks fn.fn_blocks))` by simp[] >>
  `EL n (MAP (\i. i.inst_id) (fn_insts_blocks fn.fn_blocks)) =
   EL n' (MAP (\i. i.inst_id) (fn_insts_blocks fn.fn_blocks))` by simp[listTheory.EL_MAP] >>
  `n = n'` by metis_tac[listTheory.ALL_DISTINCT_EL_IMP] >> gvs[]
QED

Theorem ao_cmp_flip_scan_lookup_safety:
  fn_inst_ids_distinct fn /\
  ao_cmp_flip_scan (dfg_build_function fn) (fn_insts fn) = (flips,removes,inserts) ==>
  (!i opc w op. MEM i (fn_insts fn) /\
     ALOOKUP flips i.inst_id = SOME (opc,w,op) ==>
     is_comparator i.inst_opcode /\ is_comparator opc) /\
  (!i. MEM i (fn_insts fn) /\ MEM i.inst_id removes ==> i.inst_opcode = ISZERO) /\
  (!i v c. MEM i (fn_insts fn) /\
     ALOOKUP inserts i.inst_id = SOME (v,c) ==> i.inst_opcode = ASSERT)
Proof
  strip_tac >>
  `EVERY (\i. MEM i (fn_insts fn)) (fn_insts fn)` by simp[listTheory.EVERY_MEM] >>
  drule_all ao_cmp_flip_scan_provenance >>
  simp[listTheory.EVERY_MEM, pairTheory.FORALL_PROD] >> strip_tac >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  imp_res_tac alistTheory.ALOOKUP_MEM >>
  metis_tac[ao_fn_inst_id_injective]
QED

val _ = List.app (fn th =>
  if null (hyp th) then () else raise Fail "residual hypotheses in AO scan")
  [ao_flip_comparison_comparator, ao_cmp_flip_scan_provenance,
   ao_fn_inst_id_injective, ao_cmp_flip_scan_lookup_safety];

Theorem ao_name_inserts_supply_numeric:
  ao_name_inserts_supply s requests = (named,s') ==>
  s'.irs_next_inst = s.irs_next_inst + LENGTH requests /\
  ALL_DISTINCT (MAP (\(a,out,id,v). id) named) /\
  EVERY (\(a,out,id,v). s.irs_next_inst <= id /\ id < s'.irs_next_inst) named /\
  MAP FST named = MAP FST requests
Proof
  map_every qid_spec_tac [`s'`, `named`, `s`] >>
  Induct_on `requests`
  >- simp[ao_name_inserts_supply_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[ao_name_inserts_supply_def, irSupplyTheory.fresh_inst_id_def,
       irSupplyTheory.fresh_ir_var_def, pairTheory.pair_case_eq] >>
  rpt strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  gvs[listTheory.EVERY_MEM, listTheory.MEM_MAP, pairTheory.FORALL_PROD] >>
  rpt strip_tac >> res_tac >> gvs[]
QED

Theorem ao_named_insert_id_injective:
  ALL_DISTINCT (MAP (\(a,out,id,v). id) named) /\
  MEM (a,out,id,v) named /\ MEM (b,out',id,v') named ==> a = b
Proof
  Induct_on `named` >> simp[] >> gen_tac >> PairCases_on `h` >>
  simp[listTheory.MEM_MAP, pairTheory.EXISTS_PROD] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ao_name_inserts_supply_lookup_unique:
  ao_name_inserts_supply s requests = (named,s') /\
  ALOOKUP named a = SOME (out,id,v) /\
  ALOOKUP named b = SOME (out',id,v') ==> a = b
Proof
  strip_tac >> drule ao_name_inserts_supply_numeric >> strip_tac >>
  imp_res_tac alistTheory.ALOOKUP_MEM >>
  metis_tac[ao_named_insert_id_injective]
QED

Theorem ao_name_inserts_supply_lookup_bound:
  ao_name_inserts_supply s requests = (named,s') /\
  ALOOKUP named a = SOME (out,id,v) ==>
  s.irs_next_inst <= id /\ id < s'.irs_next_inst
Proof
  strip_tac >> drule ao_name_inserts_supply_numeric >> strip_tac >>
  imp_res_tac alistTheory.ALOOKUP_MEM >>
  gvs[listTheory.EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]
QED

Theorem ao_name_inserts_supply_lookup_key:
  ao_name_inserts_supply s requests = (named,s') /\
  ALOOKUP named a = SOME (out,id,v) ==> MEM a (MAP FST requests)
Proof
  strip_tac >> drule ao_name_inserts_supply_numeric >> strip_tac >>
  imp_res_tac alistTheory.ALOOKUP_MEM >>
  metis_tac[listTheory.MEM_MAP, pairTheory.FST]
QED

Theorem ao_cmp_flip_apply_inst_ids:
  MAP (\i. i.inst_id) (ao_cmp_flip_apply_inst flips removes named inst) =
  if IS_SOME (ALOOKUP flips inst.inst_id) \/ MEM inst.inst_id removes then [inst.inst_id]
  else case ALOOKUP named inst.inst_id of
         NONE => [inst.inst_id]
       | SOME (out,id,v) => [id; inst.inst_id]
Proof
  Cases_on `ALOOKUP flips inst.inst_id`
  >- (simp[ao_cmp_flip_apply_inst_def] >>
      Cases_on `MEM inst.inst_id removes` >> simp[] >>
      Cases_on `ALOOKUP named inst.inst_id` >> simp[] >>
      PairCases_on `x` >> simp[]) >>
  PairCases_on `x` >> simp[ao_cmp_flip_apply_inst_def]
QED

Theorem ao_cmp_flip_apply_inst_structure:
  (!opc w op. ALOOKUP flips inst.inst_id = SOME (opc,w,op) ==>
    is_comparator inst.inst_opcode /\ is_comparator opc) /\
  (MEM inst.inst_id removes ==> inst.inst_opcode = ISZERO) /\
  (!out id v. ALOOKUP named inst.inst_id = SOME (out,id,v) ==> inst.inst_opcode = ASSERT) ==>
  ao_cmp_flip_apply_inst flips removes named inst <> [] /\
  EVERY (\j. (j.inst_opcode = PHI <=> inst.inst_opcode = PHI) /\
             (is_terminator j.inst_opcode = is_terminator inst.inst_opcode) /\
             get_successors j = get_successors inst)
    (ao_cmp_flip_apply_inst flips removes named inst) /\
  (is_terminator inst.inst_opcode ==> ao_cmp_flip_apply_inst flips removes named inst = [inst])
Proof
  strip_tac >>
  Cases_on `ALOOKUP flips inst.inst_id`
  >- (simp[ao_cmp_flip_apply_inst_def] >>
      Cases_on `MEM inst.inst_id removes` >> gvs[]
      >- simp[is_terminator_def, get_successors_def] >>
      Cases_on `ALOOKUP named inst.inst_id` >> simp[] >>
      PairCases_on `x` >> gvs[] >>
      simp[is_terminator_def, get_successors_def]) >>
  PairCases_on `x` >> gvs[] >>
  simp[ao_cmp_flip_apply_inst_def] >>
  gvs[is_comparator_def] >> simp[is_terminator_def, get_successors_def]
QED

Theorem ao_expand_insts_well_formed:
  (!i. MEM i insts ==>
    f i <> [] /\
    EVERY (\j. (j.inst_opcode = PHI <=> i.inst_opcode = PHI) /\
               (is_terminator j.inst_opcode = is_terminator i.inst_opcode)) (f i) /\
    (is_terminator i.inst_opcode ==> f i = [i])) /\
  bb_well_formed (bb with bb_instructions := insts) ==>
  bb_well_formed (bb with bb_instructions := FLAT (MAP f insts))
Proof
  Induct_on `insts`
  >- simp[bb_well_formed_def] >>
  rpt strip_tac >>
  Cases_on `insts = []`
  >- (gvs[bb_well_formed_def] >> metis_tac[]) >>
  gvs[ao_bb_cons_well_formed] >>
  (`bb_well_formed (bb with bb_instructions := FLAT (MAP f insts))` by metis_tac[] >>
   simp[] >> irule ao_bb_prefix_well_formed >> simp[] >>
   conj_tac
   >- (gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
   Cases_on `h.inst_opcode = PHI`
   >- (disj1_tac >> gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
   disj2_tac >>
   gvs[listTheory.EVERY_FLAT, listTheory.EVERY_MAP, listTheory.EVERY_MEM] >>
   metis_tac[])
QED

Theorem ao_cmp_flip_apply_inst_id_origin:
  MEM j (ao_cmp_flip_apply_inst flips removes named i) ==>
  j.inst_id = i.inst_id \/
  ?out v. ALOOKUP named i.inst_id = SOME (out,j.inst_id,v)
Proof
  Cases_on `ALOOKUP flips i.inst_id`
  >- (Cases_on `MEM i.inst_id removes`
      >- simp[ao_cmp_flip_apply_inst_def] >>
      Cases_on `ALOOKUP named i.inst_id`
      >- simp[ao_cmp_flip_apply_inst_def] >>
      PairCases_on `x` >>
      simp[ao_cmp_flip_apply_inst_def] >> rpt strip_tac >> gvs[]) >>
  PairCases_on `x` >> simp[ao_cmp_flip_apply_inst_def]
QED

Theorem ao_cmp_flip_apply_insts_distinct:
  ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\
  EVERY (\i. i.inst_id < n) insts /\
  ALL_DISTINCT (MAP (\(a,out,id,v). id) named) /\
  EVERY (\(a,out,id,v). n <= id) named ==>
  ALL_DISTINCT (MAP (\i. i.inst_id)
    (FLAT (MAP (ao_cmp_flip_apply_inst flips removes named) insts)))
Proof
  Induct_on `insts` >> simp[] >> rpt strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id)
    (FLAT (MAP (ao_cmp_flip_apply_inst flips removes named) insts)))` by metis_tac[] >>
  simp[ao_cmp_flip_apply_inst_ids, listTheory.ALL_DISTINCT_APPEND] >>
  `!i out id v. ALOOKUP named i = SOME (out,id,v) ==> n <= id` by
    (rpt strip_tac >> imp_res_tac alistTheory.ALOOKUP_MEM >>
     gvs[listTheory.EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]) >>
  `!a out id v b out' v'.
    ALOOKUP named a = SOME (out,id,v) /\
    ALOOKUP named b = SOME (out',id,v') ==> a = b` by
    (rpt strip_tac >> imp_res_tac alistTheory.ALOOKUP_MEM >>
     metis_tac[ao_named_insert_id_injective]) >>
  Cases_on `ALOOKUP named h.inst_id` >> simp[] >>
  rpt pairarg_tac >> gvs[] >>
  Cases_on `IS_SOME (ALOOKUP flips h.inst_id) \/ MEM h.inst_id removes` >> simp[] >>
  gvs[listTheory.EVERY_MEM, listTheory.MEM_MAP] >>
  simp[listTheory.MEM_MAP, listTheory.MEM_FLAT] >>
  rpt strip_tac >> gvs[] >>
  spose_not_then strip_assume_tac >> gvs[] >>
  imp_res_tac ao_cmp_flip_apply_inst_id_origin >> gvs[] >>
  res_tac >> gvs[] >> PairCases_on `x` >> gvs[] >>
  res_tac >> gvs[] >> metis_tac[]
QED

Theorem ao_expand_insts_last:
  insts <> [] /\ is_terminator (LAST insts).inst_opcode /\
  (!i. MEM i insts ==> f i <> [] /\ (is_terminator i.inst_opcode ==> f i = [i])) ==>
  FLAT (MAP f insts) <> [] /\ LAST (FLAT (MAP f insts)) = LAST insts
Proof
  Induct_on `insts` >> simp[] >> rpt strip_tac >>
  Cases_on `insts = []`
  >- (gvs[] >> metis_tac[]) >>
  gvs[listTheory.LAST_DEF] >>
  `FLAT (MAP f insts) <> [] /\ LAST (FLAT (MAP f insts)) = LAST insts` by metis_tac[] >>
  Cases_on `FLAT (MAP f insts)` >> gvs[listTheory.LAST_APPEND_CONS]
QED

Theorem ao_cmp_flip_apply_block_structure:
  bb_well_formed bb /\
  (!i. MEM i bb.bb_instructions ==>
    (!opc w op. ALOOKUP flips i.inst_id = SOME (opc,w,op) ==>
      is_comparator i.inst_opcode /\ is_comparator opc) /\
    (MEM i.inst_id removes ==> i.inst_opcode = ISZERO) /\
    (!out id v. ALOOKUP named i.inst_id = SOME (out,id,v) ==> i.inst_opcode = ASSERT)) ==>
  bb_well_formed (bb with bb_instructions :=
    FLAT (MAP (ao_cmp_flip_apply_inst flips removes named) bb.bb_instructions)) /\
  bb_succs (bb with bb_instructions :=
    FLAT (MAP (ao_cmp_flip_apply_inst flips removes named) bb.bb_instructions)) = bb_succs bb
Proof
  strip_tac >>
  `!i. MEM i bb.bb_instructions ==>
    ao_cmp_flip_apply_inst flips removes named i <> [] /\
    EVERY (\j. (j.inst_opcode = PHI <=> i.inst_opcode = PHI) /\
      (is_terminator j.inst_opcode = is_terminator i.inst_opcode) /\
      get_successors j = get_successors i) (ao_cmp_flip_apply_inst flips removes named i) /\
    (is_terminator i.inst_opcode ==> ao_cmp_flip_apply_inst flips removes named i = [i])`
    by (gen_tac >> disch_tac >>
        first_x_assum drule >> strip_tac >>
        irule ao_cmp_flip_apply_inst_structure >> simp[]) >>
  conj_tac
  >- (irule ao_expand_insts_well_formed >> simp[] >>
      gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `bb.bb_instructions <> [] /\ is_terminator (LAST bb.bb_instructions).inst_opcode`
    by gvs[bb_well_formed_def] >>
  `FLAT (MAP (ao_cmp_flip_apply_inst flips removes named) bb.bb_instructions) <> [] /\
   LAST (FLAT (MAP (ao_cmp_flip_apply_inst flips removes named) bb.bb_instructions)) =
   LAST bb.bb_instructions` by
    (irule ao_expand_insts_last >> simp[] >> metis_tac[]) >>
  simp[bb_succs_def] >>
  Cases_on `bb.bb_instructions` >> gvs[] >>
  Cases_on `FLAT (MAP (ao_cmp_flip_apply_inst flips removes named) (h::t))` >> gvs[]
QED

Theorem ao_mem_fn_insts_blocks:
  MEM i (fn_insts_blocks bbs) <=> ?bb. MEM bb bbs /\ MEM i bb.bb_instructions
Proof
  Induct_on `bbs` >> simp[fn_insts_blocks_def] >> metis_tac[]
QED

Theorem ao_cmp_flip_apply_fn_well_formed:
  wf_function fn /\ EVERY (\i. i.inst_id < n) (fn_insts fn) /\
  ALL_DISTINCT (MAP (\(a,out,id,v). id) named) /\
  EVERY (\(a,out,id,v). n <= id) named /\
  (!i. MEM i (fn_insts fn) ==>
    (!opc w op. ALOOKUP flips i.inst_id = SOME (opc,w,op) ==>
      is_comparator i.inst_opcode /\ is_comparator opc) /\
    (MEM i.inst_id removes ==> i.inst_opcode = ISZERO) /\
    (!out id v. ALOOKUP named i.inst_id = SOME (out,id,v) ==> i.inst_opcode = ASSERT)) ==>
  wf_function (ao_cmp_flip_apply_fn flips removes named fn)
Proof
  strip_tac >>
  `!bb. MEM bb fn.fn_blocks ==>
    bb_well_formed (bb with bb_instructions :=
      FLAT (MAP (ao_cmp_flip_apply_inst flips removes named) bb.bb_instructions)) /\
    bb_succs (bb with bb_instructions :=
      FLAT (MAP (ao_cmp_flip_apply_inst flips removes named) bb.bb_instructions)) = bb_succs bb` by
    (gen_tac >> disch_tac >> irule ao_cmp_flip_apply_block_structure >>
     reverse conj_tac >- metis_tac[wf_function_def] >>
     gen_tac >> disch_tac >> first_x_assum irule >>
     simp[fn_insts_def, fn_insts_blocks_def] >>
     simp[ao_mem_fn_insts_blocks] >> metis_tac[]) >>
  gvs[wf_function_def, fn_labels_def, fn_has_entry_def] >>
  simp[ao_cmp_flip_apply_fn_def, wf_function_def, fn_labels_def,
       fn_has_entry_def, listTheory.MAP_MAP_o, combinTheory.o_DEF,
       listTheory.MEM_MAP] >>
  conj_tac >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  conj_tac
  >- (gvs[fn_succs_closed_def, fn_labels_def] >>
      simp[listTheory.MEM_MAP, listTheory.MAP_MAP_o, combinTheory.o_DEF] >>
      rpt strip_tac >> gvs[] >>
      `MEM succ (MAP (\bb. bb.bb_label) fn.fn_blocks)` by metis_tac[] >>
      gvs[listTheory.MEM_MAP] >>
      qexists `bb with bb_instructions :=
        FLAT (MAP (ao_cmp_flip_apply_inst flips removes named) bb.bb_instructions)` >>
      simp[] >> metis_tac[]) >>
  `!bbs. fn_insts_blocks (MAP (\bb. bb with bb_instructions :=
      FLAT (MAP (ao_cmp_flip_apply_inst flips removes named) bb.bb_instructions)) bbs) =
    FLAT (MAP (ao_cmp_flip_apply_inst flips removes named) (fn_insts_blocks bbs))` by
    (Induct >> simp[fn_insts_blocks_def, listTheory.MAP_APPEND,
                   listTheory.FLAT_APPEND]) >>
  gvs[ao_fn_inst_ids_distinct_alt, fn_insts_def] >>
  irule ao_cmp_flip_apply_insts_distinct >> simp[] >> metis_tac[]
QED

Theorem ao_cmp_flip_function_supply_well_formed:
  wf_function fn /\ EVERY (\i. i.inst_id < s.irs_next_inst) (fn_insts fn) /\
  ao_cmp_flip_function_supply (dfg_build_function fn) s fn = (fn',s') ==>
  wf_function fn'
Proof
  strip_tac >>
  Cases_on `ao_cmp_flip_scan (dfg_build_function fn) (fn_insts fn)` >>
  PairCases_on `r` >>
  gvs[ao_cmp_flip_function_supply_def] >>
  Cases_on `NULL q` >> gvs[] >>
  Cases_on `ao_name_inserts_supply s r1` >> gvs[] >>
  rename1 `ao_name_inserts_supply s inserts = (named,s')` >>
  drule ao_name_inserts_supply_numeric >> strip_tac >>
  `fn_inst_ids_distinct fn` by gvs[wf_function_def] >>
  drule_all ao_cmp_flip_scan_lookup_safety >> strip_tac >>
  `EVERY (\i. MEM i (fn_insts fn)) (fn_insts fn)` by simp[listTheory.EVERY_MEM] >>
  drule_all ao_cmp_flip_scan_provenance >> strip_tac >>
  irule ao_cmp_flip_apply_fn_well_formed >>
  reverse conj_tac
  >- (simp[] >> qexists `s.irs_next_inst` >>
      gvs[listTheory.EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]) >>
  gen_tac >> disch_tac >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >> drule_all ao_name_inserts_supply_lookup_key >>
  simp[listTheory.MEM_MAP, pairTheory.EXISTS_PROD] >> strip_tac >>
  gvs[listTheory.EVERY_MEM, pairTheory.FORALL_PROD] >>
  metis_tac[ao_fn_inst_id_injective]
QED

val _ = List.app (fn th =>
  if null (hyp th) then () else raise Fail "residual hypotheses in AO application")
  [ao_fn_inst_ids_distinct_alt, ao_name_inserts_supply_numeric,
   ao_named_insert_id_injective, ao_name_inserts_supply_lookup_unique,
   ao_name_inserts_supply_lookup_bound, ao_name_inserts_supply_lookup_key,
   ao_cmp_flip_apply_inst_ids, ao_cmp_flip_apply_inst_structure,
   ao_expand_insts_well_formed, ao_cmp_flip_apply_inst_id_origin,
   ao_cmp_flip_apply_insts_distinct, ao_expand_insts_last,
   ao_cmp_flip_apply_block_structure, ao_mem_fn_insts_blocks,
   ao_cmp_flip_apply_fn_well_formed, ao_cmp_flip_function_supply_well_formed];

Theorem ao_preserves_wf_function_proof:
  !sup fn fn' sup'.
    wf_function fn /\
    fn_inst_wf fn /\
    EVERY label_positions_ok (fn_insts fn) /\
    ir_supply_inst_ok sup /\
    ir_supply_covers_fn sup fn /\
    ao_transform_function_supply sup fn = (fn', sup') ==>
    wf_function fn'
Proof
  cheat
QED
