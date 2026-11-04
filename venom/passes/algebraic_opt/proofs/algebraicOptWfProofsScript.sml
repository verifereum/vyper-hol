Theory algebraicOptWfProofs
Ancestors
  algebraicOptDefs passSharedDefs venomInst venomWf venomFnScheduleRunner unitShapeDefs

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
  LENGTH xs = 1 ==>
  (MAP f xs = [a] <=> EVERY (\x. f x = a) xs)
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
