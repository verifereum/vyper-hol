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

Theorem ao_opt_comparator_empty_probe[local]:
  ao_opt_comparator dfg ra lbl idx fr (inst with inst_operands := []) = ARB
Proof
  simp[ao_opt_comparator_def]
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
