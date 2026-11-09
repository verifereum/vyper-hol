Theory concretizePtrZeroPlacements
Ancestors concretizeMemLocDefs staticLayoutAllocatorProofs words list finite_map

Theorem ptr_first_fit_zero:
  !rs. first_fit_pos rs 0 0 = 0
Proof
  Induct >> simp[Once first_fit_pos_def] >>
  gen_tac >> PairCases_on `h` >> simp[first_fit_pos_def]
QED

Theorem ptr_allocate_one_zero:
  allocate_one rs 0 = (0,(0,0)::rs)
Proof
  simp[allocate_one_def, ptr_first_fit_zero]
QED

Theorem ptr_checked_scan_zero:
  !rs. checked_first_fit_scan rs 0 0 = SOME 0
Proof
  Induct >> simp[Once checked_first_fit_scan_def] >>
  gen_tac >> PairCases_on `h` >> simp[checked_first_fit_scan_def, arithmeticTheory.GREATER_EQ, dimword_def]
QED

Theorem ptr_checked_fit_zero:
  checked_first_fit occupied 0 = SOME p ==> p = 0
Proof
  simp[checked_first_fit_def, ptr_checked_scan_zero] >>
  IF_CASES_TAC >> simp[]
QED

Theorem ptr_complete_aux_zero:
  !insts positions occupied completed a.
  (!inst. MEM inst insts /\ inst.inst_opcode = ALLOCA /\
    Allocation inst.inst_id = a ==> exact_static_alloca_size inst = SOME 0) /\
  (!p. FLOOKUP positions a = SOME p ==> p = 0) /\
  complete_alloc_positions_aux insts positions occupied = SOME completed ==>
  !p. FLOOKUP completed a = SOME p ==> p = 0
Proof
  Induct >> simp[complete_alloc_positions_aux_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = ALLOCA` >>
  fs[CaseEq "option"] >>
  qpat_x_assum `!positions occupied completed a. _`
    (drule_at (Pat `complete_alloc_positions_aux _ _ _ = SOME _`)) >>
  disch_then (qspec_then `a` assume_tac) >>
  Cases_on `Allocation h.inst_id = a` >>
  gvs[FLOOKUP_UPDATE] >> metis_tac[ptr_checked_fit_zero]
QED

Theorem ptr_static_zero_instruction:
  static_alloca_items fn = SOME items /\ MEM (a,0) items /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  Allocation inst.inst_id = a ==> exact_static_alloca_size inst = SOME 0
Proof
  rpt strip_tac >>
  drule static_alloca_items_MEM >>
  disch_then (qspec_then `(a,0)` assume_tac) >>
  drule_all static_alloca_items_ALLOCA_exact >> strip_tac >>
  rename1 `inst.inst_operands = [Lit szword]` >>
  `w2n szword = 0` by
    metis_tac[static_alloca_items_exact_key_size_unique] >>
  gvs[exact_static_alloca_def, AllCaseEqs()]
QED

Theorem ptr_merge_forced_empty:
  !items positions. merge_forced_positions items FEMPTY positions = SOME positions
Proof
  Induct >> simp[merge_forced_positions_def] >>
  gen_tac >> PairCases_on `h` >> simp[merge_forced_positions_def]
QED

Theorem ptr_complete_imports_zero:
  static_alloca_items fn = SOME items /\ MEM (a,0) items /\
  (!p. FLOOKUP positions a = SOME p ==> p = 0) /\
  complete_alloc_positions_with_imports items FEMPTY reserved imported fn positions =
    SOME completed ==>
  !p. FLOOKUP completed a = SOME p ==> p = 0
Proof
  simp[complete_alloc_positions_with_imports_def, ptr_merge_forced_empty] >>
  rpt strip_tac >> gvs[CaseEq "option", CaseEq "bool"] >>
  drule_at (Pat `complete_alloc_positions_aux _ _ _ = SOME _`) ptr_complete_aux_zero >>
  disch_then (qspec_then `a` assume_tac) >>
  metis_tac[ptr_static_zero_instruction]
QED

Theorem ptr_complete_items_zero:
  static_alloca_items fn = SOME items /\ MEM (a,0) items /\
  (!p. FLOOKUP positions a = SOME p ==> p = 0) /\
  complete_alloc_positions_with_items items FEMPTY reserved fn positions = SOME completed ==>
  !p. FLOOKUP completed a = SOME p ==> p = 0
Proof
  simp[complete_alloc_positions_with_items_def, ptr_merge_forced_empty] >>
  rpt strip_tac >> gvs[CaseEq "option", CaseEq "bool"] >>
  drule_at (Pat `complete_alloc_positions_aux _ _ _ = SOME _`) ptr_complete_aux_zero >>
  disch_then (qspec_then `a` assume_tac) >>
  metis_tac[ptr_static_zero_instruction]
QED

Theorem ptr_complete_zero:
  static_alloca_items fn = SOME items /\ MEM (a,0) items /\
  (!p. FLOOKUP positions a = SOME p ==> p = 0) /\
  complete_alloc_positions FEMPTY reserved fn positions = SOME completed ==>
  !p. FLOOKUP completed a = SOME p ==> p = 0
Proof
  rpt strip_tac >> gvs[complete_alloc_positions_def] >>
  drule_all ptr_complete_items_zero >> simp[]
QED
