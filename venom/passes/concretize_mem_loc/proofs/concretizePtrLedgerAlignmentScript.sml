Theory concretizePtrLedgerAlignment
Ancestors
  concretizePtrPrefixLedger concretizeMemLocDefs removeUnusedStructProofs
  list rich_list arithmetic pred_set passSharedDefs passSimulationDefs

Theorem ptr_alignment_enumerate[local]:
  !xs. MAP (\j. EL j xs) (COUNT_LIST (LENGTH xs)) = xs
Proof
  gen_tac >> irule LIST_EQ >> simp[EL_MAP, LENGTH_COUNT_LIST, EL_COUNT_LIST]
QED

Theorem ptr_ledger_alignment_construct:
  ?indices. ptr_ledger_block_alignment positions src
    (FILTER (\i. i.inst_opcode <> NOP)
      (MAP (concretize_inst_with_positions positions) src)) indices
Proof
  qexists_tac `FILTER
    (\j. (concretize_inst_with_positions positions (EL j src)).inst_opcode <> NOP)
    (COUNT_LIST (LENGTH src))` >>
  simp[ptr_ledger_block_alignment_def] >>
  qspec_then `src`
    (fn th => CONV_TAC (LAND_CONV (RAND_CONV (RAND_CONV (REWR_CONV (GSYM th))))))
    ptr_alignment_enumerate >>
  simp[FILTER_MAP, MAP_MAP_o, combinTheory.o_DEF]
QED

Theorem ptr_ledger_alignment_cursor:
  ptr_ledger_block_alignment positions src tgt indices ==>
  LENGTH tgt = LENGTH indices /\
  (!j. j < LENGTH tgt ==>
    EL j indices < LENGTH src /\
    EL j tgt = concretize_inst_with_positions positions (EL (EL j indices) src) /\
    (EL j tgt).inst_opcode <> NOP)
Proof
  simp[ptr_ledger_block_alignment_def] >> strip_tac >> simp[EL_MAP] >>
  rpt strip_tac >>
  `MEM (EL j indices) indices` by (irule EL_MEM >> simp[]) >>
  gvs[MEM_FILTER, MEM_COUNT_LIST]
QED

Theorem ptr_ledger_alignment_order:
  ptr_ledger_block_alignment positions src tgt indices /\
  j < k /\ k < LENGTH indices ==> EL j indices < EL k indices
Proof
  strip_tac >> gvs[ptr_ledger_block_alignment_def] >>
  drule_all filter_el_mono >> strip_tac >>
  gvs[LENGTH_COUNT_LIST, EL_COUNT_LIST]
QED

Theorem ptr_ledger_alignment_source:
  ptr_ledger_block_alignment positions src tgt indices /\ i < LENGTH src /\
  (concretize_inst_with_positions positions (EL i src)).inst_opcode <> NOP ==>
  ?j. j < LENGTH tgt /\ EL j indices = i /\
    (!k. k < LENGTH tgt /\ EL k indices = i ==> k = j)
Proof
  strip_tac >>
  `MEM i indices` by gvs[ptr_ledger_block_alignment_def, MEM_FILTER, MEM_COUNT_LIST] >>
  `LENGTH tgt = LENGTH indices` by metis_tac[ptr_ledger_alignment_cursor] >>
  gvs[MEM_EL] >> qexists_tac `n` >> simp[] >> rpt strip_tac >>
  Cases_on `k < n` >- metis_tac[ptr_ledger_alignment_order, prim_recTheory.LESS_REFL] >>
  Cases_on `n < k` >- metis_tac[ptr_ledger_alignment_order, prim_recTheory.LESS_REFL] >>
  decide_tac
QED

Theorem ptr_ledger_alignment_gap:
  ptr_ledger_block_alignment positions src tgt indices /\
  j < LENGTH indices /\ i < EL j indices /\
  (j = 0 \/ EL (j-1) indices < i) ==>
  (concretize_inst_with_positions positions (EL i src)).inst_opcode = NOP
Proof
  strip_tac >>
  `LENGTH tgt = LENGTH indices /\ EL j indices < LENGTH src` by
    metis_tac[ptr_ledger_alignment_cursor] >>
  spose_not_then assume_tac >>
  `i < LENGTH src` by decide_tac >>
  drule_all ptr_ledger_alignment_source >> strip_tac >>
  rename1 `EL k indices = i` >>
  `k < j` by
    (Cases_on `j < k` >- metis_tac[ptr_ledger_alignment_order, LESS_ANTISYM] >>
     Cases_on `k = j` >- metis_tac[prim_recTheory.LESS_REFL] >> decide_tac) >>
  `j <> 0` by decide_tac >>
  Cases_on `k = j-1` >- metis_tac[prim_recTheory.LESS_REFL] >>
  `k < j-1 /\ j-1 < LENGTH indices` by decide_tac >>
  metis_tac[ptr_ledger_alignment_order, LESS_ANTISYM]
QED

Theorem ptr_ledger_alignment_tail:
  ptr_ledger_block_alignment positions src tgt indices /\
  i < LENGTH src /\ (indices = [] \/ LAST indices < i) ==>
  (concretize_inst_with_positions positions (EL i src)).inst_opcode = NOP
Proof
  rpt gen_tac >> disch_tac >> Cases_on `indices`
  >- (gvs[] >> spose_not_then assume_tac >>
      drule_all ptr_ledger_alignment_source >>
      gvs[ptr_ledger_block_alignment_def]) >>
  gvs[] >> spose_not_then assume_tac >>
  drule_all ptr_ledger_alignment_source >> strip_tac >>
  `LENGTH tgt = LENGTH (h::t)` by metis_tac[ptr_ledger_alignment_cursor] >>
  `LAST (h::t) = EL (LENGTH (h::t)-1) (h::t)` by simp[NoAsms, LAST_EL, PRE_SUB1] >>
  Cases_on `j = LENGTH (h::t)-1` >- metis_tac[prim_recTheory.LESS_REFL] >>
  `j < LENGTH (h::t)-1 /\ LENGTH (h::t)-1 < LENGTH (h::t)` by decide_tac >>
  metis_tac[ptr_ledger_alignment_order, LESS_ANTISYM]
QED

Theorem ptr_ledger_alignment_function:
  MEM bb fn.fn_blocks ==>
  ?bbt indices.
    MEM bbt (concretize_function_with_positions positions fn).fn_blocks /\
    bbt.bb_label = bb.bb_label /\
    ptr_ledger_block_alignment positions bb.bb_instructions bbt.bb_instructions indices
Proof
  strip_tac >>
  qexists_tac `clear_nops_block
    (block_map_transform (concretize_inst_with_positions positions) bb)` >>
  simp[concretize_function_with_positions_def, clear_nops_function_def,
    function_map_transform_def, MEM_MAP] >>
  simp[clear_nops_block_def, block_map_transform_def] >>
  `?indices. ptr_ledger_block_alignment positions bb.bb_instructions
    (FILTER (\i. i.inst_opcode <> NOP)
      (MAP (concretize_inst_with_positions positions) bb.bb_instructions)) indices` by
    metis_tac[ptr_ledger_alignment_construct] >>
  qexists_tac `indices` >> simp[] >>
  qexists_tac `block_map_transform (concretize_inst_with_positions positions) bb` >>
  simp[block_map_transform_def] >> qexists_tac `bb` >> simp[]
QED

Theorem ptr_ledger_alignment_image:
  ptr_ledger_block_alignment p src tgt indices ==>
  tgt = FILTER (\i. i.inst_opcode <> NOP)
    (MAP (concretize_inst_with_positions p) src)
Proof
  strip_tac >>
  strip_assume_tac (Q.INST [`positions` |-> `p`] ptr_ledger_alignment_construct) >>
  gvs[ptr_ledger_block_alignment_def]
QED

Theorem ptr_filter_rank[local]:
  !xs j. j < LENGTH (FILTER P xs) ==>
  ?i. i < LENGTH xs /\ EL j (FILTER P xs) = EL i xs /\
    LENGTH (FILTER P (TAKE i xs)) = j
Proof
  Induct_on `xs` >- simp[] >>
  gen_tac >> Cases_on `P h` >> simp[]
  >- (Cases_on `j` >> simp[]
      >- (qexists_tac `0` >> simp[]) >>
      strip_tac >> first_x_assum drule >> strip_tac >>
      qexists_tac `SUC i` >> simp[]) >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  qexists_tac `SUC i` >> simp[]
QED

Theorem ptr_ledger_alignment_prefix_count:
  ptr_ledger_block_alignment p src tgt indices /\ j < LENGTH indices ==>
  LENGTH (FILTER (\i. i.inst_opcode <> NOP)
    (MAP (concretize_inst_with_positions p) (TAKE (EL j indices) src))) = j
Proof
  rw[ptr_ledger_block_alignment_def] >>
  drule ptr_filter_rank >> strip_tac >>
  `i < LENGTH src` by fs[LENGTH_COUNT_LIST] >>
  `EL i (COUNT_LIST (LENGTH src)) = i` by simp[EL_COUNT_LIST] >>
  `TAKE i (COUNT_LIST (LENGTH src)) = COUNT_LIST i` by
    (irule LIST_EQ >> simp[LENGTH_COUNT_LIST, LENGTH_TAKE, EL_TAKE, EL_COUNT_LIST]) >>
  `TAKE i src = MAP (\k. EL k src) (COUNT_LIST i)` by
    (irule LIST_EQ >> simp[LENGTH_COUNT_LIST, LENGTH_TAKE, EL_TAKE, EL_MAP, EL_COUNT_LIST]) >>
  gvs[FILTER_MAP, MAP_MAP_o, combinTheory.o_DEF]
QED
