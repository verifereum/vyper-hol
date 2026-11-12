Theory o1DftOpcodePreservation
Ancestors
  dftDefs dftStructural venomInst venomEffects passSharedDefs ctxLookupAgreeHelpers list finite_map
Libs
  pairLib

(* DFT selects source instructions, possibly flipping a flippable opcode. *)
Theorem dft_block_opcode_predicate[local]:
  (!i. is_flippable i.inst_opcode /\ P i.inst_opcode ==>
       P (flip_operands i).inst_opcode) /\
  EVERY (\i. P i.inst_opcode) bb.bb_instructions ==>
  EVERY (\i. P i.inst_opcode) (dft_block order bb).bb_instructions
Proof
  simp[EVERY_MEM] >> rpt strip_tac >>
  Cases_on `is_pseudo i.inst_opcode`
  >- (`MEM i (FILTER (\i. is_pseudo i.inst_opcode)
                  (dft_block order bb).bb_instructions)` by simp[MEM_FILTER] >>
      qpat_x_assum `MEM i (FILTER _ _)` mp_tac >>
      rewrite_tac[dft_block_phis] >> simp[MEM_FILTER] >> metis_tac[]) >>
  `MEM i (FILTER (\i. ~is_pseudo i.inst_opcode)
                (dft_block order bb).bb_instructions)` by simp[MEM_FILTER] >>
  drule dft_block_from_orig >> simp[from_block_def] >> metis_tac[]
QED

Theorem dft_map_update_opcode_predicate[local]:
  (!i. is_flippable i.inst_opcode /\ P i.inst_opcode ==>
       P (flip_operands i).inst_opcode) /\
  EVERY (\bb. EVERY (\i. P i.inst_opcode) bb.bb_instructions) blocks /\
  MEM chosen blocks ==>
  EVERY (\bb. EVERY (\i. P i.inst_opcode) bb.bb_instructions)
    (MAP (\b. if b.bb_label = lbl then dft_block order chosen else b) blocks)
Proof
  simp[EVERY_MAP] >> strip_tac >>
  irule EVERY_MONOTONIC >>
  qexists `\b. EVERY (\i. P i.inst_opcode) b.bb_instructions` >> simp[] >>
  rpt strip_tac >> Cases_on `x.bb_label = lbl` >> simp[] >>
  irule dft_block_opcode_predicate >> simp[] >>
  qpat_x_assum `EVERY _ blocks` mp_tac >> simp[EVERY_MEM] >> metis_tac[]
QED

Theorem dft_process_one_opcode_predicate[local]:
  (!i. is_flippable i.inst_opcode /\ P i.inst_opcode ==>
       P (flip_operands i).inst_opcode) /\
  EVERY (\bb. EVERY (\i. P i.inst_opcode) bb.bb_instructions) st.dls_blocks ==>
  EVERY (\bb. EVERY (\i. P i.inst_opcode) bb.bb_instructions)
    (FST (dft_process_one cfg lr fn st lbl)).dls_blocks
Proof
  strip_tac >> simp[dft_process_one_def] >>
  Cases_on `lookup_block lbl st.dls_blocks`
  >- simp[] >>
  simp[] >> rpt (pairarg_tac >> gvs[]) >>
  Cases_on `FLOOKUP st.dls_last_order lbl` >> gvs[]
  >- (irule dft_map_update_opcode_predicate >> simp[] >>
      gvs[lookup_block_def] >> metis_tac[FIND_MEM]) >>
  IF_CASES_TAC >> gvs[] >>
  irule dft_map_update_opcode_predicate >> simp[] >>
  gvs[lookup_block_def] >> metis_tac[FIND_MEM]
QED

Theorem dft_loop_step_opcode_predicate[local]:
  (!i. is_flippable i.inst_opcode /\ P i.inst_opcode ==>
       P (flip_operands i).inst_opcode) /\
  EVERY (\bb. EVERY (\i. P i.inst_opcode) bb.bb_instructions)
    (FST trip).dls_blocks ==>
  EVERY (\bb. EVERY (\i. P i.inst_opcode) bb.bb_instructions)
    (FST (dft_loop_step cfg lr fn trip)).dls_blocks
Proof
  PairCases_on `trip` >> simp[dft_loop_step_def] >>
  Cases_on `trip2` >> simp[] >>
  Cases_on `trip1` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `dft_process_one cfg lr fn trip0 lbl = _` >>
  IF_CASES_TAC >> gvs[] >>
  strip_tac >> drule_all dft_process_one_opcode_predicate >>
  disch_then (qspecl_then [`lr`, `lbl`, `fn`, `cfg`] mp_tac) >> simp[]
QED

Theorem dft_funpow_opcode_predicate[local]:
  !n trip.
  (!i. is_flippable i.inst_opcode /\ P i.inst_opcode ==>
       P (flip_operands i).inst_opcode) /\
  EVERY (\bb. EVERY (\i. P i.inst_opcode) bb.bb_instructions)
    (FST trip).dls_blocks ==>
  EVERY (\bb. EVERY (\i. P i.inst_opcode) bb.bb_instructions)
    (FST (FUNPOW (dft_loop_step cfg lr fn) n trip)).dls_blocks
Proof
  Induct_on `n` >- simp[] >>
  gen_tac >> simp[arithmeticTheory.FUNPOW_SUC] >>
  metis_tac[dft_loop_step_opcode_predicate]
QED

Theorem dft_fn_opcode_predicate:
  (!i. is_flippable i.inst_opcode /\ P i.inst_opcode ==>
       P (flip_operands i).inst_opcode) /\
  (!i. MEM i (fn_insts fn) ==> P i.inst_opcode) ==>
  !i. MEM i (fn_insts (dft_fn fn)) ==> P i.inst_opcode
Proof
  simp[GSYM EVERY_MEM, fn_insts_def, fn_insts_EVERY_block, dft_fn_def] >>
  pairarg_tac >> gvs[] >> strip_tac >>
  `EVERY (\bb. EVERY (\i. P i.inst_opcode) bb.bb_instructions)
     (FST
       (FUNPOW
         (dft_loop_step (cfg_analyze fn) (liveness_analyze fn) fn)
         (LENGTH fn.fn_blocks * LENGTH fn.fn_blocks)
         (<| dls_blocks := fn.fn_blocks; dls_from_to := FEMPTY;
              dls_last_order := FEMPTY |>,
          (cfg_analyze fn).cfg_dfs_post, F))).dls_blocks` by
    (irule dft_funpow_opcode_predicate >> simp[]) >>
  gvs[]
QED

Theorem dft_flip_no_returndatacopy[local]:
  is_flippable inst.inst_opcode /\ inst.inst_opcode <> RETURNDATACOPY ==>
  (flip_operands inst).inst_opcode <> RETURNDATACOPY
Proof
  rpt strip_tac >>
  namedCases_on `inst.inst_operands` ["", "operand operands"] >>
  fs[flip_operands_def] >>
  namedCases_on `operands` ["", "operand2 remaining"] >>
  fs[flip_operands_def] >>
  Cases_on `remaining` >> fs[flip_operands_def] >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_flippable_def, is_commutative_def, is_comparator_def,
      flip_comparison_opcode_def]
QED

Theorem dft_fn_no_returndatacopy:
  (!i. MEM i (fn_insts fn) ==> i.inst_opcode <> RETURNDATACOPY) ==>
  !i. MEM i (fn_insts (dft_fn fn)) ==> i.inst_opcode <> RETURNDATACOPY
Proof
  strip_tac >> ho_match_mp_tac dft_fn_opcode_predicate >>
  simp[dft_flip_no_returndatacopy]
QED
