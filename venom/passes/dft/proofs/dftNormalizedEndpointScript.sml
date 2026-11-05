Theory dftNormalizedEndpoint
Ancestors
  dftFlipRuntime dftPositionalFallibleOrder dftOriginalScheduleRuntime
  dftRunRel dftWf dftDefs dftStructural venomInst venomWf list

Theorem dft_flip_rel_ids:
  !xs ys. LIST_REL flip_rel xs ys ==>
  MAP (\i. i.inst_id) xs = MAP (\i. i.inst_id) ys
Proof
  Induct >> Cases_on `ys` >> simp[flip_rel_def] >> rpt strip_tac >>
  gvs[flip_operands_inst_id]
QED

Theorem dft_fallible_order_same_ids:
  dft_fallible_order_kept f g /\
  LIST_REL (\b c. MAP (\i. i.inst_id) b.bb_instructions =
                    MAP (\i. i.inst_id) c.bb_instructions)
    m.fn_blocks g.fn_blocks ==>
  dft_fallible_order_kept f m
Proof
  simp[dft_fallible_order_kept_def, LIST_REL_EL_EQN] >> rpt strip_tac >>
  metis_tac[]
QED

Theorem dft_fn_rel_original_refl:
  dft_fn_rel f g ==> dft_original_function f f
Proof
  strip_tac >> irule dft_original_function_refl >>
  fs[dft_fn_rel_def, fn_inst_wf_def, EVERY_MEM] >> metis_tac[]
QED

Theorem dft_normalized_blocks[local]:
  !bs ds. LIST_REL (dft_original_block f) bs bs /\
  EVERY (\b. ALL_DISTINCT (MAP (\i. i.inst_id) b.bb_instructions)) bs /\
  LIST_REL dft_block_rel bs ds ==>
  ?ms. LIST_REL (dft_original_block f) bs ms /\
    LIST_REL (\b c. b.bb_label = c.bb_label /\
      LIST_REL flip_rel b.bb_instructions c.bb_instructions) ms ds
Proof
  Induct >> Cases_on `ds` >> simp[] >> rpt strip_tac >>
  drule_all dft_block_rel_guarded_reconstruction >> strip_tac >>
  first_x_assum (qspec_then `t` mp_tac) >> simp[] >>
  disch_then (qx_choose_then `ms` strip_assume_tac) >>
  qexists `mid::ms` >> simp[]
QED

Theorem dft_fn_rel_normalized_endpoint:
  dft_fn_rel f g ==>
  dft_original_function f f /\
  ?m. dft_original_function f m /\ dft_fallible_order_kept f m /\
    LIST_REL (\b c. b.bb_label = c.bb_label /\
      LIST_REL flip_rel b.bb_instructions c.bb_instructions) m.fn_blocks g.fn_blocks
Proof
  strip_tac >>
  `dft_original_function f f` by metis_tac[dft_fn_rel_original_refl] >>
  simp[] >>
  `EVERY (\b. ALL_DISTINCT (MAP (\i. i.inst_id) b.bb_instructions)) f.fn_blocks` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     irule wf_fn_block_inst_ids_distinct >> qexists `f` >> fs[dft_fn_rel_def]) >>
  `?ms. LIST_REL (dft_original_block f) f.fn_blocks ms /\
    LIST_REL (\b c. b.bb_label = c.bb_label /\
      LIST_REL flip_rel b.bb_instructions c.bb_instructions) ms g.fn_blocks` by
    (irule dft_normalized_blocks >> fs[dft_original_function_def, dft_fn_rel_def]) >>
  qexists `f with fn_blocks := ms` >> simp[] >> conj_tac
  >- fs[dft_original_function_def] >>
  irule dft_fallible_order_same_ids >> qexists `g` >>
  fs[dft_fn_rel_def] >>
  fs[LIST_REL_EL_EQN] >> rpt strip_tac >>
  irule dft_flip_rel_ids >> simp[LIST_REL_EL_EQN]
QED
