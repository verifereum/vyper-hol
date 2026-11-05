Theory dftNormalizedEndpoint
Ancestors
  dftFlipRuntime dftPositionalFallibleOrder dftOriginalScheduleRuntime
  dftRunRel dftWf dftDefs dftStructural venomInst venomWf list
  dftPositionalProvenance dftPositionalFactor dftPositionalSchedule
  dftPositionalEdit dftProtectedRuntime dftScheduleEdits relation sorting

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

Theorem dft_normalized_functions[local]:
  !fs gs. LIST_REL dft_fn_rel fs gs ==>
  ?ms. LIST_REL dft_original_function fs fs /\
    LIST_REL dft_original_function fs ms /\
    LIST_REL dft_fallible_order_kept fs ms /\
    LIST_REL (\m g. LIST_REL (\b c. b.bb_label = c.bb_label /\
      LIST_REL flip_rel b.bb_instructions c.bb_instructions) m.fn_blocks g.fn_blocks) ms gs
Proof
  Induct >> Cases_on `gs` >> simp[] >> rpt strip_tac >>
  drule dft_fn_rel_normalized_endpoint >> strip_tac >>
  first_x_assum (qspec_then `t` mp_tac) >> simp[] >>
  disch_then (qx_choose_then `ms` strip_assume_tac) >>
  qexists `m::ms` >> simp[]
QED

Theorem dft_original_context_factor_ready[local]:
  !C M. dft_original_context C C /\ dft_original_context C M ==>
  !j k. j < LENGTH C.ctx_functions /\
    k < LENGTH (EL j C.ctx_functions).fn_blocks ==>
    ALL_DISTINCT (EL k (EL j C.ctx_functions).fn_blocks).bb_instructions /\
    schedule_edges (EL k (EL j C.ctx_functions).fn_blocks).bb_instructions
      dft_must_order (EL k (EL j M.ctx_functions).fn_blocks).bb_instructions
Proof
  simp[dft_original_context_def, LIST_REL_EL_EQN,
       dft_original_function_def] >> rpt strip_tac
  >- (`ALL_DISTINCT (MAP (\i. i.inst_id)
         (EL k (EL j C.ctx_functions).fn_blocks).bb_instructions)` by
        (irule wf_fn_block_inst_ids_distinct >>
         qexists `EL j C.ctx_functions` >> simp[MEM_EL] >> metis_tac[]) >>
      metis_tac[ALL_DISTINCT_MAP]) >>
  qpat_x_assum `!n. _ ==> wf_ssa _ /\ _` (qspec_then `j` mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!n'. _ ==> dft_original_block _ _ _` (qspec_then `k` mp_tac) >>
  simp[dft_original_block_def, dft_original_schedule_def] >> metis_tac[]
QED

Theorem dft_ctx_normalized_path:
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions ==>
  ?M. dft_original_context C C /\ dft_original_context C M /\
    LIST_REL dft_fallible_order_kept C.ctx_functions M.ctx_functions /\
    LIST_REL (\m g. LIST_REL (\b c. b.bb_label = c.bb_label /\
      LIST_REL flip_rel b.bb_instructions c.bb_instructions) m.fn_blocks g.fn_blocks)
      M.ctx_functions C'.ctx_functions /\
    RTC (\A B. dft_original_context C A /\
      dft_pos_context_edge (dft_pos_provenance_guard C M) A B /\
      dft_original_context C B) C M
Proof
  strip_tac >> drule dft_normalized_functions >> strip_tac >>
  qexists `C with ctx_functions := ms` >> simp[] >>
  `dft_original_context C C /\
   dft_original_context C (C with ctx_functions := ms)` by
    simp[dft_original_context_def] >> simp[] >>
  irule dft_pos_provenance_factor >> simp[] >>
  qspecl_then [`C`, `C with ctx_functions := ms`] mp_tac
    dft_original_context_factor_ready >> simp[]
QED

Theorem dft_original_block_distinct_ids[local]:
  dft_original_function f m /\ k < LENGTH f.fn_blocks ==>
  ALL_DISTINCT (MAP (\i. i.inst_id) (EL k m.fn_blocks).bb_instructions)
Proof
  simp[dft_original_function_def, LIST_REL_EL_EQN] >> strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (EL k f.fn_blocks).bb_instructions)` by
    (irule wf_fn_block_inst_ids_distinct >> qexists `f` >> simp[MEM_EL] >> metis_tac[]) >>
  `dft_original_block f (EL k f.fn_blocks) (EL k m.fn_blocks)` by metis_tac[] >>
  drule dft_original_block_perm >> strip_tac >>
  metis_tac[PERM_MAP, ALL_DISTINCT_PERM]
QED

Theorem dft_context_provenance_guard_compatible:
  dft_original_context C M /\
  LIST_REL dft_fallible_order_kept C.ctx_functions M.ctx_functions /\
  fi < LENGTH C.ctx_functions /\ bi < LENGTH (EL fi C.ctx_functions).fn_blocks /\
  dft_pos_provenance_guard C M fi bi pre x y post ==>
  abort_compatible x.inst_opcode y.inst_opcode
Proof
  strip_tac >>
  `dft_original_function (EL fi C.ctx_functions) (EL fi M.ctx_functions)` by
    fs[dft_original_context_def, LIST_REL_EL_EQN] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id)
     (EL bi (EL fi M.ctx_functions).fn_blocks).bb_instructions)` by
    metis_tac[dft_original_block_distinct_ids] >>
  fs[dft_pos_provenance_guard_def, LIST_REL_EL_EQN] >>
  metis_tac[dft_pos_guard_abort_compatible]
QED

Theorem dft_normalized_reversed_order[local]:
  ALL_DISTINCT (pre ++ [x;y] ++ post) ==>
  ~id_before (pre ++ [y;x] ++ post) x y
Proof
  strip_tac >>
  `ALL_DISTINCT (pre ++ [y;x] ++ post)` by
    (fs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  irule id_before_asym >> simp[] >>
  simp[id_before_def] >> qexistsl [`LENGTH pre`, `SUC (LENGTH pre)`] >>
  simp[EL_APPEND_EQN]
QED

Theorem dft_normalized_provenance_edge:
  dft_original_context C M /\
  LIST_REL dft_fallible_order_kept C.ctx_functions M.ctx_functions /\
  dft_original_context C A /\ dft_original_context C B /\
  dft_pos_context_edge (dft_pos_provenance_guard C M) A B ==>
  ?fi bi pre x y post.
    fi < LENGTH A.ctx_functions /\
    bi < LENGTH (EL fi A.ctx_functions).fn_blocks /\
    (EL bi (EL fi A.ctx_functions).fn_blocks).bb_instructions = pre ++ [x;y] ++ post /\
    B = dft_pos_edit_ctx fi bi pre x y post A /\
    dft_original_context C A /\ dft_original_context C B /\
    ~dft_must_order x y /\
    ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
    ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
    dft_pos_provenance_guard C M fi bi pre x y post /\
    abort_compatible x.inst_opcode y.inst_opcode
Proof
  strip_tac >>
  `?fi bi pre x y post.
    fi < LENGTH A.ctx_functions /\
    bi < LENGTH (EL fi A.ctx_functions).fn_blocks /\
    (EL bi (EL fi A.ctx_functions).fn_blocks).bb_instructions = pre ++ [x;y] ++ post /\
    B = dft_pos_edit_ctx fi bi pre x y post A /\
    dft_pos_provenance_guard C M fi bi pre x y post` by
    (fs[dft_pos_context_edge_def] >> metis_tac[]) >>
  qexistsl [`fi`, `bi`, `pre`, `x`, `y`, `post`] >> simp[] >>
  `fi < LENGTH C.ctx_functions /\ bi < LENGTH (EL fi C.ctx_functions).fn_blocks` by
    (qpat_assum `dft_original_context C A` mp_tac >>
     simp[NoAsms, dft_original_context_def, LIST_REL_EL_EQN] >> strip_tac >>
     first_x_assum (qspec_then `fi` mp_tac) >>
     simp[dft_original_function_def, LIST_REL_EL_EQN] >> metis_tac[]) >>
  `abort_compatible x.inst_opcode y.inst_opcode` by
    metis_tac[dft_context_provenance_guard_compatible] >>
  `~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
   ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode` by
    fs[dft_pos_provenance_guard_def, dft_pos_schedule_guard_def] >> simp[] >>
  `dft_original_function (EL fi C.ctx_functions) (EL fi A.ctx_functions)` by
    fs[dft_original_context_def, LIST_REL_EL_EQN] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id)
    (EL bi (EL fi A.ctx_functions).fn_blocks).bb_instructions)` by
    metis_tac[dft_original_block_distinct_ids] >>
  `ALL_DISTINCT (pre ++ [x;y] ++ post)` by metis_tac[ALL_DISTINCT_MAP] >>
  strip_tac >>
  `id_before (pre ++ [y;x] ++ post) x y` by
    fs[dft_pos_provenance_guard_def, dft_pos_schedule_guard_def, schedule_edges_def] >>
  metis_tac[dft_normalized_reversed_order]
QED
