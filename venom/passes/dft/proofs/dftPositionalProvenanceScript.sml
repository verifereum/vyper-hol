Theory dftPositionalProvenance
Ancestors
  dftPositionalSchedule dftPositionalEdit dftPositionalFactor
  dftOriginalScheduleRuntime dftProtectedRuntime dftWf dftDefs dftScheduleOrder dftScheduleEdits sorting relation list

Definition dft_pos_provenance_guard_def:
  dft_pos_provenance_guard Corig Cdest j k pre x y post <=>
    dft_pos_schedule_guard
      (EL k (EL j Corig.ctx_functions).fn_blocks)
      (EL k (EL j Cdest.ctx_functions).fn_blocks)
      dft_must_order j k pre x y post
End

Theorem dft_pos_edge_original_context:
  dft_original_context Corig C /\
  dft_pos_context_edge (dft_pos_provenance_guard Corig Cdest) C D ==>
  dft_original_context Corig D
Proof
  simp[dft_pos_context_edge_def, dft_pos_provenance_guard_def,
       dft_pos_schedule_guard_def] >> rpt strip_tac >>
  gvs[] >> irule dft_pos_edit_original_context >> simp[] >> metis_tac[]
QED

Theorem dft_pos_path_original_context:
  dft_original_context Corig C /\
  RTC (dft_pos_context_edge (dft_pos_provenance_guard Corig Cdest)) C D ==>
  dft_original_context Corig D
Proof
  `!C D. RTC (dft_pos_context_edge (dft_pos_provenance_guard Corig Cdest)) C D ==>
     dft_original_context Corig C ==> dft_original_context Corig D`
    suffices_by metis_tac[] >>
  ho_match_mp_tac RTC_INDUCT >> simp[] >> rpt strip_tac >>
  metis_tac[dft_pos_edge_original_context]
QED

Theorem dft_pos_provenance_factor_plain[local]:
  dft_original_context Corig Corig /\ dft_original_context Corig Cdest /\
  (!j k. j < LENGTH Corig.ctx_functions /\
    k < LENGTH (EL j Corig.ctx_functions).fn_blocks ==>
    ALL_DISTINCT (EL k (EL j Corig.ctx_functions).fn_blocks).bb_instructions /\
    schedule_edges (EL k (EL j Corig.ctx_functions).fn_blocks).bb_instructions
      dft_must_order (EL k (EL j Cdest.ctx_functions).fn_blocks).bb_instructions) ==>
  RTC (dft_pos_context_edge (dft_pos_provenance_guard Corig Cdest)) Corig Cdest
Proof
  strip_tac >> irule dft_pos_context_factor >>
  `LENGTH Cdest.ctx_functions = LENGTH Corig.ctx_functions /\
   (!j. j < LENGTH Corig.ctx_functions ==>
     dft_original_function (EL j Corig.ctx_functions) (EL j Corig.ctx_functions) /\
     dft_original_function (EL j Corig.ctx_functions) (EL j Cdest.ctx_functions))`
    by fs[dft_original_context_def, LIST_REL_EL_EQN] >>
  reverse conj_tac >- (conj_tac >- simp[] >> fs[dft_original_context_def]) >>
  simp[] >> rpt strip_tac >>
  qpat_x_assum `!j. _ ==> dft_original_function _ _ /\ _` drule >> strip_tac >>
  fs[dft_original_function_def, LIST_REL_EL_EQN] >>
  `RTC (dft_pos_block_swap
      (dft_pos_schedule_guard (EL k (EL j Corig.ctx_functions).fn_blocks)
        (EL k (EL j Cdest.ctx_functions).fn_blocks) dft_must_order) j k)
      (EL k (EL j Corig.ctx_functions).fn_blocks)
      (EL k (EL j Cdest.ctx_functions).fn_blocks)` by
    (irule dft_pos_original_block_factor >> simp[] >> metis_tac[]) >>
  pop_assum mp_tac >> match_mp_tac RTC_MONOTONE >>
  simp[dft_pos_block_swap_def, dft_pos_provenance_guard_def]
QED

Theorem dft_pos_path_with_provenance:
  !C D. RTC (dft_pos_context_edge (dft_pos_provenance_guard Corig Cdest)) C D ==>
    dft_original_context Corig C ==>
    RTC (\C D. dft_original_context Corig C /\
      dft_pos_context_edge (dft_pos_provenance_guard Corig Cdest) C D /\
      dft_original_context Corig D) C D
Proof
  ho_match_mp_tac RTC_INDUCT >> simp[] >> rpt strip_tac >>
  rename1 `dft_pos_context_edge _ C Cnext` >>
  `dft_original_context Corig Cnext` by
    metis_tac[dft_pos_edge_original_context] >>
  irule RTC_TRANS >> qexists `Cnext` >> conj_tac
  >- (irule RTC_SINGLE >> simp[]) >> simp[]
QED

Theorem dft_pos_provenance_factor:
  dft_original_context Corig Corig /\ dft_original_context Corig Cdest /\
  (!j k. j < LENGTH Corig.ctx_functions /\
    k < LENGTH (EL j Corig.ctx_functions).fn_blocks ==>
    ALL_DISTINCT (EL k (EL j Corig.ctx_functions).fn_blocks).bb_instructions /\
    schedule_edges (EL k (EL j Corig.ctx_functions).fn_blocks).bb_instructions
      dft_must_order (EL k (EL j Cdest.ctx_functions).fn_blocks).bb_instructions) ==>
  RTC (\C D. dft_original_context Corig C /\
    dft_pos_context_edge (dft_pos_provenance_guard Corig Cdest) C D /\
    dft_original_context Corig D) Corig Cdest
Proof
  strip_tac >> irule dft_pos_path_with_provenance >> simp[] >>
  irule dft_pos_provenance_factor_plain >> simp[]
QED

Theorem dft_pos_original_distinct[local]:
  dft_original_function f g /\ k < LENGTH f.fn_blocks ==>
  ALL_DISTINCT (EL k g.fn_blocks).bb_instructions
Proof
  simp[dft_original_function_def, LIST_REL_EL_EQN] >> strip_tac >>
  `ALL_DISTINCT (EL k f.fn_blocks).bb_instructions` by
    metis_tac[wf_fn_block_inst_ids_distinct, ALL_DISTINCT_MAP, MEM_EL] >>
  metis_tac[dft_original_block_perm, ALL_DISTINCT_PERM]
QED

Theorem dft_pos_before_asymmetric[local]:
  ALL_DISTINCT xs /\ id_before xs a b ==> ~id_before xs b a
Proof
  strip_tac >> pure_rewrite_tac[id_before_def] >> strip_tac >>
  qpat_x_assum `id_before _ _ _` mp_tac >>
  pure_rewrite_tac[id_before_def] >> strip_tac >>
  `i < LENGTH xs /\ i' < LENGTH xs` by simp[] >>
  `i = j' /\ j = i'` by metis_tac[ALL_DISTINCT_EL_IMP] >> gvs[]
QED

Theorem dft_pos_reversed_order[local]:
  ALL_DISTINCT (pre ++ [y;x] ++ post) ==>
  ~id_before (pre ++ [y;x] ++ post) x y
Proof
  strip_tac >> irule dft_pos_before_asymmetric >> simp[] >>
  simp[id_before_def] >> qexistsl [`LENGTH pre`, `SUC (LENGTH pre)`] >>
  simp[EL_APPEND_EQN]
QED

Theorem dft_pos_provenance_edge_extract:
  dft_original_context Corig C /\ dft_original_context Corig D /\
  dft_pos_context_edge (dft_pos_provenance_guard Corig Cdest) C D ==>
  ?fi bi pre x y post.
    fi < LENGTH C.ctx_functions /\
    bi < LENGTH (EL fi C.ctx_functions).fn_blocks /\
    (EL bi (EL fi C.ctx_functions).fn_blocks).bb_instructions = pre ++ [x;y] ++ post /\
    D = dft_pos_edit_ctx fi bi pre x y post C /\
    dft_original_context Corig C /\ dft_original_context Corig D /\
    ~dft_must_order x y /\
    ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
    ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode
Proof
  strip_tac >>
  qpat_x_assum `dft_pos_context_edge _ _ _` mp_tac >>
  simp[dft_pos_context_edge_def, dft_pos_provenance_guard_def,
       dft_pos_schedule_guard_def] >> strip_tac >>
  qexistsl [`j`, `k`, `pre`, `x`, `y`, `post`] >> simp[] >>
  `dft_original_function (EL j Corig.ctx_functions) (EL j C.ctx_functions)` by
    fs[dft_original_context_def, LIST_REL_EL_EQN] >>
  `k < LENGTH (EL j Corig.ctx_functions).fn_blocks` by
    fs[dft_original_function_def, LIST_REL_EL_EQN] >>
  `ALL_DISTINCT (pre ++ [x;y] ++ post)` by
    metis_tac[dft_pos_original_distinct] >>
  `ALL_DISTINCT (pre ++ [y;x] ++ post)` by (fs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  strip_tac >>
  `id_before (pre ++ [y;x] ++ post) x y` by fs[schedule_edges_def] >>
  metis_tac[dft_pos_reversed_order]
QED
