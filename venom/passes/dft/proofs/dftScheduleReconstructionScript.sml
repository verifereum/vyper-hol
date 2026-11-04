Theory dftScheduleReconstruction
Ancestors
  dftOriginalScheduleRuntime dftProtectedRuntime dftScheduleOrder
  dftScheduleReconstruct dftScheduleEdits dftRunRel dftDefs dftStructural
  list rich_list sorting relation venomWf venomInst

Theorem dft_reconstruction_unique_id:
  ALL_DISTINCT (MAP key xs) /\ MEM a xs /\ MEM b xs /\ key a = key b ==>
  a = b
Proof
  simp[MEM_EL] >> rpt strip_tac >>
  `n < LENGTH (MAP key xs) /\ n' < LENGTH (MAP key xs)` by simp[] >>
  `EL n (MAP key xs) = EL n' (MAP key xs)` by gvs[EL_MAP] >>
  `n = n'` by metis_tac[ALL_DISTINCT_EL_IMP] >> gvs[]
QED

Theorem dft_reconstruction_flips:
  !mid bs. ALL_DISTINCT (MAP (\i. i.inst_id) orig) /\
  EVERY (\i. MEM i orig) mid /\
  EVERY (from_block orig) bs /\
  MAP (\i. i.inst_id) mid = MAP (\i. i.inst_id) bs ==>
  LIST_REL (\i j. j = i \/ j = flip_operands i) mid bs
Proof
  Induct >> rpt gen_tac >> Cases_on `bs` >> simp[] >> rpt strip_tac
  >- metis_tac[from_block_id_cases] >>
  first_x_assum irule >> simp[]
QED

Theorem dft_reconstruction_bs:
  ALL_DISTINCT (MAP (\i. i.inst_id) orig) /\
  PERM (MAP (\i. i.inst_id) bs)
    (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) orig)) /\
  EVERY (from_block orig) bs ==>
  ?mid. PERM mid (FILTER (\i. ~is_pseudo i.inst_opcode) orig) /\
    MAP (\i. i.inst_id) mid = MAP (\i. i.inst_id) bs /\
    LIST_REL (\i j. j = i \/ j = flip_operands i) mid bs
Proof
  strip_tac >>
  `PERM (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) orig))
      (MAP (\i. i.inst_id) bs)` by metis_tac[PERM_SYM] >>
  drule dft_perm_map_reconstruct >> strip_tac >> qexists `mid` >>
  simp[] >> conj_tac >- metis_tac[PERM_SYM] >>
  irule dft_reconstruction_flips >> simp[] >> qexists `orig` >> simp[] >>
  simp[EVERY_MEM] >> metis_tac[PERM_MEM_EQ, MEM_FILTER]
QED

Theorem dft_reconstruction_before_append[local]:
  !p q a b. id_before (p ++ q) a b <=>
    id_before p a b \/ (MEM a p /\ MEM b q) \/ id_before q a b
Proof
  Induct >- simp[id_before_def] >>
  simp[id_before_cons] >> metis_tac[]
QED

Theorem dft_reconstruction_edges:
  orig = FILTER P orig ++ FILTER (\i. ~P i) orig /\
  PERM mid (FILTER (\i. ~P i) orig) /\
  (!a b. MEM a orig /\ MEM b orig /\ ~P a /\ ~P b /\
    id_before orig a b /\ R a b ==> id_before mid a b) ==>
  schedule_edges orig R (FILTER P orig ++ mid)
Proof
  strip_tac >> simp[schedule_edges_def] >> rpt strip_tac >>
  `MEM a orig /\ MEM b orig` by metis_tac[id_before_mem] >>
  Cases_on `P a` >> Cases_on `P b`
  >- (simp[dft_reconstruction_before_append] >> disj1_tac >>
      metis_tac[id_before_filter])
  >- (simp[dft_reconstruction_before_append, MEM_FILTER] >>
      disj2_tac >> disj1_tac >> simp[] >>
      drule PERM_MEM_EQ >> disch_then (fn th => rewrite_tac[th]) >>
      simp[MEM_FILTER])
  >- (qpat_x_assum `id_before orig a b` mp_tac >>
      qpat_assum `orig = _ ++ _` (fn th => once_rewrite_tac[th]) >>
      simp[dft_reconstruction_before_append, MEM_FILTER] >>
      strip_tac >> drule id_before_mem >> simp[MEM_FILTER]) >>
  simp[dft_reconstruction_before_append] >> metis_tac[]
QED

Theorem dft_reconstruction_split[local]:
  orig = FILTER P orig ++ tail /\ PERM tail (FILTER (\i. ~P i) orig) ==>
  orig = FILTER P orig ++ FILTER (\i. ~P i) orig
Proof
  strip_tac >>
  `EVERY (\i. ~P i) tail` by
    (drule PERM_EVERY >> disch_then (qspec_then `\i. ~P i` mp_tac) >>
     simp[EVERY_FILTER]) >>
  `FILTER (\i. ~P i) orig = tail` by
    (qpat_assum `orig = _ ++ _` (fn th => once_rewrite_tac[th]) >>
     simp[FILTER_APPEND, FILTER_FILTER, FILTER_EQ_ID, GSYM EVERY_DEF]) >>
  metis_tac[]
QED

Theorem dft_reconstruction_order:
  ALL_DISTINCT (MAP key orig) /\ PERM orig xs /\
  MEM a orig /\ MEM b orig /\ id_before (MAP key xs) (key a) (key b) ==>
  id_before xs a b
Proof
  metis_tac[dft_unique_key_before]
QED

Theorem dft_block_rel_reconstruction:
  dft_original_block f b b /\
  ALL_DISTINCT (MAP (\i. i.inst_id) b.bb_instructions) /\
  dft_block_rel b dest ==>
  ?mid. dft_original_block f b mid /\
    mid.bb_label = dest.bb_label /\
    LIST_REL (\i j. j = i \/ j = flip_operands i)
      mid.bb_instructions dest.bb_instructions
Proof
  strip_tac >>
  `wf_ssa f /\ wf_function f /\ MEM b f.fn_blocks /\
   EVERY inst_wf b.bb_instructions /\ b.bb_instructions <> [] /\
   b.bb_instructions = FILTER (\i. is_pseudo i.inst_opcode) b.bb_instructions ++
     FILTER (\i. ~is_pseudo i.inst_opcode) b.bb_instructions` by
    (fs[dft_original_block_def, dft_original_schedule_def] >>
     metis_tac[dft_reconstruction_split]) >>
  qpat_x_assum `dft_block_rel b dest` mp_tac >>
  simp[dft_block_rel_def] >> strip_tac >>
  rename1 `EVERY (from_block b.bb_instructions) bs` >>
  `?ms. PERM ms (FILTER (\i. ~is_pseudo i.inst_opcode) b.bb_instructions) /\
    MAP (\i. i.inst_id) ms = MAP (\i. i.inst_id) bs /\
    LIST_REL (\i j. j = i \/ j = flip_operands i) ms bs` by
    metis_tac[dft_reconstruction_bs] >>
  qabbrev_tac `q = b with bb_instructions :=
    FILTER (\i. is_pseudo i.inst_opcode) b.bb_instructions ++ ms` >>
  `PERM q.bb_instructions b.bb_instructions` by
    (simp[Abbr `q`] >>
     qpat_assum `b.bb_instructions = _ ++ _` (fn th => once_rewrite_tac[th]) >>
     simp[FILTER_APPEND, FILTER_FILTER, PERM_APPEND_IFF]) >>
  `dft_block_rel b q` by
    (simp[dft_block_rel_def, Abbr `q`] >>
     simp[EVERY_MEM, from_block_def] >> rpt strip_tac >>
     qexists `e` >> simp[] >>
     qpat_x_assum `PERM ms _` (mp_tac o MATCH_MP PERM_MEM_EQ) >>
     disch_then (qspec_then `e` mp_tac) >> simp[MEM_FILTER]) >>
  `bb_well_formed b` by fs[wf_function_def] >>
  `LAST q.bb_instructions = LAST b.bb_instructions` by
    metis_tac[dftRunRelTheory.dft_block_rel_last] >>
  `q.bb_instructions <> []` by metis_tac[PERM_NIL] >>
  `schedule_edges b.bb_instructions dft_must_order q.bb_instructions` by
    (simp[Abbr `q`] >> irule dft_reconstruction_edges >> simp[] >>
     rpt strip_tac >>
     `id_before (MAP (\i. i.inst_id) b.bb_instructions) a.inst_id b'.inst_id` by
       metis_tac[dft_unique_key_before, PERM_REFL] >>
     `id_before (MAP (\i. i.inst_id) ms) a.inst_id b'.inst_id` by metis_tac[] >>
     `ALL_DISTINCT (MAP (\i. i.inst_id)
       (FILTER (\i. ~is_pseudo i.inst_opcode) b.bb_instructions))` by
       (irule dftCorrectnessTheory.all_distinct_map_filter >> simp[]) >>
     `MEM a (FILTER (\i. ~is_pseudo i.inst_opcode) b.bb_instructions) /\
      MEM b' (FILTER (\i. ~is_pseudo i.inst_opcode) b.bb_instructions)` by
       simp[MEM_FILTER] >>
     `PERM (FILTER (\i. ~is_pseudo i.inst_opcode) b.bb_instructions) ms` by
       metis_tac[PERM_SYM] >>
     irule (INST_TYPE [alpha |-> ``:num``] dft_reconstruction_order) >>
     qexistsl [`\i. i.inst_id`, `FILTER (\i. ~is_pseudo i.inst_opcode) b.bb_instructions`] >>
     simp[]) >>
  qexists `q` >> simp[dft_original_block_def, dft_original_schedule_def] >>
  conj_tac >- (simp[Abbr `q`] >> qexists `ms` >> simp[]) >>
  simp[Abbr `q`] >> irule LIST_REL_APPEND_suff >> simp[] >>
  irule LIST_REL_refl >> simp[]
QED
