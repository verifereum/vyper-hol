Theory dftPositionalSchedule
Ancestors
  dftPositionalFactor dftScheduleEdits dftOriginalScheduleRuntime
  dftScheduleOrder dftProtectedRuntime dftDefs
  list rich_list sorting relation venomWf venomInst

Definition dft_pos_schedule_guard_def:
  dft_pos_schedule_guard b dest R j k pre x y post <=>
    id_before b.bb_instructions x y /\
    id_before dest.bb_instructions y x /\
    ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
    ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
    schedule_edges b.bb_instructions R (pre ++ [y;x] ++ post)
End

Theorem dft_pos_before_append[local]:
  !p q a b. id_before (p ++ q) a b <=>
    id_before p a b \/ (MEM a p /\ MEM b q) \/ id_before q a b
Proof
  Induct >- simp[id_before_def] >>
  simp[id_before_cons] >> metis_tac[]
QED

Theorem dft_pos_before_mem[local]:
  id_before xs a b ==> MEM a xs /\ MEM b xs
Proof
  simp[id_before_def] >> metis_tac[MEM_EL, arithmeticTheory.LESS_TRANS]
QED

Theorem dft_pos_before_asym[local]:
  ALL_DISTINCT xs /\ id_before xs a b ==> ~id_before xs b a
Proof
  strip_tac >> pure_rewrite_tac[id_before_def] >> strip_tac >>
  qpat_x_assum `id_before _ _ _` mp_tac >>
  pure_rewrite_tac[id_before_def] >> strip_tac >>
  `i < LENGTH xs /\ i' < LENGTH xs` by simp[] >>
  `i = j' /\ j = i'` by metis_tac[ALL_DISTINCT_EL_IMP] >> gvs[]
QED

Theorem dft_pos_prefix_inversion[local]:
  !P pp us vs x y. ALL_DISTINCT (pp ++ us) /\
  EVERY P pp /\ EVERY (\z. ~P z) us /\ EVERY (\z. ~P z) vs /\
  id_before (pp ++ us) x y /\ id_before (pp ++ vs) y x ==>
  ~P x /\ ~P y
Proof
  rpt gen_tac >> strip_tac >>
  `!z. MEM z pp ==> P z` by fs[EVERY_MEM] >>
  `!z. MEM z us ==> ~P z` by fs[EVERY_MEM] >>
  `!z. MEM z vs ==> ~P z` by fs[EVERY_MEM] >>
  fs[dft_pos_before_append] >>
  imp_res_tac dft_pos_before_mem >>
  metis_tac[dft_pos_before_asym, ALL_DISTINCT_APPEND]
QED

Theorem dft_pos_perm_filter[local]:
  PERM xs (FILTER P ys) ==> EVERY P xs
Proof
  simp[EVERY_MEM] >> metis_tac[PERM_MEM_EQ, MEM_FILTER]
QED

Theorem dft_pos_original_inversion_nonpseudo:
  dft_original_block f b b /\ dft_original_block f b dest /\
  ALL_DISTINCT b.bb_instructions /\
  id_before b.bb_instructions x y /\ id_before dest.bb_instructions y x ==>
  ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode
Proof
  simp[dft_original_block_def, dft_original_schedule_def] >> strip_tac >>
  rename1 `b.bb_instructions = _ ++ us` >>
  rename1 `dest.bb_instructions = _ ++ vs` >>
  `EVERY (\i. ~is_pseudo i.inst_opcode) us /\
   EVERY (\i. ~is_pseudo i.inst_opcode) vs`
    by metis_tac[dft_pos_perm_filter] >>
  irule (SRULE [] (Q.SPEC `\i. is_pseudo i.inst_opcode`
    (INST_TYPE [alpha |-> ``:instruction``] dft_pos_prefix_inversion))) >>
  qexistsl [`FILTER (\i. is_pseudo i.inst_opcode) b.bb_instructions`, `us`, `vs`] >>
  simp[EVERY_FILTER] >> metis_tac[]
QED

Theorem dft_pos_wf_before_nonterm[local]:
  bb_well_formed b /\ id_before b.bb_instructions x y ==>
  ~is_terminator x.inst_opcode
Proof
  simp[bb_well_formed_def, id_before_def] >> rpt strip_tac >>
  `i < LENGTH b.bb_instructions` by simp[] >>
  `i = PRE (LENGTH b.bb_instructions)` by metis_tac[] >> gvs[]
QED

Theorem dft_pos_original_inversion_nonterm:
  dft_original_block f b b /\ dft_original_block f b dest /\
  ALL_DISTINCT b.bb_instructions /\
  id_before b.bb_instructions x y /\ id_before dest.bb_instructions y x ==>
  ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode
Proof
  strip_tac >>
  `bb_well_formed b` by
    fs[dft_original_block_def, dft_original_schedule_def, wf_function_def] >>
  conj_tac >- metis_tac[dft_pos_wf_before_nonterm] >>
  `ALL_DISTINCT dest.bb_instructions` by
    metis_tac[dft_original_block_perm, ALL_DISTINCT_PERM] >>
  `schedule_edges b.bb_instructions dft_must_order dest.bb_instructions` by
    fs[dft_original_block_def, dft_original_schedule_def] >>
  strip_tac >>
  `id_before dest.bb_instructions x y` by
    fs[schedule_edges_def, dft_must_order_def] >>
  metis_tac[dft_pos_before_asym]
QED

Definition dft_pos_original_edge_def:
  dft_pos_original_edge f b dest R j k u v <=>
    dft_original_block f b u /\ dft_original_block f b v /\
    dft_pos_block_swap (dft_pos_schedule_guard b dest R) j k u v
End

Theorem dft_pos_original_edge_swap[local]:
  dft_original_block f b b /\ dft_original_block f b dest /\
  ALL_DISTINCT b.bb_instructions /\
  dft_original_block f b u /\
  schedule_edges b.bb_instructions R u.bb_instructions /\
  schedule_edges b.bb_instructions R dest.bb_instructions /\
  inv_edit b.bb_instructions dest.bb_instructions u.bb_instructions vs ==>
  dft_original_block f b (u with bb_instructions := vs) /\
  schedule_edges b.bb_instructions R vs /\
  dft_pos_original_edge f b dest R j k u (u with bb_instructions := vs)
Proof
  strip_tac >>
  `ALL_DISTINCT dest.bb_instructions` by
    metis_tac[dft_original_block_perm, ALL_DISTINCT_PERM] >>
  `schedule_edges b.bb_instructions dft_must_order u.bb_instructions /\
   schedule_edges b.bb_instructions dft_must_order dest.bb_instructions` by
    fs[dft_original_block_def, dft_original_schedule_def] >>
  `schedule_edges b.bb_instructions R vs /\
   schedule_edges b.bb_instructions dft_must_order vs` by
    metis_tac[inv_edit_schedule_edges] >>
  fs[inv_edit_def] >>
  `~is_pseudo a.inst_opcode /\ ~is_pseudo b'.inst_opcode` by
    metis_tac[dft_pos_original_inversion_nonpseudo] >>
  `~is_terminator a.inst_opcode /\ ~is_terminator b'.inst_opcode` by
    metis_tac[dft_pos_original_inversion_nonterm] >>
  `dft_original_block f b (u with bb_instructions := p ++ [b';a] ++ q)` by
    (irule dft_original_block_swap >> simp[] >> metis_tac[]) >>
  simp[dft_pos_original_edge_def, dft_pos_block_swap_def,
       dft_pos_schedule_guard_def] >>
  qexistsl [`p`, `a`, `b'`, `q`] >> simp[] >> metis_tac[]
QED

Theorem dft_pos_original_path[local]:
  dft_original_block f b b /\ dft_original_block f b dest /\
  ALL_DISTINCT b.bb_instructions /\
  schedule_edges b.bb_instructions R dest.bb_instructions ==>
  !xs ys. RTC (inv_edit b.bb_instructions dest.bb_instructions) xs ys ==>
    xs = b.bb_instructions ==>
    dft_original_block f b (b with bb_instructions := ys) /\
    schedule_edges b.bb_instructions R ys /\
    RTC (dft_pos_original_edge f b dest R j k) b (b with bb_instructions := ys)
Proof
  strip_tac >> ho_match_mp_tac RTC_INDUCT_RIGHT1 >> conj_tac
  >- (rpt strip_tac >> gvs[] >> simp[schedule_edges_def]) >>
  rpt gen_tac >> strip_tac >> disch_tac >> gvs[] >>
  drule_all (SRULE [] (Q.INST
    [{redex = `u`, residue = `b with bb_instructions := ys`}]
    dft_pos_original_edge_swap)) >>
  strip_tac >> simp[] >> irule RTC_TRANS >>
  first_assum (irule_at Any) >> irule RTC_SINGLE >> simp[]
QED

Theorem dft_pos_original_block_factor_strong:
  dft_original_block f b b /\ dft_original_block f b dest /\
  ALL_DISTINCT b.bb_instructions /\
  schedule_edges b.bb_instructions R dest.bb_instructions ==>
  RTC (dft_pos_original_edge f b dest R j k) b dest
Proof
  strip_tac >>
  `RTC (inv_edit b.bb_instructions dest.bb_instructions)
      b.bb_instructions dest.bb_instructions` by
    (irule inv_edit_factor >> metis_tac[dft_original_block_perm, PERM_SYM]) >>
  `b with bb_instructions := dest.bb_instructions = dest` by
    (fs[dft_original_block_def, dft_original_schedule_def] >>
     Cases_on `b` >> Cases_on `dest` >>
     gvs[basic_block_fn_updates, combinTheory.K_THM]) >>
  metis_tac[dft_pos_original_path]
QED

Theorem dft_pos_original_block_factor:
  dft_original_block f b b /\ dft_original_block f b dest /\
  ALL_DISTINCT b.bb_instructions /\
  schedule_edges b.bb_instructions R dest.bb_instructions ==>
  RTC (dft_pos_block_swap (dft_pos_schedule_guard b dest R) j k) b dest
Proof
  strip_tac >> drule_all dft_pos_original_block_factor_strong >>
  disch_then (qspecl_then [`k`, `j`] mp_tac) >>
  match_mp_tac RTC_MONOTONE >> simp[dft_pos_original_edge_def]
QED
