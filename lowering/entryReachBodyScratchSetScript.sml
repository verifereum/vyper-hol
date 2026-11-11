(* Allocation credit counts actual counter sites, independently of execution count. *)
Theory entryReachBodyScratchSet
Ancestors
  abiDecoderAllocation venomState finite_map pred_set arithmetic

Definition entry_scratch_missing_def:
  entry_scratch_missing sites s = sites DIFF FDOM s.vs_allocas
End

Definition entry_scratch_ready_def:
  entry_scratch_ready sites b cap s <=>
    FINITE sites /\ b <= s.vs_alloca_next /\
    s.vs_alloca_next + 32 * CARD (entry_scratch_missing sites s) <= b+cap /\
    (!i r. i IN sites /\ FLOOKUP s.vs_allocas i = SOME r ==>
      SND r = 32 /\ b <= FST r /\ FST r+32 <= s.vs_alloca_next)
End

Theorem entry_scratch_missing_finite[simp]:
  FINITE sites ==> FINITE (entry_scratch_missing sites s)
Proof simp[entry_scratch_missing_def]
QED

Theorem entry_scratch_ready_empty[simp]:
  entry_scratch_ready {} b cap s <=>
    b <= s.vs_alloca_next /\ s.vs_alloca_next <= b+cap
Proof simp[entry_scratch_ready_def, entry_scratch_missing_def]
QED

Theorem entry_scratch_ready_frame:
  s.vs_allocas = t.vs_allocas /\ s.vs_alloca_next = t.vs_alloca_next ==>
  (entry_scratch_ready sites b cap s <=> entry_scratch_ready sites b cap t)
Proof simp[entry_scratch_ready_def, entry_scratch_missing_def]
QED

Theorem entry_scratch_missing_subset:
  child_sites SUBSET sites ==> entry_scratch_missing child_sites s SUBSET entry_scratch_missing sites s
Proof simp[entry_scratch_missing_def] >> SET_TAC[]
QED

Theorem entry_scratch_ready_subset:
  entry_scratch_ready sites b cap s /\ child_sites SUBSET sites ==>
  entry_scratch_ready child_sites b cap s
Proof
  rw[entry_scratch_ready_def]
  >- metis_tac[SUBSET_FINITE]
  >- (`CARD (entry_scratch_missing child_sites s) <= CARD (entry_scratch_missing sites s)` by
        (irule CARD_SUBSET >> simp[entry_scratch_missing_subset]) >> decide_tac) >>
  metis_tac[SUBSET_DEF]
QED

Theorem entry_scratch_missing_insert:
  t.vs_allocas = s.vs_allocas |+ (a,r) ==>
  entry_scratch_missing sites t = entry_scratch_missing sites s DELETE a
Proof
  simp[entry_scratch_missing_def, EXTENSION] >> metis_tac[]
QED

Theorem entry_scratch_missing_credit:
  FINITE sites /\ a IN sites /\ FLOOKUP s.vs_allocas a = NONE ==>
  CARD (entry_scratch_missing sites s) =
    SUC (CARD (entry_scratch_missing sites s DELETE a))
Proof
  strip_tac >>
  `a IN entry_scratch_missing sites s` by
    gvs[entry_scratch_missing_def, FLOOKUP_DEF] >>
  `entry_scratch_missing sites s = a INSERT (entry_scratch_missing sites s DELETE a)` by
    (simp[EXTENSION] >> metis_tac[]) >>
  pop_assum (fn th => once_rewrite_tac[th]) >> simp[CARD_INSERT]
QED

Theorem entry_scratch_ready_insert:
  entry_scratch_ready sites b cap s /\ a IN sites /\
  FLOOKUP s.vs_allocas a = NONE /\
  t.vs_allocas = s.vs_allocas |+ (a,(s.vs_alloca_next,32)) /\
  t.vs_alloca_next = s.vs_alloca_next+32 ==>
  entry_scratch_ready sites b cap t
Proof
  strip_tac >>
  `FINITE sites` by fs[entry_scratch_ready_def] >>
  drule_all entry_scratch_missing_credit >> strip_tac >>
  drule entry_scratch_missing_insert >> strip_tac >>
  qpat_x_assum `entry_scratch_ready _ _ _ s` mp_tac >>
  simp_tac bool_ss [entry_scratch_ready_def] >> strip_tac >>
  asm_rewrite_tac[] >> conj_tac >- decide_tac >>
  conj_tac >-
    (qpat_x_assum `s.vs_alloca_next + 32 * _ <= _` mp_tac >>
     qpat_x_assum `CARD _ = SUC _` (fn th => rewrite_tac[th]) >>
     POP_ASSUM_LIST (K all_tac) >> simp[RIGHT_ADD_DISTRIB, MULT_SUC]) >>
  rpt gen_tac >> Cases_on `i = a` >> simp[FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[] >> first_x_assum drule >>
  disch_then drule >> simp[]
QED

Theorem entry_scratch_ready_existing:
  entry_scratch_ready sites b cap s /\ i IN sites /\
  FLOOKUP s.vs_allocas i = SOME (p,sz) ==>
  sz = 32 /\ b <= p /\ p+32 <= s.vs_alloca_next /\ p+32 <= b+cap
Proof
  rw[entry_scratch_ready_def] >> first_x_assum drule >>
  disch_then drule >> simp[] >> decide_tac
QED

Theorem entry_scratch_ready_fresh:
  entry_scratch_ready sites b cap s /\ i IN sites /\
  FLOOKUP s.vs_allocas i = NONE ==> s.vs_alloca_next+32 <= b+cap
Proof
  strip_tac >> `FINITE sites` by fs[entry_scratch_ready_def] >>
  drule_all entry_scratch_missing_credit >> strip_tac >>
  qpat_x_assum `entry_scratch_ready _ _ _ _` mp_tac >>
  simp_tac bool_ss [entry_scratch_ready_def] >> strip_tac >>
  qpat_x_assum `s.vs_alloca_next + 32 * _ <= _` mp_tac >>
  qpat_x_assum `CARD _ = SUC _` (fn th => rewrite_tac[th]) >>
  POP_ASSUM_LIST (K all_tac) >> simp[MULT_SUC]
QED

Theorem entry_scratch_ready_two:
  entry_scratch_ready sites b cap s /\ cid IN sites /\ iid IN sites /\ cid <> iid /\
  FLOOKUP s.vs_allocas iid = NONE ==>
  s.vs_alloca_next + (if FLOOKUP s.vs_allocas cid = NONE then 32 else 0) + 32 <= b+cap
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas cid = NONE` >> simp[]
  >- (`entry_scratch_ready {cid;iid} b cap s` by
        (irule entry_scratch_ready_subset >> qexists_tac `sites` >> simp[]) >>
      qpat_x_assum `entry_scratch_ready {cid;iid} _ _ _` mp_tac >>
      `entry_scratch_missing {cid;iid} s = {cid;iid}` by
        (Cases_on `cid IN FDOM s.vs_allocas` >>
         Cases_on `iid IN FDOM s.vs_allocas` >>
         gvs[FLOOKUP_DEF, entry_scratch_missing_def, EXTENSION]) >>
      simp[entry_scratch_ready_def]) >>
  drule_all entry_scratch_ready_fresh >> simp[]
QED
