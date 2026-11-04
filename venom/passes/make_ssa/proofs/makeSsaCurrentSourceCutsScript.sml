Theory makeSsaCurrentSourceCuts
Ancestors
  list rich_list makeSsaCurrentTreeTrace makeSsaCurrentRenameTrace

Theorem current_local_trace_lengths:
  !aa xs s rs H E ys s' rs' H' E'.
  current_local_trace aa xs s rs H E ys s' rs' H' E' ==>
  LENGTH aa = LENGTH xs /\ LENGTH ys = LENGTH xs
Proof
  Induct >> simp[current_local_trace_def] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem current_local_trace_append:
  !ap xp yp s rs H E aq xq yq s' rs' H' E'.
  LENGTH ap = LENGTH xp /\ LENGTH ap = LENGTH yp ==>
  (current_local_trace (ap ++ aq) (xp ++ xq) s rs H E
     (yp ++ yq) s' rs' H' E' <=>
   ?sm rm Hm Em.
     current_local_trace ap xp s rs H E yp sm rm Hm Em /\
     current_local_trace aq xq sm rm Hm Em yq s' rs' H' E')
Proof
  Induct >> Cases_on `xp` >> Cases_on `yp` >>
  simp[current_local_trace_def] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`t`, `t'`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem current_local_trace_split_at:
  !n aa xs ys s rs H E s' rs' H' E'.
  n <= LENGTH aa /\ n <= LENGTH xs /\ n <= LENGTH ys ==>
  (current_local_trace aa xs s rs H E ys s' rs' H' E' <=>
   ?sm rm Hm Em.
     current_local_trace (TAKE n aa) (TAKE n xs) s rs H E
       (TAKE n ys) sm rm Hm Em /\
     current_local_trace (DROP n aa) (DROP n xs) sm rm Hm Em
       (DROP n ys) s' rs' H' E')
Proof
  Induct >- simp[current_local_trace_def] >>
  Cases_on `aa` >> Cases_on `xs` >> Cases_on `ys` >>
  simp[NoAsms, current_local_trace_def] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`t`, `t'`, `t''`] mp_tac) >>
  simp[NoAsms] >> metis_tac[]
QED

Definition current_source_cut_def:
  current_source_cut A
    (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,
     (bbs1 : basic_block list),(bbs2 : basic_block list)) n rs E <=>
  ?ap aq xp xq yp yq sm Hm.
    A l = ap ++ aq /\ bb.bb_instructions = xp ++ xq /\ ren = yp ++ yq /\
    LENGTH ap = n /\ LENGTH xp = n /\ LENGTH yp = n /\
    current_local_trace ap xp s0 rs0 H0 E0 yp sm rs Hm E /\
    current_local_trace aq xq sm rs Hm E yq s1 rs1 H1 E1
End

Theorem current_source_cut_exists:
  current_event_trace A finalH
    (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2) /\
  n <= LENGTH bb.bb_instructions ==>
  ?rs E. current_source_cut A
    (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2) n rs E
Proof
  simp[current_event_trace_def] >> rpt strip_tac >>
  drule current_local_trace_lengths >> strip_tac >>
  `?sm rm Hm Em.
     current_local_trace (TAKE n (A l)) (TAKE n bb.bb_instructions)
       s0 rs0 H0 E0 (TAKE n ren) sm rm Hm Em /\
     current_local_trace (DROP n (A l)) (DROP n bb.bb_instructions)
       sm rm Hm Em (DROP n ren) s1 rs1 H1 E1` by
    metis_tac[current_local_trace_split_at] >>
  qexistsl_tac [`rm`, `Em`] >> simp[current_source_cut_def] >>
  qexistsl_tac [`TAKE n (A l)`, `DROP n (A l)`,
    `TAKE n bb.bb_instructions`, `DROP n bb.bb_instructions`,
    `TAKE n ren`, `DROP n ren`, `sm`, `Hm`] >>
  simp[TAKE_DROP, LENGTH_TAKE]
QED

Theorem current_source_cut_start:
  current_source_cut A
    (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2) 0 rs E <=>
  rs = rs0 /\ E = E0 /\
  current_local_trace (A l) bb.bb_instructions s0 rs0 H0 E0
    ren s1 rs1 H1 E1
Proof
  simp[current_source_cut_def, current_local_trace_def] >> metis_tac[]
QED

Theorem current_source_cut_end:
  current_source_cut A
    (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2)
    (LENGTH bb.bb_instructions) rs E <=>
  rs = rs1 /\ E = E1 /\
  current_local_trace (A l) bb.bb_instructions s0 rs0 H0 E0
    ren s1 rs1 H1 E1
Proof
  eq_tac
  >- (simp[current_source_cut_def] >> rpt strip_tac >>
      `xq = []` by
        (qpat_x_assum `LENGTH xp = _` mp_tac >>
         qpat_assum `bb.bb_instructions = _` (fn th => rewrite_tac[th]) >>
         simp[]) >>
      qpat_x_assum `xq = []` SUBST_ALL_TAC >>
      drule current_local_trace_lengths >> strip_tac >>
      qpat_x_assum `LENGTH xp = _` kall_tac >>
      qpat_x_assum `LENGTH ap = _` kall_tac >>
      qpat_x_assum `LENGTH yp = _` kall_tac >>
      gvs[current_local_trace_def]) >>
  rpt strip_tac >> gvs[current_source_cut_def] >>
  drule current_local_trace_lengths >> strip_tac >>
  qexistsl_tac [`A l`, `[]`, `bb.bb_instructions`, `[]`, `ren`, `[]`, `s1`, `H1`] >>
  simp[current_local_trace_def]
QED

Theorem current_source_cut_step:
  current_source_cut A
    (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2) n rs E /\
  n < LENGTH bb.bb_instructions ==>
  ?sm Hm sn rn Hn En.
    current_local_trace (TAKE n (A l)) (TAKE n bb.bb_instructions)
      s0 rs0 H0 E0 (TAKE n ren) sm rs Hm E /\
    current_inst_trace (EL n (A l)) (EL n bb.bb_instructions)
      sm rs Hm E (EL n ren) sn rn Hn En /\
    current_source_cut A
      (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2) (SUC n) rn En
Proof
  simp[current_source_cut_def] >> rpt strip_tac >>
  `xq <> []` by
    (strip_tac >> gvs[] >> fs[]) >>
  Cases_on `aq` >> Cases_on `xq` >> Cases_on `yq` >>
  fs[current_local_trace_def] >>
  rename1 `current_inst_trace h h' sm rs Hm E h'' sn rn Hn En` >>
  qexistsl_tac [`sm`, `Hm`, `sn`, `rn`, `Hn`, `En`] >>
  conj_tac
  >- metis_tac[TAKE_LENGTH_APPEND, APPEND_ASSOC] >>
  conj_tac
  >- simp[EL_APPEND_EQN] >>
  qexistsl_tac [`ap ++ [h]`, `t`, `xp ++ [h']`, `t'`,
    `yp ++ [h'']`, `t''`, `sn`, `Hn`] >>
  simp[APPEND_ASSOC, current_local_trace_append, current_local_trace_def] >>
  metis_tac[]
QED
