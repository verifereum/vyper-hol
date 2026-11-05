Theory makeSsaCurrentLiveOriginTransfer
Ancestors makeSsaCurrentDynamicStores makeSsaCurrentRenameTrace list combin

Definition current_live_origin_agree_def:
  current_live_origin_agree D E ms ks <=>
    !v. D v ==> ms v = ks (E v)
End

Theorem current_live_origin_agree_initial:
  current_live_origin_agree D CurrentDefault
    current_origin_initial current_token_initial
Proof
  simp[current_live_origin_agree_def, current_token_initial_def]
QED

Theorem current_annotation_fold_absent[local]:
  !anns E v. ~MEM v (MAP SND anns) ==>
    FOLDL (\env (t,w). (w =+ t) env) E anns v = E v
Proof
  Induct >- simp[] >> gen_tac >> PairCases_on `h` >>
  simp[] >> rpt strip_tac >> first_x_assum drule >>
  simp[combinTheory.APPLY_UPDATE_THM]
QED

Theorem current_annotation_fold_avoids[local]:
  !anns E v t. ~MEM t (MAP FST anns) /\ E v <> t ==>
    FOLDL (\env (u,w). (w =+ u) env) E anns v <> t
Proof
  Induct >- simp[] >> gen_tac >> PairCases_on `h` >>
  rpt gen_tac >> strip_tac >> rewrite_tac[FOLDL] >> first_x_assum irule >>
  gvs[combinTheory.APPLY_UPDATE_THM] >> metis_tac[]
QED

Theorem current_annotation_origin_transfer[local]:
  !anns E ms ks v k.
    ALL_DISTINCT (MAP FST anns) /\ ALL_DISTINCT (MAP SND anns) /\
    ~MEM (E v) (MAP FST anns) /\
    (~MEM v (MAP SND anns) ==> ms v = ks (E v)) ==>
    current_origin_snapshot ms
      (current_occurrence_bindings n k (MAP SND anns)) v =
    current_origin_snapshot ks
      (current_occurrence_bindings n k (MAP FST anns))
      (FOLDL (\env (t,w). (w =+ t) env) E anns v)
Proof
  Induct >- simp[current_occurrence_bindings_def, current_origin_snapshot_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[] >> strip_tac >> Cases_on `v = h1`
  >- (gvs[] >>
      `FOLDL (\env (t,w). (w =+ t) env) ((h1 =+ h0) E) anns h1 = h0` by
        simp[current_annotation_fold_absent, combinTheory.APPLY_UPDATE_THM] >>
      simp[current_occurrence_bindings_def, current_origin_snapshot_def]) >>
  simp[current_occurrence_bindings_def, current_origin_snapshot_def] >>
  `FOLDL (\env (t,w). (w =+ t) env) ((h1 =+ h0) E) anns v <> h0` by
    (irule current_annotation_fold_avoids >>
     simp[combinTheory.APPLY_UPDATE_THM]) >>
  simp[] >> first_x_assum irule >>
  simp[combinTheory.APPLY_UPDATE_THM] >> metis_tac[]
QED

Theorem current_outputs_trace_live_origin:
  current_outputs_trace anns s rs H E names s' rs' H' E' /\
  current_annotations_ok V H anns /\ ALL_DISTINCT (MAP SND anns) /\
  (!v. E v = CurrentDefault v \/ MEM (E v) (MAP FST H)) /\
  current_live_origin_agree (\v. D v /\ ~MEM v (MAP SND anns)) E ms ks ==>
  current_live_origin_agree D E'
    (current_origin_write ms n (MAP SND anns))
    (current_origin_write ks n (MAP FST anns))
Proof
  strip_tac >> drule current_outputs_trace_exit_env >> strip_tac >>
  gvs[current_live_origin_agree_def, current_origin_write_def] >>
  rpt strip_tac >> irule current_annotation_origin_transfer >>
  gvs[current_annotations_ok_def] >>
  `~MEM (E v) (MAP FST anns)` suffices_by metis_tac[] >>
  simp[MEM_MAP] >> rpt strip_tac >> PairCases_on `y` >> gvs[] >>
  fs[EVERY_MEM] >>
  qpat_x_assum `!e. MEM e anns ==> _` drule >> simp[] >> metis_tac[]
QED
