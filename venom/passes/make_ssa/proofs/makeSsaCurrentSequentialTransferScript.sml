Theory makeSsaCurrentSequentialTransfer
Ancestors makeSsaCurrentSequentialOrigins makeSsaCurrentLiveOriginTransfer
  makeSsaCurrentRenameTrace makeSsaCurrentDynamicStores list combin

Theorem current_sequential_annotation_transfer[local]:
  !anns E ms ks v k.
    ALL_DISTINCT (MAP FST anns) /\
    ~MEM (E v) (MAP FST anns) /\
    (~MEM v (MAP SND anns) ==> ms v = ks (E v)) ==>
    current_origin_sequential ms
      (current_occurrence_bindings n k (MAP SND anns)) v =
    current_origin_sequential ks
      (current_occurrence_bindings n k (MAP FST anns))
      (FOLDL (\env (t,w). (w =+ t) env) E anns v)
Proof
  Induct >- simp[current_origin_sequential_def, current_occurrence_bindings_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> strip_tac >>
  rewrite_tac[MAP, current_occurrence_bindings_def, current_origin_sequential_def, FOLDL] >>
  rewrite_tac[GSYM current_origin_sequential_def] >>
  first_x_assum irule >>
  gvs[APPLY_UPDATE_THM] >> Cases_on `h1 = v` >> gvs[APPLY_UPDATE_THM] >>
  metis_tac[]
QED

Theorem current_outputs_trace_live_origin_last:
  current_outputs_trace anns s rs H E names s' rs' H' E' /\
  current_annotations_ok V H anns /\
  (!v. E v = CurrentDefault v \/ MEM (E v) (MAP FST H)) /\
  current_live_origin_agree (\v. D v /\ ~MEM v (MAP SND anns)) E ms ks ==>
  current_live_origin_agree D E'
    (current_origin_write_last ms n (MAP SND anns))
    (current_origin_write_last ks n (MAP FST anns))
Proof
  strip_tac >> drule current_outputs_trace_exit_env >> strip_tac >>
  gvs[current_live_origin_agree_def, current_origin_write_last_def] >>
  rpt strip_tac >> irule current_sequential_annotation_transfer >>
  gvs[current_annotations_ok_def] >>
  `~MEM (E v) (MAP FST anns)` suffices_by metis_tac[] >>
  simp[MEM_MAP] >> rpt strip_tac >> PairCases_on `y` >> gvs[] >>
  fs[EVERY_MEM] >>
  qpat_x_assum `!e. MEM e anns ==> _` drule >> simp[] >> metis_tac[]
QED
