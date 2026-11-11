(* Robust heterogeneous field prefixes, without assumptions on padding. *)
Theory typedCopyReturnFieldLayoutPtr
Ancestors typedCopyRobustTransportPtr typedCopyTuplePtr typedMemoryCopy
  bodyPtrSubscriptMemoryRebuild list arithmetic

Theorem typed_copy_fields_prefix_frame:
  !tvs vs off k tn mem tn' mem' len.
    k <= LENGTH tvs /\ LENGTH vs = LENGTH tvs /\
    (!i. i < k ==> val_wf (EL i tvs) (EL i vs)) /\
    (!i. i < k ==> !m. mem_agree_outside tn mem m ==>
      val_in_memory (EL i tvs) (EL i vs)
        (off + SUM (MAP type_memory_size (TAKE i tvs))) m) /\
    (!x. ~(off + SUM (MAP type_memory_size (TAKE k tvs)) <= x /\
           x < off + SUM (MAP type_memory_size (TAKE k tvs)) + len) ==>
      mem_bytes_at x 1 mem' = mem_bytes_at x 1 mem /\
      (x IN tn' <=> x IN tn)) ==>
    !i. i < k ==> !m. mem_agree_outside tn' mem' m ==>
      val_in_memory (EL i tvs) (EL i vs)
        (off + SUM (MAP type_memory_size (TAKE i tvs))) m
Proof
  rpt gen_tac >> strip_tac >> rpt strip_tac >>
  irule robust_representation_exterior_frame >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`off + SUM (MAP type_memory_size (TAKE k tvs))`,
    `mem`, `mem'`, `len`, `tn`, `tn'`] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >-
    (disj1_tac >>
     drule_all sum_take_element_before >>
     disch_then (qspec_then `type_memory_size` mp_tac) >> decide_tac) >>
  simp[]
QED

Theorem typed_copy_fields_prefix_step:
  !tvs vs off k tn mem tn' mem'.
    k < LENGTH tvs /\ LENGTH vs = LENGTH tvs /\
    (!i. i < k ==> val_wf (EL i tvs) (EL i vs)) /\
    (!i. i < k ==> !m. mem_agree_outside tn mem m ==>
      val_in_memory (EL i tvs) (EL i vs)
        (off + SUM (MAP type_memory_size (TAKE i tvs))) m) /\
    (!x. ~(off + SUM (MAP type_memory_size (TAKE k tvs)) <= x /\
           x < off + SUM (MAP type_memory_size (TAKE k tvs)) +
             type_memory_size (EL k tvs)) ==>
      mem_bytes_at x 1 mem' = mem_bytes_at x 1 mem /\
      (x IN tn' <=> x IN tn)) /\
    (!m. mem_agree_outside tn' mem' m ==>
      val_in_memory (EL k tvs) (EL k vs)
        (off + SUM (MAP type_memory_size (TAKE k tvs))) m) ==>
    !i. i < SUC k ==> !m. mem_agree_outside tn' mem' m ==>
      val_in_memory (EL i tvs) (EL i vs)
        (off + SUM (MAP type_memory_size (TAKE i tvs))) m
Proof
  rpt gen_tac >> strip_tac >> rpt strip_tac >>
  Cases_on `i = k` >- gvs[] >>
  `i < k /\ k <= LENGTH tvs` by decide_tac >>
  drule_all typed_copy_fields_prefix_frame >>
  metis_tac[]
QED

Theorem typed_copy_fields_robust_tuple:
  !tvs vs off tn mem.
    LENGTH vs = LENGTH tvs /\
    (!i. i < LENGTH tvs ==> !m. mem_agree_outside tn mem m ==>
      val_in_memory (EL i tvs) (EL i vs)
        (off + SUM (MAP type_memory_size (TAKE i tvs))) m) ==>
    !m. mem_agree_outside tn mem m ==>
      val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) off m
Proof
  rpt strip_tac >> simp[Once valueEncodingTheory.val_in_memory_def] >>
  irule tuple_in_memory_from_elements >> metis_tac[]
QED

Theorem typed_copy_fields_robust_struct:
  !names tvs vs off tn mem.
    LENGTH names = LENGTH tvs /\ LENGTH vs = LENGTH tvs /\
    (!i. i < LENGTH tvs ==> !m. mem_agree_outside tn mem m ==>
      val_in_memory (EL i tvs) (EL i vs)
        (off + SUM (MAP type_memory_size (TAKE i tvs))) m) ==>
    !m. mem_agree_outside tn mem m ==>
      val_in_memory (StructTV (ZIP (names,tvs)))
        (StructV (ZIP (names,vs))) off m
Proof
  rpt strip_tac >> simp[Once valueEncodingTheory.val_in_memory_def] >>
  simp[typed_copy_fields_tuple_zip] >>
  irule tuple_in_memory_from_elements >> metis_tac[]
QED
