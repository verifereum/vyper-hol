(* Robust indexed representations for recursive array copying. *)
Theory bodyPtrTypedCopyArrayFrame
Ancestors externalReturnCopyArrays typedCopyRobustTransportPtr
  normalizationPrefixPtr representationCleanPtr arithmetic list

Theorem robust_sarray_indexed:
  value_has_type (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) ==>
  ((!m. mem_agree_outside tn mem m ==>
      val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) off m) <=>
   (!i. i < n ==> !m. mem_agree_outside tn mem m ==>
      val_in_memory tv
        (case ALOOKUP kvs i of NONE => default_value tv | SOME v => v)
        (off + i * type_memory_size tv) m))
Proof
  strip_tac >> eq_tac
  >- metis_tac[return_copy_sarray_element] >>
  metis_tac[return_copy_sarray_indexed]
QED

(* The value family may be sparse/defaulted or dense; no source stride is
   identified with the destination stride. *)
Theorem robust_indexed_prefix_advance:
  !tv f d i tn tn' mem mem'.
    (!j. j < i ==> val_wf tv (f j)) /\
    (!j. j < i ==> !m. mem_agree_outside tn mem m ==>
      val_in_memory tv (f j) (d + j * type_memory_size tv) m) /\
    (!x. ~(d + i * type_memory_size tv <= x /\
           x < d + i * type_memory_size tv + type_memory_size tv) ==>
      mem_bytes_at x 1 mem' = mem_bytes_at x 1 mem /\
      (x IN tn' <=> x IN tn)) /\
    (!m. mem_agree_outside tn' mem' m ==>
      val_in_memory tv (f i) (d + i * type_memory_size tv) m) ==>
    !j. j < SUC i ==> !m. mem_agree_outside tn' mem' m ==>
      val_in_memory tv (f j) (d + j * type_memory_size tv) m
Proof
  rpt gen_tac >> strip_tac >> qx_gen_tac `j` >> strip_tac >>
  Cases_on `j = i` >- gvs[] >>
  `j < i` by decide_tac >>
  `(j+1) * type_memory_size tv <= i * type_memory_size tv` by
    (irule LESS_MONO_MULT >> decide_tac) >>
  `d + j * type_memory_size tv + type_memory_size tv <=
   d + i * type_memory_size tv` by
    (qpat_x_assum `(j+1) * _ <= _` mp_tac >>
     pure_rewrite_tac[LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, MULT_CLAUSES] >>
     decide_tac) >>
  rpt strip_tac >> irule robust_representation_exterior_frame >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`d + i * type_memory_size tv`, `mem`, `mem'`,
    `type_memory_size tv`, `tn`, `tn'`] >>
  simp[] >> metis_tac[]
QED

Theorem robust_indexed_source_frame:
  !tv f so N dst n tn tn' mem mem'.
    (so + N * type_memory_size tv <= dst \/ dst + n <= so) /\
    (!j. j < N ==> val_wf tv (f j)) /\
    (!j. j < N ==> !m. mem_agree_outside tn mem m ==>
      val_in_memory tv (f j) (so + j * type_memory_size tv) m) /\
    (!x. ~(dst <= x /\ x < dst + n) ==>
      mem_bytes_at x 1 mem' = mem_bytes_at x 1 mem /\
      (x IN tn' <=> x IN tn)) ==>
    !j. j < N ==> !m. mem_agree_outside tn' mem' m ==>
      val_in_memory tv (f j) (so + j * type_memory_size tv) m
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qx_gen_tac `j` >> strip_tac >>
  `(j+1) * type_memory_size tv <= N * type_memory_size tv` by
    (irule LESS_MONO_MULT >> decide_tac) >>
  `so + j * type_memory_size tv + type_memory_size tv <=
   so + N * type_memory_size tv` by
    (qpat_x_assum `(j+1) * _ <= _` mp_tac >>
     pure_rewrite_tac[LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, MULT_CLAUSES] >>
     decide_tac) >>
  rpt strip_tac >> irule robust_representation_exterior_frame >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`dst`, `mem`, `mem'`, `n`, `tn`, `tn'`] >>
  simp[] >> metis_tac[DECIDE ``a <= b /\ b <= c ==> a <= c``,
    DECIDE ``a <= b ==> a <= b + c``]
QED

Theorem robust_dynarray_indexed:
  (!m. mem_agree_outside tn mem m ==>
    val_in_memory (ArrayTV tv (Dynamic capacity))
      (ArrayV (DynArrayV vs)) off m) <=>
  (!m. mem_agree_outside tn mem m ==>
    mem_word_at off m = n2w (LENGTH vs)) /\
  (!i. i < LENGTH vs ==> !m. mem_agree_outside tn mem m ==>
    val_in_memory tv (EL i vs) (off + 32 + i * type_memory_size tv) m)
Proof
  simp[return_copy_dynarray_representation] >> metis_tac[]
QED
