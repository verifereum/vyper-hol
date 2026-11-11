(* Robust semantic prefixes for counted typed array copying. *)
Theory typedCopyReturnArrayLayoutPtr
Ancestors typedMemoryCopy typedCopyRobustTransportPtr typedCopyLayoutPtr
  normalizationPrefixPtr bodyPtrDefs arithmetic list

Theorem typed_copy_index_prefix_robust_frame:
  !f tv off N k tn mem tn' mem' len.
    (!m. mem_agree_outside tn mem m ==>
         typed_copy_index_prefix f tv off N k m) /\
    (!i. i < k ==> val_wf tv (f i)) /\
    (!x. ~(off + k * type_memory_size tv <= x /\
           x < off + k * type_memory_size tv + len) ==>
       mem_bytes_at x 1 mem' = mem_bytes_at x 1 mem /\
       (x IN tn' <=> x IN tn)) ==>
    !m. mem_agree_outside tn' mem' m ==>
         typed_copy_index_prefix f tv off N k m
Proof
  rpt gen_tac >> strip_tac >>
  `k <= N` by
    (first_x_assum (qspec_then `mem` mp_tac) >>
     simp[mem_agree_outside_def, typed_copy_index_prefix_def]) >>
  simp[typed_copy_index_prefix_def] >> rpt strip_tac >>
  irule robust_representation_exterior_frame >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`off + k * type_memory_size tv`, `mem`, `mem'`,
    `len`, `tn`, `tn'`] >>
  conj_tac >- metis_tac[typed_copy_index_prefix_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >-
    (disj1_tac >>
     `SUC i * type_memory_size tv <= k * type_memory_size tv` by
       (irule LESS_MONO_MULT >> decide_tac) >>
     pop_assum mp_tac >> pure_rewrite_tac[MULT_CLAUSES] >> decide_tac) >>
  simp[]
QED

Theorem typed_copy_index_prefix_robust_step:
  !f tv off N k tn mem tn' mem'.
    (!m. mem_agree_outside tn mem m ==>
         typed_copy_index_prefix f tv off N k m) /\
    (!i. i < k ==> val_wf tv (f i)) /\ k < N /\
    (!x. ~(off + k * type_memory_size tv <= x /\
           x < off + k * type_memory_size tv + type_memory_size tv) ==>
       mem_bytes_at x 1 mem' = mem_bytes_at x 1 mem /\
       (x IN tn' <=> x IN tn)) /\
    (!m. mem_agree_outside tn' mem' m ==>
       val_in_memory tv (f k) (off + k * type_memory_size tv) m) ==>
    !m. mem_agree_outside tn' mem' m ==>
         typed_copy_index_prefix f tv off N (SUC k) m
Proof
  rpt gen_tac >> strip_tac >>
  rpt strip_tac >> irule typed_copy_index_prefix_step >>
  simp[] >> irule typed_copy_index_prefix_robust_frame >>
  metis_tac[]
QED

Theorem typed_copy_index_prefix_robust_dynarray:
  !tv vs cap off tn mem.
    (!m. mem_agree_outside tn mem m ==>
         mem_word_at off m = n2w (LENGTH vs)) /\
    (!m. mem_agree_outside tn mem m ==>
         typed_copy_index_prefix (\i. EL i vs) tv (off + 32)
           (LENGTH vs) (LENGTH vs) m) ==>
    !m. mem_agree_outside tn mem m ==>
         val_in_memory (ArrayTV tv (Dynamic cap))
           (ArrayV (DynArrayV vs)) off m
Proof
  rpt strip_tac >> irule robust_dynarray_assemble >>
  gvs[typed_copy_index_prefix_complete] >> metis_tac[]
QED

Theorem typed_copy_index_prefix_robust_sarray:
  !tv kvs N off tn mem.
    value_has_type (ArrayTV tv (Fixed N)) (ArrayV (SArrayV kvs)) /\
    (!m. mem_agree_outside tn mem m ==>
       typed_copy_index_prefix
         (\i. case ALOOKUP kvs i of NONE => default_value tv | SOME v => v)
         tv off N N m) ==>
    !m. mem_agree_outside tn mem m ==>
       val_in_memory (ArrayTV tv (Fixed N)) (ArrayV (SArrayV kvs)) off m
Proof
  rpt strip_tac >> irule typed_copy_sarray_indexed >>
  gvs[typed_copy_index_prefix_complete] >> metis_tac[]
QED
