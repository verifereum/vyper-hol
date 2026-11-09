(* Semantic child layout boundaries for pointer-safe typed copying. *)
Theory typedCopyLayoutPtr
Ancestors
  bodyPtrDefs tupleMemoryLayout exprSimAggregateEncoding valueEncodingProofs
  valueTypingMemoryProps arithmetic loweringPosts exprSimProps
Theorem tuple_in_memory_robust_element:
  !vs tvs addr mem tn i.
    LENGTH vs = LENGTH tvs /\ i < LENGTH tvs /\
    (!m. mem_agree_outside tn.t_mem mem m ==>
         tuple_in_memory vs tvs addr m) ==>
    !m. mem_agree_outside tn.t_mem mem m ==>
        val_in_memory (EL i tvs) (EL i vs)
          (addr + SUM (MAP type_memory_size (TAKE i tvs))) m
Proof
  metis_tac[tuple_in_memory_element]
QED

Theorem tuple_child_footprint_contained:
  !tvs vs i.
    values_have_types tvs vs /\ i < LENGTH tvs ==>
    SUM (MAP type_memory_size (TAKE i tvs)) +
      val_footprint (EL i tvs) (EL i vs) <= SUM (MAP type_memory_size tvs)
Proof
  rpt strip_tac >> drule_all tuple_element_footprint >>
  drule tuple_element_interval >> decide_tac
QED

Theorem dynarray_in_memory_robust_element:
  !tv cap vs addr mem tn i.
    i < LENGTH vs /\
    (!m. mem_agree_outside tn.t_mem mem m ==>
         val_in_memory (ArrayTV tv (Dynamic cap))
           (ArrayV (DynArrayV vs)) addr m) ==>
    !m. mem_agree_outside tn.t_mem mem m ==>
        val_in_memory tv (EL i vs)
          (addr + 32 + i * type_memory_size tv) m
Proof
  rpt strip_tac >>
  `elems_in_memory vs (addr + 32) tv m` by
    (first_x_assum drule >> simp[valueEncodingTheory.val_in_memory_def]) >>
  drule_all elems_in_memory_EL >> simp[]
QED

Theorem sarray_in_memory_robust_element:
  !tv cap kvs addr mem tn i v.
    i < cap /\
    v = (case ALOOKUP kvs i of SOME x => x | NONE => default_value tv) /\
    (!m. mem_agree_outside tn.t_mem mem m ==>
         val_in_memory (ArrayTV tv (Fixed cap))
           (ArrayV (SArrayV kvs)) addr m) ==>
    !m. mem_agree_outside tn.t_mem mem m ==>
        val_in_memory tv v (addr + i * type_memory_size tv) m
Proof
  rpt strip_tac >>
  `val_in_memory (ArrayTV tv (Fixed cap))
     (ArrayV (SArrayV kvs)) addr m` by metis_tac[] >>
  gvs[valueEncodingTheory.val_in_memory_def] >>
  Cases_on `ALOOKUP kvs i` >> gvs[] >>
  metis_tac[kvs_in_memory_lookup]
QED

(* Common arithmetic boundary for live elements of either array layout.
   The dynamic header is represented separately by prefix=32. *)
Theorem array_child_footprint_contained:
  !tv v i cap prefix.
    value_has_type tv v /\ i < cap ==>
    prefix + i * type_memory_size tv + val_footprint tv v <=
    prefix + cap * type_memory_size tv
Proof
  rpt strip_tac >>
  `val_footprint tv v <= type_memory_size tv` by
    metis_tac[exprSimPropsTheory.val_footprint_le, value_has_type_memory_wf] >>
  `SUC i * type_memory_size tv <= cap * type_memory_size tv` by
    (irule LESS_MONO_MULT >> decide_tac) >>
  qpat_x_assum `SUC i * _ <= _` mp_tac >>
  pure_rewrite_tac[MULT_CLAUSES] >> decide_tac
QED

Theorem dynarray_length_footprint_contained:
  !tv cap vs.
    32 <= val_footprint (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs))
Proof
  simp[loweringPostsTheory.val_footprint_def, valueEncodingTheory.type_memory_size_def]
QED

Theorem dynarray_in_memory_robust_length:
  !tv cap vs addr mem tn.
    (!m. mem_agree_outside tn.t_mem mem m ==>
         val_in_memory (ArrayTV tv (Dynamic cap))
           (ArrayV (DynArrayV vs)) addr m) ==>
    !m. mem_agree_outside tn.t_mem mem m ==>
        mem_word_at addr m = n2w (LENGTH vs)
Proof
  simp[valueEncodingTheory.val_in_memory_def]
QED

Theorem dynarray_live_child_footprint:
  !tv cap vs i.
    value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
    i < LENGTH vs ==>
    32 + i * type_memory_size tv + val_footprint tv (EL i vs) <=
      val_footprint (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs))
Proof
  rpt strip_tac >>
  gvs[vyperTypingTheory.value_has_type_def] >>
  `value_has_type tv (EL i vs)` by
    (fs[vyperTypingTheory.all_have_type_EVERY, listTheory.EVERY_EL]) >>
  `i < cap` by decide_tac >>
  drule_all array_child_footprint_contained >>
  disch_then (qspec_then `32` mp_tac) >>
  CONV_TAC (RAND_CONV (RAND_CONV (SIMP_CONV (srw_ss())
    [loweringPostsTheory.val_footprint_def, valueEncodingTheory.type_memory_size_def]))) >>
  decide_tac
QED

Theorem sarray_live_child_footprint:
  !tv cap kvs i v.
    value_has_type (ArrayTV tv (Fixed cap)) (ArrayV (SArrayV kvs)) /\
    i < cap /\ ALOOKUP kvs i = SOME v ==>
    i * type_memory_size tv + val_footprint tv v <=
      val_footprint (ArrayTV tv (Fixed cap)) (ArrayV (SArrayV kvs))
Proof
  rpt strip_tac >> gvs[vyperTypingTheory.value_has_type_def] >>
  `value_has_type tv v` by metis_tac[sparse_has_type_lookup] >>
  drule_all array_child_footprint_contained >>
  disch_then (qspec_then `0` mp_tac) >>
  CONV_TAC (RAND_CONV (RAND_CONV (SIMP_CONV (srw_ss())
    [loweringPostsTheory.val_footprint_def, valueEncodingTheory.type_memory_size_def]))) >>
  decide_tac
QED

Theorem store_size_in_slot:
  !tv v off bound.
    val_wf tv v /\ off + type_memory_size tv <= bound ==>
    off + val_store_size tv v <= bound
Proof
  rpt strip_tac >> drule exprSimPropsTheory.val_store_size_le >> decide_tac
QED

Theorem tuple_child_store_size_contained:
  !tvs vs i.
    values_have_types tvs vs /\ i < LENGTH tvs ==>
    SUM (MAP type_memory_size (TAKE i tvs)) +
      val_store_size (EL i tvs) (EL i vs) <= SUM (MAP type_memory_size tvs)
Proof
  Induct >> Cases_on `vs` >> simp[vyperTypingTheory.value_has_type_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `i` >> gvs[]
  >- (drule value_has_type_memory_wf >> strip_tac >>
      drule exprSimPropsTheory.val_store_size_le >> decide_tac) >>
  first_x_assum drule_all >> decide_tac
QED

Theorem array_child_store_size_contained:
  !tv v i cap prefix.
    value_has_type tv v /\ i < cap ==>
    prefix + i * type_memory_size tv + val_store_size tv v <=
      prefix + cap * type_memory_size tv
Proof
  rpt strip_tac >> irule store_size_in_slot >>
  reverse conj_tac >- metis_tac[value_has_type_memory_wf] >>
  `SUC i * type_memory_size tv <= cap * type_memory_size tv` by
    (irule LESS_MONO_MULT >> decide_tac) >>
  qpat_x_assum `SUC i * _ <= _` mp_tac >>
  pure_rewrite_tac[MULT_CLAUSES] >> decide_tac
QED
