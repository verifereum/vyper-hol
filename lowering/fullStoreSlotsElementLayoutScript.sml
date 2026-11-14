(* Semantic resources for recursive array-to-slot stores. *)
Theory fullStoreSlotsElementLayout
Ancestors
  typedCopyLayoutPtr exprSimAggregateEncoding valueTypingMemoryProps
  valueEncoding valueEncodingDefs vyperTyping loweringPosts exprSimProps
  bodyPtrDefs representationCleanPtr vyperLookupStorage list rich_list arithmetic

Theorem store_slots_element_resources:
  all_have_type tv vs /\ j < LENGTH vs /\
  (!m. mem_agree_outside tn.t_mem mem m ==> elems_in_memory vs addr tv m) /\
  addr + LENGTH vs * type_memory_size tv <= frontier /\
  addr + LENGTH vs * type_memory_size tv < dimword(:256) /\
  slot + LENGTH vs * type_slot_size tv <= dimword(:256) ==>
  value_has_type tv (EL j vs) /\
  j * type_memory_size tv + val_store_size tv (EL j vs) <=
    LENGTH vs * type_memory_size tv /\
  addr + j * type_memory_size tv + val_store_size tv (EL j vs) <= frontier /\
  addr + j * type_memory_size tv + val_store_size tv (EL j vs) < dimword(:256) /\
  (!m. mem_agree_outside tn.t_mem mem m ==>
    val_in_memory tv (EL j vs) (addr + j * type_memory_size tv) m) /\
  slot + j * type_slot_size tv + type_slot_size tv <= dimword(:256)
Proof
  strip_tac >>
  `value_has_type tv (EL j vs)` by
    (fs[all_have_type_EVERY,EVERY_EL]) >>
  `j * type_memory_size tv + val_store_size tv (EL j vs) <=
     LENGTH vs * type_memory_size tv` by
    (qspecl_then [`tv`,`EL j vs`,`j`,`LENGTH vs`,`0`]
       mp_tac array_child_store_size_contained >> simp[]) >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- decide_tac >>
  conj_tac >- decide_tac >>
  conj_tac >- metis_tac[elems_in_memory_EL] >>
  `j * type_slot_size tv + type_slot_size tv <=
     LENGTH vs * type_slot_size tv` by
    (irule array_index_element_end_bound >> simp[]) >>
  decide_tac
QED

Theorem store_slots_element_support_step:
  FLAT (GENLIST (\i. MAP ((+) (i*slots)) (EL i supports)) (SUC j)) =
  FLAT (GENLIST (\i. MAP ((+) (i*slots)) (EL i supports)) j) ++
  MAP ((+) (j*slots)) (EL j supports)
Proof
  simp[GENLIST,FLAT_SNOC]
QED

Theorem store_slots_dynarray_resources:
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  (!m. mem_agree_outside tn.t_mem mem m ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) addr m) /\
  addr + val_store_size (ArrayTV tv (Dynamic cap))
    (ArrayV (DynArrayV vs)) <= frontier /\
  addr + type_memory_size (ArrayTV tv (Dynamic cap)) < dimword(:256) /\
  slot + type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword(:256) ==>
  all_have_type tv vs /\ LENGTH vs <= cap /\
  (!m. mem_agree_outside tn.t_mem mem m ==>
    mem_word_at addr m = n2w (LENGTH vs) /\
    elems_in_memory vs (addr+32) tv m) /\
  (!i. addr <= i /\ i < addr+32 ==> i NOTIN tn.t_mem) /\
  addr + 32 + LENGTH vs * type_memory_size tv <= frontier /\
  addr + 32 + LENGTH vs * type_memory_size tv < dimword(:256) /\
  slot + 1 + LENGTH vs * type_slot_size tv <= dimword(:256)
Proof
  strip_tac >>
  `all_have_type tv vs /\ LENGTH vs <= cap` by
    gvs[value_has_type_def] >>
  `!m. mem_agree_outside tn.t_mem mem m ==>
    mem_word_at addr m = n2w (LENGTH vs) /\
    elems_in_memory vs (addr+32) tv m` by
    (gvs[valueEncodingDefsTheory.val_in_memory_def]) >>
  `!i. addr <= i /\ i < addr+32 ==> i NOTIN tn.t_mem` by
    metis_tac[robust_mem_word_at_clean] >>
  `LENGTH vs * type_memory_size tv <= cap * type_memory_size tv /\
   LENGTH vs * type_slot_size tv <= cap * type_slot_size tv` by
    (conj_tac >> irule LESS_MONO_MULT >> simp[]) >>
  qpat_x_assum `addr + val_store_size _ _ <= frontier` mp_tac >>
  qpat_x_assum `addr + type_memory_size _ < _` mp_tac >>
  qpat_x_assum `slot + type_slot_size _ <= _` mp_tac >>
  simp[val_store_size_def,type_memory_size_def,vyperValueTheory.type_slot_size_def] >>
  decide_tac
QED
