(* Capacity widening transports live data only; unused capacity may be tainted. *)
Theory appendDynamicTransportPtr
Ancestors liveArrayTransportPtr typedCopyRobustTransportPtr
  valueTypingMemoryProps exprSimProps vyperTyping list arithmetic

Theorem append_dynamic_live_transport:
  !tv vs sn dn src dst tn tn' mem mem'.
    value_has_type (ArrayTV tv (Dynamic sn)) (ArrayV (DynArrayV vs)) /\
    sn <= dn /\
    (!m. mem_agree_outside tn mem m ==>
      val_in_memory (ArrayTV tv (Dynamic sn)) (ArrayV (DynArrayV vs)) src m) /\
    (!m. mem_agree_outside tn' mem' m ==>
      mem_word_at dst m = n2w (LENGTH vs)) /\
    mem_bytes_at (dst+32) (LENGTH vs * type_memory_size tv) mem' =
      mem_bytes_at (src+32) (LENGTH vs * type_memory_size tv) mem /\
    (!i. i < LENGTH vs * type_memory_size tv ==>
      (dst+32+i IN tn' <=> src+32+i IN tn)) ==>
    !m. mem_agree_outside tn' mem' m ==>
      val_in_memory (ArrayTV tv (Dynamic dn)) (ArrayV (DynArrayV vs)) dst m
Proof
  rpt gen_tac >> strip_tac >> rpt strip_tac >>
  simp[valueEncodingPropsTheory.val_in_memory_dynarray] >>
  irule robust_elems_in_memory_copy_transport >>
  conj_tac
  >- (gvs[value_has_type_def, all_have_type_EVERY, EVERY_MEM] >>
      metis_tac[value_has_type_memory_wf, val_footprint_le]) >>
  qexistsl_tac [`mem`, `mem'`, `LENGTH vs * type_memory_size tv`, `src+32`, `tn`, `tn'`] >>
  gvs[valueEncodingPropsTheory.val_in_memory_dynarray]
QED
