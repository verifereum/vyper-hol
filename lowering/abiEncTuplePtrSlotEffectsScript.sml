Theory abiEncTuplePtrSlotEffects
Ancestors
  abiEncTuplePtrRawSlot abiEncTuplePtrStoreFrame abiTupleEncodeInput
  abiDecodeStaticProps valueEncodingProps bodyPtrDefs words arithmetic pred_set

Theorem abi_tuple_slot_effects_exterior:
  n = type_memory_bytes ce ty /\ (is_word_type ty ==> n = 32) /\
  t.vs_memory = (if is_word_type ty then mstore d v s
    else if n = 0 then s else mcopy d (w2n v) n s).vs_memory /\
  tm.t_mem = (if is_word_type ty then tn.t_mem DIFF {j | d <= j /\ j < d+n}
    else (tn.t_mem DIFF {j | d <= j /\ j < d+n}) UNION
      {d+j | j < n /\ w2n v+j IN tn.t_mem}) ==>
  !i. ~(d <= i /\ i < d+n) ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tm.t_mem <=> i IN tn.t_mem)
Proof
  strip_tac >> Cases_on `is_word_type ty`
  >- (gvs[] >> gen_tac >> disch_tac >>
      irule mem_bytes_at_mstore_outside >> decide_tac) >>
  gvs[] >> gen_tac >> disch_tac >> conj_tac
  >- (Cases_on `type_memory_bytes ce ty = 0` >> gvs[] >>
      irule mcopy_mem_bytes_at_disjoint >> decide_tac) >>
  simp[] >> eq_tac >> simp[] >> rpt strip_tac >> gvs[] >> decide_tac
QED

Theorem abi_tuple_slot_effects_robust:
  n = type_memory_bytes ce ty /\ (is_word_type ty ==> n = 32) /\
  eval_operand op s = SOME v /\
  t.vs_memory = (if is_word_type ty then mstore d v s
    else if n = 0 then s else mcopy d (w2n v) n s).vs_memory /\
  tm.t_mem = (if is_word_type ty then tn.t_mem DIFF {j | d <= j /\ j < d+n}
    else (tn.t_mem DIFF {j | d <= j /\ j < d+n}) UNION
      {d+j | j < n /\ w2n v+j IN tn.t_mem}) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    abi_tuple_encode_input sf ce ty at av op next lo hi (s with vs_memory := mem)) ==>
  !mem. mem_agree_outside tm.t_mem t.vs_memory mem ==>
    abi_tuple_encode_memory sf ce [(op,ty)] [at] [av] d mem
Proof
  strip_tac >> gen_tac >> strip_tac >> irule abi_tuple_slot_robust_contents >>
  qexistsl [`hi`,`lo`,`next`,`s`,`t`,`tm`,`tn`] >> simp[] >>
  Cases_on `is_word_type ty`
  >- gvs[mem_bytes_at_mstore_same] >>
  `abi_tuple_encode_input sf ce ty at av op next lo hi s` by
    (first_x_assum (qspec_then `s.vs_memory` mp_tac) >>
     simp[mem_agree_outside_def]) >>
  qpat_x_assum `abi_tuple_encode_input _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[abi_tuple_encode_input_def] >> strip_tac >>
  gvs[] >> qexists `sb` >> simp[] >>
  (Cases_on `type_memory_bytes ce ty = 0`
   >- simp[valueEncodingDefsTheory.mem_bytes_at_def] >>
   simp[mcopy_mem_bytes_at_same])
QED
