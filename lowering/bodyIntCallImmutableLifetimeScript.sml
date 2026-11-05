(* Full-capacity constructor immutable frames, including dead array bytes. *)
Theory bodyIntCallImmutableLifetime
Ancestors
  loweringPosts valueEncodingProps valueEncodingProofs valueTypingMemoryProps
  immutableMemoryFrame valueEncoding

Theorem immutable_holds_capacity_frame:
  immutable_holds cenv cx ty raw w es s0 /\
  (cenv.ce_is_ctor ==> !name off itv iv.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
               NONE => FEMPTY
             | SOME imms => get_source_immutables cenv.ce_module imms) name =
      SOME (itv,iv) ==>
    mem_bytes_at off (type_memory_size itv) s.vs_memory =
      mem_bytes_at off (type_memory_size itv) s0.vs_memory) ==>
  immutable_holds cenv cx ty raw w es s
Proof
  simp[immutable_holds_def] >> rpt strip_tac >>
  qexistsl_tac [`name`, `off`, `itv`, `iv`, `k`, `tvt`, `v`] >> simp[] >>
  disj2_tac >> simp[] >>
  `mem_bytes_at off (type_memory_size itv) s.vs_memory =
   mem_bytes_at off (type_memory_size itv) s0.vs_memory` by metis_tac[] >>
  `mem_bytes_at (off+k) (type_memory_size tvt) s.vs_memory =
   mem_bytes_at (off+k) (type_memory_size tvt) s0.vs_memory` by
    (drule mem_bytes_at_agree_window >> simp[]) >>
  irule val_in_memory_mem_agree >>
  conj_tac >- metis_tac[value_has_type_memory_wf] >>
  qexistsl_tac [`type_memory_size tvt`, `s0.vs_memory`] >>
  gvs[arithmeticTheory.ADD_COMM]
QED

Theorem immutable_holds_write_after_capacity:
  immutable_holds cenv cx ty raw w es s /\
  cap <= LENGTH s.vs_memory /\ cap <= at /\
  (!name off itv iv.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
               NONE => FEMPTY
             | SOME imms => get_source_immutables cenv.ce_module imms) name =
      SOME (itv,iv) ==> off + type_memory_size itv <= cap) ==>
  immutable_holds cenv cx ty raw w es (write_memory_with_expansion at bs s)
Proof
  strip_tac >> irule immutable_holds_capacity_frame >>
  qexists_tac `s` >> simp[] >> strip_tac >> rpt gen_tac >> strip_tac >>
  `off + type_memory_size itv <= cap` by metis_tac[] >>
  `TAKE (type_memory_size itv)
      (DROP off (write_memory_with_expansion at bs s).vs_memory) =
   TAKE (type_memory_size itv) (DROP off s.vs_memory)` by
    (irule immutable_write_memory_disjoint >> simp[]) >>
  `off + type_memory_size itv <=
   LENGTH (write_memory_with_expansion at bs s).vs_memory` by
    simp[immutable_write_memory_capacity, arithmeticTheory.MAX_DEF] >>
  simp[mem_bytes_at_def, listTheory.TAKE_APPEND1]
QED

Theorem immutable_holds_reserved_allocation_write:
  immutable_holds cenv cx ty raw w es s /\
  static_position_wf reserved pos sz /\ MEM (0,cap) reserved /\
  0 < w2n sz /\ cap <= LENGTH s.vs_memory /\
  (!name off itv iv.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
               NONE => FEMPTY
             | SOME imms => get_source_immutables cenv.ce_module imms) name =
      SOME (itv,iv) ==> off + type_memory_size itv <= cap) ==>
  immutable_holds cenv cx ty raw w es
    (write_memory_with_expansion (pos+k) bs s)
Proof
  strip_tac >> drule_all immutable_static_position_after_region >> strip_tac >>
  irule immutable_holds_write_after_capacity >> simp[] >>
  qexists_tac `cap` >> simp[] >> metis_tac[]
QED
