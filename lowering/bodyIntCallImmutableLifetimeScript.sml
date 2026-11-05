(* Full-capacity constructor immutable frames, including dead array bytes. *)
Theory bodyIntCallImmutableLifetime
Ancestors
  loweringPosts valueEncodingProps valueEncodingProofs valueTypingMemoryProps

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
