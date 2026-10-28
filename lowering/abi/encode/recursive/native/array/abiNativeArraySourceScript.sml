(* TOP-LEVEL: an enclosing traversal preserves the original array header
   and recursive source fields, including their independent strides. *)
Theory abiNativeArraySource
Ancestors
  abiNativeTraversal abiNativeEncodingDefs abiMemoryEncodingFrame abiMemoryEncoding
  memoryReadProps valueEncodingProofs compileEnv venomMemDefs venomState list words arithmetic

Theorem abi_native_array_source:
  !ctx func root_cs root_after source_id target_id root_addr source_capacity dst_addr payload initial cs ss
      entries fields length_word.
    abi_native_memory_ready func root_cs root_after source_id target_id (root_addr:bytes32) source_capacity dst_addr payload initial /\
    abi_native_traversal ctx func root_cs root_after dst_addr payload initial cs ss /\ 32 <= source_capacity /\
    abi_memory_fields entries (w2n root_addr + 32) (source_capacity - 32) initial.vs_memory fields /\
    mload (w2n root_addr) initial = length_word ==>
    abi_memory_fields entries (w2n root_addr + 32) (source_capacity - 32) ss.vs_memory fields /\
    mload (w2n root_addr) ss = length_word
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_native_traversal_source >> DISCH_TAC >>
  qspecl_then [`w2n root_addr`, `source_capacity`, `32`, `ss.vs_memory`, `initial.vs_memory`]
    mp_tac abi_memory_window_suffix >> impl_tac >- (conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  conj_tac
  >- (irule (CONJUNCT2 abi_memory_encoding_frame) >> qexists_tac `initial.vs_memory` >>
      conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  qspecl_then [`w2n root_addr`, `source_capacity`, `ss.vs_memory`, `initial.vs_memory`]
    mp_tac abi_memory_window_header >> impl_tac >- (conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  simp[mem_word_at_eq_mload_proof]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed native array source observation: " ^ name)
  end) (DB.thms "abiNativeArraySource")
