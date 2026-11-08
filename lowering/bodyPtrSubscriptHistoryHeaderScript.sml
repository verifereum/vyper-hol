(* A selected dynamic-array Pop writes its header, not its payload.
   This local transition does not frame enclosing or historical owners. *)
Theory bodyPtrSubscriptHistoryHeader
Ancestors
  abiDecoderArrayPrefix valueEncodingProps valueEncoding venomState list rich_list
  arithmetic

Theorem elems_in_memory_front_last:
  !vs off tv mem.
    vs <> [] /\ elems_in_memory vs off tv mem ==>
    elems_in_memory (FRONT vs) off tv mem /\
    val_in_memory tv (LAST vs)
      (off + (LENGTH vs - 1) * type_memory_size tv) mem
Proof
  rpt gen_tac >> strip_tac >>
  `vs = FRONT vs ++ [LAST vs]` by simp[APPEND_FRONT_LAST] >>
  `elems_in_memory (FRONT vs ++ [LAST vs]) off tv mem` by metis_tac[] >>
  qpat_x_assum `vs = _` kall_tac >>
  `PRE (LENGTH vs) = LENGTH vs - 1` by decide_tac >>
  gvs[elems_in_memory_append, val_in_memory_def, LENGTH_FRONT]
QED

Theorem header_store_preserves_elements:
  !vs b tv s w.
    elems_in_memory vs (b + 32) tv s.vs_memory /\
    elems_val_wf vs tv ==>
    elems_in_memory vs (b + 32) tv (mstore b w s).vs_memory
Proof
  rpt strip_tac >>
  drule (cj 3 mstore_preserves_val_in_memory) >>
  disch_then (qspecl_then [`s`, `b`, `w`] mp_tac) >> simp[]
QED

Theorem pop_header_shortened_array:
  !etv cap vs b s.
    val_in_memory (ArrayTV etv (Dynamic cap)) (ArrayV (DynArrayV vs))
      b s.vs_memory /\ elems_val_wf vs etv /\ vs <> [] ==>
    val_in_memory (ArrayTV etv (Dynamic cap))
      (ArrayV (DynArrayV (FRONT vs))) b
      (mstore b (n2w (LENGTH vs - 1)) s).vs_memory
Proof
  simp[val_in_memory_def] >> rpt strip_tac >>
  drule_all header_store_preserves_elements >>
  disch_then (qspec_then `n2w (LENGTH vs - 1)` assume_tac) >>
  drule_all elems_in_memory_front_last >>
  simp[mstore_mem_word_at_same, LENGTH_FRONT]
QED

Theorem pop_header_last_element:
  !etv cap vs b s.
    val_in_memory (ArrayTV etv (Dynamic cap)) (ArrayV (DynArrayV vs))
      b s.vs_memory /\ elems_val_wf vs etv /\ vs <> [] ==>
    val_in_memory etv (LAST vs)
      (b + 32 + (LENGTH vs - 1) * type_memory_size etv)
      (mstore b (n2w (LENGTH vs - 1)) s).vs_memory
Proof
  simp[val_in_memory_def] >> rpt strip_tac >>
  drule_all header_store_preserves_elements >>
  disch_then (qspec_then `n2w (LENGTH vs - 1)` assume_tac) >>
  drule_all elems_in_memory_front_last >> simp[]
QED
