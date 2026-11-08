(* Restore enclosing resources across an allocating nested decoder. *)
Theory entryReachBodyEnclosingCounter
Ancestors
  entryReachBodyOwnedLoop entryReachBodyOwnedRegion
  entryReachBodyRegisteredChild abiEncoderRegisteredEffect
  venomMemDefs venomState valueEncoding finite_map pred_set arithmetic

Theorem entry_enclosing_resources_restore:
  entry_owned_loop_resources ctx fn site cid p oid root extent d cap s /\
  entry_owned_loop_resources ctx fn site iid q oid root extent c k t /\
  abi_encoder_registered_effect ids [(c,k)] s t ==>
  entry_owned_loop_resources ctx fn site cid p oid root extent d cap t
Proof
  simp_tac bool_ss [entry_owned_loop_resources_def, entry_owned_region_def] >>
  strip_tac >>
  `FLOOKUP t.vs_allocas cid = SOME (p,32)` by
    metis_tac[abi_encoder_registered_effect_allocated] >>
  `FLOOKUP t.vs_allocas oid = SOME (root,extent)` by
    metis_tac[abi_encoder_registered_effect_allocated] >>
  asm_rewrite_tac[]
QED

Theorem entry_enclosing_counter_preserved:
  entry_owned_loop_resources ctx fn site cid p oid root extent d cap s /\
  alloca_inv t /\ cid <> oid /\ cid NOTIN ids /\
  d <= c /\ c+k <= d+cap /\
  abi_encoder_registered_effect ids [(c,k)] s t ==>
  mload p t = mload p s
Proof
  strip_tac >>
  `alloca_inv s /\ FLOOKUP s.vs_allocas cid = SOME (p,32) /\
   entry_owned_region oid root extent d cap s` by
    fs[entry_owned_loop_resources_def] >>
  `d+cap <= p \/ p+32 <= d` by
    metis_tac[entry_owned_region_counter_separation] >>
  `mem_bytes_at p 32 t.vs_memory = mem_bytes_at p 32 s.vs_memory` by
    (irule entry_registered_child_slice >>
     conj_tac >- asm_rewrite_tac[] >>
     qexistsl_tac [`c`,`32`,`p`,`ids`,`k`,`cid`] >>
     asm_rewrite_tac[] >> decide_tac) >>
  fs[mem_bytes_at_def, mload_def]
QED
