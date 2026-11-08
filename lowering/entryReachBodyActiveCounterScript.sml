(* Active counter protection uses the child's effect sites, not ambient readiness. *)
Theory entryReachBodyActiveCounter
Ancestors
  entryReachBodyRegisteredChild entryReachBodyOwnedRegion
  entryReachBodyExactArrayLoop abiEncoderRegisteredEffect abiDecoderContract
  venomMemDefs venomState valueEncoding finite_map pred_set arithmetic

Theorem entry_active_counter_preserved:
  abi_encoder_registered_effect child_ids [(cell,k)] s t /\
  alloca_inv s /\ alloca_inv t /\ FLOOKUP s.vs_allocas cid = SOME (p,32) /\
  entry_owned_region oid root extent cell k s /\ cid <> oid /\ cid NOTIN child_ids ==>
  mload p t = mload p s
Proof
  strip_tac >>
  `cell+k <= p \/ p+32 <= cell` by
    metis_tac[entry_owned_region_counter_separation] >>
  `mem_bytes_at p 32 t.vs_memory = mem_bytes_at p 32 s.vs_memory` by
    (irule entry_registered_child_slice >>
     qpat_assum `abi_encoder_registered_effect _ _ _ _` (irule_at Any) >>
     qpat_assum `FLOOKUP _ _ = SOME _` (irule_at Any) >>
     asm_rewrite_tac[] >> decide_tac) >>
  fs[mem_bytes_at_def, mload_def]
QED

Theorem entry_active_counter_value:
  abi_encoder_registered_effect child_ids [(cell,k)] s t /\
  alloca_inv s /\ alloca_inv t /\ FLOOKUP s.vs_allocas cid = SOME (p,32) /\
  entry_owned_region oid root extent cell k s /\ cid <> oid /\ cid NOTIN child_ids /\
  mload p s = n2w j ==>
  mload p t = n2w j
Proof
  strip_tac >> drule_all entry_active_counter_preserved >> simp[]
QED

(* Counter contents are exported separately: child_end itself records only the
   live operands and source load, not the memory contents of the index slot. *)
Theorem entry_active_counter_child_end:
  lookup_block tail fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts bid iv nv ip hdr /\
  t.vs_current_bb = tail /\ t.vs_inst_idx = LENGTH prefix /\ ~t.vs_halted /\
  eval_operand (Var iv) t = SOME (n2w j) /\ eval_operand ip t = SOME p /\
  eval_operand src t = SOME srcaddr /\ entry_loop_fields s t /\
  abi_decode_load CALLDATALOAD srcaddr s = n2w n /\
  abi_encoder_registered_effect child_ids [(cell,k)] s t /\
  alloca_inv s /\ alloca_inv t /\ FLOOKUP s.vs_allocas cid = SOME (w2n p,32) /\
  entry_owned_region oid root extent cell k s /\ cid <> oid /\ cid NOTIN child_ids /\
  mload (w2n p) s = n2w j ==>
  entry_loop_child_end fn tail prefix bid iv nv ip hdr src p srcaddr n j t /\
  mload (w2n p) t = n2w j /\ FLOOKUP t.vs_allocas cid = SOME (w2n p,32)
Proof
  strip_tac >>
  `mload (w2n p) t = n2w j` by metis_tac[entry_active_counter_value] >>
  `FLOOKUP t.vs_allocas cid = SOME (w2n p,32)` by
    metis_tac[abi_encoder_registered_effect_allocated] >>
  `abi_decode_load CALLDATALOAD srcaddr t = n2w n` by
    fs[entry_loop_fields_def, abi_decode_load_def, abi_decode_source_def] >>
  simp[entry_loop_child_end_def] >> metis_tac[]
QED
