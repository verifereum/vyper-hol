(* Registered physical writes and allocator invariants at primitive endpoints. *)
Theory abiEncoderPrimitiveEffect
Ancestors
  abiEncoderRegisteredEffect abiEncoderWrites
  valueEncodingProps venomMemDefs venomState venomExecSemantics
  finite_map pred_set list arithmetic

Theorem abi_encoder_registered_effect_mstore:
  (!a. EVERY (\(b,n). a < b \/ b+n <= a) outs /\
    (!i b sz. i IN ids /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==>
      a < b \/ b+sz <= a) ==> a < p \/ p+32 <= a) ==>
  abi_encoder_registered_effect ids outs s (mstore p w s)
Proof
  strip_tac >>
  `!a. EVERY (\(b,n). a < b \/ b+n <= a) outs /\
    (!i b sz. i IN ids /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==>
      a < b \/ b+sz <= a) ==>
    mem_bytes_at a 1 (mstore p w s).vs_memory = mem_bytes_at a 1 s.vs_memory` by
    (rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >>
     `a < p \/ p+32 <= a` by metis_tac[] >> decide_tac) >>
  simp_tac bool_ss [abi_encoder_registered_effect_def, abi_encoder_write_observations] >>
  asm_rewrite_tac[] >>
  simp[mstore_def, write_memory_with_expansion_def]
QED

Theorem abi_encoder_registered_slot_store:
  id IN ids /\ FLOOKUP s.vs_allocas id = SOME (p,32) ==>
  abi_encoder_registered_effect ids outs s (mstore p w s)
Proof
  strip_tac >> irule abi_encoder_registered_effect_mstore >>
  rpt strip_tac >> first_x_assum irule >> qexists_tac `id` >> simp[]
QED

Theorem abi_encoder_output_store:
  d <= p /\ p+32 <= d+n ==>
  abi_encoder_registered_effect ids [(d,n)] s (mstore p w s)
Proof
  strip_tac >> irule abi_encoder_registered_effect_mstore >> simp[] >>
  rpt strip_tac >> decide_tac
QED

Theorem abi_encoder_primitive_alloca_inv:
  (alloca_inv s ==> alloca_inv (mstore p w s)) /\
  (alloca_inv s ==> alloca_inv (mcopy d src n s)) /\
  (alloca_inv s ==> alloca_inv (update_var x v s))
Proof
  simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
    mstore_def, mcopy_def, write_memory_with_expansion_def, update_var_def]
QED

Theorem abi_encoder_registered_output_copy:
  abi_encoder_registered_effect ids [(d,n)] s (mcopy d src n s)
Proof
  `!a. (a < d \/ d+n <= a) ==>
    mem_bytes_at a 1 (mcopy d src n s).vs_memory = mem_bytes_at a 1 s.vs_memory` by
    (rpt strip_tac >> irule mcopy_mem_bytes_at_disjoint >> decide_tac) >>
  simp_tac bool_ss [abi_encoder_registered_effect_def, abi_encoder_write_observations] >>
  conj_tac
  >- (simp[] >> metis_tac[]) >>
  simp[mcopy_def, write_memory_with_expansion_def]
QED

Theorem abi_encoder_register_alloca_inv:
  alloca_inv s /\ FLOOKUP s.vs_allocas id = NONE ==>
  alloca_inv (s with <|vs_allocas := s.vs_allocas |+ (id,(s.vs_alloca_next,32));
    vs_alloca_next := s.vs_alloca_next+32|>)
Proof
  simp_tac bool_ss [alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
  strip_tac >> conj_tac
  >- (simp[FLOOKUP_UPDATE] >> rpt strip_tac >>
      Cases_on `id = a1` >> Cases_on `id = a2` >> gvs[] >> metis_tac[]) >>
  simp[FLOOKUP_UPDATE] >> rpt strip_tac >>
  Cases_on `id = aid` >> gvs[] >>
  rename1 `base' + sz <= s.vs_alloca_next + 32` >>
  `base'+sz <= s.vs_alloca_next` by metis_tac[] >> decide_tac
QED

Theorem abi_encoder_registered_allocation:
  id IN ids /\ FLOOKUP s.vs_allocas id = NONE ==>
  abi_encoder_registered_effect ids outs s
    (s with <|vs_allocas := s.vs_allocas |+ (id,(p,32));
      vs_alloca_next := next|>)
Proof
  simp[abi_encoder_registered_effect_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `id = i` >> gvs[]
QED

Theorem abi_encoder_registered_update_var:
  abi_encoder_registered_effect ids outs s (update_var x v s)
Proof
  simp[abi_encoder_registered_effect_def, update_var_def]
QED

Theorem abi_encoder_registered_inst_idx:
  abi_encoder_registered_effect ids outs s (s with vs_inst_idx := ix)
Proof
  simp[abi_encoder_registered_effect_def]
QED

Theorem abi_encoder_inst_idx_alloca_inv:
  alloca_inv s ==> alloca_inv (s with vs_inst_idx := ix)
Proof
  simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def]
QED
