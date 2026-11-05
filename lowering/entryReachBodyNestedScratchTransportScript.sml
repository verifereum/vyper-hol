(* Reusable nested counter slots: the fresh-room obligation disappears on reuse. *)
Theory entryReachBodyNestedScratchTransport
Ancestors
  abiDecoderExecution venomState venomMemDefs finite_map arithmetic

Definition entry_nested_scratch_ready_def:
  entry_nested_scratch_ready iid b cap s <=>
    b <= s.vs_alloca_next /\
    (FLOOKUP s.vs_allocas iid = NONE ==> s.vs_alloca_next+32 <= b+cap) /\
    (!q. FLOOKUP s.vs_allocas iid = SOME (q,32) ==> b <= q /\ q+32 <= b+cap)
End

Theorem entry_nested_scratch_ready_transition:
  entry_nested_scratch_ready iid b cap s /\
  FLOOKUP t.vs_allocas iid = SOME (q,32) /\
  (if FLOOKUP s.vs_allocas iid = NONE then
     q = s.vs_alloca_next /\ t.vs_alloca_next = s.vs_alloca_next+32
   else FLOOKUP s.vs_allocas iid = SOME (q,32) /\
        t.vs_alloca_next = s.vs_alloca_next) ==>
  entry_nested_scratch_ready iid b cap t
Proof
  Cases_on `FLOOKUP s.vs_allocas iid = NONE` >>
  simp[entry_nested_scratch_ready_def] >> rpt strip_tac >> gvs[]
QED

Theorem entry_nested_scratch_ready_cong:
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next ==>
  (entry_nested_scratch_ready iid b cap t <=> entry_nested_scratch_ready iid b cap s)
Proof
  simp[entry_nested_scratch_ready_def]
QED

Theorem entry_nested_scratch_ready_header[local]:
  entry_nested_scratch_ready iid b cap
    (jump_to lbl (abi_decode_header_state iv cv cmp done j n s)) <=>
  entry_nested_scratch_ready iid b cap s
Proof
  simp[entry_nested_scratch_ready_def, jump_to_def,
       abi_decode_header_state_def, update_var_def]
QED

Theorem entry_nested_scratch_ready_backedge[local]:
  entry_nested_scratch_ready iid b cap (jump_to lbl (mstore p w (update_var v x s))) <=>
  entry_nested_scratch_ready iid b cap s
Proof
  simp[entry_nested_scratch_ready_def, jump_to_def, mstore_def, update_var_def]
QED
