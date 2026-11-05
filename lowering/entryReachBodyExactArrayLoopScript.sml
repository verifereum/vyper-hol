(* Exact-source-list array loop shell: observable fields and indexed memory. *)
Theory entryReachBodyExactArrayLoop
Ancestors
  calldataDynOwned abiDecoderExecution abiDecoderFrameCompose
  valueEncoding valueEncodingProps venomState venomExecSemantics words list
  arithmetic

Definition entry_loop_fields_def:
  entry_loop_fields s t <=>
    (t.vs_accounts, t.vs_transient, t.vs_logs, t.vs_tx_ctx,
     t.vs_block_ctx, t.vs_outcomes, t.vs_requests, t.vs_pending_deletions,
     t.vs_gas_readings, t.vs_fmp, t.vs_call_ctx, t.vs_data_section) =
    (s.vs_accounts, s.vs_transient, s.vs_logs, s.vs_tx_ctx,
     s.vs_block_ctx, s.vs_outcomes, s.vs_requests, s.vs_pending_deletions,
     s.vs_gas_readings, s.vs_fmp, s.vs_call_ctx, s.vs_data_section)
End

Theorem entry_loop_fields_refl[local]:
  entry_loop_fields s s
Proof
  simp[entry_loop_fields_def]
QED

Theorem entry_loop_fields_trans[local]:
  entry_loop_fields s t /\ entry_loop_fields t u ==> entry_loop_fields s u
Proof
  simp[entry_loop_fields_def] >> metis_tac[]
QED

Theorem entry_loop_header_fields[local]:
  t = jump_to lbl (abi_decode_header_state iv cv cmp done j n s) ==>
  entry_loop_fields s t /\ t.vs_halted = s.vs_halted /\
  t.vs_current_bb = lbl /\ t.vs_inst_idx = 0
Proof
  simp[abi_decode_header_state_def, update_var_def, jump_to_def,
       entry_loop_fields_def]
QED

Theorem entry_loop_backedge_fields[local]:
  t = jump_to hdr (mstore p (n2w (SUC j)) (update_var nv (n2w (SUC j)) s)) ==>
  entry_loop_fields s t /\ t.vs_halted = s.vs_halted /\
  t.vs_current_bb = hdr /\ t.vs_inst_idx = 0
Proof
  simp[update_var_def, jump_to_def, mstore_def,
       write_memory_with_expansion_def, entry_loop_fields_def]
QED

Definition entry_loop_prefix_def:
  entry_loop_prefix tv xs d j s <=>
    !k. k < j ==> val_in_memory tv (EL k xs)
      (d+32+k*type_memory_size tv) s.vs_memory
End

Theorem entry_loop_prefix_zero[local]:
  entry_loop_prefix tv xs d 0 s
Proof
  simp[entry_loop_prefix_def]
QED

Theorem entry_loop_prefix_extend[local]:
  entry_loop_prefix tv xs d j s /\
  val_in_memory tv (EL j xs) (d+32+j*type_memory_size tv) s.vs_memory ==>
  entry_loop_prefix tv xs d (SUC j) s
Proof
  simp[entry_loop_prefix_def] >> rpt strip_tac >>
  Cases_on `k = j` >> gvs[] >> first_x_assum irule >> decide_tac
QED

Theorem entry_loop_prefix_header[local]:
  entry_loop_prefix tv xs d j s ==>
  entry_loop_prefix tv xs d j (jump_to lbl (abi_decode_header_state iv cv cmp done i n s))
Proof
  simp[entry_loop_prefix_def, jump_to_def, abi_decode_header_state_def, update_var_def]
QED

Theorem entry_loop_prefix_backedge[local]:
  entry_loop_prefix tv xs d j s /\ j <= LENGTH xs /\ EVERY (val_wf tv) xs /\
  (!k. k < j ==> p+32 <= d+32+k*type_memory_size tv \/
     d+32+k*type_memory_size tv+type_memory_size tv <= p) ==>
  entry_loop_prefix tv xs d j
    (jump_to hdr (mstore p (n2w (SUC i)) (update_var nv (n2w (SUC i)) s)))
Proof
  simp_tac bool_ss [entry_loop_prefix_def] >> rpt strip_tac >>
  `val_wf tv (EL k xs)` by
    (gvs[EVERY_EL] >> first_x_assum irule >> decide_tac) >>
  `val_in_memory tv (EL k xs) (d+32+k*type_memory_size tv) s.vs_memory` by simp[] >>
  `p+32 <= d+32+k*type_memory_size tv \/
   d+32+k*type_memory_size tv+type_memory_size tv <= p` by simp[] >>
  `val_in_memory tv (EL k xs) (d+32+k*type_memory_size tv)
    (mstore p (n2w (SUC i)) (s with vs_memory := s.vs_memory)).vs_memory` by
    (irule (cj 1 mstore_preserves_val_in_memory) >> simp[]) >>
  gvs[update_var_def, jump_to_def, mstore_def, write_memory_with_expansion_def]
QED
