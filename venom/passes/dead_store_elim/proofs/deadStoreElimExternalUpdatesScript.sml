Theory deadStoreElimExternalUpdates
Ancestors
  deadStoreElimLocal deadStoreElimPending deadStoreElimMemory deadStoreElimSafety
  deadStoreElimDefs deadStoreElimStoreSteps venomExecSemantics venomState list
Libs
  deadStoreElimFrameLib

val _ = augment_srw_ss [deadStoreElimFrameLib.frame_ss];

(* All fields adopted from an external outcome, without the separate
 * return-buffer memory write. DELEGATECALL keeps outcomes/requests unchanged. *)
Definition dse_external_update_def:
  dse_external_update accounts ts logs deletions returndata outcomes requests s =
    s with <| vs_accounts := accounts; vs_transient := ts;
              vs_logs := logs; vs_pending_deletions := deletions;
              vs_returndata := returndata; vs_outcomes := outcomes;
              vs_requests := requests |>
End

Theorem dse_external_update_allocas[simp]:
  (dse_external_update accounts ts logs dels rd os rqs s).vs_allocas = s.vs_allocas
Proof
  simp[dse_external_update_def]
QED

Theorem dse_local_agrees_external_update:
  dse_local_agrees AddrSp_Memory P s t ==>
  dse_local_agrees AddrSp_Memory P
    (dse_external_update accounts ts logs dels rd os rqs s)
    (dse_external_update accounts ts logs dels rd os rqs t)
Proof
  simp[dse_external_update_def, dse_local_agrees_def, dse_pending_space_def,
       dse_safety_agrees_def, dse_operational_agrees_def, dse_equiv_def,
       dse_pending_memory_def, dse_memory_byte_def, lookup_var_def]
QED

