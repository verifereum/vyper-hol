Theory loadElimOccurrenceRead
Ancestors
  loadElimOccurrence loadElimKeyReadOperational loadElimKeyRead
  venomExecProofs venomState

(* Fixed-address reads ignore the bookkeeping changed at occurrence edges. *)
Theorem le_read_address_vars[simp]:
  le_read_address space a (s with vs_vars := vars) = le_read_address space a s
Proof
  Cases_on `space` >>
  simp[le_read_address_def, mload_def, sload_def, tload_def,
       read_memory_def, contract_storage_def, contract_transient_def]
QED

Theorem le_read_address_index[simp]:
  le_read_address space a (s with vs_inst_idx := n) = le_read_address space a s
Proof
  Cases_on `space` >>
  simp[le_read_address_def, mload_def, sload_def, tload_def,
       read_memory_def, contract_storage_def, contract_transient_def]
QED

Theorem le_read_address_phis:
  eval_phis s insts = OK t ==>
  le_read_address space a t = le_read_address space a s
Proof
  strip_tac >> drule eval_phis_only_updates_vs_vars >>
  disch_then SUBST1_TAC >> simp[]
QED

Theorem le_read_address_occ_after:
  le_read_address space a (le_occ_after e) =
  le_read_address space a (le_occ_post e)
Proof
  Cases_on `e` >> simp[le_occ_after_def, le_occ_post_def] >>
  IF_CASES_TAC >> simp[]
QED

Theorem le_calldata_read_occ:
  le_occ_valid C fn e ==>
  le_read_address AddrSp_Calldata a (le_occ_post e) =
  le_read_address AddrSp_Calldata a (le_occ_pre e)
Proof
  Cases_on `e` >>
  simp[le_occ_valid_def, le_occ_post_def, le_occ_pre_def] >>
  strip_tac
  >- (drule le_calldata_read_step >> simp[]) >>
  drule le_calldata_read_phis >> simp[]
QED

Theorem le_data_read_occ:
  le_occ_valid C fn e ==>
  le_read_address AddrSp_Data a (le_occ_post e) =
  le_read_address AddrSp_Data a (le_occ_pre e)
Proof
  Cases_on `e` >>
  simp[le_occ_valid_def, le_occ_post_def, le_occ_pre_def] >>
  strip_tac
  >- (drule le_data_read_step >> simp[]) >>
  drule le_data_read_phis >> simp[]
QED

Theorem le_phi_read_occ:
  le_occ_valid C fn (PhiOcc bb s t) ==>
  le_read_address space a (le_occ_post (PhiOcc bb s t)) =
  le_read_address space a (le_occ_pre (PhiOcc bb s t))
Proof
  simp[le_occ_valid_def, le_occ_post_def, le_occ_pre_def] >>
  strip_tac >> drule le_read_address_phis >> simp[]
QED

Theorem le_calldata_read_occ_after:
  le_occ_valid C fn e ==>
  le_read_address AddrSp_Calldata a (le_occ_after e) =
  le_read_address AddrSp_Calldata a (le_occ_pre e)
Proof
  rewrite_tac[le_read_address_occ_after] >>
  metis_tac[le_calldata_read_occ]
QED

Theorem le_data_read_occ_after:
  le_occ_valid C fn e ==>
  le_read_address AddrSp_Data a (le_occ_after e) =
  le_read_address AddrSp_Data a (le_occ_pre e)
Proof
  rewrite_tac[le_read_address_occ_after] >>
  metis_tac[le_data_read_occ]
QED

Theorem le_phi_read_occ_after:
  le_occ_valid C fn (PhiOcc bb s t) ==>
  le_read_address space a (le_occ_after (PhiOcc bb s t)) =
  le_read_address space a (le_occ_pre (PhiOcc bb s t))
Proof
  rewrite_tac[le_read_address_occ_after] >>
  metis_tac[le_phi_read_occ]
QED
