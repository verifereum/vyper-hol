Theory loadElimKeyReadOperational
Ancestors
  loadElimKeyRead memAliasProps mem2varBlockSimHelpers deadStoreElimProofs
  venomMemDefs venomEffects words

Theorem le_memory_read_nonalias_store:
  wf_alias_sets aliases /\ ~ma_may_alias aliases readloc writeloc /\
  allocas_non_overlapping s /\ memloc_within_alloca readloc s /\
  memloc_within_alloca writeloc s /\
  memloc_runtime_region readloc s = SOME (a,addr_space_word_scale AddrSp_Memory) /\
  memloc_runtime_region writeloc s = SOME (b,addr_space_word_scale AddrSp_Memory) /\
  a < dimword (:256) /\ b < dimword (:256) ==>
  le_read_address AddrSp_Memory a (mstore b value s) =
  le_read_address AddrSp_Memory a s
Proof
  strip_tac >> drule_all ma_may_alias_sound >>
  simp[regions_disjoint_def, addr_space_word_scale_def] >>
  strip_tac >> simp[] >> irule mload_mstore_disjoint >> simp[]
QED

Theorem le_storage_read_nonalias_store:
  wf_alias_sets aliases /\ ~ma_may_alias aliases readloc writeloc /\
  allocas_non_overlapping s /\ memloc_within_alloca readloc s /\
  memloc_within_alloca writeloc s /\
  memloc_runtime_region readloc s = SOME (a,addr_space_word_scale AddrSp_Storage) /\
  memloc_runtime_region writeloc s = SOME (b,addr_space_word_scale AddrSp_Storage) /\
  a < dimword (:256) /\ b < dimword (:256) ==>
  le_read_address AddrSp_Storage a (sstore (n2w b) value s) =
  le_read_address AddrSp_Storage a s
Proof
  strip_tac >> drule_all ma_may_alias_sound >>
  simp[regions_disjoint_def, addr_space_word_scale_def] >>
  strip_tac >> simp[] >> irule sload_sstore_disjoint >>
  simp[n2w_11] >> decide_tac
QED

Theorem le_transient_read_nonalias_store:
  wf_alias_sets aliases /\ ~ma_may_alias aliases readloc writeloc /\
  allocas_non_overlapping s /\ memloc_within_alloca readloc s /\
  memloc_within_alloca writeloc s /\
  memloc_runtime_region readloc s = SOME (a,addr_space_word_scale AddrSp_Transient) /\
  memloc_runtime_region writeloc s = SOME (b,addr_space_word_scale AddrSp_Transient) /\
  a < dimword (:256) /\ b < dimword (:256) ==>
  le_read_address AddrSp_Transient a (tstore (n2w b) value s) =
  le_read_address AddrSp_Transient a s
Proof
  strip_tac >> drule_all ma_may_alias_sound >>
  simp[regions_disjoint_def, addr_space_word_scale_def] >>
  strip_tac >> simp[] >> irule tload_tstore_disjoint >>
  simp[n2w_11] >> decide_tac
QED
