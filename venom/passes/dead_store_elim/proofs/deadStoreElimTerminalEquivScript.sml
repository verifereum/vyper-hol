Theory deadStoreElimTerminalEquiv
Ancestors
  deadStoreElimEquiv deadStoreElimDefs deadStoreElimFrame venomState
Libs
  deadStoreElimFrameLib

val _ = augment_srw_ss [deadStoreElimFrameLib.frame_ss];

Theorem dse_equiv_set_returndata:
  dse_equiv sp s t ==>
  dse_equiv sp (set_returndata bytes s) (set_returndata bytes t)
Proof
  simp[dse_equiv_def, set_returndata_def, lookup_var_def]
QED

Theorem dse_equiv_halt_state:
  dse_equiv sp s t ==> dse_equiv sp (halt_state s) (halt_state t)
Proof
  simp[dse_equiv_def, halt_state_def, lookup_var_def]
QED

Theorem dse_equiv_revert_state:
  dse_equiv sp s t ==> dse_equiv sp (revert_state s) (revert_state t)
Proof
  simp[dse_equiv_def, revert_state_def, lookup_var_def]
QED
