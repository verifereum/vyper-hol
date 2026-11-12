(* State/ghost projections sufficient to carry coverage between segments. *)
Theory exprPtrUnwrapFrames
Ancestors
  bodyPtrDefs decoderGhostFramePtr ghostPcTransportPtr ptrDiscipline
  ptrSafeRun venomState venomExecSemantics finite_map

Theorem copy_ptr_covers_transport:
  lookup_var root t = lookup_var root s /\
  FLOOKUP H root = FLOOKUP G root /\
  op_taint tm (Var root) = op_taint tn (Var root) ==>
  (ptr_covers H tm root t n <=> ptr_covers G tn root s n)
Proof
  simp[ptr_covers_def]
QED

Theorem copy_allocas_update[simp]:
  allocas_from lo (update_var name value s) = allocas_from lo s /\
  allocas_below_fmp (update_var name value s) = allocas_below_fmp s
Proof
  simp[allocas_from_def, allocas_below_fmp_def, update_var_def]
QED

Theorem copy_allocas_inst_idx[simp]:
  allocas_from lo (s with vs_inst_idx := k) = allocas_from lo s /\
  allocas_below_fmp (s with vs_inst_idx := k) = allocas_below_fmp s
Proof
  simp[allocas_from_def, allocas_below_fmp_def]
QED

Theorem copy_update_inst_idx[simp]:
  update_var name value (s with vs_inst_idx := k) =
    (update_var name value s) with vs_inst_idx := k
Proof
  simp[update_var_def]
QED

Theorem copy_mstore_inst_idx[simp]:
  mstore off value (s with vs_inst_idx := k) =
    (mstore off value s) with vs_inst_idx := k
Proof
  simp[mstore_def]
QED
