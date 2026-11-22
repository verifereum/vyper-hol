(* Closed cuts for the production CREATE snapshot actions. *)
Theory createSizeConcreteSnapshots
Ancestors
  createSizeSnapshotCode createSizeLocationCode createSizeTypedCopyCode

Theorem create_bytecode_snapshot_cut_code:
  create_cut_code {} a (SND (compile_create_snapshot ce vv ty a))
Proof
  irule create_bytecode_snapshot_case >>
  simp[create_slot_to_memory_cut_code, create_imm_copy_cut_code]
QED

Theorem create_vv_snapshot_cut_code:
  create_cut_code {} a (SND (compile_snapshot_vv ce copy vv a))
Proof
  irule create_vv_snapshot_case >>
  simp[create_unwrap_cut_code, create_store_memory_cut_code]
QED
