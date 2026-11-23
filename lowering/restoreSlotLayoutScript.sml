(* Static placement facts for the storage/transient restore suffix.  The
   compiler's block certificate is retained under a subject-specific name so
   upper restore proofs can consume it without depending on implementation
   scripts directly. *)
Theory restoreSlotLayout
Ancestors
  exprPtrUnwrapEnsureShape exprSimPtrTopLevelStorageCopy
  fragExec compileEnv venomInst venomState list rich_list arithmetic

Theorem restore_slot_loop_fetch_bounds =
  toplevel_copy_compile_blocks

Theorem restore_slot_linear_fetch_bounds =
  ensure_slot_memory_loop_code
