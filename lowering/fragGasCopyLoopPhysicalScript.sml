(* Publish the guarded counted-copy witness without changing the
   established unguarded storage-copy theorem. *)
Theory fragGasCopyLoopPhysical
Ancestors
  fragGasCopyLoop

Theorem storage_copy_loop_origin_ptr_physical = storage_copy_loop_origin_ptr_walk;
