(* TOP-LEVEL: memory-copy code changes RAM, SSA variables and control only.
   Its frame retains external state and the complete allocator state. *)
Theory typedCopyStateFrame
Ancestors
  abiStateFrame venomExecSemantics venomState list

Definition copy_state_frame_def:
  copy_state_frame before after <=>
    abi_state_frame before after /\
    after.vs_allocas = before.vs_allocas /\ after.vs_alloca_next = before.vs_alloca_next
End

Theorem copy_state_frame_refl[simp]:
  !ss. copy_state_frame ss ss
Proof
  simp[copy_state_frame_def]
QED

Theorem copy_state_frame_sym:
  !before after. copy_state_frame before after ==> copy_state_frame after before
Proof
  simp[copy_state_frame_def, abi_state_frame_def]
QED

Theorem copy_state_frame_trans:
  !before middle after.
    copy_state_frame before middle /\ copy_state_frame middle after ==>
    copy_state_frame before after
Proof
  simp[copy_state_frame_def, abi_state_frame_def]
QED

Theorem copy_state_frame_mutable[simp]:
  !before after mem vars prev bb index.
    (copy_state_frame before (after with vs_memory := mem) <=> copy_state_frame before after) /\
    (copy_state_frame before (after with vs_vars := vars) <=> copy_state_frame before after) /\
    (copy_state_frame before (after with vs_prev_bb := prev) <=> copy_state_frame before after) /\
    (copy_state_frame before (after with vs_current_bb := bb) <=> copy_state_frame before after) /\
    (copy_state_frame before (after with vs_inst_idx := index) <=> copy_state_frame before after)
Proof
  simp[copy_state_frame_def, abi_state_frame_def]
QED

Theorem copy_state_frame_primitives[simp]:
  !before after name value offset bytes src byte_count label.
    (copy_state_frame before (update_var name value after) <=> copy_state_frame before after) /\
    (copy_state_frame before (mstore offset value after) <=> copy_state_frame before after) /\
    (copy_state_frame before (write_memory_with_expansion offset bytes after) <=> copy_state_frame before after) /\
    (copy_state_frame before (mcopy offset src byte_count after) <=> copy_state_frame before after) /\
    (copy_state_frame before (jump_to label after) <=> copy_state_frame before after)
Proof
  simp[update_var_def, mstore_def, write_memory_with_expansion_def, mcopy_def, jump_to_def, LET_THM]
QED

Theorem copy_state_frame_external:
  !before after. copy_state_frame before after ==> abi_state_frame before after
Proof
  simp[copy_state_frame_def]
QED

Theorem copy_state_frame_var_image:
  !before after index.
    after with vs_vars := before.vs_vars = before with vs_inst_idx := index ==>
    copy_state_frame before after
Proof
  rpt gen_tac >> disch_then (mp_tac o AP_TERM ``copy_state_frame before``) >> simp[]
QED

Theorem copy_state_frame_allocator:
  !before after. copy_state_frame before after ==>
    after.vs_allocas = before.vs_allocas /\ after.vs_alloca_next = before.vs_alloca_next
Proof
  simp[copy_state_frame_def]
QED
