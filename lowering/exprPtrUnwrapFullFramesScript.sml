Theory exprPtrUnwrapFullFrames
Ancestors
  exprPtrUnwrapCopyFrames slotCopyExecution exprSimStorageCopy
  venomMemProps valueEncodingProps venomState venomExecSemantics
  finite_map arithmetic

(* These projections accompany the counted witness, rather than a separate run. *)
Theorem copy_initial_static:
  copy_static (slot_copy_initial cs s) = copy_static s
Proof
  simp[slot_copy_initial_def, copy_static_def, update_var_def, jump_to_def]
QED

Theorem copy_condition_static:
  copy_static (slot_copy_cond_result cs n i s) = copy_static s
Proof
  simp[slot_copy_cond_result_def, copy_static_def, update_var_def, jump_to_def]
QED

Theorem copy_body_static:
  copy_static (slot_copy_body_result cs p d load i s) = copy_static s
Proof
  simp[slot_copy_body_result_def, copy_static_def, update_var_def, jump_to_def,
    mstore_def, write_memory_with_expansion_def]
QED

Theorem copy_body_memory_length:
  LENGTH s.vs_memory <= LENGTH (slot_copy_body_result cs p d load i s).vs_memory
Proof
  simp[slot_copy_body_result_def, update_var_def, jump_to_def, LENGTH_mstore_eq]
QED

Theorem copy_body_exterior_slice:
  w2n d + 32*n < 2**256 /\ i < n /\
  (a+k <= w2n d \/ w2n d+32*n <= a) ==>
  mem_bytes_at a k (slot_copy_body_result cs p d load i s).vs_memory =
    mem_bytes_at a k s.vs_memory
Proof
  strip_tac >>
  `w2n (d+n2w i*32w) = w2n d+32*i` by
    (irule slot_copy_body_nonwrapping >> qexists `n` >> simp[]) >>
  `a+k <= 32*i+w2n d \/ 32*i+w2n d+32 <= a` by decide_tac >>
  simp[slot_copy_body_result_def, update_var_def, jump_to_def, mstore_mem_bytes_at_disjoint]
QED
