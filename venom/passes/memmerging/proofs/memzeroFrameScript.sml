(* Residual memzero frame. Variables are separately related; only memory
   is ignored. Every other component, including future fields, is retained.
   TOP-LEVEL: memzero_frame; reconstruction, projection and update boundaries. *)
Theory memzeroFrame
Ancestors
  venomState finite_map

Definition memzero_frame_def:
  memzero_frame (s:venom_state) = s with <| vs_vars := FEMPTY; vs_memory := [] |>
End

Theorem memzero_frame_idempotent[simp]:
  memzero_frame (memzero_frame s) = memzero_frame s
Proof
  simp[memzero_frame_def]
QED

Theorem memzero_frame_erased_updates[simp]:
  memzero_frame (s with vs_vars := vars) = memzero_frame s /\
  memzero_frame (s with vs_memory := mem) = memzero_frame s /\
  memzero_frame (update_var x v s) = memzero_frame s
Proof
  simp[memzero_frame_def, update_var_def]
QED

Theorem memzero_frame_reconstruct:
  (memzero_frame s with <| vs_vars := s.vs_vars; vs_memory := s.vs_memory |>) = s
Proof
  simp[memzero_frame_def]
QED

Theorem memzero_frame_eq_reconstruct:
  memzero_frame s1 = memzero_frame s2 <=>
  (s1 with <| vs_vars := s2.vs_vars; vs_memory := s2.vs_memory |>) = s2
Proof
  simp[memzero_frame_def, venom_state_component_equality]
QED

Theorem memzero_frame_projection:
  (!s. project (memzero_frame s) = project s) /\
  memzero_frame s1 = memzero_frame s2 ==> project s1 = project s2
Proof
  metis_tac[]
QED

Theorem memzero_frame_update:
  (!s. memzero_frame (update s) = update_frame (memzero_frame s)) /\
  memzero_frame s1 = memzero_frame s2 ==>
  memzero_frame (update s1) = memzero_frame (update s2)
Proof
  metis_tac[]
QED
