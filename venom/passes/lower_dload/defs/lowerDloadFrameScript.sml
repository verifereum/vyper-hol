(* LowerDload residual frames. Scratch memory, return data, alloca map and
   bump pointer may differ; variables are compared separately modulo fresh
   names. The terminal frame additionally ignores all three control fields.
   No other field is erased. TOP-LEVEL: ld_frame, ld_execution_frame. *)
Theory lowerDloadFrame
Ancestors
  venomState finite_map

Definition ld_frame_def:
  ld_frame (s:venom_state) = s with <|
    vs_vars := FEMPTY; vs_memory := []; vs_returndata := [];
    vs_allocas := FEMPTY; vs_alloca_next := 0 |>
End

Definition ld_execution_frame_def:
  ld_execution_frame (s:venom_state) = ld_frame s with <|
    vs_current_bb := ""; vs_inst_idx := 0; vs_prev_bb := NONE |>
End

Theorem ld_frame_idempotent[simp]:
  ld_frame (ld_frame s) = ld_frame s /\
  ld_execution_frame (ld_execution_frame s) = ld_execution_frame s
Proof
  simp[ld_frame_def, ld_execution_frame_def]
QED

Theorem ld_frame_erased_updates[simp]:
  ld_frame (s with vs_vars := vars) = ld_frame s /\
  ld_frame (s with vs_memory := mem) = ld_frame s /\
  ld_frame (s with vs_returndata := data) = ld_frame s /\
  ld_frame (s with vs_allocas := allocas) = ld_frame s /\
  ld_frame (s with vs_alloca_next := next) = ld_frame s /\
  ld_frame (update_var x v s) = ld_frame s /\
  ld_execution_frame (s with vs_vars := vars) = ld_execution_frame s /\
  ld_execution_frame (s with vs_memory := mem) = ld_execution_frame s /\
  ld_execution_frame (s with vs_returndata := data) = ld_execution_frame s /\
  ld_execution_frame (s with vs_allocas := allocas) = ld_execution_frame s /\
  ld_execution_frame (s with vs_alloca_next := next) = ld_execution_frame s /\
  ld_execution_frame (s with vs_current_bb := bb) = ld_execution_frame s /\
  ld_execution_frame (s with vs_inst_idx := idx) = ld_execution_frame s /\
  ld_execution_frame (s with vs_prev_bb := prev) = ld_execution_frame s /\
  ld_execution_frame (update_var x v s) = ld_execution_frame s
Proof
  simp[ld_frame_def, ld_execution_frame_def, update_var_def]
QED

Theorem ld_frame_reconstruct:
  (ld_frame s with <| vs_vars := s.vs_vars; vs_memory := s.vs_memory;
    vs_returndata := s.vs_returndata; vs_allocas := s.vs_allocas;
    vs_alloca_next := s.vs_alloca_next |>) = s /\
  (ld_execution_frame s with <| vs_vars := s.vs_vars; vs_memory := s.vs_memory;
    vs_returndata := s.vs_returndata; vs_allocas := s.vs_allocas;
    vs_alloca_next := s.vs_alloca_next; vs_current_bb := s.vs_current_bb;
    vs_inst_idx := s.vs_inst_idx; vs_prev_bb := s.vs_prev_bb |>) = s
Proof
  simp[ld_frame_def, ld_execution_frame_def]
QED

Theorem ld_frame_eq_reconstruct:
  (ld_frame s1 = ld_frame s2 <=>
    (s1 with <| vs_vars := s2.vs_vars; vs_memory := s2.vs_memory;
      vs_returndata := s2.vs_returndata; vs_allocas := s2.vs_allocas;
      vs_alloca_next := s2.vs_alloca_next |>) = s2) /\
  (ld_execution_frame s1 = ld_execution_frame s2 <=>
    (s1 with <| vs_vars := s2.vs_vars; vs_memory := s2.vs_memory;
      vs_returndata := s2.vs_returndata; vs_allocas := s2.vs_allocas;
      vs_alloca_next := s2.vs_alloca_next; vs_current_bb := s2.vs_current_bb;
      vs_inst_idx := s2.vs_inst_idx; vs_prev_bb := s2.vs_prev_bb |>) = s2)
Proof
  simp[ld_frame_def, ld_execution_frame_def, venom_state_component_equality]
QED

Theorem ld_frame_execution:
  ld_frame s1 = ld_frame s2 <=>
  ld_execution_frame s1 = ld_execution_frame s2 /\
  s1.vs_current_bb = s2.vs_current_bb /\ s1.vs_inst_idx = s2.vs_inst_idx /\
  s1.vs_prev_bb = s2.vs_prev_bb
Proof
  simp[ld_frame_def, ld_execution_frame_def, venom_state_component_equality] >>
  metis_tac[]
QED

Theorem ld_frame_projection:
  (!s. project (ld_frame s) = project s) /\
  ld_frame s1 = ld_frame s2 ==> project s1 = project s2
Proof
  metis_tac[]
QED

Theorem ld_execution_frame_projection:
  (!s. project (ld_execution_frame s) = project s) /\
  ld_execution_frame s1 = ld_execution_frame s2 ==> project s1 = project s2
Proof
  metis_tac[]
QED

Theorem ld_frame_update:
  (!s. ld_frame (update s) = update_frame (ld_frame s)) /\
  ld_frame s1 = ld_frame s2 ==>
  ld_frame (update s1) = ld_frame (update s2)
Proof
  metis_tac[]
QED

Theorem ld_execution_frame_update:
  (!s. ld_execution_frame (update s) = update_frame (ld_execution_frame s)) /\
  ld_execution_frame s1 = ld_execution_frame s2 ==>
  ld_execution_frame (update s1) = ld_execution_frame (update s2)
Proof
  metis_tac[]
QED
