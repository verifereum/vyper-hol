(* Residual SSA frames: variables are related by sigma, instruction indices
   may differ. Terminal comparison additionally ignores both block labels.
   Every other field is retained, including future record extensions.
   TOP-LEVEL: ssa_frame, ssa_execution_frame; reconstruction/update boundaries. *)
Theory ssaFrame
Ancestors
  venomState finite_map

Definition ssa_frame_def:
  ssa_frame (s:venom_state) = s with <| vs_vars := FEMPTY; vs_inst_idx := 0 |>
End

Definition ssa_execution_frame_def:
  ssa_execution_frame (s:venom_state) = s with <|
    vs_vars := FEMPTY; vs_inst_idx := 0;
    vs_current_bb := ""; vs_prev_bb := NONE |>
End

Theorem ssa_frame_idempotent[simp]:
  ssa_frame (ssa_frame s) = ssa_frame s /\
  ssa_execution_frame (ssa_execution_frame s) = ssa_execution_frame s
Proof
  simp[ssa_frame_def, ssa_execution_frame_def]
QED

Theorem ssa_frame_erased_updates[simp]:
  ssa_frame (s with vs_vars := vars) = ssa_frame s /\
  ssa_frame (s with vs_inst_idx := idx) = ssa_frame s /\
  ssa_frame (update_var x v s) = ssa_frame s /\
  ssa_execution_frame (s with vs_vars := vars) = ssa_execution_frame s /\
  ssa_execution_frame (s with vs_inst_idx := idx) = ssa_execution_frame s /\
  ssa_execution_frame (s with vs_current_bb := bb) = ssa_execution_frame s /\
  ssa_execution_frame (s with vs_prev_bb := prev) = ssa_execution_frame s /\
  ssa_execution_frame (update_var x v s) = ssa_execution_frame s
Proof
  simp[ssa_frame_def, ssa_execution_frame_def, update_var_def]
QED

Theorem ssa_frame_reconstruct:
  (ssa_frame s with <| vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx |>) = s /\
  (ssa_execution_frame s with <| vs_vars := s.vs_vars;
    vs_inst_idx := s.vs_inst_idx; vs_current_bb := s.vs_current_bb;
    vs_prev_bb := s.vs_prev_bb |>) = s
Proof
  simp[ssa_frame_def, ssa_execution_frame_def]
QED

Theorem ssa_frame_eq_reconstruct:
  (ssa_frame s1 = ssa_frame s2 <=>
    (s1 with <| vs_vars := s2.vs_vars; vs_inst_idx := s2.vs_inst_idx |>) = s2) /\
  (ssa_execution_frame s1 = ssa_execution_frame s2 <=>
    (s1 with <| vs_vars := s2.vs_vars; vs_inst_idx := s2.vs_inst_idx;
      vs_current_bb := s2.vs_current_bb; vs_prev_bb := s2.vs_prev_bb |>) = s2)
Proof
  simp[ssa_frame_def, ssa_execution_frame_def, venom_state_component_equality]
QED

Theorem ssa_frame_execution:
  ssa_frame s1 = ssa_frame s2 <=>
  ssa_execution_frame s1 = ssa_execution_frame s2 /\
  s1.vs_current_bb = s2.vs_current_bb /\ s1.vs_prev_bb = s2.vs_prev_bb
Proof
  simp[ssa_frame_def, ssa_execution_frame_def, venom_state_component_equality] >>
  metis_tac[]
QED

Theorem ssa_frame_projection:
  (!s. project (ssa_frame s) = project s) /\
  ssa_frame s1 = ssa_frame s2 ==> project s1 = project s2
Proof
  metis_tac[]
QED

Theorem ssa_execution_frame_projection:
  (!s. project (ssa_execution_frame s) = project s) /\
  ssa_execution_frame s1 = ssa_execution_frame s2 ==> project s1 = project s2
Proof
  metis_tac[]
QED

Theorem ssa_frame_update:
  (!s. ssa_frame (update s) = update_frame (ssa_frame s)) /\
  ssa_frame s1 = ssa_frame s2 ==>
  ssa_frame (update s1) = ssa_frame (update s2)
Proof
  metis_tac[]
QED

Theorem ssa_execution_frame_update:
  (!s. ssa_execution_frame (update s) = update_frame (ssa_execution_frame s)) /\
  ssa_execution_frame s1 = ssa_execution_frame s2 ==>
  ssa_execution_frame (update s1) = ssa_execution_frame (update s2)
Proof
  metis_tac[]
QED
