(* Residual record frames. Only explicitly excepted fields are erased;
   every other field, including future record extensions, remains in the frame.
   TOP-LEVEL: state_frame, execution_frame; projection, update, reconstruction.
   No fixed-selector characterization is exported. *)
Theory stateFrame
Ancestors
  venomState finite_map

(* Variables are compared separately, modulo a caller-supplied exception set. *)
Definition state_frame_def:
  state_frame (s:venom_state) = s with vs_vars := FEMPTY
End

(* Execution equivalence additionally ignores exactly the three control fields. *)
Definition execution_frame_def:
  execution_frame (s:venom_state) = s with <|
    vs_vars := FEMPTY; vs_current_bb := "";
    vs_inst_idx := 0; vs_prev_bb := NONE |>
End

Theorem state_frame_idempotent[simp]:
  state_frame (state_frame s) = state_frame s
Proof
  simp[state_frame_def]
QED

Theorem execution_frame_idempotent[simp]:
  execution_frame (execution_frame s) = execution_frame s
Proof
  simp[execution_frame_def]
QED

Theorem execution_frame_state_frame[simp]:
  execution_frame (state_frame s) = execution_frame s /\
  state_frame (execution_frame s) = execution_frame s
Proof
  simp[state_frame_def, execution_frame_def]
QED

Theorem state_frame_vars[simp]:
  state_frame (s with vs_vars := vars) = state_frame s
Proof
  simp[state_frame_def]
QED

Theorem execution_frame_updates[simp]:
  execution_frame (s with vs_vars := vars) = execution_frame s /\
  execution_frame (s with vs_current_bb := bb) = execution_frame s /\
  execution_frame (s with vs_inst_idx := idx) = execution_frame s /\
  execution_frame (s with vs_prev_bb := prev) = execution_frame s
Proof
  simp[execution_frame_def]
QED

(* Reconstruction retains unknown fields rather than enumerating them. *)
Theorem state_frame_reconstruct:
  (state_frame s with vs_vars := s.vs_vars) = s
Proof
  simp[state_frame_def]
QED

Theorem execution_frame_reconstruct:
  (execution_frame s with <| vs_vars := s.vs_vars;
    vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
    vs_prev_bb := s.vs_prev_bb |>) = s
Proof
  simp[execution_frame_def]
QED

Theorem state_frame_eq_reconstruct:
  state_frame s1 = state_frame s2 <=>
  (s1 with vs_vars := s2.vs_vars) = s2
Proof
  simp[state_frame_def, venom_state_component_equality]
QED

Theorem execution_frame_eq_reconstruct:
  execution_frame s1 = execution_frame s2 <=>
  (s1 with <| vs_vars := s2.vs_vars; vs_current_bb := s2.vs_current_bb;
    vs_inst_idx := s2.vs_inst_idx; vs_prev_bb := s2.vs_prev_bb |>) = s2
Proof
  simp[execution_frame_def, venom_state_component_equality]
QED

Theorem state_frame_eq:
  state_frame s1 = state_frame s2 /\ s1.vs_vars = s2.vs_vars <=>
  s1 = s2
Proof
  simp[state_frame_def, venom_state_component_equality] >> metis_tac[]
QED

Theorem execution_frame_eq:
  execution_frame s1 = execution_frame s2 /\
  s1.vs_vars = s2.vs_vars /\ s1.vs_current_bb = s2.vs_current_bb /\
  s1.vs_inst_idx = s2.vs_inst_idx /\ s1.vs_prev_bb = s2.vs_prev_bb <=>
  s1 = s2
Proof
  simp[execution_frame_def, venom_state_component_equality] >> metis_tac[]
QED

Theorem state_frame_execution_frame:
  state_frame s1 = state_frame s2 <=>
  execution_frame s1 = execution_frame s2 /\
  s1.vs_current_bb = s2.vs_current_bb /\
  s1.vs_inst_idx = s2.vs_inst_idx /\ s1.vs_prev_bb = s2.vs_prev_bb
Proof
  simp[state_frame_def, execution_frame_def,
       venom_state_component_equality] >> metis_tac[]
QED

Theorem frame_update_var[simp]:
  state_frame (update_var x v s) = state_frame s /\
  execution_frame (update_var x v s) = execution_frame s
Proof
  simp[update_var_def]
QED

(* Selector-parametric projection: usable unchanged for a future field. *)
Theorem state_frame_projection:
  (!s. project (state_frame s) = project s) /\
  state_frame s1 = state_frame s2 ==> project s1 = project s2
Proof
  metis_tac[]
QED

Theorem execution_frame_projection:
  (!s. project (execution_frame s) = project s) /\
  execution_frame s1 = execution_frame s2 ==> project s1 = project s2
Proof
  metis_tac[]
QED

(* A frame-respecting update can be transported without knowing its fields. *)
Theorem state_frame_update:
  (!s. state_frame (update s) = update_frame (state_frame s)) /\
  state_frame s1 = state_frame s2 ==>
  state_frame (update s1) = state_frame (update s2)
Proof
  metis_tac[]
QED

Theorem execution_frame_update:
  (!s. execution_frame (update s) = update_frame (execution_frame s)) /\
  execution_frame s1 = execution_frame s2 ==>
  execution_frame (update s1) = execution_frame (update s2)
Proof
  metis_tac[]
QED
