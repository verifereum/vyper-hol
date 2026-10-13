(* Residual mem2var frame. Variables and promoted memory are independently
   related; instruction indices and call-entry FMP were already ignored.
   All remaining components, including future fields, are retained.
   TOP-LEVEL: m2v_frame; reconstruction, projection and update boundaries. *)
Theory mem2varFrame
Ancestors
  venomState finite_map

Definition m2v_frame_def:
  m2v_frame (s:venom_state) = s with <|
    vs_vars := FEMPTY; vs_memory := []; vs_inst_idx := 0;
    vs_call_entry_fmp := 0w |>
End

Theorem m2v_frame_idempotent[simp]:
  m2v_frame (m2v_frame s) = m2v_frame s
Proof
  simp[m2v_frame_def]
QED

Theorem m2v_frame_erased_updates[simp]:
  m2v_frame (s with vs_vars := vars) = m2v_frame s /\
  m2v_frame (s with vs_memory := mem) = m2v_frame s /\
  m2v_frame (s with vs_inst_idx := idx) = m2v_frame s /\
  m2v_frame (s with vs_call_entry_fmp := fmp) = m2v_frame s /\
  m2v_frame (update_var x v s) = m2v_frame s
Proof
  simp[m2v_frame_def, update_var_def]
QED

Theorem m2v_frame_reconstruct:
  (m2v_frame s with <| vs_vars := s.vs_vars; vs_memory := s.vs_memory;
    vs_inst_idx := s.vs_inst_idx; vs_call_entry_fmp := s.vs_call_entry_fmp |>) = s
Proof
  simp[m2v_frame_def]
QED

Theorem m2v_frame_eq_reconstruct:
  m2v_frame s1 = m2v_frame s2 <=>
  (s1 with <| vs_vars := s2.vs_vars; vs_memory := s2.vs_memory;
    vs_inst_idx := s2.vs_inst_idx; vs_call_entry_fmp := s2.vs_call_entry_fmp |>) = s2
Proof
  simp[m2v_frame_def, venom_state_component_equality]
QED

Theorem m2v_frame_projection:
  (!s. project (m2v_frame s) = project s) /\
  m2v_frame s1 = m2v_frame s2 ==> project s1 = project s2
Proof
  metis_tac[]
QED

Theorem m2v_frame_update:
  (!s. m2v_frame (update s) = update_frame (m2v_frame s)) /\
  m2v_frame s1 = m2v_frame s2 ==>
  m2v_frame (update s1) = m2v_frame (update s2)
Proof
  metis_tac[]
QED
