(* Parameterized execution equivalence: extensible frame/reconstruction contract.
   The masks erase exactly the independently related register environment and,
   for terminal results only, the deliberately ignored control-flow fields.
   Every other component (including future components) remains in the record. *)
Theory execEquivParamDefs
Ancestors
  stateEquiv venomExecSemantics venomState venomInst finite_map
Libs
  execEquivParamMaskLib

val _ = Theory.add_ML_dependency "execEquivParamMaskLib";

Definition vsr_frame_def:
  vsr_frame s = s with vs_vars := FEMPTY
End

Definition vsr_term_frame_def:
  vsr_term_frame s = s with <| vs_vars := FEMPTY;
    vs_prev_bb := NONE; vs_current_bb := ""; vs_inst_idx := 0 |>
End

Definition valid_state_rel_def:
  valid_state_rel
    (R_ok : venom_state -> venom_state -> bool)
    (R_term : venom_state -> venom_state -> bool) <=>
    (!s1 s2. R_ok s1 s2 ==> vsr_frame s1 = vsr_frame s2) /\
    (!s1 s2. R_term s1 s2 ==> vsr_term_frame s1 = vsr_term_frame s2) /\
    (!s1 s2 x v. R_ok s1 s2 ==>
                  R_ok (update_var x v s1) (update_var x v s2)) /\
    (!s1 s2 x v. R_term s1 s2 ==>
                  R_term (update_var x v s1) (update_var x v s2)) /\
    (!s1 s2 op. R_ok s1 s2 /\
       (!x. op = Var x ==> lookup_var x s1 = lookup_var x s2) ==>
       eval_operand op s1 = eval_operand op s2) /\
    (!s1 s2 op. R_term s1 s2 /\
       (!x. op = Var x ==> lookup_var x s1 = lookup_var x s2) ==>
       eval_operand op s1 = eval_operand op s2) /\
    (!s1 s2. R_ok s1 s2 ==> R_term s1 s2) /\
    (!s. R_ok s s) /\
    (!s. R_term s s) /\
    (!s1 s2 t1 t2. R_ok s1 s2 /\
      t1.vs_vars = s1.vs_vars /\ t2.vs_vars = s2.vs_vars /\
      vsr_frame t1 = vsr_frame t2 ==> R_ok t1 t2) /\
    (!s1 s2 t1 t2. R_term s1 s2 /\
      t1.vs_vars = s1.vs_vars /\ t2.vs_vars = s2.vs_vars /\
      vsr_term_frame t1 = vsr_term_frame t2 ==> R_term t1 t2)
End

(* Public reconstruction premises retain the entire residual record. *)
Theorem vsr_reconstruct_R_ok:
  valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
  t1.vs_vars = s1.vs_vars /\ t2.vs_vars = s2.vs_vars /\
  vsr_frame t1 = vsr_frame t2 ==> R_ok t1 t2
Proof
  rw[valid_state_rel_def, Excl "vsr_complete_mask_equality"] >> metis_tac[]
QED

Theorem vsr_reconstruct_R_term:
  valid_state_rel R_ok R_term /\ R_term s1 s2 /\
  t1.vs_vars = s1.vs_vars /\ t2.vs_vars = s2.vs_vars /\
  vsr_term_frame t1 = vsr_term_frame t2 ==> R_term t1 t2
Proof
  rw[valid_state_rel_def, Excl "vsr_complete_mask_equality"] >> metis_tac[]
QED

(* Exact reconstruction, not an exhaustive selector characterization. *)
Theorem vsr_frame_restore[simp]:
  vsr_frame s with vs_vars := s.vs_vars = s
Proof
  simp[vsr_frame_def]
QED

Theorem vsr_term_frame_restore[simp]:
  vsr_term_frame s with <| vs_vars := s.vs_vars;
    vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
    vs_inst_idx := s.vs_inst_idx |> = s
Proof
  simp[vsr_term_frame_def]
QED

Theorem vsr_frame_idempotent[simp]:
  vsr_frame (vsr_frame s) = vsr_frame s /\
  vsr_term_frame (vsr_term_frame s) = vsr_term_frame s /\
  vsr_term_frame (vsr_frame s) = vsr_term_frame s /\
  vsr_frame (vsr_term_frame s) = vsr_term_frame s
Proof
  simp[vsr_frame_def, vsr_term_frame_def]
QED

Theorem vsr_frame_vars[simp]:
  vsr_frame (s with vs_vars := env) = vsr_frame s /\
  vsr_term_frame (s with vs_vars := env) = vsr_term_frame s /\
  vsr_frame (update_var x v s) = vsr_frame s /\
  vsr_term_frame (update_var x v s) = vsr_term_frame s
Proof
  simp[vsr_frame_def, vsr_term_frame_def, update_var_def]
QED

Theorem vsr_term_frame_control[simp]:
  vsr_term_frame (s with vs_prev_bb := prev) = vsr_term_frame s /\
  vsr_term_frame (s with vs_current_bb := current) = vsr_term_frame s /\
  vsr_term_frame (s with vs_inst_idx := idx) = vsr_term_frame s
Proof
  simp[vsr_term_frame_def]
QED

Theorem vsr_frame_shared_updates[simp]:
  vsr_frame (s with vs_memory := m) = vsr_frame s with vs_memory := m /\
  vsr_frame (s with vs_transient := t) = vsr_frame s with vs_transient := t /\
  vsr_frame (s with vs_accounts := a) = vsr_frame s with vs_accounts := a /\
  vsr_frame (s with vs_returndata := r) = vsr_frame s with vs_returndata := r /\
  vsr_frame (s with vs_halted := h) = vsr_frame s with vs_halted := h /\
  vsr_frame (s with vs_logs := l) = vsr_frame s with vs_logs := l /\
  vsr_frame (s with vs_immutables := im) = vsr_frame s with vs_immutables := im /\
  vsr_frame (s with vs_allocas := al) = vsr_frame s with vs_allocas := al /\
  vsr_frame (s with vs_alloca_next := n) = vsr_frame s with vs_alloca_next := n /\
  vsr_frame (s with vs_fmp := fmp) = vsr_frame s with vs_fmp := fmp /\
  vsr_frame (s with vs_inst_idx := i) = vsr_frame s with vs_inst_idx := i /\
  vsr_frame (s with vs_prev_bb := p) = vsr_frame s with vs_prev_bb := p /\
  vsr_frame (s with vs_current_bb := c) = vsr_frame s with vs_current_bb := c
Proof
  simp[vsr_frame_def]
QED

Theorem vsr_term_frame_shared_updates[simp]:
  vsr_term_frame (s with vs_memory := m) = vsr_term_frame s with vs_memory := m /\
  vsr_term_frame (s with vs_transient := t) = vsr_term_frame s with vs_transient := t /\
  vsr_term_frame (s with vs_accounts := a) = vsr_term_frame s with vs_accounts := a /\
  vsr_term_frame (s with vs_returndata := r) = vsr_term_frame s with vs_returndata := r /\
  vsr_term_frame (s with vs_halted := h) = vsr_term_frame s with vs_halted := h /\
  vsr_term_frame (s with vs_logs := l) = vsr_term_frame s with vs_logs := l /\
  vsr_term_frame (s with vs_immutables := im) = vsr_term_frame s with vs_immutables := im /\
  vsr_term_frame (s with vs_allocas := al) = vsr_term_frame s with vs_allocas := al /\
  vsr_term_frame (s with vs_alloca_next := n) = vsr_term_frame s with vs_alloca_next := n /\
  vsr_term_frame (s with vs_fmp := fmp) = vsr_term_frame s with vs_fmp := fmp
Proof
  simp[vsr_term_frame_def]
QED

(* Removing redundant writes without expanding residual-record equality. *)
Theorem vsr_frame_same_updates[simp]:
  (vsr_frame s with vs_memory := s.vs_memory) = vsr_frame s /\
  (vsr_frame s with vs_transient := s.vs_transient) = vsr_frame s /\
  (vsr_frame s with vs_accounts := s.vs_accounts) = vsr_frame s /\
  (vsr_frame s with vs_returndata := s.vs_returndata) = vsr_frame s /\
  (vsr_frame s with vs_halted := s.vs_halted) = vsr_frame s /\
  (vsr_frame s with vs_logs := s.vs_logs) = vsr_frame s /\
  (vsr_frame s with vs_immutables := s.vs_immutables) = vsr_frame s /\
  (vsr_frame s with vs_allocas := s.vs_allocas) = vsr_frame s /\
  (vsr_frame s with vs_alloca_next := s.vs_alloca_next) = vsr_frame s /\
  (vsr_frame s with vs_fmp := s.vs_fmp) = vsr_frame s /\
  (vsr_frame s with vs_inst_idx := s.vs_inst_idx) = vsr_frame s /\
  (vsr_frame s with vs_prev_bb := s.vs_prev_bb) = vsr_frame s /\
  (vsr_frame s with vs_current_bb := s.vs_current_bb) = vsr_frame s
Proof
  simp[vsr_frame_def, venom_state_component_equality]
QED

Theorem vsr_term_frame_same_updates[simp]:
  (vsr_term_frame s with vs_memory := s.vs_memory) = vsr_term_frame s /\
  (vsr_term_frame s with vs_transient := s.vs_transient) = vsr_term_frame s /\
  (vsr_term_frame s with vs_accounts := s.vs_accounts) = vsr_term_frame s /\
  (vsr_term_frame s with vs_returndata := s.vs_returndata) = vsr_term_frame s /\
  (vsr_term_frame s with vs_halted := s.vs_halted) = vsr_term_frame s /\
  (vsr_term_frame s with vs_logs := s.vs_logs) = vsr_term_frame s /\
  (vsr_term_frame s with vs_immutables := s.vs_immutables) = vsr_term_frame s /\
  (vsr_term_frame s with vs_allocas := s.vs_allocas) = vsr_term_frame s /\
  (vsr_term_frame s with vs_alloca_next := s.vs_alloca_next) = vsr_term_frame s /\
  (vsr_term_frame s with vs_fmp := s.vs_fmp) = vsr_term_frame s
Proof
  simp[vsr_term_frame_def, venom_state_component_equality]
QED

Theorem vsr_frame_setup_callee_mask[simp]:
  setup_callee fn args (vsr_frame s) = setup_callee fn args s
Proof
  simp[setup_callee_def, vsr_frame_def]
QED

Theorem vsr_frame_setup_callee:
  vsr_frame s1 = vsr_frame s2 ==> setup_callee fn args s1 = setup_callee fn args s2
Proof
  strip_tac >>
  qpat_x_assum `vsr_frame s1 = _`
    (mp_tac o AP_TERM ``setup_callee fn args``) >> simp[]
QED


