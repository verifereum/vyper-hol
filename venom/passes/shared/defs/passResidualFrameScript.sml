(* Residual frames for shared/concretize/copy-forward relations.
   Clear only independently related or deliberately ignored components.
   All other components, including future fields, remain in the record.
   TOP-LEVEL: five masks; erased updates, reconstruction, projection, transport.
   The four FMP components remain in commute/alloca/concretize frames. *)
Theory passResidualFrame
Ancestors
  venomState finite_map
Libs
  passResidualFrameLib

val _ = Theory.add_ML_dependency "passResidualFrameLib";

Definition commute_frame_def:
  commute_frame (s:venom_state) = s with <|
    vs_vars := FEMPTY; vs_allocas := FEMPTY; vs_alloca_next := 0 |>
End

Definition alloca_remap_frame_def:
  alloca_remap_frame (s:venom_state) = s with <|
    vs_vars := FEMPTY; vs_memory := [];
    vs_allocas := FEMPTY; vs_alloca_next := 0 |>
End

Definition concretize_frame_def:
  concretize_frame (s:venom_state) = s with <|
    vs_vars := FEMPTY; vs_memory := []; vs_allocas := FEMPTY;
    vs_inst_idx := 0; vs_immutables := FEMPTY; vs_alloca_next := 0 |>
End

(* Observable clauses remain separate in copy_fwd_rel, not discarded.
   Frame metadata was already unconstrained by this relation. *)
Definition copy_fwd_frame_def:
  copy_fwd_frame (s:venom_state) = s with <|
    vs_vars := FEMPTY; vs_memory := [];
    vs_accounts := empty_accounts; vs_transient := empty_transient_storage;
    vs_halted := F;
    vs_returndata := []; vs_logs := []; vs_immutables := FEMPTY;
    vs_fmp := 0w; vs_call_entry_fmp := 0w;
    vs_initial_fmp := 0w; vs_return_pc_token := 0w |>
End

Definition icf_frame_def:
  icf_frame (s:venom_state) = s with <|
    vs_vars := FEMPTY; vs_memory := []; vs_alloca_next := 0;
    vs_fmp := 0w; vs_call_entry_fmp := 0w;
    vs_initial_fmp := 0w; vs_return_pc_token := 0w |>
End

(* Goal-only projection avoids the global mask-equality conversion and
   record-update normalizer. Cache the datatype-derived selector rules. *)
val residual_frame_ss = bool_ss ++ rewrites
  [venom_state_component_equality, venom_state_accfupds,
   combinTheory.K_THM];

(* Project each mask equality once, before substituting updated states.
   Erased updates then traverse just one update per retained selector. *)
val residual_frame_update_ss = residual_frame_ss ++ rewrites
  (update_var_def :: map
    (SIMP_CONV residual_frame_ss
      [commute_frame_def, alloca_remap_frame_def, concretize_frame_def,
       copy_fwd_frame_def, icf_frame_def])
    [``commute_frame s1 = commute_frame s2``,
     ``alloca_remap_frame s1 = alloca_remap_frame s2``,
     ``concretize_frame s1 = concretize_frame s2``,
     ``copy_fwd_frame s1 = copy_fwd_frame s2``,
     ``icf_frame s1 = icf_frame s2``]);

Theorem commute_frame_idempotent[simp]:
  commute_frame (commute_frame s) = commute_frame s
Proof
  simp_tac residual_frame_ss [commute_frame_def]
QED

Theorem alloca_remap_frame_idempotent[simp]:
  alloca_remap_frame (alloca_remap_frame s) = alloca_remap_frame s
Proof
  simp_tac residual_frame_ss [alloca_remap_frame_def]
QED

Theorem concretize_frame_idempotent[simp]:
  concretize_frame (concretize_frame s) = concretize_frame s
Proof
  simp_tac residual_frame_ss [concretize_frame_def]
QED

Theorem copy_fwd_frame_idempotent[simp]:
  copy_fwd_frame (copy_fwd_frame s) = copy_fwd_frame s
Proof
  simp_tac residual_frame_ss [copy_fwd_frame_def]
QED

Theorem icf_frame_idempotent[simp]:
  icf_frame (icf_frame s) = icf_frame s
Proof
  simp_tac residual_frame_ss [icf_frame_def]
QED

Theorem commute_frame_erased_updates[simp]:
  commute_frame (s with vs_vars := vars) = commute_frame s /\
  commute_frame (s with vs_allocas := allocas) = commute_frame s /\
  commute_frame (s with vs_alloca_next := next) = commute_frame s /\
  commute_frame (update_var x v s) = commute_frame s
Proof
  simp_tac residual_frame_update_ss []
QED

Theorem alloca_remap_frame_erased_updates[simp]:
  alloca_remap_frame (s with vs_vars := vars) = alloca_remap_frame s /\
  alloca_remap_frame (s with vs_memory := mem) = alloca_remap_frame s /\
  alloca_remap_frame (s with vs_allocas := allocas) = alloca_remap_frame s /\
  alloca_remap_frame (s with vs_alloca_next := next) = alloca_remap_frame s /\
  alloca_remap_frame (update_var x v s) = alloca_remap_frame s
Proof
  simp_tac residual_frame_update_ss []
QED

Theorem concretize_frame_erased_updates[simp]:
  concretize_frame (s with vs_vars := vars) = concretize_frame s /\
  concretize_frame (s with vs_memory := mem) = concretize_frame s /\
  concretize_frame (s with vs_allocas := allocas) = concretize_frame s /\
  concretize_frame (s with vs_inst_idx := idx) = concretize_frame s /\
  concretize_frame (s with vs_immutables := imm) = concretize_frame s /\
  concretize_frame (s with vs_alloca_next := next) = concretize_frame s /\
  concretize_frame (update_var x v s) = concretize_frame s
Proof
  simp_tac residual_frame_update_ss []
QED

Theorem copy_fwd_frame_erased_updates[simp]:
  copy_fwd_frame (s with vs_vars := vars) = copy_fwd_frame s /\
  copy_fwd_frame (s with vs_memory := mem) = copy_fwd_frame s /\
  copy_fwd_frame (s with vs_accounts := accounts) = copy_fwd_frame s /\
  copy_fwd_frame (s with vs_transient := transient) = copy_fwd_frame s /\
  copy_fwd_frame (s with vs_halted := halted) = copy_fwd_frame s /\
  copy_fwd_frame (s with vs_returndata := data) = copy_fwd_frame s /\
  copy_fwd_frame (s with vs_logs := logs) = copy_fwd_frame s /\
  copy_fwd_frame (s with vs_immutables := imm) = copy_fwd_frame s /\
  copy_fwd_frame (s with vs_fmp := fmp) = copy_fwd_frame s /\
  copy_fwd_frame (s with vs_call_entry_fmp := entry) = copy_fwd_frame s /\
  copy_fwd_frame (s with vs_initial_fmp := initial) = copy_fwd_frame s /\
  copy_fwd_frame (s with vs_return_pc_token := token) = copy_fwd_frame s /\
  copy_fwd_frame (update_var x v s) = copy_fwd_frame s
Proof
  simp_tac residual_frame_update_ss []
QED

Theorem icf_frame_erased_updates[simp]:
  icf_frame (s with vs_vars := vars) = icf_frame s /\
  icf_frame (s with vs_memory := mem) = icf_frame s /\
  icf_frame (s with vs_alloca_next := next) = icf_frame s /\
  icf_frame (s with vs_fmp := fmp) = icf_frame s /\
  icf_frame (s with vs_call_entry_fmp := entry) = icf_frame s /\
  icf_frame (s with vs_initial_fmp := initial) = icf_frame s /\
  icf_frame (s with vs_return_pc_token := token) = icf_frame s /\
  icf_frame (update_var x v s) = icf_frame s
Proof
  simp_tac residual_frame_update_ss []
QED

(* Restore exactly the erased components. No retained-field inventory. *)
Theorem commute_frame_reconstruct:
  (commute_frame s with <| vs_vars := s.vs_vars;
    vs_allocas := s.vs_allocas; vs_alloca_next := s.vs_alloca_next |>) = s
Proof
  simp_tac residual_frame_ss [commute_frame_def]
QED

Theorem alloca_remap_frame_reconstruct:
  (alloca_remap_frame s with <| vs_vars := s.vs_vars; vs_memory := s.vs_memory;
    vs_allocas := s.vs_allocas; vs_alloca_next := s.vs_alloca_next |>) = s
Proof
  simp_tac residual_frame_ss [alloca_remap_frame_def]
QED

Theorem concretize_frame_reconstruct:
  (concretize_frame s with <| vs_vars := s.vs_vars; vs_memory := s.vs_memory;
    vs_allocas := s.vs_allocas; vs_inst_idx := s.vs_inst_idx;
    vs_immutables := s.vs_immutables; vs_alloca_next := s.vs_alloca_next |>) = s
Proof
  simp_tac residual_frame_ss [concretize_frame_def]
QED

Theorem copy_fwd_frame_reconstruct:
  (copy_fwd_frame s with <| vs_vars := s.vs_vars; vs_memory := s.vs_memory;
    vs_accounts := s.vs_accounts; vs_transient := s.vs_transient;
    vs_halted := s.vs_halted; vs_returndata := s.vs_returndata;
    vs_logs := s.vs_logs; vs_immutables := s.vs_immutables;
    vs_fmp := s.vs_fmp; vs_call_entry_fmp := s.vs_call_entry_fmp;
    vs_initial_fmp := s.vs_initial_fmp;
    vs_return_pc_token := s.vs_return_pc_token |>) = s
Proof
  simp_tac residual_frame_ss [copy_fwd_frame_def]
QED

Theorem icf_frame_reconstruct:
  (icf_frame s with <| vs_vars := s.vs_vars; vs_memory := s.vs_memory;
    vs_alloca_next := s.vs_alloca_next;
    vs_fmp := s.vs_fmp; vs_call_entry_fmp := s.vs_call_entry_fmp;
    vs_initial_fmp := s.vs_initial_fmp;
    vs_return_pc_token := s.vs_return_pc_token |>) = s
Proof
  simp_tac residual_frame_ss [icf_frame_def]
QED

Theorem commute_frame_eq_reconstruct:
  commute_frame s1 = commute_frame s2 <=>
  (s1 with <| vs_vars := s2.vs_vars; vs_allocas := s2.vs_allocas;
    vs_alloca_next := s2.vs_alloca_next |>) = s2
Proof
  simp_tac residual_frame_ss [commute_frame_def]
QED

Theorem alloca_remap_frame_eq_reconstruct:
  alloca_remap_frame s1 = alloca_remap_frame s2 <=>
  (s1 with <| vs_vars := s2.vs_vars; vs_memory := s2.vs_memory;
    vs_allocas := s2.vs_allocas; vs_alloca_next := s2.vs_alloca_next |>) = s2
Proof
  simp_tac residual_frame_ss [alloca_remap_frame_def]
QED

Theorem concretize_frame_eq_reconstruct:
  concretize_frame s1 = concretize_frame s2 <=>
  (s1 with <| vs_vars := s2.vs_vars; vs_memory := s2.vs_memory;
    vs_allocas := s2.vs_allocas; vs_inst_idx := s2.vs_inst_idx;
    vs_immutables := s2.vs_immutables; vs_alloca_next := s2.vs_alloca_next |>) = s2
Proof
  simp_tac residual_frame_ss [concretize_frame_def]
QED

Theorem copy_fwd_frame_eq_reconstruct:
  copy_fwd_frame s1 = copy_fwd_frame s2 <=>
  (s1 with <| vs_vars := s2.vs_vars; vs_memory := s2.vs_memory;
    vs_accounts := s2.vs_accounts; vs_transient := s2.vs_transient;
    vs_halted := s2.vs_halted; vs_returndata := s2.vs_returndata;
    vs_logs := s2.vs_logs; vs_immutables := s2.vs_immutables;
    vs_fmp := s2.vs_fmp; vs_call_entry_fmp := s2.vs_call_entry_fmp;
    vs_initial_fmp := s2.vs_initial_fmp;
    vs_return_pc_token := s2.vs_return_pc_token |>) = s2
Proof
  simp_tac residual_frame_ss [copy_fwd_frame_def]
QED

Theorem icf_frame_eq_reconstruct:
  icf_frame s1 = icf_frame s2 <=>
  (s1 with <| vs_vars := s2.vs_vars; vs_memory := s2.vs_memory;
    vs_alloca_next := s2.vs_alloca_next;
    vs_fmp := s2.vs_fmp; vs_call_entry_fmp := s2.vs_call_entry_fmp;
    vs_initial_fmp := s2.vs_initial_fmp;
    vs_return_pc_token := s2.vs_return_pc_token |>) = s2
Proof
  simp_tac residual_frame_ss [icf_frame_def]
QED

(* Full equality requires exactly the erased components as well. *)
Theorem commute_frame_eq:
  commute_frame s1 = commute_frame s2 /\
  s1.vs_vars = s2.vs_vars /\ s1.vs_allocas = s2.vs_allocas /\
  s1.vs_alloca_next = s2.vs_alloca_next <=> s1 = s2
Proof
  simp_tac residual_frame_ss [commute_frame_def] >> metis_tac[]
QED

(* Selector-parametric elimination and frame-respecting update transport. *)
Theorem commute_frame_projection:
  (!s. project (commute_frame s) = project s) /\
  commute_frame s1 = commute_frame s2 ==> project s1 = project s2
Proof
  metis_tac[Excl "pass_residual_mask_equality"]
QED

Theorem alloca_remap_frame_projection:
  (!s. project (alloca_remap_frame s) = project s) /\
  alloca_remap_frame s1 = alloca_remap_frame s2 ==> project s1 = project s2
Proof
  metis_tac[Excl "pass_residual_mask_equality"]
QED

Theorem concretize_frame_projection:
  (!s. project (concretize_frame s) = project s) /\
  concretize_frame s1 = concretize_frame s2 ==> project s1 = project s2
Proof
  metis_tac[Excl "pass_residual_mask_equality"]
QED

Theorem copy_fwd_frame_projection:
  (!s. project (copy_fwd_frame s) = project s) /\
  copy_fwd_frame s1 = copy_fwd_frame s2 ==> project s1 = project s2
Proof
  metis_tac[Excl "pass_residual_mask_equality"]
QED

Theorem icf_frame_projection:
  (!s. project (icf_frame s) = project s) /\
  icf_frame s1 = icf_frame s2 ==> project s1 = project s2
Proof
  metis_tac[Excl "pass_residual_mask_equality"]
QED

Theorem commute_frame_update:
  (!s. commute_frame (update s) = update_frame (commute_frame s)) /\
  commute_frame s1 = commute_frame s2 ==>
  commute_frame (update s1) = commute_frame (update s2)
Proof
  metis_tac[Excl "pass_residual_mask_equality"]
QED

Theorem alloca_remap_frame_update:
  (!s. alloca_remap_frame (update s) = update_frame (alloca_remap_frame s)) /\
  alloca_remap_frame s1 = alloca_remap_frame s2 ==>
  alloca_remap_frame (update s1) = alloca_remap_frame (update s2)
Proof
  metis_tac[Excl "pass_residual_mask_equality"]
QED

Theorem concretize_frame_update:
  (!s. concretize_frame (update s) = update_frame (concretize_frame s)) /\
  concretize_frame s1 = concretize_frame s2 ==>
  concretize_frame (update s1) = concretize_frame (update s2)
Proof
  metis_tac[Excl "pass_residual_mask_equality"]
QED

Theorem copy_fwd_frame_update:
  (!s. copy_fwd_frame (update s) = update_frame (copy_fwd_frame s)) /\
  copy_fwd_frame s1 = copy_fwd_frame s2 ==>
  copy_fwd_frame (update s1) = copy_fwd_frame (update s2)
Proof
  metis_tac[Excl "pass_residual_mask_equality"]
QED

Theorem icf_frame_update:
  (!s. icf_frame (update s) = update_frame (icf_frame s)) /\
  icf_frame s1 = icf_frame s2 ==>
  icf_frame (update s1) = icf_frame (update s2)
Proof
  metis_tac[Excl "pass_residual_mask_equality"]
QED
