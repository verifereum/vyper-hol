Theory lowerDloadPhaseBoundary
Ancestors
  lowerDloadPairedBoundary lowerDloadAllocation ptrDiscipline venomExecSemantics
  venomState venomInstProps list arithmetic

Inductive ld_target_prefix:
[~zero:]
  (!C code t0 u0. ld_target_prefix C code t0 u0 0 t0 u0)
[~succ:]
  (!C code t0 u0 n t u z fuel.
    ld_target_prefix C code t0 u0 n t u /\ n < LENGTH code /\
    step_inst fuel C (EL n code) t = OK z ==>
    ld_target_prefix C code t0 u0 (SUC n)
      (z with vs_inst_idx := SUC t.vs_inst_idx)
      (step_taint (EL n code) t z u))
End

Theorem ld_target_prefix_bound:
  !C code t0 u0 n t u.
    ld_target_prefix C code t0 u0 n t u ==> n <= LENGTH code
Proof
  ho_match_mp_tac ld_target_prefix_ind >> simp[]
QED

Theorem ld_target_prefix_empty:
  ld_target_prefix C code t0 u0 0 t u <=> t = t0 /\ u = u0
Proof
  once_rewrite_tac[ld_target_prefix_cases] >> simp[]
QED

Theorem ld_target_prefix_step_iff:
  ld_target_prefix C code t0 u0 (SUC n) t u <=>
  ?v w z fuel. ld_target_prefix C code t0 u0 n v w /\
    n < LENGTH code /\ step_inst fuel C (EL n code) v = OK z /\
    t = z with vs_inst_idx := SUC v.vs_inst_idx /\
    u = step_taint (EL n code) v z w
Proof
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [ld_target_prefix_cases])) >>
  simp[] >> metis_tac[]
QED

Theorem ld_target_prefix_index:
  !C code t0 u0 n t u.
    ld_target_prefix C code t0 u0 n t u ==>
    t.vs_inst_idx = t0.vs_inst_idx + n
Proof
  ho_match_mp_tac ld_target_prefix_ind >> simp[ADD_CLAUSES]
QED

Theorem ld_target_prefix_source_witness:
  P s /\ ld_target_prefix C code t0 u0 n t u /\ n < LENGTH code /\
  step_inst fuel C (EL n code) t = OK z ==>
  P s /\ ld_target_prefix C code t0 u0 (SUC n)
    (z with vs_inst_idx := SUC t.vs_inst_idx)
    (step_taint (EL n code) t z u)
Proof
  metis_tac[ld_target_prefix_rules]
QED

(* Interface probes for the four-step and two-step configured expansions. *)
Theorem ld_target_prefix_expansion_bounds[local]:
  (ld_target_prefix C [a;b;c;d] t0 u0 n t u ==> n <= 4) /\
  (ld_target_prefix C [a;b] t0 u0 n t u ==> n <= 2)
Proof
  conj_tac >> strip_tac >> drule ld_target_prefix_bound >> simp[]
QED

(* Suspended caller facts deliberately contain no saved-memory relation. *)
Definition ld_saved_locals_def:
  ld_saved_locals V E keys d A f g <=>
    f.lf_inst.inst_outputs = g.lf_inst.inst_outputs /\
    LIST_REL (ld_owned_selection E) f.lf_params g.lf_params /\
    (!v. ld_owned_selection E (FLOOKUP f.lf_prov v) (FLOOKUP g.lf_prov v)) /\
    (!id. ld_owned_selection E (FLOOKUP f.lf_local id) (FLOOKUP g.lf_local id)) /\
    ld_erase f.lf_local = f.lf_state.vs_allocas /\
    ld_erase g.lf_local = g.lf_state.vs_allocas /\
    ld_owned_vars V E f.lf_prov g.lf_prov
      (entry_taint with t_var := f.lf_tvar)
      (entry_taint with t_var := g.lf_tvar) f.lf_state g.lf_state /\
    ld_alloc_account keys d A f.lf_state g.lf_state
End

Theorem ld_saved_locals_params:
  ld_saved_locals V E keys d A f g ==>
  LIST_REL (ld_owned_selection E) f.lf_params g.lf_params
Proof
  simp[ld_saved_locals_def]
QED

Theorem ld_saved_locals_prov:
  ld_saved_locals V E keys d A f g ==>
  !v. ld_owned_selection E (FLOOKUP f.lf_prov v) (FLOOKUP g.lf_prov v)
Proof
  simp[ld_saved_locals_def]
QED

Theorem ld_saved_locals_local:
  ld_saved_locals V E keys d A f g ==>
  !id. ld_owned_selection E (FLOOKUP f.lf_local id) (FLOOKUP g.lf_local id)
Proof
  simp[ld_saved_locals_def]
QED

Theorem ld_saved_locals_erasure:
  ld_saved_locals V E keys d A f g ==>
  ld_erase f.lf_local = f.lf_state.vs_allocas /\
  ld_erase g.lf_local = g.lf_state.vs_allocas
Proof
  simp[ld_saved_locals_def]
QED

Theorem ld_saved_locals_vars:
  ld_saved_locals V E keys d A f g ==>
  ld_owned_vars V E f.lf_prov g.lf_prov
    (entry_taint with t_var := f.lf_tvar)
    (entry_taint with t_var := g.lf_tvar) f.lf_state g.lf_state
Proof
  simp[ld_saved_locals_def]
QED

Theorem ld_saved_locals_account:
  ld_saved_locals V E keys d A f g ==>
  ld_alloc_account keys d A f.lf_state g.lf_state
Proof
  simp[ld_saved_locals_def]
QED

Theorem ld_saved_locals_return_account:
  ld_saved_locals V E keys d A f g ==>
  ld_alloc_account keys d A (merge_callee_state f.lf_state s_end)
    (merge_callee_state g.lf_state t_end)
Proof
  strip_tac >> irule ld_alloc_account_return >>
  metis_tac[ld_saved_locals_account]
QED

Theorem ld_merge_lookup_var[simp]:
  lookup_var v (merge_callee_state s u) = lookup_var v s
Proof
  simp[lookup_var_def, merge_callee_state_def]
QED

Theorem ld_merge_labels[simp]:
  (merge_callee_state s u).vs_labels = s.vs_labels
Proof
  simp[merge_callee_state_def]
QED

Theorem ld_owned_vars_merge:
  ld_owned_vars V E AG AH tn un s t ==>
  ld_owned_vars V E AG AH tn un (merge_callee_state s u) (merge_callee_state t v)
Proof
  simp[ld_owned_vars_def]
QED

Theorem ld_saved_locals_return_vars:
  ld_saved_locals V E keys d A f g ==>
  ld_owned_vars V E f.lf_prov g.lf_prov
    (entry_taint with t_var := f.lf_tvar)
    (entry_taint with t_var := g.lf_tvar)
    (merge_callee_state f.lf_state s_end) (merge_callee_state g.lf_state t_end)
Proof
  strip_tac >> irule ld_owned_vars_merge >> metis_tac[ld_saved_locals_vars]
QED

(* Stack certificates carry frame-specific domains and allocation budgets. *)
Theorem ld_saved_stack_shapes[local]:
  (LIST_REL (\f g. ?V keys d A. ld_saved_locals V E keys d A f g)
    [] gs <=> gs = []) /\
  (LIST_REL (\f g. ?V keys d A. ld_saved_locals V E keys d A f g)
    (f::fs) (g::gs) <=>
    (?V keys d A. ld_saved_locals V E keys d A f g) /\
    LIST_REL (\f g. ?V keys d A. ld_saved_locals V E keys d A f g) fs gs)
Proof
  simp[]
QED

Theorem ld_target_prefix_control:
  !C code t0 u0 n t u.
    ld_target_prefix C code t0 u0 n t u /\
    EVERY (\i. ~is_terminator i.inst_opcode) code ==>
    t.vs_current_bb = t0.vs_current_bb /\ t.vs_prev_bb = t0.vs_prev_bb
Proof
  rewrite_tac[GSYM AND_IMP_INTRO] >>
  ho_match_mp_tac ld_target_prefix_ind >> simp[] >>
  rpt strip_tac >>
  `~is_terminator (EL n code).inst_opcode` by
    (qpat_x_assum `EVERY _ code` mp_tac >>
     simp[listTheory.EVERY_EL] >> disch_then (qspec_then `n` mp_tac) >> simp[]) >>
  drule_all venomInstPropsTheory.step_preserves_control_flow >>
  simp[]
QED
