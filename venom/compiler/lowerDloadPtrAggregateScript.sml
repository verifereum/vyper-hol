Theory lowerDloadPtrAggregate
Ancestors
  lowerDloadPtrRel lowerDloadPtrCall lowerDloadPtrPhase lowerDloadPtrEntry
  ptrDiscipline o1PassContract venomState finite_map list words

(* V and Ws contain observable original variables, excluding opaque retpc_var
   closures. Suspended snapshots constrain local metadata only. *)
Definition dload_boundary_core_def:
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds <=>
    dload_live_layout lo s.vs_alloca_next t.vs_alloca_next fs /\
    dload_table_stack fs (s::MAP (\c. c.cf_state) cs)
                        (t::MAP (\d. d.cf_state) ds) /\
    dload_vars_match fs V G H tn un s t /\
    dload_param_values fs PG PH s.vs_params t.vs_params /\
    dload_memory_match lo fs tn un s t /\
    dload_shared_store tn un s t /\
    dload_equal_environment s t /\
    LENGTH Ws = LENGTH cs /\ LENGTH cs = LENGTH ds /\
    (!k. k < LENGTH cs ==>
      dload_saved_metadata (DROP (SUC k) fs) (EL k Ws) (EL k cs) (EL k ds))
End

(* The allocation/memory boundary is at t0, never at a partial expansion. *)
Definition dload_phase_core_def:
  dload_phase_core fuel C supply fn gn inst emitted phase
    lo fs V Ws PG PH G tn s t H un cs ds <=>
    ?t0 H0 un0.
      dload_boundary_core lo fs V Ws PG PH G H0 tn un0 s t0 cs ds /\
      dload_control_match supply fn gn s t0 inst emitted 0 /\
      dload_prefix_match fuel C PH emitted phase t0 H0 un0 t H un /\
      dload_control_match supply fn gn s t inst emitted phase
End

Theorem dload_boundary_initial:
  o1_run_state_ok vs /\ lo <= vs.vs_alloca_next /\
  vs.vs_alloca_next < dimword (:256) ==>
  dload_boundary_core lo
    [<|dr_source := FEMPTY; dr_target := FEMPTY; dr_scratch := {}|>]
    V [] [] [] FEMPTY FEMPTY entry_taint entry_taint vs vs [] []
Proof
  strip_tac >> drule dload_initial_components >> strip_tac >>
  simp[dload_boundary_core_def, dload_live_layout_initial,
       dload_param_values_unprovenanced_refl, dload_shared_store_refl,
       dload_equal_environment_refl]
QED

Theorem dload_boundary_layout:
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds ==>
  dload_live_layout lo s.vs_alloca_next t.vs_alloca_next fs
Proof
  simp[dload_boundary_core_def]
QED

Theorem dload_boundary_tables:
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds ==>
  dload_table_stack fs (s::MAP (\c. c.cf_state) cs)
                      (t::MAP (\d. d.cf_state) ds)
Proof
  simp[dload_boundary_core_def]
QED

Theorem dload_boundary_vars:
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds ==>
  dload_vars_match fs V G H tn un s t
Proof
  simp[dload_boundary_core_def]
QED

Theorem dload_boundary_params:
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds ==>
  dload_param_values fs PG PH s.vs_params t.vs_params
Proof
  simp[dload_boundary_core_def]
QED

Theorem dload_boundary_memory:
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds ==>
  dload_memory_match lo fs tn un s t
Proof
  simp[dload_boundary_core_def]
QED

Theorem dload_boundary_shared_store:
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds ==>
  dload_shared_store tn un s t
Proof
  simp[dload_boundary_core_def]
QED

Theorem dload_boundary_environment:
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds ==>
  dload_equal_environment s t
Proof
  simp[dload_boundary_core_def]
QED

Theorem dload_boundary_saved:
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\ k < LENGTH cs ==>
  dload_saved_metadata (DROP (SUC k) fs) (EL k Ws) (EL k cs) (EL k ds)
Proof
  simp[dload_boundary_core_def]
QED

Theorem dload_phase_zero:
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  dload_control_match supply fn gn s t inst emitted 0 ==>
  dload_phase_core fuel C supply fn gn inst emitted 0
    lo fs V Ws PG PH G tn s t H un cs ds
Proof
  strip_tac >> simp[dload_phase_core_def] >>
  qexistsl [`t`,`H`,`un`] >> simp[dload_prefix_zero]
QED

Theorem dload_phase_anchor:
  dload_phase_core fuel C supply fn gn inst emitted phase
    lo fs V Ws PG PH G tn s t H un cs ds ==>
  ?t0 H0 un0.
    dload_boundary_core lo fs V Ws PG PH G H0 tn un0 s t0 cs ds /\
    dload_control_match supply fn gn s t0 inst emitted 0 /\
    dload_prefix_match fuel C PH emitted phase t0 H0 un0 t H un /\
    dload_control_match supply fn gn s t inst emitted phase
Proof
  simp[dload_phase_core_def]
QED

Theorem dload_phase_bound:
  dload_phase_core fuel C supply fn gn inst emitted phase
    lo fs V Ws PG PH G tn s t H un cs ds ==> phase < LENGTH emitted
Proof
  simp[dload_phase_core_def, dload_control_match_def] >> metis_tac[]
QED

Theorem dload_phase_extend:
  dload_phase_core fuel C supply fn gn inst emitted k
    lo fs V Ws PG PH G tn s t H un cs ds /\
  step_inst fuel C (EL k emitted) t = OK v /\
  dload_control_match supply fn gn s
    (v with vs_inst_idx := SUC t.vs_inst_idx) inst emitted (SUC k) ==>
  dload_phase_core fuel C supply fn gn inst emitted (SUC k)
    lo fs V Ws PG PH G tn s (v with vs_inst_idx := SUC t.vs_inst_idx)
    (step_prov PH H (EL k emitted) v) (step_taint (EL k emitted) t v un) cs ds
Proof
  strip_tac >> drule dload_phase_bound >> strip_tac >>
  fs[dload_phase_core_def] >>
  qexistsl [`t0`,`H0`,`un0`] >> simp[] >>
  irule dload_prefix_extend >> simp[]
QED

(* Restrict only the active observations, retaining saved caller metadata. *)
Theorem dload_boundary_vars_restrict:
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  V' SUBSET V ==>
  dload_boundary_core lo fs V' Ws PG PH G H tn un s t cs ds
Proof
  simp[dload_boundary_core_def, dload_vars_match_def, pred_setTheory.SUBSET_DEF] >>
  metis_tac[]
QED
