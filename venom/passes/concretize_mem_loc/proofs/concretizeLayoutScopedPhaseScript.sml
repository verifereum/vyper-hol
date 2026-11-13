Theory concretizeLayoutScopedPhase
Ancestors concretizeLayoutPhaseCorridor concretizeLayoutPhaseOrigin
          concretizeLayoutPhaseCompose frameScopedPhaseCertificates
          frameIndexedCertificates frameFiniteExecution ptrDiscipline
          venomExecSemantics venomState

(* The link is about the newly chosen PHI witness h, not the old run index g.
   Existing layout_phase_begins owns the source-origin projection. *)
Definition layout_scoped_phi_link_def:
  layout_scoped_phi_link g h (fn:ir_function) (fn':ir_function)
      (s:venom_state) (t:venom_state) bb bb' phi (phi':venom_state) <=>
    layout_phase_begins h bb
      (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) /\
    (layout_phase_origin h).lbo_target = bb' /\ ~layout_phase_pending h
End

Definition layout_scoped_entry_def:
  (layout_scoped_entry D lo vs0 C C' q0 es qs q (INL g) s t <=>
    layout_ordinary_entry D lo vs0 C C' q0 es qs q g s t) /\
  (layout_scoped_entry D lo vs0 C C' q0 es qs q (INR g) s t <=>
    layout_corridor_entry C g s t)
End

(* Ret retains the ending ghost as well as payload and states, and is still
   to be produced at RETURN. No origin equality is imposed on completed
   function outcomes; Ret may carry the endpoint facts needed by caller pop. *)
Definition layout_scoped_run_outcome_def:
  layout_scoped_run_outcome D Ret
      (g:layout_ordinary_phase + layout_terminal_phase)
      (h:layout_ordinary_phase + layout_terminal_phase) r r' <=>
    case (r,r') of
      (Halt s,Halt t) => dead_result_rel D (Halt s) (Halt t)
    | (Abort a s,Abort b t) => dead_result_rel D (Abort a s) (Abort b t)
    | (IntRet ret s,IntRet ret' t) => Ret h ret s ret' t
    | _ => F
End

(* Only OK segments carry a block origin.  Their endpoint entry may be the
   persistent corridor, but linked completed-block exclusion removes it. *)
Definition layout_scoped_outcome_def:
  layout_scoped_outcome D Ret Entry g h r r' <=>
    case (r,r') of
      (OK s,OK t) => layout_phase_origin g = layout_phase_origin h /\
        Entry h s t /\ s.vs_halted = t.vs_halted
    | _ => layout_scoped_run_outcome D Ret g h r r'
End

Theorem layout_scoped_run_shape:
  indexed_outcome_shape (layout_scoped_run_outcome D Ret)
Proof
  rw[indexed_outcome_shape_def] >> Cases_on `r` >> Cases_on `r'` >>
  gvs[layout_scoped_run_outcome_def] >> metis_tac[]
QED

Theorem layout_scoped_outcome_shape:
  indexed_outcome_shape (layout_scoped_outcome D Ret Entry)
Proof
  rw[indexed_outcome_shape_def] >> Cases_on `r` >> Cases_on `r'` >>
  gvs[layout_scoped_outcome_def, layout_scoped_run_outcome_def] >> metis_tac[]
QED

Theorem layout_scoped_outcome_ok_exit:
  indexed_ok_exit (\g s. T) Entry (layout_scoped_outcome D Ret Entry)
Proof
  simp[indexed_ok_exit_def, layout_scoped_outcome_def, indexed_entry_def]
QED

Theorem layout_scoped_completed_not_corridor:
  layout_scoped_phi_link g h fn fn' s t bb bb' phi phi' /\
  layout_scoped_outcome D Ret
    (layout_scoped_entry D lo vs0 C C' q0 es qs q) h (INR k) (OK u) (OK v) /\
  finite_block C bb
    (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) (OK u) ==>
  F
Proof
  rpt strip_tac >>
  fs[layout_scoped_phi_link_def, layout_scoped_outcome_def,
    layout_scoped_entry_def, layout_phase_begins_def, layout_phase_origin_def] >>
  drule layout_corridor_origin_exclusion >> metis_tac[]
QED

(* This restoration exposes only an ordinary endpoint, not the unproved
   whole Run invariant.  Ordinary completed-block restoration is separate. *)
Theorem layout_scoped_completed_ordinary:
  layout_scoped_phi_link g h fn fn' s t bb bb' phi phi' /\
  layout_scoped_outcome D Ret
    (layout_scoped_entry D lo vs0 C C' q0 es qs q) h k (OK u) (OK v) /\
  finite_block C bb
    (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) (OK u) ==>
  ?a. k = INL a /\ layout_ordinary_entry D lo vs0 C C' q0 es qs q a u v
Proof
  rpt strip_tac >> Cases_on `k`
  >- gvs[layout_scoped_outcome_def, layout_scoped_entry_def] >>
  metis_tac[layout_scoped_completed_not_corridor]
QED

Theorem layout_scoped_nonok_conversion:
  layout_scoped_outcome D Ret Entry h k r r' /\ (!u. r <> OK u) ==>
  layout_scoped_run_outcome D Ret g k r r'
Proof
  Cases_on `r` >> Cases_on `r'` >>
  simp[layout_scoped_outcome_def, layout_scoped_run_outcome_def]
QED

Theorem layout_scoped_halt_conversion:
  dead_result_rel D (Halt u) (Halt v) ==>
  layout_scoped_run_outcome D Ret g k (Halt u) (Halt v)
Proof
  simp[layout_scoped_run_outcome_def]
QED

Theorem layout_scoped_run_reindex:
  layout_scoped_run_outcome D Ret h k r r' ==>
  layout_scoped_run_outcome D Ret g k r r'
Proof
  simp[layout_scoped_run_outcome_def]
QED

Theorem layout_scoped_return_conversion:
  Ret h ret s ret' t ==>
  layout_scoped_run_outcome D Ret g h (IntRet ret s) (IntRet ret' t)
Proof
  simp[layout_scoped_run_outcome_def]
QED

(* Run composition and non-OK conversion are now honest certificates,
   independent of a universal transport law for block Q. *)
Theorem layout_scoped_run_next_certificate:
  scoped_phase_run_next C C' Run
    (layout_scoped_outcome D Ret Entry)
    (layout_scoped_run_outcome D Ret) PhiLink
Proof
  rw[scoped_phase_run_next_def] >>
  drule layout_scoped_run_reindex >> simp[]
QED

Theorem layout_scoped_run_exit_certificate:
  scoped_phase_run_exit C C' Run
    (layout_scoped_outcome D Ret Entry)
    (layout_scoped_run_outcome D Ret) PhiLink
Proof
  rw[scoped_phase_run_exit_def] >>
  metis_tac[layout_scoped_nonok_conversion]
QED

val _ = export_theory();
