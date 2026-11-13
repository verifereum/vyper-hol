Theory concretizeLayoutRequestRelations
Ancestors concretizeLayoutCanonicalDeferred concretizeLayoutCanonicalDriver
  concretizeLayoutSupplement
  concretizeLayoutPhaseOrigin concretizeLayoutCallResult contextCodegenRel
  venomExecProofs o1RequestContract venomState list

(* Request histories form a separate observation from the old abort relation. *)
Definition layout_request_state_def:
  layout_request_state D s t <=>
    LIST_REL (request_agree_except D) s.vs_requests t.vs_requests
End

Definition layout_request_guard_def:
  layout_request_guard D r r' <=>
    case (r,r') of
      (OK s,OK t) => layout_request_state D s t
    | (Abort a s,Abort b t) => layout_request_state D s t
    | _ => T
End

Definition layout_request_ES_def:
  layout_request_ES D lo vs0 C C' q0 path es qs ass qend q n i s j t <=>
    layout_canonical_ES D lo vs0 C C' q0 path es qs ass qend q n i s j t /\
    layout_request_state D s t
End

Definition layout_request_EB_def:
  layout_request_EB D lo vs0 C C' q0 es qs ass qend q n bb s bb' t <=>
    layout_canonical_EB D lo vs0 C C' q0 es qs ass qend q n bb s bb' t /\
    layout_request_state D s t
End

Definition layout_request_OS_def:
  layout_request_OS D lo vs0 C C' q0 path es qs ass qend q n qe m i s j t r r' <=>
    layout_deferred_OS D lo vs0 C C' q0 path es qs ass qend q n qe m i s j t r r' /\
    layout_request_guard D r r'
End

Definition layout_request_OB_def:
  layout_request_OB D lo vs0 C C' q0 es qs ass qend q n qe m bb s bb' t r r' <=>
    layout_canonical_OB D lo vs0 C C' q0 es qs ass qend q n qe m bb s bb' t r r' /\
    layout_request_guard D r r'
End

Definition layout_request_OutR_def:
  layout_request_OutR D lo vs0 C C' q0 es qs ass qend q n qe m fn s fn' t r r' <=>
    layout_canonical_OutR D lo vs0 C C' q0 es qs ass qend q n qe m fn s fn' t r r' /\
    layout_request_guard D r r'
End

Theorem layout_request_state_refl[simp]:
  layout_request_state D s s
Proof
  simp[layout_request_state_def] >> irule EVERY2_refl >>
  simp[request_agree_except_refl]
QED

Theorem layout_request_state_fields:
  layout_request_state D s t /\
  u.vs_requests = s.vs_requests /\ v.vs_requests = t.vs_requests ==>
  layout_request_state D u v
Proof
  simp[layout_request_state_def]
QED

Theorem layout_request_state_var_control[simp]:
  layout_request_state D
    (s with <| vs_vars := sv; vs_inst_idx := si; vs_current_bb := sb;
               vs_prev_bb := sp |>)
    (t with <| vs_vars := tv; vs_inst_idx := ti; vs_current_bb := tb;
               vs_prev_bb := tp |>) <=> layout_request_state D s t
Proof
  simp[layout_request_state_def]
QED

Theorem layout_request_state_normalize[simp]:
  layout_request_state D (layout_phase_normalize p s)
    (layout_phase_normalize p' t) <=> layout_request_state D s t
Proof
  Cases_on `p` >> Cases_on `p'` >>
  simp[layout_phase_normalize_def, layout_request_state_def]
QED

Theorem eval_phis_requests:
  eval_phis s insts = OK p ==> p.vs_requests = s.vs_requests
Proof
  strip_tac >> drule eval_phis_only_updates_vs_vars >>
  disch_then (mp_tac o Q.AP_TERM `\u. u.vs_requests`) >> simp[]
QED

Theorem enters_block_requests:
  enters_block fn s p ==> p.vs_requests = s.vs_requests
Proof
  simp[enters_block_def] >> rpt strip_tac >>
  drule eval_phis_requests >> simp[]
QED

Theorem layout_request_state_phis:
  layout_request_state D s t /\
  eval_phis s insts = OK p /\ eval_phis t insts' = OK p' ==>
  layout_request_state D p p'
Proof
  metis_tac[layout_request_state_fields, eval_phis_requests]
QED

Theorem layout_request_state_enters_block:
  enters_block fn s p /\ enters_block fn' t p' ==>
  (layout_request_state D s t <=> layout_request_state D p p')
Proof
  simp[layout_request_state_def] >>
  metis_tac[enters_block_requests]
QED

Theorem concretize_supplement_requests:
  concretize_supplement D tn s t ==> layout_request_state D s t
Proof
  simp[concretize_supplement_def, layout_request_state_def]
QED

Theorem layout_ordinary_state_requests:
  layout_ordinary_state D lo C' q0 es qs g s t ==>
  layout_request_state D s t
Proof
  Cases_on `g.lop_config` >>
  simp[layout_ordinary_state_def] >>
  metis_tac[concretize_supplement_requests]
QED

Theorem layout_ordinary_entry_requests:
  layout_ordinary_entry D lo vs0 C C' q0 es qs q g s t ==>
  layout_request_state D s t
Proof
  metis_tac[layout_ordinary_entry_def, layout_ordinary_state_requests]
QED

Theorem layout_canonical_run_requests:
  layout_canonical_run D lo vs0 C C' q0 es qs ass qend q n fn s fn' t ==>
  layout_request_state D s t
Proof
  simp[layout_canonical_run_def] >> rpt strip_tac >>
  drule layout_ordinary_state_requests >>
  metis_tac[layout_request_state_enters_block]
QED

Theorem layout_ret_endpoint_requests:
  layout_ret_endpoint D lo vs0 C C' q0 es qs q g s t ret ret' ==>
  layout_request_state D s t
Proof
  metis_tac[layout_ret_endpoint_def, layout_ordinary_entry_requests]
QED

Theorem layout_canonical_ret_requests:
  layout_canonical_ret D lo vs0 C C' q0 es qs ass qend qe m ret s ret' t ==>
  layout_request_state D s t
Proof
  metis_tac[layout_canonical_ret_def, layout_ret_endpoint_requests]
QED

Theorem layout_request_guard_OK[simp]:
  layout_request_guard D (OK s) (OK t) <=> layout_request_state D s t
Proof
  simp[layout_request_guard_def]
QED

Theorem layout_request_guard_Abort[simp]:
  layout_request_guard D (Abort a s) (Abort b t) <=> layout_request_state D s t
Proof
  simp[layout_request_guard_def]
QED

Theorem layout_request_ES_forget:
  layout_request_ES D lo vs0 C C' q0 path es qs ass qend q n i s j t ==>
  layout_canonical_ES D lo vs0 C C' q0 path es qs ass qend q n i s j t
Proof
  simp[layout_request_ES_def]
QED

Theorem layout_request_EB_forget:
  layout_request_EB D lo vs0 C C' q0 es qs ass qend q n bb s bb' t ==>
  layout_canonical_EB D lo vs0 C C' q0 es qs ass qend q n bb s bb' t
Proof
  simp[layout_request_EB_def]
QED

Theorem layout_request_OS_forget:
  layout_request_OS D lo vs0 C C' q0 path es qs ass qend q n qe m i s j t r r' ==>
  layout_deferred_OS D lo vs0 C C' q0 path es qs ass qend q n qe m i s j t r r'
Proof
  simp[layout_request_OS_def]
QED

Theorem layout_request_OB_forget:
  layout_request_OB D lo vs0 C C' q0 es qs ass qend q n qe m bb s bb' t r r' ==>
  layout_canonical_OB D lo vs0 C C' q0 es qs ass qend q n qe m bb s bb' t r r'
Proof
  simp[layout_request_OB_def]
QED

Theorem layout_request_OutR_forget:
  layout_request_OutR D lo vs0 C C' q0 es qs ass qend q n qe m fn s fn' t r r' ==>
  layout_canonical_OutR D lo vs0 C C' q0 es qs ass qend q n qe m fn s fn' t r r'
Proof
  simp[layout_request_OutR_def]
QED

Theorem layout_request_ES_intro:
  layout_canonical_ES D lo vs0 C C' q0 path es qs ass qend q n i s j t /\
  layout_request_state D s t ==>
  layout_request_ES D lo vs0 C C' q0 path es qs ass qend q n i s j t
Proof
  simp[layout_request_ES_def]
QED

Theorem layout_request_EB_intro:
  layout_canonical_EB D lo vs0 C C' q0 es qs ass qend q n bb s bb' t /\
  layout_request_state D s t ==>
  layout_request_EB D lo vs0 C C' q0 es qs ass qend q n bb s bb' t
Proof
  simp[layout_request_EB_def]
QED

Theorem layout_request_OS_intro:
  layout_deferred_OS D lo vs0 C C' q0 path es qs ass qend q n qe m i s j t r r' /\
  layout_request_guard D r r' ==>
  layout_request_OS D lo vs0 C C' q0 path es qs ass qend q n qe m i s j t r r'
Proof
  simp[layout_request_OS_def]
QED

Theorem layout_request_OB_intro:
  layout_canonical_OB D lo vs0 C C' q0 es qs ass qend q n qe m bb s bb' t r r' /\
  layout_request_guard D r r' ==>
  layout_request_OB D lo vs0 C C' q0 es qs ass qend q n qe m bb s bb' t r r'
Proof
  simp[layout_request_OB_def]
QED

Theorem layout_request_OutR_intro:
  layout_canonical_OutR D lo vs0 C C' q0 es qs ass qend q n qe m fn s fn' t r r' /\
  layout_request_guard D r r' ==>
  layout_request_OutR D lo vs0 C C' q0 es qs ass qend q n qe m fn s fn' t r r'
Proof
  simp[layout_request_OutR_def]
QED

Theorem layout_request_ES_requests:
  layout_request_ES D lo vs0 C C' q0 path es qs ass qend q n i s j t ==>
  layout_request_state D s t
Proof
  simp[layout_request_ES_def]
QED

Theorem layout_request_EB_requests:
  layout_request_EB D lo vs0 C C' q0 es qs ass qend q n bb s bb' t ==>
  layout_request_state D s t
Proof
  simp[layout_request_EB_def]
QED

Theorem layout_request_OS_guard:
  layout_request_OS D lo vs0 C C' q0 path es qs ass qend q n qe m i s j t r r' ==>
  layout_request_guard D r r'
Proof
  simp[layout_request_OS_def]
QED

Theorem layout_request_OB_guard:
  layout_request_OB D lo vs0 C C' q0 es qs ass qend q n qe m bb s bb' t r r' ==>
  layout_request_guard D r r'
Proof
  simp[layout_request_OB_def]
QED

Theorem layout_request_OutR_guard:
  layout_request_OutR D lo vs0 C C' q0 es qs ass qend q n qe m fn s fn' t r r' ==>
  layout_request_guard D r r'
Proof
  simp[layout_request_OutR_def]
QED
