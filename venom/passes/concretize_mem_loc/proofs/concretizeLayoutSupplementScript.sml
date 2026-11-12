Theory concretizeLayoutSupplement
Ancestors ptrDiscipline venomExecProofs venomExecSemantics venomState
  finite_map list pred_set

(* The local observation deliberately does not use the final task mask. *)
Definition concretize_local_obs_def:
  concretize_local_obs s t <=>
  dead_result_rel
    <| d_stor := K (K UNIV); d_trans := K (K UNIV);
       d_imm := K UNIV; d_ret := K {} |> (Halt s) (Halt t)
End

Definition concretize_supplement_def:
  concretize_supplement D tn s t <=>
  accounts_agree_except
    (D with d_stor := (\a st. if a = s.vs_call_ctx.cc_address then tn.t_stor else {}))
    s.vs_accounts t.vs_accounts /\
  transient_agree_except
    (D with d_trans := (\a st. if a = s.vs_call_ctx.cc_address then tn.t_trans else {}))
    s.vs_transient t.vs_transient /\
  imms_agree_except (D with d_imm := K tn.t_imm) s.vs_immutables t.vs_immutables /\
  LIST_REL (request_agree_except D) s.vs_requests t.vs_requests /\
  s.vs_outcomes = t.vs_outcomes
End

Theorem concretize_supplement_refl[simp]:
  concretize_supplement D tn s s
Proof
  simp[concretize_supplement_def, accounts_agree_except_def,
       transient_agree_except_def, imms_agree_except_def,
       storage_agree_except_def, word_agree_except_def] >>
  irule EVERY2_refl >> simp[request_agree_except_def,
       accounts_agree_except_def, transient_agree_except_def,
       storage_agree_except_def, word_agree_except_def]
QED

Theorem concretize_supplement_fields:
  concretize_supplement D tn s t /\
  sn.vs_accounts = s.vs_accounts /\ tnxt.vs_accounts = t.vs_accounts /\
  sn.vs_transient = s.vs_transient /\ tnxt.vs_transient = t.vs_transient /\
  sn.vs_immutables = s.vs_immutables /\ tnxt.vs_immutables = t.vs_immutables /\
  sn.vs_requests = s.vs_requests /\ tnxt.vs_requests = t.vs_requests /\
  sn.vs_outcomes = s.vs_outcomes /\ tnxt.vs_outcomes = t.vs_outcomes /\
  sn.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address /\
  un.t_stor = tn.t_stor /\ un.t_trans = tn.t_trans /\ un.t_imm = tn.t_imm ==>
  concretize_supplement D un sn tnxt
Proof
  simp[concretize_supplement_def]
QED

Theorem concretize_supplement_var_control:
  concretize_supplement D tn s t ==>
  concretize_supplement D (tn with t_var := tv)
    ((s with <| vs_vars := sv; vs_inst_idx := si; vs_current_bb := sb;
                 vs_prev_bb := sp |>))
    ((t with <| vs_vars := uv; vs_inst_idx := ti; vs_current_bb := tb;
                 vs_prev_bb := tp |>))
Proof
  simp[concretize_supplement_def]
QED

Theorem concretize_supplement_phis:
  concretize_supplement D tn s t /\
  eval_phis s insts = OK post /\ eval_phis t insts' = OK tpost ==>
  concretize_supplement D (tn with t_var := phis_taint s.vs_prev_bb tn insts)
    (post with vs_inst_idx := si) (tpost with vs_inst_idx := ti)
Proof
  strip_tac >>
  drule eval_phis_only_updates_vs_vars >> strip_tac >>
  qpat_x_assum `eval_phis s _ = OK _`
    (mp_tac o MATCH_MP eval_phis_only_updates_vs_vars) >> strip_tac >>
  gvs[concretize_supplement_def, venom_state_component_equality]
QED

Theorem concretize_local_obs_var_control:
  concretize_local_obs s t ==>
  concretize_local_obs
    (s with <| vs_vars := sv; vs_inst_idx := si; vs_current_bb := sb;
               vs_prev_bb := sp |>)
    (t with <| vs_vars := uv; vs_inst_idx := ti; vs_current_bb := tb;
               vs_prev_bb := tp |>)
Proof
  simp[concretize_local_obs_def, dead_result_rel_def]
QED

Theorem concretize_supplement_update_var:
  concretize_supplement D tn s t ==>
  concretize_supplement D tn (update_var v x s) (update_var w y t)
Proof
  simp[concretize_supplement_def, update_var_def]
QED
