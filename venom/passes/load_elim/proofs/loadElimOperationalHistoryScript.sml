Theory loadElimOperationalHistory
Ancestors
  loadElimHistoryHelpers venomInstProofs venomExecProofs venomExecSemantics venomState list

(* Caller-level events include INVOKE output binding, without flattening the
   callee execution or recording its private variable environment. *)
Theorem le_step_inst_event:
  step_inst fuel ctx inst s = OK t ==>
  le_framed_history s [(set inst.inst_outputs,t)]
Proof
  simp[le_framed_history_def] >> rpt strip_tac >>
  Cases_on `is_terminator inst.inst_opcode`
  >- metis_tac[step_terminator_preserves_vars] >>
  metis_tac[step_preserves_non_output_vars]
QED

(* The leading PHI prefix (take-while, expressed recursively). *)
Definition le_phi_prefix_def:
  le_phi_prefix [] = [] /\
  le_phi_prefix (i::is) =
    if i.inst_opcode = PHI then i::le_phi_prefix is else []
End

Definition le_phi_outputs_def:
  le_phi_outputs insts = set (FLAT (MAP (\i. i.inst_outputs) (le_phi_prefix insts)))
End

Theorem le_eval_phis_snapshot:
  !insts s t. eval_phis s insts = OK t <=>
    le_snapshot_batch eval_one_phi s (le_phi_prefix insts) = SOME t
Proof
  Induct_on `insts` >- simp[eval_phis_def, le_phi_prefix_def, le_snapshot_batch_def] >>
  rpt gen_tac >> Cases_on `h.inst_opcode = PHI`
  >- (simp[eval_phis_def, le_phi_prefix_def, le_snapshot_batch_def] >>
      Cases_on `eval_one_phi s h` >- simp[] >>
      PairCases_on `x` >> simp[] >>
      Cases_on `le_snapshot_batch eval_one_phi s (le_phi_prefix insts)`
      >- (Cases_on `eval_phis s insts` >> gvs[] >>
          first_x_assum (qspecl_then [`s`, `v`] mp_tac) >> simp[]) >>
      first_x_assum (qspecl_then [`s`, `x`] mp_tac) >>
      simp[] >> strip_tac >> simp[]) >>
  simp[eval_phis_def, le_phi_prefix_def, le_snapshot_batch_def]
QED

Theorem le_eval_phis_event:
  eval_phis s insts = OK t ==>
  le_framed_history s [(le_phi_outputs insts,t)]
Proof
  rewrite_tac[le_eval_phis_snapshot] >> strip_tac >>
  irule (INST_TYPE [``:'a`` |-> ``:instruction``] le_snapshot_batch_event) >>
  conj_tac >- simp[le_phi_outputs_def] >>
  qexistsl [`eval_one_phi`, `le_phi_prefix insts`] >>
  simp[le_phi_outputs_def, MEM_FLAT, MEM_MAP] >>
  rpt strip_tac >> drule eval_one_phi_output_mem >>
  metis_tac[]
QED

Theorem le_eval_phis_selected:
  eval_phis s insts = OK t /\
  le_phi_prefix insts = pre ++ i::post /\
  eval_one_phi s i = SOME (v,w) /\
  (!j u. MEM j pre ==> eval_one_phi s j <> SOME (v,u)) ==>
  lookup_var v t = SOME w
Proof
  rewrite_tac[le_eval_phis_snapshot] >> rpt strip_tac >>
  irule (INST_TYPE [``:'a`` |-> ``:instruction``] le_snapshot_batch_selected) >>
  metis_tac[]
QED

(* This records semantic edges, not CFG reachability or instruction provenance. *)
Definition le_oper_event_def:
  le_oper_event s outs t <=>
    (?fuel ctx inst. step_inst fuel ctx inst s = OK t /\ outs = set inst.inst_outputs) \/
    (?insts. eval_phis s insts = OK t /\ outs = le_phi_outputs insts) \/
    (outs = {} /\ !v. lookup_var v t = lookup_var v s)
End

Definition le_oper_history_def:
  (le_oper_history s [] <=> T) /\
  (le_oper_history s ((outs,t)::h) <=>
    le_oper_event s outs t /\ le_oper_history t h)
End

Theorem le_oper_event_frame:
  le_oper_event s outs t ==> le_framed_history s [(outs,t)]
Proof
  rw[le_oper_event_def]
  >- metis_tac[le_step_inst_event]
  >- metis_tac[le_eval_phis_event] >>
  simp[le_framed_history_def]
QED

Theorem le_oper_history_frame:
  !h s. le_oper_history s h ==> le_framed_history s h
Proof
  Induct_on `h` >- simp[le_framed_history_def] >>
  Cases >> simp[le_oper_history_def, le_framed_history_def] >>
  metis_tac[le_oper_event_frame, le_framed_history_def]
QED

Theorem le_oper_history_append:
  le_oper_history s (a ++ b) <=>
  le_oper_history s a /\ le_oper_history (le_history_end s a) b
Proof
  qid_spec_tac `s` >> Induct_on `a` >> simp[le_oper_history_def, le_history_end_def] >>
  Cases_on `h` >> simp[le_oper_history_def, le_history_end_def] >> metis_tac[]
QED

Theorem le_oper_history_interval_lookup:
  le_oper_history s (prefix ++ interval ++ suffix) /\
  le_epoch prefix v = le_epoch (prefix ++ interval) v ==>
  lookup_var v (le_history_end s (prefix ++ interval)) =
  lookup_var v (le_history_end s prefix)
Proof
  metis_tac[le_oper_history_frame, le_history_interval_lookup]
QED

Theorem le_oper_history_extend:
  le_oper_history s h /\ le_oper_event (le_history_end s h) outs t ==>
  le_oper_history s (h ++ [(outs,t)])
Proof
  simp[le_oper_history_append, le_oper_history_def]
QED

Theorem le_oper_step_event:
  step_inst fuel ctx inst s = OK t ==>
  le_oper_event s (set inst.inst_outputs) t
Proof
  rw[le_oper_event_def] >> disj1_tac >> metis_tac[]
QED

Theorem le_oper_phi_event:
  eval_phis s insts = OK t ==> le_oper_event s (le_phi_outputs insts) t
Proof
  rw[le_oper_event_def] >> disj2_tac >> disj1_tac >> metis_tac[]
QED

Theorem le_oper_neutral_event:
  (!v. lookup_var v t = lookup_var v s) ==> le_oper_event s {} t
Proof
  simp[le_oper_event_def]
QED

Theorem le_oper_index_event:
  le_oper_event s {} (s with vs_inst_idx := idx)
Proof
  irule le_oper_neutral_event >> simp[lookup_var_def]
QED

Theorem le_oper_edge_event:
  le_oper_event s {} (s with <| vs_inst_idx := 0;
    vs_current_bb := dest; vs_prev_bb := SOME prev |> )
Proof
  irule le_oper_neutral_event >> simp[lookup_var_def]
QED

Theorem le_oper_history_singleton:
  le_oper_history s [(outs,t)] <=> le_oper_event s outs t
Proof
  simp[le_oper_history_def]
QED

Theorem le_oper_history_step_extend:
  le_oper_history s h /\
  step_inst fuel ctx inst (le_history_end s h) = OK t ==>
  le_oper_history s (h ++ [(set inst.inst_outputs,t)])
Proof
  metis_tac[le_oper_history_extend, le_oper_step_event]
QED

Theorem le_oper_history_phi_extend:
  le_oper_history s h /\ eval_phis (le_history_end s h) insts = OK t ==>
  le_oper_history s (h ++ [(le_phi_outputs insts,t)])
Proof
  metis_tac[le_oper_history_extend, le_oper_phi_event]
QED

Theorem le_oper_history_neutral_extend:
  le_oper_history s h /\ (!v. lookup_var v t = lookup_var v (le_history_end s h)) ==>
  le_oper_history s (h ++ [({},t)])
Proof
  metis_tac[le_oper_history_extend, le_oper_neutral_event]
QED
