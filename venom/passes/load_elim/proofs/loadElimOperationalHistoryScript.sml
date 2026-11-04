Theory loadElimOperationalHistory
Ancestors
  loadElimHistoryHelpers venomInstProofs venomExecProofs venomExecSemantics list

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
