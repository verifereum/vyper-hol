(* Abort observations forget only the remaining GAS readings. *)
Theory acAbortRelProofs
Ancestors
  acBaseProofs assertCombinerDefs stateEquiv stateEquivProps stateFrame
  venomState venomExecSemantics venomExecProofs venomInstProps
  analysisSimDefs list pred_set

Definition ac_abort_equiv_def:
  ac_abort_equiv s t <=>
    ?gs. execution_equiv UNIV s (t with vs_gas_readings := gs)
End

(* A canonical frame removes precisely the approved extra field. *)
Theorem ac_abort_equiv_frame:
  !s t. ac_abort_equiv s t <=>
    (execution_frame s with vs_gas_readings := []) =
    (execution_frame t with vs_gas_readings := [])
Proof
  rpt gen_tac >>
  simp[ac_abort_equiv_def, execution_equiv_def, execution_frame_def,
       venom_state_component_equality] >>
  metis_tac[]
QED

Theorem ac_abort_equiv_refl[simp]:
  !s. ac_abort_equiv s s
Proof
  simp[ac_abort_equiv_frame]
QED

Theorem ac_abort_equiv_trans:
  !s t u. ac_abort_equiv s t /\ ac_abort_equiv t u ==>
    ac_abort_equiv s u
Proof
  simp[ac_abort_equiv_frame]
QED

Theorem ac_abort_equiv_sym:
  !s t. ac_abort_equiv s t ==> ac_abort_equiv t s
Proof
  simp[ac_abort_equiv_frame]
QED

Theorem execution_equiv_ac_abort_equiv:
  !s t. execution_equiv UNIV s t ==> ac_abort_equiv s t
Proof
  simp[ac_abort_equiv_frame, execution_equiv_def,
       execution_frame_def, venom_state_component_equality]
QED

Theorem ac_abort_equiv_gas_updates[simp]:
  (!s t gs. ac_abort_equiv s (t with vs_gas_readings := gs) <=>
     ac_abort_equiv s t) /\
  (!s t gs. ac_abort_equiv (s with vs_gas_readings := gs) t <=>
     ac_abort_equiv s t)
Proof
  simp[ac_abort_equiv_frame, execution_frame_def]
QED

Theorem ac_abort_equiv_update_var[simp]:
  (!s t x v. ac_abort_equiv s (update_var x v t) <=> ac_abort_equiv s t) /\
  (!s t x v. ac_abort_equiv (update_var x v s) t <=> ac_abort_equiv s t)
Proof
  simp[ac_abort_equiv_frame, update_var_def, execution_frame_def]
QED

Theorem ac_abort_equiv_revert_returndata:
  !s t. ac_abort_equiv s t ==>
    ac_abort_equiv (revert_state (set_returndata [] s))
      (revert_state (set_returndata [] t))
Proof
  simp[ac_abort_equiv_frame, execution_frame_def,
       revert_state_def, set_returndata_def, venom_state_component_equality]
QED

Theorem ac_gas_step_abort_equiv:
  !fuel ctx inst s t.
    inst.inst_opcode = GAS /\ step_inst fuel ctx inst s = OK t ==>
    ac_abort_equiv s t
Proof
  rpt strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_def, exec_gas_def,
      AllCaseEqs()] >>
  simp[]
QED

Theorem ac_effect_free_step_abort_equiv:
  !fuel ctx inst s t.
    is_effect_free_op inst.inst_opcode /\
    step_inst fuel ctx inst s = OK t ==> ac_abort_equiv s t
Proof
  rpt strip_tac >>
  irule execution_equiv_ac_abort_equiv >>
  `state_equiv (set inst.inst_outputs) s t` by
    metis_tac[step_effect_free_state_equiv] >>
  gvs[state_equiv_def, execution_equiv_def]
QED

Theorem ac_effect_free_or_gas_step_abort_equiv:
  !fuel ctx inst s t.
    (is_effect_free_op inst.inst_opcode \/ inst.inst_opcode = GAS) /\
    step_inst fuel ctx inst s = OK t ==> ac_abort_equiv s t
Proof
  metis_tac[ac_gas_step_abort_equiv, ac_effect_free_step_abort_equiv]
QED

Theorem ac_safe_step_abort_equiv:
  !fuel ctx inst s t.
    ac_is_safe_between inst /\ step_inst fuel ctx inst s = OK t ==>
    ac_abort_equiv s t
Proof
  metis_tac[ac_safe_between_effect_free_or_gas,
            ac_effect_free_or_gas_step_abort_equiv]
QED

Theorem ac_safe_step_revert_abort_equiv:
  !fuel ctx inst s t.
    ac_is_safe_between inst /\ step_inst fuel ctx inst s = OK t ==>
    ac_abort_equiv (revert_state (set_returndata [] s))
      (revert_state (set_returndata [] t))
Proof
  metis_tac[ac_safe_step_abort_equiv, ac_abort_equiv_revert_returndata]
QED

Theorem ac_run_insts_abort_equiv:
  !insts fuel ctx s t.
    EVERY (\i. is_effect_free_op i.inst_opcode \/ i.inst_opcode = GAS) insts /\
    run_insts fuel ctx insts s = OK t ==> ac_abort_equiv s t
Proof
  Induct >> rw[run_insts_def] >>
  Cases_on `step_inst fuel ctx h s` >> gvs[] >>
  metis_tac[ac_effect_free_or_gas_step_abort_equiv, ac_abort_equiv_trans]
QED

Theorem ac_run_insts_revert_abort_equiv:
  !insts fuel ctx s t.
    EVERY (\i. is_effect_free_op i.inst_opcode \/ i.inst_opcode = GAS) insts /\
    run_insts fuel ctx insts s = OK t ==>
    ac_abort_equiv (revert_state (set_returndata [] s))
      (revert_state (set_returndata [] t))
Proof
  metis_tac[ac_run_insts_abort_equiv, ac_abort_equiv_revert_returndata]
QED
