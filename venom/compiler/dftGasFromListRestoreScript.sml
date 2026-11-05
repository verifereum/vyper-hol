Theory dftGasFromListRestore
Ancestors
  dftGasOracleDefs gasOracleReplay contextCodegenRel o1PassContract
  stateEquiv venomExecSemantics venomState venomInst list

Definition restore_result_def:
  restore_result gs r =
    case r of
      OK s => OK (s with vs_gas_readings := gs)
    | Halt s => Halt (s with vs_gas_readings := gs)
    | IntRet v s => IntRet v (s with vs_gas_readings := gs)
    | Abort a s => Abort a (s with vs_gas_readings := gs)
    | Error e => Error e
End

Theorem restore_result_rel:
  gas_res_rel r (restore_result gs r)
Proof
  Cases_on `r` >> simp[restore_result_def, gas_res_rel_def, gas_variant_def]
QED

Definition restore_rel_def:
  restore_rel gs r r' <=>
    case (r,r') of
      (OK s, OK t) => t = (s with vs_gas_readings := gs)
    | (Halt s, Halt t) => t = (s with vs_gas_readings := gs)
    | (IntRet v s, IntRet v' t) =>
        v' = v /\ t = (s with vs_gas_readings := gs)
    | (Abort a s, Abort a' t) =>
        a' = a /\ t = (s with vs_gas_readings := gs)
    | (Error e, Error e') => T
    | _ => F
End

Theorem restore_rel_gas_res:
  restore_rel gs r r' ==> gas_res_rel r r'
Proof
  Cases_on `r` >> Cases_on `r'` >>
  simp[restore_rel_def, gas_res_rel_def, gas_variant_def] >>
  strip_tac >> gvs[]
QED

Theorem replay_zero_restore:
  gas_replay_at 0 f s ==>
  restore_rel gs (f s) (f (s with vs_gas_readings := gs))
Proof
  simp[gas_replay_at_def] >>
  disch_then (qspec_then `gs` mp_tac) >>
  Cases_on `f s` >>
  Cases_on `f (s with vs_gas_readings := gs)` >>
  simp[lift_result_def, restore_rel_def] >> strip_tac >> gvs[]
QED

Theorem eval_phis_restore:
  restore_rel gs (eval_phis s insts)
    (eval_phis (s with vs_gas_readings := gs) insts)
Proof
  qspecl_then [`insts`, `s`] assume_tac gas_eval_phis >>
  drule replay_zero_restore >> simp[]
QED

Theorem step_base_restore:
  inst.inst_opcode <> GAS ==>
  restore_rel gs (step_inst_base inst s)
    (step_inst_base inst (s with vs_gas_readings := gs))
Proof
  strip_tac >> irule replay_zero_restore >>
  irule gas_base_non_gas >> simp[]
QED

Theorem active_inst_restore[simp]:
  active_inst fn inst (s with vs_gas_readings := gs) <=> active_inst fn inst s
Proof
  simp[active_inst_def]
QED

Theorem enters_block_restore:
  enters_block fn s t ==>
  enters_block fn (s with vs_gas_readings := gs)
    (t with vs_gas_readings := gs)
Proof
  simp[enters_block_def] >> rpt strip_tac >>
  qexistsl_tac [`bb`, `s_phi with vs_gas_readings := gs`] >>
  mp_tac (Q.INST [`gs` |-> `gs`, `s` |-> `s`,
    `insts` |-> `bb.bb_instructions`] eval_phis_restore) >>
  simp[restore_rel_def] >>
  Cases_on `eval_phis (s with vs_gas_readings := gs) bb.bb_instructions` >>
  simp[restore_rel_def] >> strip_tac >> gvs[]
QED

Theorem ev_gas_restore:
  w = (case s.vs_gas_readings of [] => 0w | x::xs => x) ==>
  ev_gas w inst (s with vs_gas_readings := gs) =
    restore_result gs (exec_gas inst s)
Proof
  strip_tac >> Cases_on `s.vs_gas_readings` >>
  simp[exec_gas_def, ev_gas_def] >>
  Cases_on `inst.inst_outputs` >> simp[restore_result_def] >>
  rename1 `inst.inst_outputs = out::outs` >>
  Cases_on `outs` >> simp[restore_result_def]
QED

Theorem restore_rel_cases[simp]:
  (restore_rel gs (OK s) r <=> r = OK (s with vs_gas_readings := gs)) /\
  (restore_rel gs (Halt s) r <=> r = Halt (s with vs_gas_readings := gs)) /\
  (restore_rel gs (IntRet v s) r <=>
     r = IntRet v (s with vs_gas_readings := gs)) /\
  (restore_rel gs (Abort a s) r <=>
     r = Abort a (s with vs_gas_readings := gs)) /\
  (restore_rel gs (Error e) r <=> ?msg. r = Error msg)
Proof
  Cases_on `r` >> simp[restore_rel_def, EQ_SYM_EQ]
QED
