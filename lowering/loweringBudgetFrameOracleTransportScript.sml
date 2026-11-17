Theory loweringBudgetFrameOracleTransport
Ancestors
  ptrDiscipline gasEvents oracleStateProps contextCodegenRel codegenRel
  venomExecSemantics venomState list

Theorem active_inst_outcomes_update:
  active_inst fn i (s with vs_outcomes := os) <=> active_inst fn i s
Proof
  simp[active_inst_def]
QED

Theorem operand_outcomes_update[local]:
  eval_operand op (s with vs_outcomes := os) = eval_operand op s
Proof
  mp_tac (eval_operand_oracle_updates |> SPEC_ALL |> Q.INST [`rqs` |-> `s.vs_requests`]) >>
  simp[Excl "eval_operand_oracle_updates"]
QED

Theorem eval_operands_outcomes_update:
  eval_operands ops (s with vs_outcomes := os) = eval_operands ops s
Proof
  mp_tac (eval_operands_oracle_updates |> SPEC_ALL |> Q.INST [`rqs` |-> `s.vs_requests`]) >>
  simp[Excl "eval_operands_oracle_updates"]
QED

Theorem one_phi_outcomes_update[local]:
  eval_one_phi (s with vs_outcomes := os) i = eval_one_phi s i
Proof
  simp[eval_one_phi_def, operand_outcomes_update]
QED

Theorem phis_outcomes_update[local]:
  !insts s t os. eval_phis s insts = OK t ==>
    eval_phis (s with vs_outcomes := os) insts =
      OK (t with vs_outcomes := os)
Proof
  Induct >> simp[eval_phis_def] >> rpt gen_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[eval_phis_def] >>
  simp[one_phi_outcomes_update, AllCaseEqs()] >> rpt strip_tac >>
  gvs[] >> first_x_assum drule >> disch_then (qspec_then `os` mp_tac) >>
  simp[update_var_def]
QED

Theorem enters_block_outcomes_update:
  enters_block fn s t ==>
  enters_block fn (s with vs_outcomes := os) (t with vs_outcomes := os)
Proof
  simp[enters_block_def] >> rpt strip_tac >>
  drule phis_outcomes_update >> disch_then (qspec_then `os` assume_tac) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem setup_callee_outcomes_update:
  setup_callee fn args s = SOME t ==>
  setup_callee fn args (s with vs_outcomes := os) =
    SOME (t with vs_outcomes := os)
Proof
  simp[setup_callee_def] >> rpt strip_tac >> gvs[]
QED

Theorem merge_callee_outcomes_update:
  merge_callee_state (caller with vs_outcomes := xs)
    (callee with vs_outcomes := ys) =
  (merge_callee_state caller callee) with vs_outcomes := ys
Proof
  simp[merge_callee_state_def]
QED

Theorem adopt_return_outcomes_update:
  adopt_return_fmp ret (s with vs_outcomes := os) =
    (adopt_return_fmp ret s) with vs_outcomes := os
Proof
  Cases_on `ret.iret_adopt_fmp` >> simp[adopt_return_fmp_def]
QED

Theorem bind_fold_outcomes_update[local]:
  !pairs s os.
    FOLDL (\u (out,v). update_var out v u) (s with vs_outcomes := os) pairs =
    (FOLDL (\u (out,v). update_var out v u) s pairs) with vs_outcomes := os
Proof
  Induct >> simp[] >> rpt gen_tac >> PairCases_on `h` >>
  first_x_assum (qspecl_then [`update_var h0 h1 s`, `os`] mp_tac) >>
  simp[update_var_def]
QED

Theorem bind_outputs_outcomes_update:
  bind_outputs outs vals s = SOME t ==>
  bind_outputs outs vals (s with vs_outcomes := os) =
    SOME (t with vs_outcomes := os)
Proof
  simp[bind_outputs_def, bind_fold_outcomes_update] >> rpt strip_tac >> gvs[]
QED

Theorem gas_events_step_outcomes_update:
  i.inst_opcode <> INVOKE ==>
  gas_events_step fuel ctx owner i (s with vs_outcomes := os) =
    gas_events_step fuel ctx owner i s
Proof
  simp[gas_events_step_def]
QED

Theorem step_prov_outcomes_update:
  step_prov PG G i (t with vs_outcomes := os) = step_prov PG G i t
Proof
  simp[step_prov_def, out_prov_def, lookup_var_def]
QED

Theorem entry_prov_outcomes_update:
  entry_prov fn (s with vs_outcomes := os) G = entry_prov fn s G
Proof
  simp[entry_prov_def]
QED

Theorem entry_taint_outcomes_update:
  entry_taint_vars fn (s with vs_outcomes := os) tn = entry_taint_vars fn s tn
Proof
  simp[entry_taint_vars_def]
QED

Theorem write_ranges_outcomes_update[local]:
  source_memory_write_ranges i (s with vs_outcomes := os) =
    source_memory_write_ranges i s
Proof
  simp[source_memory_write_ranges_def, fixed_source_write_range_def,
    sized_source_write_range_def, operand_outcomes_update,
    eval_operands_outcomes_update]
QED

Theorem ghost_components_outcomes_update[local]:
  mem_taint tn i (s with vs_outcomes := xs) (t with vs_outcomes := ys) =
    mem_taint tn i s t /\
  out_taint tn i (s with vs_outcomes := xs) = out_taint tn i s /\
  store_taint opc tn i (s with vs_outcomes := xs) X = store_taint opc tn i s X /\
  imm_taint tn i (s with vs_outcomes := xs) = imm_taint tn i s
Proof
  simp[mem_taint_def, new_site_bytes_def, step_writes_def,
    written_taint_def, out_taint_def, store_taint_def, imm_taint_def,
    write_ranges_outcomes_update, operand_outcomes_update]
QED

Theorem step_taint_noncall_outcomes_update:
  i.inst_opcode <> CALL ==>
  step_taint i (s with vs_outcomes := xs) (t with vs_outcomes := ys) tn =
    step_taint i s t tn
Proof
  simp[step_taint_def, ghost_components_outcomes_update, adopt_reset_def]
QED

Theorem step_taint_same_head_outcomes_update:
  s.vs_outcomes = oc::tail /\ t.vs_outcomes = tail ==>
  step_taint i (s with vs_outcomes := oc::rest)
    (t with vs_outcomes := rest) tn = step_taint i s t tn
Proof
  strip_tac >>
  `tail <> oc::tail /\ rest <> oc::rest` by
    (conj_tac >> strip_tac >>
     pop_assum (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  simp[step_taint_def, ghost_components_outcomes_update]
QED
