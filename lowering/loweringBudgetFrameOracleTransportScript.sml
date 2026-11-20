Theory loweringBudgetFrameOracleTransport
Ancestors
  ptrDiscipline gasEvents oracleStateProps contextCodegenRel codegenRel
  memSafeRun unitTransformDefs dftCommutation
  venomExecSemantics venomState list

Theorem active_inst_outcomes_update:
  active_inst fn i (s with vs_outcomes := os) <=> active_inst fn i s
Proof
  simp[active_inst_def]
QED

Theorem operand_outcomes_update:
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

Theorem one_phi_outcomes_update:
  eval_one_phi (s with vs_outcomes := os) i = eval_one_phi s i
Proof
  simp[eval_one_phi_def, operand_outcomes_update]
QED

Theorem state_operations_outcomes_update:
  (update_var x v (s with vs_outcomes := os) =
    (update_var x v s with vs_outcomes := os)) /\
  (mload n (s with vs_outcomes := os) = mload n s) /\
  (sload k (s with vs_outcomes := os) = sload k s) /\
  (tload k (s with vs_outcomes := os) = tload k s) /\
  (mstore n v (s with vs_outcomes := os) = (mstore n v s with vs_outcomes := os)) /\
  (mstore8 n v (s with vs_outcomes := os) = (mstore8 n v s with vs_outcomes := os)) /\
  (sstore k v (s with vs_outcomes := os) = (sstore k v s with vs_outcomes := os)) /\
  (tstore k v (s with vs_outcomes := os) = (tstore k v s with vs_outcomes := os)) /\
  (write_memory_with_expansion n bs (s with vs_outcomes := os) =
    (write_memory_with_expansion n bs s with vs_outcomes := os)) /\
  (mcopy n m z (s with vs_outcomes := os) = (mcopy n m z s with vs_outcomes := os)) /\
  (istore n v (s with vs_outcomes := os) = (istore n v s with vs_outcomes := os)) /\
  (halt_state (s with vs_outcomes := os) = (halt_state s with vs_outcomes := os)) /\
  (revert_state (s with vs_outcomes := os) = (revert_state s with vs_outcomes := os)) /\
  (set_returndata bs (s with vs_outcomes := os) = (set_returndata bs s with vs_outcomes := os)) /\
  (jump_to lbl (s with vs_outcomes := os) = (jump_to lbl s with vs_outcomes := os))
Proof
  simp[update_var_def, mload_def, sload_def, tload_def, contract_storage_def,
       contract_transient_def, mstore_def, mstore8_def, sstore_def,
       tstore_def, write_memory_with_expansion_def, mcopy_def, istore_def,
       halt_state_def, revert_state_def, set_returndata_def, jump_to_def]
QED

Theorem eval_phis_outcomes_update:
  !insts s os. eval_phis (s with vs_outcomes := os) insts =
    map_result_state (\t. t with vs_outcomes := os) (eval_phis s insts)
Proof
  Induct >> simp[eval_phis_def, map_result_state_def] >> rpt gen_tac >>
  rename1 `eval_one_phi _ inst` >>
  Cases_on `inst.inst_opcode = PHI` >> simp[one_phi_outcomes_update] >>
  Cases_on `eval_one_phi s inst` >> simp[map_result_state_def] >>
  rename1 `eval_one_phi s inst = SOME p` >> Cases_on `p` >>
  Cases_on `eval_phis s insts` >>
  simp[map_result_state_def, state_operations_outcomes_update]
QED

Theorem phis_outcomes_update[local]:
  !insts s t os. eval_phis s insts = OK t ==>
    eval_phis (s with vs_outcomes := os) insts =
      OK (t with vs_outcomes := os)
Proof
  simp[eval_phis_outcomes_update, map_result_state_def]
QED

Theorem enters_block_outcomes_update:
  enters_block fn s t ==>
  enters_block fn (s with vs_outcomes := os) (t with vs_outcomes := os)
Proof
  simp[enters_block_def] >> rpt strip_tac >>
  drule phis_outcomes_update >> disch_then (qspec_then `os` assume_tac) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem enters_block_outcome_suffix:
  enters_block fn s t ==>
  enters_block fn (s with vs_outcomes := s.vs_outcomes ++ extra)
    (t with vs_outcomes := t.vs_outcomes ++ extra)
Proof
  strip_tac >>
  `t.vs_outcomes = s.vs_outcomes` by
    (fs[enters_block_def] >> drule venomExecProofsTheory.eval_phis_only_updates_vs_vars >>
     disch_then (mp_tac o Q.AP_TERM `\u. u.vs_outcomes`) >> simp[]) >>
  drule enters_block_outcomes_update >>
  disch_then (qspec_then `s.vs_outcomes ++ extra` mp_tac) >> simp[]
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
  Induct >> simp[pairTheory.FORALL_PROD, state_operations_outcomes_update]
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

Theorem write_ranges_outcomes_update:
  source_memory_write_ranges i (s with vs_outcomes := os) =
    source_memory_write_ranges i s
Proof
  simp[source_memory_write_ranges_def, fixed_source_write_range_def,
    sized_source_write_range_def, operand_outcomes_update,
    eval_operands_outcomes_update]
QED

Theorem ghost_components_outcomes_update:
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
  ~MEM i.inst_opcode [CALL; DELEGATECALL; CREATE; CREATE2] ==>
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

Theorem lookup_var_outcomes_update:
  lookup_var v (s with vs_outcomes := os) = lookup_var v s
Proof
  mp_tac (Q.INST [`op` |-> `Var v`] operand_outcomes_update) >>
  simp[eval_operand_def]
QED

Theorem taint_parts_outcomes_update:
  written_taint tn inst (s with vs_outcomes := os) = written_taint tn inst s /\
  ret_taint tn inst (s with vs_outcomes := os) = ret_taint tn inst s
Proof
  simp[written_taint_def, ret_taint_def, operand_outcomes_update]
QED

Theorem read_ranges_outcomes_update:
  source_memory_read_ranges inst (s with vs_outcomes := os) =
    source_memory_read_ranges inst s
Proof
  simp[source_memory_read_ranges_def, dret_memory_read_ranges_def,
       memory_range_of_operands_def, operand_outcomes_update,
       eval_operands_outcomes_update]
QED

Theorem ptr_predicates_outcomes_update:
  access_ok lo G fn inst (s with vs_outcomes := os) = access_ok lo G fn inst s /\
  taint_ok fn tn inst (s with vs_outcomes := os) = taint_ok fn tn inst s /\
  allocas_from lo (s with vs_outcomes := os) = allocas_from lo s /\
  allocas_below_fmp (s with vs_outcomes := os) = allocas_below_fmp s
Proof
  simp[access_ok_def, taint_ok_def, about_to_revert_def, in_revert_forward_def,
       active_inst_def, allocas_from_def, allocas_below_fmp_def,
       read_ranges_outcomes_update, write_ranges_outcomes_update,
       taint_parts_outcomes_update, operand_outcomes_update,
       eval_operands_outcomes_update, lookup_var_outcomes_update]
QED

Theorem memory_checks_outcomes_update:
  (inst_mem_below_frontier inst (s with vs_outcomes := os) =
    inst_mem_below_frontier inst s) /\
  (inst_dload_in_section inst (s with vs_outcomes := os) =
    inst_dload_in_section inst s)
Proof
  simp[inst_mem_below_frontier_def, inst_dload_in_section_def,
       read_ranges_outcomes_update, write_ranges_outcomes_update,
       operand_outcomes_update, eval_operands_outcomes_update]
QED

Theorem mem_safe_step_outcomes_update:
  inst.inst_opcode <> INVOKE ==>
  mem_safe_step fuel ctx inst (s with vs_outcomes := os) =
    mem_safe_step fuel ctx inst s
Proof
  simp[mem_safe_step_non_invoke, memory_checks_outcomes_update,
       inst_mem_below_frontiers_def, read_ranges_outcomes_update,
       write_ranges_outcomes_update]
QED
