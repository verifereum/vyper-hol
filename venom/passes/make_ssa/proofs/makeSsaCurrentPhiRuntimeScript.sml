Theory makeSsaCurrentPhiRuntime
Ancestors
  makeSsaCurrentAllocation makeSsaCurrentSimDefs makeSsaCurrentEdgeTrace
  makeSsaCurrentTokens makeSsaCurrentDefs venomExecSemantics venomState
  stateFrame venomInst finite_map list pair

Definition current_token_values_def:
  current_token_values H E D st st' <=>
    !v. MEM v D ==> ?n. current_token_name H (E v) = SOME n /\
      lookup_var v st = lookup_var n st'
End

Theorem current_token_values_restrict:
  current_token_values H E D st st' /\
  (!v. MEM v smaller ==> MEM v D) ==>
  current_token_values H E smaller st st'
Proof
  simp[current_token_values_def] >> metis_tac[]
QED

Theorem current_token_values_lookup:
  current_token_values H E D st st' /\ MEM v D /\
  current_token_name H (E v) = SOME n ==>
  lookup_var v st = lookup_var n st'
Proof
  simp[current_token_values_def] >> metis_tac[optionTheory.SOME_11]
QED

Theorem current_token_values_projection:
  current_token_values H E D st st' /\
  (!v. MEM v D ==> current_token_name H (E v) = SOME (latest_current_name rs v)) ==>
  current_name_agree rs D st st'
Proof
  simp[current_name_agree_def] >> metis_tac[current_token_values_lookup]
QED

Theorem current_token_values_initial:
  st.vs_vars = FEMPTY /\ st'.vs_vars = FEMPTY ==>
  current_token_values H CurrentDefault D st st'
Proof
  simp[current_token_values_def, lookup_var_def]
QED

(* FIND, not membership, specifies the first matching predecessor slot. *)
Theorem current_resolve_phi_slots:
  !slots. resolve_phi prev (current_phi_slots slots) =
    OPTION_MAP (Var o SND) (FIND (\slot. FST slot = prev) slots)
Proof
  Induct >> simp[current_phi_slots_def, resolve_phi_def, FIND_thm] >>
  gen_tac >> PairCases_on `h` >>
  simp[current_phi_slots_def, resolve_phi_def, FIND_thm] >>
  Cases_on `h0 = prev` >> gvs[current_phi_slots_def]
QED

Theorem current_selected_slot_phi:
  inst.inst_outputs = [out] /\ inst.inst_operands = current_phi_slots slots /\
  st.vs_prev_bb = SOME prev /\
  FIND (\slot. FST slot = prev) slots = SOME (prev,v) ==>
  eval_one_phi st inst = OPTION_MAP (\value. (out,value)) (lookup_var v st)
Proof
  strip_tac >>
  simp[eval_one_phi_def, current_resolve_phi_slots, eval_operand_def] >>
  Cases_on `lookup_var v st` >> simp[]
QED

Theorem current_selected_slots_correspond:
  inst.inst_outputs = [out] /\ inst.inst_operands = current_phi_slots slots /\
  inst'.inst_outputs = [out'] /\ inst'.inst_operands = current_phi_slots slots' /\
  st.vs_prev_bb = SOME prev /\ st'.vs_prev_bb = SOME prev /\
  FIND (\slot. FST slot = prev) slots = SOME (prev,v) /\
  FIND (\slot. FST slot = prev) slots' = SOME (prev,n) /\
  current_token_values H E D st st' /\ MEM v D /\
  current_token_name H (E v) = SOME n /\ lookup_var v st = SOME value ==>
  eval_one_phi st inst = SOME (out,value) /\
  eval_one_phi st' inst' = SOME (out',value)
Proof
  strip_tac >>
  `lookup_var n st' = SOME value` by metis_tac[current_token_values_lookup] >>
  metis_tac[current_selected_slot_phi, optionTheory.OPTION_MAP_DEF]
QED

(* The entire PHI batch reads the incoming state; the ordinary copy reads
   its result. No sequential interpretation of the PHI batch is used. *)
Theorem current_parallel_phi_copy:
  phi.inst_opcode = PHI /\ eval_one_phi st phi = SOME (renamed,value) /\
  copy.inst_opcode = ASSIGN /\ copy.inst_operands = [Var renamed] /\
  copy.inst_outputs = [out] ==>
  eval_phis st [phi;copy] = OK (update_var renamed value st) /\
  step_inst_base copy (update_var renamed value st) =
    OK (update_var out value (update_var renamed value st)) /\
  execution_frame (update_var out value (update_var renamed value st)) =
    execution_frame st
Proof
  strip_tac >>
  simp[eval_phis_def, step_inst_base_def, eval_operand_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED
