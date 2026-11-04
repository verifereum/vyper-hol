Theory makeSsaCurrentPrefixValues
Ancestors
  makeSsaCurrentPhiRuntime makeSsaCurrentPhiBatch makeSsaCurrentTokens
  makeSsaCurrentSimDefs venomExecSemantics venomState venomInst stateFrame
  list pair alist finite_map

Theorem current_phi_batch_values:
  !prefix. (suffix = [] \/ (HD suffix).inst_opcode <> PHI) /\
  EVERY (\i. i.inst_opcode = PHI) prefix /\
  (!i. MEM i prefix ==> ?name value.
    i.inst_outputs = [name] /\ eval_one_phi st i = SOME (name,value) /\
    Q name = SOME value) ==>
  ?post. eval_phis st (prefix ++ suffix) = OK post /\
    (!n. MEM n (FLAT (MAP (\i. i.inst_outputs) prefix)) ==>
       lookup_var n post = Q n) /\
    (!n. ~MEM n (FLAT (MAP (\i. i.inst_outputs) prefix)) ==>
       lookup_var n post = lookup_var n st)
Proof
  Induct
  >- (rpt strip_tac >> Cases_on `suffix` >> gvs[eval_phis_def]) >>
  rpt strip_tac >>
  `?name value. h.inst_outputs = [name] /\
    eval_one_phi st h = SOME (name,value) /\ Q name = SOME value` by
    metis_tac[MEM] >>
  `?post. eval_phis st (prefix ++ suffix) = OK post /\
    (!n. MEM n (FLAT (MAP (\i. i.inst_outputs) prefix)) ==>
       lookup_var n post = Q n) /\
    (!n. ~MEM n (FLAT (MAP (\i. i.inst_outputs) prefix)) ==>
       lookup_var n post = lookup_var n st)` by
    (first_x_assum irule >> gvs[] >> metis_tac[MEM]) >>
  qexists_tac `update_var name value post` >>
  gvs[eval_phis_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `n = name` >> gvs[]
QED

Theorem current_selected_batch_values:
  EVERY (\i. i.inst_opcode = PHI) prefix /\
  (suffix = [] \/ (HD suffix).inst_opcode <> PHI) /\
  st.vs_prev_bb = SOME p /\
  (!i. MEM i prefix ==> ?name slots v value.
    i.inst_outputs = [name] /\ i.inst_operands = current_phi_slots slots /\
    FIND (\slot. FST slot = p) slots = SOME (p,v) /\
    lookup_var v st = SOME value /\ Q name = SOME value) ==>
  ?post. eval_phis st (prefix ++ suffix) = OK post /\
    (!n. MEM n (FLAT (MAP (\i. i.inst_outputs) prefix)) ==>
       lookup_var n post = Q n) /\
    (!n. ~MEM n (FLAT (MAP (\i. i.inst_outputs) prefix)) ==>
       lookup_var n post = lookup_var n st)
Proof
  strip_tac >> irule current_phi_batch_values >> simp[] >>
  rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  qexistsl_tac [`name`, `value`] >> simp[] >>
  drule_all current_selected_slot_phi >> simp[]
QED

Theorem current_phi_batch_values_lookup:
  EVERY (\i. i.inst_opcode = PHI) prefix /\
  (suffix = [] \/ (HD suffix).inst_opcode <> PHI) /\
  (!i. MEM i prefix ==> ?name value.
    i.inst_outputs = [name] /\ eval_one_phi st i = SOME (name,value) /\
    Q name = SOME value) /\
  eval_phis st (prefix ++ suffix) = OK post ==>
  lookup_var n post =
    if MEM n (FLAT (MAP (\i. i.inst_outputs) prefix)) then Q n
    else lookup_var n st
Proof
  strip_tac >>
  `?result. eval_phis st (prefix ++ suffix) = OK result /\
    (!n. MEM n (FLAT (MAP (\i. i.inst_outputs) prefix)) ==>
      lookup_var n result = Q n) /\
    (!n. ~MEM n (FLAT (MAP (\i. i.inst_outputs) prefix)) ==>
      lookup_var n result = lookup_var n st)` by
    (irule current_phi_batch_values >> simp[]) >>
  gvs[] >> Cases_on `MEM n (FLAT (MAP (\i. i.inst_outputs) prefix))` >> simp[]
QED

Theorem current_selected_batch_frame:
  EVERY (\i. i.inst_opcode = PHI) prefix /\
  (suffix = [] \/ (HD suffix).inst_opcode <> PHI) /\
  eval_phis st (prefix ++ suffix) = OK post ==>
  execution_frame post = execution_frame st
Proof
  metis_tac[current_eval_phis_batch_frame]
QED

Theorem current_batch_token_values:
  (!n. MEM n written ==> lookup_var n post = Q n) /\
  (!n. ~MEM n written ==> lookup_var n post = lookup_var n incoming) /\
  (!v. MEM v D ==> ?n. current_token_name H (E v) = SOME n /\
    ((MEM n written /\ Q n = lookup_var v source) \/
     (~MEM n written /\ lookup_var n incoming = lookup_var v source))) ==>
  current_token_values H E D source post
Proof
  simp[current_token_values_def] >> metis_tac[]
QED
