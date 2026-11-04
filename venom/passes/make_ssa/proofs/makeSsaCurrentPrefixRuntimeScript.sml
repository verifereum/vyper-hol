Theory makeSsaCurrentPrefixRuntime
Ancestors
  makeSsaCurrentPrefixValues makeSsaCurrentOrderedCopies makeSsaCurrentTokens
  makeSsaCurrentPhiRuntime
  venomExecSemantics venomState venomInst stateFrame list

Theorem current_selected_prefix_ready:
  EVERY (\i. i.inst_opcode = PHI) prefix /\
  (copies ++ ordinary = [] \/ (HD (copies ++ ordinary)).inst_opcode <> PHI) /\
  incoming.vs_prev_bb = SOME p /\
  (!i. MEM i prefix ==> ?name slots v value.
    i.inst_outputs = [name] /\ i.inst_operands = current_phi_slots slots /\
    FIND (\slot. FST slot = p) slots = SOME (p,v) /\
    lookup_var v incoming = SOME value /\ Q name = SOME value) /\
  (!n. MEM n known ==> ~MEM n (FLAT (MAP (\i. i.inst_outputs) prefix)) /\
    lookup_var n incoming = Q n) /\
  current_copy_schedule Q (known ++ FLAT (MAP (\i. i.inst_outputs) prefix)) copies ==>
  ?post ready.
    eval_phis incoming (prefix ++ (copies ++ ordinary)) = OK post /\
    current_copies_run copies post = OK ready /\
    (!n. MEM n (known ++ FLAT (MAP (\i. i.inst_outputs) prefix) ++
      FLAT (MAP (\i. i.inst_outputs) copies)) ==> lookup_var n ready = Q n) /\
    execution_frame post = execution_frame incoming /\
    execution_frame ready = execution_frame incoming /\
    (!n. ~MEM n (FLAT (MAP (\i. i.inst_outputs) prefix)) /\
      ~MEM n (FLAT (MAP (\i. i.inst_outputs) copies)) ==>
      lookup_var n ready = lookup_var n incoming)
Proof
  strip_tac >>
  `?post. eval_phis incoming (prefix ++ (copies ++ ordinary)) = OK post /\
    (!n. MEM n (FLAT (MAP (\i. i.inst_outputs) prefix)) ==>
      lookup_var n post = Q n) /\
    (!n. ~MEM n (FLAT (MAP (\i. i.inst_outputs) prefix)) ==>
      lookup_var n post = lookup_var n incoming)` by
    (irule current_selected_batch_values >> asm_rewrite_tac[] >> qexists_tac `p` >> asm_rewrite_tac[]) >>
  `!n. MEM n (known ++ FLAT (MAP (\i. i.inst_outputs) prefix)) ==>
    lookup_var n post = Q n` by (simp[] >> metis_tac[]) >>
  drule_all current_copy_schedule_run >> strip_tac >>
  `execution_frame post = execution_frame incoming` by
    metis_tac[current_selected_batch_frame] >>
  `execution_frame ready = execution_frame incoming` by
    metis_tac[current_copy_schedule_frame] >>
  qexistsl_tac [`post`, `ready`] >> asm_rewrite_tac[] >>
  metis_tac[current_copy_schedule_untouched]
QED

Theorem current_prefix_ready_token_values:
  (!n. MEM n available ==> lookup_var n ready = Q n) /\
  (!n. ~MEM n writes ==> lookup_var n ready = lookup_var n incoming) /\
  (!v. MEM v demands ==> ?n. current_token_name H (E v) = SOME n /\
    ((MEM n available /\ Q n = lookup_var v source) \/
     (~MEM n writes /\ lookup_var n incoming = lookup_var v source))) ==>
  current_token_values H E demands source ready
Proof
  simp[current_token_values_def] >> metis_tac[]
QED

Theorem current_selected_prefix_intermediate:
  eval_phis incoming (phis ++ suffix) = OK post /\
  EVERY (\i. i.inst_opcode = PHI) phis /\
  (suffix = [] \/ (HD suffix).inst_opcode <> PHI) /\
  current_copy_schedule Q known (prefix ++ rest) /\
  (!n. MEM n known ==> lookup_var n post = Q n) ==>
  ?mid. current_copies_run prefix post = OK mid /\
    (!n. MEM n (known ++ FLAT (MAP (\i. i.inst_outputs) prefix)) ==>
      lookup_var n mid = Q n) /\
    execution_frame mid = execution_frame incoming
Proof
  strip_tac >> drule_all current_copy_schedule_prefix >> strip_tac >>
  qexists_tac `mid` >> asm_rewrite_tac[] >>
  metis_tac[current_selected_batch_frame]
QED
