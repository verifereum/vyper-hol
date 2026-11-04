Theory makeSsaCurrentRetention
Ancestors
  makeSsaCurrentAllocation makeSsaCurrentCleanupBoundary
  makeSsaCurrentTokens makeSsaCurrentEdgeTrace makeSsaCurrentDefs venomInst

(* Defaults are deliberately excluded: a first allocation can retain the
   source spelling and hence alias its default token's name. *)
Theorem current_allocated_names_distinct:
  current_history_valid V H /\
  (!w. t <> CurrentDefault w) /\ (!w. u <> CurrentDefault w) /\
  t <> u /\ current_token_name H t = SOME a /\
  current_token_name H u = SOME b ==>
  a <> b
Proof
  metis_tac[current_allocated_name_injective]
QED

Theorem current_allocated_phi_retained:
  current_history_valid V H /\
  (!w. ta <> CurrentDefault w) /\
  (!w. tb <> CurrentDefault w) /\
  (!w. tout <> CurrentDefault w) /\
  ta <> tb /\ ta <> tout /\ tb <> tout /\
  current_token_name H ta = SOME a /\
  current_token_name H tb = SOME b /\
  current_token_name H tout = SOME out /\
  inst.inst_opcode = PHI /\ inst.inst_outputs = [out] /\
  inst.inst_operands = current_phi_slots slots /\
  MEM (p,a) slots /\ MEM (q,b) slots ==>
  simplify_current_phi inst = inst
Proof
  strip_tac >> irule current_phi_slots_retained >>
  goal_assum $ drule_at Any >>
  metis_tac[current_allocated_names_distinct]
QED
