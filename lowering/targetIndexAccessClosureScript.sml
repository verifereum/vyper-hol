Theory targetIndexAccessClosure
Ancestors
  vyperSubscriptOverlap list rich_list

Theorem direct_callee_access_in_expr:
  MEM fn (int_calls_expr e) /\ MEM a (function_accesses mods fn) ==>
  MEM a (expr_accesses mods e)
Proof
  simp[expr_accesses_def, reached_functions_def, MEM_nub, MEM_FLAT, MEM_MAP] >>
  metis_tac[]
QED

Theorem callee_state_access_preserved:
  (!ref. a <> ReadAcc (LocalRef ref) /\ a <> WriteAcc (LocalRef ref)) ==>
  (MEM a (callee_accesses accs) <=> MEM a accs)
Proof
  qid_spec_tac `accs` >>
  recInduct callee_accesses_ind >> simp[callee_accesses_def] >>
  rpt strip_tac >> metis_tac[]
QED
