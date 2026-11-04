(* Bounded branch-feasibility investigation; search is not exclusion proof. *)
Theory makeSsaCurrentBranchProbe
Ancestors makeSsaCurrentTemporalProbe makeSsaCurrentCleanupClassify
  makeSsaCurrentHistoryProbe makeSsaCurrentSimDefs makeSsaCurrentDefs

Definition branch_probe_local_def:
  branch_probe_local = mk_raw_function "probe"
  [history_probe_bb "E"
    [current_probe_inst 0 ASSIGN [Lit 1w] ["a"];
     current_probe_inst 1 ASSIGN [Lit 2w] ["b"];
     current_probe_inst 2 JMP [Label "H"] []];
   history_probe_bb "H"
    [current_probe_inst 3 PHI
       [Label "E";Var "a";Label "D";Var "b"] ["v"];
     current_probe_inst 4 ASSIGN [Lit 3w] ["x"];
     current_probe_inst 5 ADD [Var "x";Var "v"] ["z"];
     current_probe_inst 6 JMP [Label "D"] []];
   history_probe_bb "D" [current_probe_inst 7 JMP [Label "H"] []]]
End

Definition branch_probe_two_entries_def:
  branch_probe_two_entries = mk_raw_function "probe"
  [history_probe_bb "E"
    [current_probe_inst 0 ASSIGN [Lit 1w] ["a"];
     current_probe_inst 1 ASSIGN [Lit 2w] ["b"];
     current_probe_inst 2 JNZ [Var "a";Label "L";Label "R"] []];
   history_probe_bb "L"
    [current_probe_inst 3 ASSIGN [Lit 3w] ["x"];
     current_probe_inst 4 JMP [Label "H"] []];
   history_probe_bb "R"
    [current_probe_inst 5 ASSIGN [Lit 4w] ["x"];
     current_probe_inst 6 JMP [Label "I"] []];
   history_probe_bb "H"
    [current_probe_inst 7 PHI
       [Label "L";Var "a";Label "I";Var "b"] ["v"];
     current_probe_inst 8 ADD [Var "x";Var "v"] ["z"];
     current_probe_inst 9 JMP [Label "I"] []];
   history_probe_bb "I"
    [current_probe_inst 10 ADD [Var "x";Var "a"] ["w"];
     current_probe_inst 11 JMP [Label "H"] []]]
End

Theorem branch_probe_local_insert:
  temporal_insert_summary branch_probe_local =
  [("H",["v"],[Label "E";Var "v";Label "D";Var "formal_var_0"],["v"],ASSIGN)]
Proof
  EVAL_TAC
QED

Theorem branch_probe_two_entries_insert:
  temporal_insert_summary branch_probe_two_entries =
  [("H",["x"],[Label "L";Var "formal_var_2";Label "I";Var "x"],
      ["formal_var_0"],PHI);
   ("I",["x"],[Label "R";Var "formal_var_1";Label "H";Var "formal_var_0"],
      ["x"],PHI)]
Proof
  EVAL_TAC
QED

(* Family 2 (entry definition plus loop redefinition) is the already checked
   history_probe_backedges. None of these families is a new branch witness.
   This computation does not certify admissibility or universal exclusion. *)
Theorem branch_probe_uncovered_remain:
  EVERY (\(_,owners,_,_,op). op <> NOP /\ (op = ASSIGN ==> owners = ["v"]))
    (temporal_insert_summary branch_probe_local ++
     temporal_insert_summary history_probe_backedges ++
     temporal_insert_summary branch_probe_two_entries)
Proof
  rewrite_tac[branch_probe_local_insert,branch_probe_two_entries_insert,
    temporal_insert_summary_def,history_probe_backedges_insert] >> EVAL_TAC
QED
