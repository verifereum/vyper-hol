Theory concretizePtrLedgerProbe
Ancestors
  concretizePtrPrefixProbe concretizeMemLocDefs venomInst words
Libs wordsLib

Definition ptr_ledger_probe_source_def:
  ptr_ledger_probe_source = ptr_probe_fn
    [mk_inst 10 ALLOCA [Lit 32w] ["p"];
     mk_inst 11 MSTORE [Var "p"; Lit 42w] [];
     mk_inst 12 NOP [] [];
     mk_inst 13 MLOAD [Var "p"] ["r"];
     mk_inst 14 STOP [] []]
End

Definition ptr_ledger_probe_target_def:
  ptr_ledger_probe_target = (ptr_probe_fn
    [mk_inst 10 ASSIGN [Lit 0w] ["p"];
     mk_inst 11 MSTORE [Var "p"; Lit 42w] [];
     mk_inst 13 MLOAD [Var "p"] ["r"];
     mk_inst 14 STOP [] []]) with
    <| fn_eom := SOME 32; fn_mems_used := [(Allocation 10,0,32)] |>
End

Theorem ptr_ledger_probe_production_transform:
  concretize_function_fuel_in_context 100
    (mk_venom_context [ptr_ledger_probe_source] (SOME "probe")) []
    ptr_ledger_probe_source = SOME ptr_ledger_probe_target
Proof
  EVAL_TAC
QED
