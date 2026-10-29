(* A storage write and memory hash before a read/write call. Their dependency
   insertion order determines where a later DFS places literal store values. *)
Theory dftEffectOrderTest
Ancestors dftDefs venomInst finite_map

Definition effect_order_program_def:
  effect_order_program =
    [<|inst_id := 1; inst_opcode := SSTORE;
       inst_operands := [Lit 0w; Lit 5w]; inst_outputs := []|>;
     <|inst_id := 2; inst_opcode := MSTORE;
       inst_operands := [Lit 0w; Lit 1w]; inst_outputs := []|>;
     <|inst_id := 3; inst_opcode := SHA3;
       inst_operands := [Lit 0w; Lit 64w]; inst_outputs := ["hash"]|>;
     <|inst_id := 4; inst_opcode := INVOKE;
       inst_operands := [Label "g"]; inst_outputs := []|>]
End

Theorem effect_order_storage_before_memory:
  OPTION_MAP (MAP (λi. i.inst_id))
    (FLOOKUP (build_eda effect_order_program) 4) = SOME [1; 3; 2]
Proof
  EVAL_TAC
QED
