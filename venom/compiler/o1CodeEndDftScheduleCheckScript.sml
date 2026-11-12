(* A bounded schedule diagnostic.  The literal block keeps the generated
   DLOADBYTES packet intact; its destination is an earlier call's result.
   No new definition is needed for this single reduction. *)
Theory o1CodeEndDftScheduleCheck
Ancestors dftDefs lowerDloadDefs venomInst finite_map

Theorem generated_add_before_destination_call:
  MAP (\i. i.inst_id)
    (dft_block []
      <|bb_label := "entry"; bb_instructions :=
        [<|inst_id := 1; inst_opcode := INVOKE;
           inst_operands := [Label "g"]; inst_outputs := ["dst"]|>;
         <|inst_id := 2; inst_opcode := ADD;
           inst_operands := [Lit (n2w (2 ** 255)) ; Label "code_end"];
           inst_outputs := ["src"]|>;
         <|inst_id := 3; inst_opcode := CODECOPY;
           inst_operands := [Var "dst"; Var "src"; Lit 32w];
           inst_outputs := []|>;
         <|inst_id := 4; inst_opcode := STOP;
           inst_operands := []; inst_outputs := []|>]|>).bb_instructions =
  [2;1;3;4]
Proof
  EVAL_TAC
QED
