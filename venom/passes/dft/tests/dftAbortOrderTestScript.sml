(* DFT keeps aborting instructions of different kinds in program order
   (vyperlang/vyper#5336): an assert stays after an earlier invoke and an
   earlier returndatacopy. *)
Theory dftAbortOrderTest
Ancestors dftDefs venomInst

Definition assert_after_invoke_block_def:
  assert_after_invoke_block =
    <| bb_label := "main";
       bb_instructions :=
         [mk_inst 1 INVOKE [Label "f"] [];
          mk_inst 2 CALLDATALOAD [Lit 0w] ["x"];
          mk_inst 3 ADD [Var "x"; Lit 1w] ["y"];
          mk_inst 4 GT [Var "x"; Var "y"] ["c"];
          mk_inst 5 ISZERO [Var "c"] ["ok"];
          mk_inst 6 ASSERT [Var "ok"] [];
          mk_inst 7 MSTORE [Lit 0w; Var "y"] [];
          mk_inst 8 RETURN [Lit 0w; Lit 32w] []] |>
End

Theorem dft_assert_after_invoke:
  MAP (\i. i.inst_id) (dft_block [] assert_after_invoke_block).bb_instructions =
  [1; 2; 3; 4; 5; 6; 7; 8]
Proof
  EVAL_TAC
QED

Definition assert_after_returndatacopy_block_def:
  assert_after_returndatacopy_block =
    <| bb_label := "main";
       bb_instructions :=
         [mk_inst 1 RETURNDATACOPY [Lit 64w; Lit 0w; Lit 32w] [];
          mk_inst 2 CALLDATALOAD [Lit 0w] ["x"];
          mk_inst 3 ISZERO [Var "x"] ["ok"];
          mk_inst 4 ASSERT [Var "ok"] [];
          mk_inst 5 MLOAD [Lit 64w] ["y"];
          mk_inst 6 MSTORE [Lit 32w; Var "y"] [];
          mk_inst 7 RETURN [Lit 32w; Lit 32w] []] |>
End

Theorem dft_assert_after_returndatacopy:
  MAP (\i. i.inst_id)
    (dft_block [] assert_after_returndatacopy_block).bb_instructions =
  [1; 2; 3; 4; 5; 6; 7]
Proof
  EVAL_TAC
QED
