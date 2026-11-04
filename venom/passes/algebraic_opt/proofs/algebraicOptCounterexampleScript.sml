Theory algebraicOptCounterexample
Ancestors
  algebraicOptDefs venomWf venomFnScheduleRunner unitShapeDefs

Theorem ao_signed_width_guard:
  (0w:bytes32) >= (0w-1w)
Proof
  wordsLib.WORD_DECIDE_TAC
QED

Theorem ao_signed_width_values:
  sign_extend (0w-1w) 128w = 128w /\
  sign_extend 0w 128w <> 128w
Proof
  EVAL_TAC >>
  CONV_TAC (DEPTH_CONV wordsLib.WORD_CONV) >>
  simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  EVAL_TAC
QED

Definition ao_bad_fn_def:
  ao_bad_fn = mk_raw_function "bad"
    [<| bb_label := "entry"; bb_instructions :=
      [mk_inst 0 SIGNEXTEND [Lit (0w-1w); Lit 128w] ["x"];
       mk_inst 1 SIGNEXTEND [Lit 0w; Var "x"] ["y"];
       mk_inst 2 MSTORE [Lit 0w; Var "y"] [];
       mk_inst 3 STOP [] []] |>]
End

Definition ao_bad_supply_def:
  ao_bad_supply = <| irs_next_inst := 20; irs_next_var := 0;
    irs_next_label := 0; irs_used_inst_ids := [0;1;2;3];
    irs_used_vars := ["x";"y"]; irs_used_labels := ["entry"] |>
End

Theorem ao_bad_transform:
  MAP (\i. (i.inst_opcode, i.inst_operands))
    (fn_insts (FST (ao_transform_function_supply ao_bad_supply ao_bad_fn))) =
  [(SIGNEXTEND,[Lit (0w-1w); Lit 128w]); (ASSIGN,[Var "x"]);
   (MSTORE,[Lit 0w; Var "y"]); (STOP,[])]
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC >>
  CONV_TAC (DEPTH_CONV wordsLib.WORD_CONV) >>
  simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  EVAL_TAC
QED
