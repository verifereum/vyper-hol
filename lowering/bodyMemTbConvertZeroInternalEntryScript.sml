(* Bounded target host test for an internal zero-byte Bool conversion. *)
Theory bodyMemTbConvertZeroInternalEntry
Ancestors
  bodyMemTbConvertZeroEntry

Theorem convert_zero_internal_unit_exists:
  IS_SOME (lower_vyper_runtime_unit
    [FunctionDecl Internal Pure F F "zero_probe" [] [] (BaseT BoolT)
      [Return (SOME (TypeBuiltin (BaseT BoolT) Convert (BaseT BoolT)
        [Literal (BaseT (BytesT (Dynamic 0))) (BytesL [])]))]]
    <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
       rpol_final_assembly := FAP_Optimize |>)
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

Theorem convert_zero_internal_function_names:
  MAP (\f. f.fn_name)
    (THE (lower_vyper_runtime_unit
      [FunctionDecl Internal Pure F F "zero_probe" [] [] (BaseT BoolT)
        [Return (SOME (TypeBuiltin (BaseT BoolT) Convert (BaseT BoolT)
          [Literal (BaseT (BytesT (Dynamic 0))) (BytesL [])]))]]
      <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
         rpol_final_assembly := FAP_Optimize |>)).cu_context.ctx_functions =
  ["__entry"; "internal 0 zero_probe()_runtime"]
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

Theorem convert_zero_internal_inventory:
  fn_insts (EL 1
    (THE (lower_vyper_runtime_unit
      [FunctionDecl Internal Pure F F "zero_probe" [] [] (BaseT BoolT)
        [Return (SOME (TypeBuiltin (BaseT BoolT) Convert (BaseT BoolT)
          [Literal (BaseT (BytesT (Dynamic 0))) (BytesL [])]))]]
      <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
         rpol_final_assembly := FAP_Optimize |>)).cu_context.ctx_functions) =
    [<| inst_id := 8; inst_opcode := RETPC_PARAM; inst_operands := [Lit 0w]; inst_outputs := ["%5"] |>;
     <| inst_id := 9; inst_opcode := ALLOCA; inst_operands := [Lit 32w]; inst_outputs := ["%6"] |>;
     <| inst_id := 10; inst_opcode := ALLOCA; inst_operands := [Lit 32w]; inst_outputs := ["%7"] |>;
     <| inst_id := 11; inst_opcode := MSTORE; inst_operands := [Var "%7"; Lit 0w]; inst_outputs := [] |>;
     <| inst_id := 12; inst_opcode := RET; inst_operands := [Lit 0w; Var "%5"]; inst_outputs := [] |>]
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, venomInstTheory.fn_insts_blocks_def]
QED
