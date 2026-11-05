(* Bounded supported-but-ill-typed equality producer experiment. *)
Theory bodyPtrBopInEqualityProbe
Ancestors
  bodyPtrBopInUnequalEntry exprLowering supportedProgram

Theorem word_annotated_string_equality_supported:
  supported_program
    [FunctionDecl External View F F "probe" [] [] (BaseT BoolT)
      [Return (SOME (Builtin (BaseT BoolT) (Bop Eq)
        [Literal (BaseT (UintT 256)) (StringL "a");
         Literal (BaseT (UintT 256)) (StringL "b")]))]]
Proof
  EVAL_TAC
QED

Theorem word_annotated_string_equality_opcodes:
  (case compile_expr cenv (BaseT BoolT)
    (Builtin (BaseT BoolT) (Bop Eq)
      [Literal (BaseT (UintT 256)) (StringL "a");
       Literal (BaseT (UintT 256)) (StringL "b")])
    <| cs_next_var := 0; cs_next_label := 0; cs_next_id := 0;
       cs_current_bb := "entry"; cs_current_insts := [];
       cs_blocks := []; cs_data_sections := [] |> of
    (vv, st) => MAP (\i. i.inst_opcode) st.cs_current_insts =
      [ALLOCA; MSTORE; ADD; MSTORE; MLOAD;
       ALLOCA; MSTORE; ADD; MSTORE; MLOAD; EQ])
Proof
  EVAL_TAC
QED

Theorem unequal_membership_opcodes:
  (case compile_expr cenv (BaseT BoolT)
    (Builtin (BaseT BoolT) (Bop In)
      [Literal (BaseT (StringT 1)) (StringL "a");
       Builtin (ArrayT (BaseT (StringT 1)) (Fixed 1))
         (MakeArray (SOME (BaseT (StringT 1))) (Fixed 1))
         [Literal (BaseT (StringT 1)) (StringL "b")]])
    <| cs_next_var := 0; cs_next_label := 0; cs_next_id := 0;
       cs_current_bb := "entry"; cs_current_insts := [];
       cs_blocks := []; cs_data_sections := [] |> of
    (vv, st) => MAP (\i. i.inst_opcode) st.cs_current_insts =
      [ALLOCA; MSTORE; ADD; MSTORE; ALLOCA; MSTORE; ADD; MSTORE; EQ])
Proof
  EVAL_TAC
QED
