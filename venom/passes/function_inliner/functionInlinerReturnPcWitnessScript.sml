(* Upstream #5254: an inlined return-PC binding must not evaluate the
   removed callee's label as a value. *)
Theory functionInlinerReturnPcWitness
Ancestors
  functionInlinerDefs venomExecSemantics venomState venomInst list

Theorem inlined_retpc_assigns_zero:
  !args callee outs ret_label inst out s.
    inst.inst_opcode = RETPC_PARAM /\ inst.inst_outputs = [out] ==>
    step_inst_base
      (HD (FST (rewrite_inline_inst
        (rotate_invoke_ops (Label callee::args)) outs ret_label inst
        (LENGTH args)))) s = OK (update_var out 0w s)
Proof
  rpt strip_tac >>
  simp[rotate_invoke_ops_def, rewrite_inline_inst_def,
       is_param_opcode_def, EL_APPEND_EQN, step_inst_base_def,
       eval_operand_def]
QED

(* Splitting the first block puts its second INVOKE in a continuation
   after the second block. The snapshot must still schedule it first. *)
Theorem inliner_uses_snapshotted_call_order:
  !ctx caller callee invoke.
    invoke = (\id. <| inst_id := id; inst_opcode := INVOKE;
                     inst_operands := [Label "callee"]; inst_outputs := [] |>) /\
    caller = <| fn_name := "entry"; fn_noinline := F;
      fn_blocks := [
        <| bb_label := "entry"; bb_instructions :=
           [invoke 0; invoke 1;
            <| inst_id := 2; inst_opcode := JMP;
               inst_operands := [Label "second"]; inst_outputs := [] |>] |>;
        <| bb_label := "second"; bb_instructions :=
           [invoke 3;
            <| inst_id := 4; inst_opcode := STOP;
               inst_operands := []; inst_outputs := [] |>] |>] |> /\
    callee = <| fn_name := "callee"; fn_noinline := F;
      fn_blocks := [<| bb_label := "callee"; bb_instructions :=
        [<| inst_id := 5; inst_opcode := RET;
            inst_operands := [Lit 0w]; inst_outputs := [] |>] |>] |> /\
    ctx = <| ctx_entry := SOME "entry"; ctx_functions := [caller; callee] |> ==>
    MAP (\label. OPTION_MAP (\bb. (LAST bb.bb_instructions).inst_operands)
      (lookup_block label (HD (function_inliner_ctx 0 ctx).ctx_functions).fn_blocks))
      ["entry"; "inl0_inline_return0"; "second"] =
    [SOME [Label "inl0_callee"]; SOME [Label "inl1_callee"];
     SOME [Label "inl2_callee"]]
Proof
  rpt strip_tac >> gvs[] >> EVAL_TAC >> simp[]
QED
