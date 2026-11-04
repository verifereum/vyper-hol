Theory o1ContractLowerDloadZeroProbe
Ancestors
  o1PassContract lowerDloadDefs ptrDiscipline venomExecSemantics words finite_map

(* Finite fixtures for the zero-size provenance-identity probe. *)
Definition zero_probe_insts_def:
  zero_probe_insts =
    [<| inst_id := 0; inst_opcode := ALLOCA;
        inst_operands := [Lit 0w]; inst_outputs := ["p"] |>;
     <| inst_id := 1; inst_opcode := DLOAD;
        inst_operands := [Lit 0w]; inst_outputs := ["d"] |>;
     <| inst_id := 2; inst_opcode := ALLOCA;
        inst_operands := [Lit 0w]; inst_outputs := ["q"] |>;
     <| inst_id := 3; inst_opcode := EQ;
        inst_operands := [Var "p"; Var "q"]; inst_outputs := ["eq"] |>;
     <| inst_id := 4; inst_opcode := STOP;
        inst_operands := []; inst_outputs := [] |>]
End

Definition zero_probe_fn_def:
  zero_probe_fn = mk_raw_function "main"
    [<| bb_label := "entry"; bb_instructions := zero_probe_insts |>]
End

Definition zero_probe_supply_def:
  zero_probe_supply = <| irs_next_inst := 5; irs_next_var := 0;
    irs_next_label := 0; irs_used_inst_ids := [0;1;2;3;4];
    irs_used_vars := ["p";"d";"q";"eq"]; irs_used_labels := ["main";"entry"] |>
End

Definition zero_probe_lowered_def:
  zero_probe_lowered = FST (lower_dload_function_supply zero_probe_supply zero_probe_fn)
End

Definition zero_probe_initial_def:
  zero_probe_initial = (init_venom_state "entry") with
    vs_labels := FEMPTY |+ ("code_end", 0w)
End

Theorem zero_probe_source_values:
  case exec_block 0 ARB (HD zero_probe_fn.fn_blocks) zero_probe_initial of
    Halt s => lookup_var "p" s = SOME 0w /\
              lookup_var "q" s = SOME 0w /\
              lookup_var "eq" s = SOME 1w
  | _ => F
Proof
  EVAL_TAC >> simp[dimword_def, bool_to_word_def] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> simp[bool_to_word_def]
QED

Theorem zero_probe_target_values:
  case exec_block 0 ARB (HD zero_probe_lowered.fn_blocks) zero_probe_initial of
    Halt s => lookup_var "p" s = SOME 0w /\
              lookup_var "q" s = SOME 32w /\
              lookup_var "eq" s = SOME 0w
  | _ => F
Proof
  EVAL_TAC >> simp[dimword_def, bool_to_word_def] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> simp[bool_to_word_def]
QED

Theorem zero_probe_source_provenance:
  case exec_block 0 ARB (HD zero_probe_fn.fn_blocks) zero_probe_initial of
    Halt s =>
      let G = step_prov []
                (step_prov []
                  (step_prov [] FEMPTY (EL 0 zero_probe_insts) s)
                  (EL 1 zero_probe_insts) s)
                (EL 2 zero_probe_insts) s in
      FLOOKUP G "p" = SOME (0,0) /\
      FLOOKUP G "q" = SOME (0,0) /\
      access_ok 0 G zero_probe_fn (EL 3 zero_probe_insts) s
  | _ => F
Proof
  EVAL_TAC >> simp[FLOOKUP_UPDATE]
QED

Theorem zero_probe_alloca_syntax:
  inst_wf (EL 0 zero_probe_insts) /\
  inst_wf_exec (EL 0 zero_probe_insts) /\
  inst_wf (EL 2 zero_probe_insts) /\
  inst_wf_exec (EL 2 zero_probe_insts)
Proof
  EVAL_TAC
QED

Theorem zero_probe_supply_covers:
  ir_supply_covers_fn zero_probe_supply zero_probe_fn
Proof
  EVAL_TAC
QED
