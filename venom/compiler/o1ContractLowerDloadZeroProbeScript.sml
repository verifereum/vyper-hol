Theory o1ContractLowerDloadZeroProbe
Ancestors
  o1PassContract lowerDloadDefs ptrDiscipline venomExecSemantics words finite_map unitShapeDefs

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
    [<| bb_label := "main"; bb_instructions := zero_probe_insts |>]
End

Definition zero_probe_supply_def:
  zero_probe_supply = <| irs_next_inst := 5; irs_next_var := 0;
    irs_next_label := 0; irs_used_inst_ids := [0;1;2;3;4];
    irs_used_vars := ["p";"d";"q";"eq"]; irs_used_labels := ["main";"main"] |>
End

Definition zero_probe_lowered_def:
  zero_probe_lowered = FST (lower_dload_function_supply zero_probe_supply zero_probe_fn)
End

Definition zero_probe_initial_def:
  zero_probe_initial = (init_venom_state "main") with
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

Definition zero_probe_branch_fn_def:
  zero_probe_branch_fn = mk_raw_function "main"
    [<| bb_label := "main"; bb_instructions :=
        TAKE 4 zero_probe_insts ++
        [<| inst_id := 4; inst_opcode := JNZ;
            inst_operands := [Var "eq"; Label "safe"; Label "unsafe"];
            inst_outputs := [] |>] |>;
     <| bb_label := "safe"; bb_instructions :=
        [<| inst_id := 5; inst_opcode := STOP;
            inst_operands := []; inst_outputs := [] |>] |>;
     <| bb_label := "unsafe"; bb_instructions :=
        [<| inst_id := 6; inst_opcode := ALLOCA;
            inst_operands := [Lit 32w]; inst_outputs := ["buf"] |>;
         <| inst_id := 7; inst_opcode := MLOAD;
            inst_operands := [Var "buf"]; inst_outputs := ["unwritten"] |>;
         <| inst_id := 8; inst_opcode := SSTORE;
            inst_operands := [Lit 0w; Var "unwritten"]; inst_outputs := [] |>;
         <| inst_id := 9; inst_opcode := STOP;
            inst_operands := []; inst_outputs := [] |>] |>]
End

Definition zero_probe_ctx_def:
  zero_probe_ctx = mk_venom_context [zero_probe_branch_fn] (SOME "main")
End

Theorem zero_probe_no_opaque:
  !origin. (origin = GAS \/ origin = RETPC_PARAM) ==>
    !x. ~copy_phi_var origin zero_probe_branch_fn x
Proof
  gen_tac >> strip_tac >> match_mp_tac copy_phi_var_no_seed >>
  EVAL_TAC >> rpt strip_tac >> gvs[]
QED

Theorem zero_probe_shape:
  o1_ctx_shape zero_probe_ctx
Proof
  simp[o1_ctx_shape_def, zero_probe_ctx_def,
       venomInstTheory.mk_venom_context_def, o1_fn_shape_def,
       fn_shape_ok_def, opaque_use_ok_def, gas_var_def, retpc_var_def,
       zero_probe_no_opaque] >>
  EVAL_TAC >> rpt strip_tac >> gvs[]
QED

Theorem zero_probe_run_state_ok:
  o1_run_state_ok zero_probe_initial
Proof
  EVAL_TAC >> CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  qexists_tac `[]` >> simp[]
QED

Theorem zero_probe_callee_first:
  callee_first ["main"] zero_probe_ctx.ctx_functions
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `MEM _ _` mp_tac >> EVAL_TAC
QED

Definition zero_probe_unit_def:
  zero_probe_unit = <| cu_context := zero_probe_ctx; cu_data_segment := [] |>
End

Definition zero_probe_out_def:
  zero_probe_out = THE (execute_configured_fn_pass ARB
    (CFP_Simple VP_LowerDload) zero_probe_unit
    (init_ir_supply zero_probe_unit) zero_probe_branch_fn)
End

Definition zero_probe_target_ctx_def:
  zero_probe_target_ctx = zero_probe_ctx with
    ctx_functions := [zero_probe_out.fpo_function]
End

Theorem zero_probe_fn_pass_step:
  fn_pass_step ARB (CFP_Simple VP_LowerDload) zero_probe_unit
    (init_ir_supply zero_probe_unit) zero_probe_branch_fn zero_probe_out
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[]
QED

Theorem zero_probe_stage:
  ctx_pass_stage ARB (CFP_Simple VP_LowerDload) (\C fn obs. T)
    zero_probe_ctx zero_probe_target_ctx
Proof
  simp[ctx_pass_stage_def, zero_probe_target_ctx_def,
       zero_probe_ctx_def, venomInstTheory.mk_venom_context_def] >>
  qexistsl_tac [`zero_probe_unit`, `init_ir_supply zero_probe_unit`,
               `zero_probe_out`] >>
  simp[zero_probe_fn_pass_step, zero_probe_unit_def, zero_probe_ctx_def,
       venomInstTheory.mk_venom_context_def]
QED

(* The six active points on the sole source path.  The unsafe block is
   deliberately absent; closure below, not a terminating-run test, justifies it. *)
Definition zero_probe_S_def:
  zero_probe_S k =
    let s0 = zero_probe_initial in
    let s1 = (update_var "p" 0w s0) with
      <| vs_allocas := FEMPTY |+ (0,(0,0)); vs_inst_idx := 1 |> in
    let s2 = (update_var "d" 0w s1) with vs_inst_idx := 2 in
    let s3 = (update_var "q" 0w s2) with
      <| vs_allocas := s2.vs_allocas |+ (2,(0,0)); vs_inst_idx := 3 |> in
    let s4 = (update_var "eq" 1w s3) with vs_inst_idx := 4 in
    let s5 = s4 with <| vs_prev_bb := SOME "main";
                        vs_current_bb := "safe"; vs_inst_idx := 0 |> in
    EL k [s0;s1;s2;s3;s4;s5]
End

Definition zero_probe_I_def:
  zero_probe_I k =
    if k < 5 then EL k (HD zero_probe_branch_fn.fn_blocks).bb_instructions
    else HD (EL 1 zero_probe_branch_fn.fn_blocks).bb_instructions
End

Theorem zero_probe_index_cases[local]:
  (k:num) < 6 ==> k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5
Proof
  decide_tac
QED

Theorem zero_probe_active:
  k < 6 ==> active_inst zero_probe_branch_fn (zero_probe_I k) (zero_probe_S k)
Proof
  strip_tac >> rewrite_tac[contextCodegenRelTheory.active_inst_def] >>
  qexists_tac `if k < 5 then HD zero_probe_branch_fn.fn_blocks
               else EL 1 zero_probe_branch_fn.fn_blocks` >>
  drule zero_probe_index_cases >> strip_tac >> gvs[] >> EVAL_TAC
QED

Theorem zero_probe_no_invoke:
  k < 6 ==> (zero_probe_I k).inst_opcode <> INVOKE
Proof
  strip_tac >> drule zero_probe_index_cases >> strip_tac >> gvs[] >> EVAL_TAC
QED

Theorem zero_probe_step:
  k < 6 ==>
  step_inst fuel zero_probe_ctx (zero_probe_I k) (zero_probe_S k) =
    if k < 4 then OK ((zero_probe_S (SUC k)) with vs_inst_idx := k)
    else if k = 4 then OK (zero_probe_S 5)
    else Halt ((zero_probe_S 5) with vs_halted := T)
Proof
  strip_tac >> drule zero_probe_index_cases >> strip_tac >> gvs[] >>
  EVAL_TAC >> simp[bool_to_word_def]
QED
