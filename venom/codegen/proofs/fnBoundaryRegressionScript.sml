(* Small boundary/label regression cohort; no admitted simulation is applied. *)
Theory fnBoundaryRegression
Ancestors
  fnBoundaryProps venomToAsmProps codegenRel contextCodegenRel
  asmOracleRegression asmSem asmIR symbolResolve venomState venomInst
  venomExecSemantics stackPlanGen stackPlanTypes finite_map list rich_list
Libs finite_mapLib

val _ = Parse.hide "cp";
val () = computeLib.upd_compset add_finite_map_compset

Definition boundary_callee_def:
  boundary_callee = mk_raw_function "callee"
    [<| bb_label := "callee"; bb_instructions :=
      [mk_inst 0 PARAM [Lit 0w] ["x"];
       mk_inst 1 RETPC_PARAM [] ["retpc"];
       mk_inst 2 RET [Var "x"; Var "retpc"] []] |>]
End

(* A fresh setup frame really admits a nonempty caller suffix and an assembly
   return address different from the source token. No equal-stack-length or
   valued-variable entry premise is used. cp is not asserted generated here. *)
Theorem fresh_callee_opaque_address_and_suffix:
  let caller = (init_venom_state "callee") with
        vs_initial_fmp := n2w cp.cp_initial_fmp in
  let vs = caller with <| vs_params := [7w]; vs_return_pc_token := 7w |> in
  let as1 = asm_oracle_initial with as_stack := [99w; 7w; 11w; 12w] in
    setup_callee boundary_callee [7w] caller = SOME vs /\
    fn_has_retpc boundary_callee /\
    fn_entry_state_rel cp boundary_callee vs as1 99w [11w; 12w] /\
    vs.vs_vars = FEMPTY /\ vs.vs_return_pc_token <> 99w /\
    LENGTH as1.as_stack =
      LENGTH (get_params (HD boundary_callee.fn_blocks).bb_instructions) + 2
Proof
  simp[boundary_callee_def, mk_raw_function_def, mk_inst_def,
       setup_callee_def, fn_has_retpc_def, get_params_def,
       is_param_opcode_def, fn_entry_state_rel_def, shared_state_rel_def,
       venom_asm_terminal_rel_def, init_venom_state_def,
       asm_oracle_initial_def, context_memory_rel_def,
       wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >> EVAL_TAC
QED

(* Function leftovers are explicit; terminal leftovers remain unconstrained. *)
Theorem function_leftovers_not_terminal_contract:
  let vs = init_venom_state "entry" in
  let as1 = asm_oracle_initial with as_outcomes := [outcome] in
    venom_asm_terminal_rel vs as1 /\
    ~shared_state_rel vs as1 /\
    ~fn_return_state_rel ctx cp fn vs asm_oracle_initial as1
Proof
  simp[init_venom_state_def, asm_oracle_initial_def,
       shared_state_rel_def, fn_return_state_rel_def, venom_asm_terminal_rel_def]
QED

(* Permanent FMP/token fields are not mistaken for an assembly return address.
   Initial FMP remains constrained by cp; the other frame tokens are free here. *)
Theorem entry_frame_tokens_not_address_constraints:
  fn_entry_state_rel cp fn
    (vs with <| vs_fmp := fmp; vs_call_entry_fmp := entry_fmp;
                vs_return_pc_token := token |>) as ra rest <=>
  fn_entry_state_rel cp fn vs as ra rest
Proof
  simp[fn_entry_state_rel_def, shared_state_rel_def, venom_asm_terminal_rel_def]
QED

(* Both maps come from the SAME concrete program: byte offset 4 maps to
   assembly index 2. FEMPTY loses that jump destination. *)
Theorem concrete_label_maps_jump_regression:
  let prog = [AsmPushLabel "ret"; AsmOp "JUMP";
              AsmLabel "ret"; AsmOp "STOP"] in
  let lo = SND (compute_label_offsets prog) in
  let o2pc = build_offset_to_pc prog in
    FLOOKUP lo "ret" = SOME 4 /\
    FLOOKUP o2pc 4 = SOME 2 /\
    asm_steps lo o2pc prog 2 asm_oracle_initial =
      AsmOK (asm_oracle_initial with as_pc := 2) /\
    asm_steps lo FEMPTY prog 2 asm_oracle_initial =
      AsmError "jump: invalid destination" /\
    lo <> FEMPTY /\ o2pc <> FEMPTY
Proof
  EVAL_TAC >>
  simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``]
QED
