(* Actual compilation of the fixed nested replacement candidate. *)
Theory augAssignNestedCompileProbe
Ancestors
  augAssignNestedReachProbe compileVyper vyperCompiler exprLowering stmtLowering
  context alist analysisSimDefs venomExecSemantics venomState
Libs finite_mapLib computeLib wordsLib

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])

Definition nested_compile_env_def:
  nested_compile_env = build_compile_env nested_reach_tops Internal Nonpayable
    "f" [] (BaseT (UintT 256)) [] F
End

Theorem nested_replacement_emission_probe:
  (SND (compile_expr nested_compile_env nested_reach_outer_ty
    nested_reach_replacement (initial_compile_state "entry"))).cs_current_insts =
  [<|inst_id := 0; inst_opcode := ALLOCA; inst_operands := [Lit 96w]; inst_outputs := ["%0"]|>;
   <|inst_id := 1; inst_opcode := MSTORE; inst_operands := [Var "%0"; Lit 1w]; inst_outputs := []|>;
   <|inst_id := 2; inst_opcode := ALLOCA; inst_operands := [Lit 64w]; inst_outputs := ["%1"]|>;
   <|inst_id := 3; inst_opcode := MSTORE; inst_operands := [Var "%1"; Lit 0w]; inst_outputs := []|>;
   <|inst_id := 4; inst_opcode := ADD; inst_operands := [Var "%0"; Lit 32w]; inst_outputs := ["%2"]|>;
   <|inst_id := 5; inst_opcode := MCOPY; inst_operands := [Var "%2"; Var "%1"; Lit 64w]; inst_outputs := []|>]
Proof
  EVAL_TAC
QED

Theorem nested_assignment_emission_probe:
  MAP (\bb. (bb.bb_label, MAP (\i. i.inst_opcode) bb.bb_instructions))
    (SND (compile_stmt nested_compile_env NoLoop (BaseT (UintT 256))
      (Assign (BaseTarget (TopLevelNameTarget (NONE,"a"))) nested_reach_replacement)
      (initial_compile_state "entry"))).cs_blocks =
    [("@wcopy_exit_5",[ADD;ASSIGN;JMP]);
     ("@wcopy_body_4",[MUL;ADD;MLOAD;ADD;SSTORE;ADD;ASSIGN;JMP]);
     ("@wcopy_cond_3",[EQ;JNZ]);
     ("@dyn_body_1",[MUL;ADD;ADD;MUL;ADD;ADD;ASSIGN;JMP]);
     ("@dyn_cond_0",[LT;ISZERO;JNZ]);
     ("entry",[ALLOCA;MSTORE;ALLOCA;MSTORE;ADD;MCOPY;MLOAD;ASSIGN;JMP])]
Proof
  EVAL_TAC
QED

Theorem nested_replacement_run:
  ?t. run_insts 1 ctx
    (SND (compile_expr nested_compile_env nested_reach_outer_ty
      nested_reach_replacement (initial_compile_state "entry"))).cs_current_insts
    (init_venom_state "entry") = OK t /\
    lookup_var "%0" t = SOME 0w /\ lookup_var "%1" t = SOME 96w /\
    mload 0 t = 1w /\ mload 32 t = 0w /\ mload 64 t = 0w
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC
QED

Definition nested_assignment_state_def:
  nested_assignment_state = SND
    (compile_stmt nested_compile_env NoLoop (BaseT (UintT 256))
      (Assign (BaseTarget (TopLevelNameTarget (NONE,"a"))) nested_reach_replacement)
      (initial_compile_state "entry"))
End

(* A STOP only seals the fragment endpoint for finite run_function evaluation. *)
Definition nested_assignment_function_def:
  nested_assignment_function = mk_raw_function "probe"
    (REVERSE nested_assignment_state.cs_blocks ++
      [<|bb_label := nested_assignment_state.cs_current_bb;
         bb_instructions := nested_assignment_state.cs_current_insts ++
           [<|inst_id := 34; inst_opcode := STOP; inst_operands := [];
              inst_outputs := []|>]|>])
End

Theorem nested_assignment_run:
  ?t. run_function 20 ctx nested_assignment_function
      (sstore 2w 7w (init_venom_state "entry")) = Halt t /\
    sload 0w t = 1w /\ sload 1w t = 0w /\ sload 2w t = 0w
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC
QED
