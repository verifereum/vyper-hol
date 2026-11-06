(* Bounded candidate test: named source fixtures permit checked evaluation.
   This does not assert a counterexample to the frozen struct-literal theorem. *)
Theory bodyPtrStructLitWidenedCandidate
Ancestors bodyPtrStructLitProgramLink supportedDecls supportedTypes
  supportedProgram bodySim compileVyper vyperAST vyperTypeSystem words
  contextCodegenRel ptrDiscipline memLocDefs venomInst venomState
Libs wordsLib

Definition structlit_identity_type_def:
  structlit_identity_type n =
    TupleT [BaseT (BytesT (Dynamic n)); BaseT (BytesT (Dynamic 1))]
End

(* Bytes are supported scalar elements, unlike the earlier array fixture. *)
Theorem structlit_identity_return_supported:
  !tops n. supported_function_return tops Internal (structlit_identity_type n)
Proof
  simp[structlit_identity_type_def, supported_function_return_def,
    supported_return_type_def, supported_value_type_def,
    supported_scalar_type_def, supported_word_type_def,
    supported_string_type_def]
QED

Theorem structlit_identity_narrow_return_accepted:
  supported_function_return [] Internal (structlit_identity_type 1)
Proof
  EVAL_TAC
QED

Definition structlit_identity_call_def:
  structlit_identity_call =
    Call (structlit_identity_type 33) (IntCall (NONE,"identity"))
      [Name (structlit_identity_type 1) "p"] NONE
End

Definition structlit_identity_program_def:
  structlit_identity_program =
    [StructDecl "S" [("x",structlit_identity_type 33)];
     FunctionDecl Internal Pure F F "identity"
       [("p",structlit_identity_type 1)] [] (structlit_identity_type 1)
       [Return (SOME (Name (structlit_identity_type 1) "p"))]]
End

Theorem structlit_identity_program_supported:
  supported_program structlit_identity_program
Proof
  EVAL_TAC
QED

Definition structlit_identity_env_def:
  structlit_identity_env =
    build_compile_env structlit_identity_program Internal Pure "identity"
      [("p",structlit_identity_type 1)] (structlit_identity_type 1)
      [Return (SOME (Name (structlit_identity_type 1) "p"))] F
End

Definition structlit_identity_return_compiled_def:
  structlit_identity_return_compiled =
    compile_stmt structlit_identity_env NoLoop (structlit_identity_type 1)
      (Return (SOME (Name (structlit_identity_type 1) "p")))
      (initial_compile_state "identity")
End

Theorem structlit_identity_return_opcodes:
  MAP (\i. i.inst_opcode)
    (SND structlit_identity_return_compiled).cs_current_insts =
    [MLOAD; MLOAD; MCOPY; RET]
Proof
  EVAL_TAC
QED

Theorem structlit_identity_return_instructions:
  (SND structlit_identity_return_compiled).cs_current_insts =
    [mk_inst 0 MLOAD [Lit 160w] ["%0"];
     mk_inst 1 MLOAD [Lit 128w] ["%1"];
     mk_inst 2 MCOPY [Var "%1"; Lit 0w; Lit 128w] [];
     mk_inst 3 RET [Var "%0"] []]
Proof
  EVAL_TAC
QED

Theorem structlit_identity_annotation_widens:
  !tenv. type_widens_to tenv (structlit_identity_type 1)
    (structlit_identity_type 33)
Proof
  gen_tac >> EVAL_TAC
QED

Definition structlit_identity_call_compiled_def:
  structlit_identity_call_compiled =
    lower_value compile_expr structlit_identity_env (structlit_identity_type 33)
      structlit_identity_call (initial_compile_state "caller")
End

Theorem structlit_identity_call_opcodes:
  MAP (\i. i.inst_opcode)
    (SND structlit_identity_call_compiled).cs_current_insts =
    [ALLOCA; ALLOCA; MCOPY; INVOKE]
Proof
  EVAL_TAC
QED

Theorem structlit_identity_call_instructions:
  (SND structlit_identity_call_compiled).cs_current_insts =
    [mk_inst 0 ALLOCA [Lit 128w] ["%0"];
     mk_inst 1 ALLOCA [Lit 128w] ["%1"];
     mk_inst 2 MCOPY [Var "%1"; Lit 0w; Lit 128w] [];
     mk_inst 3 INVOKE
       [Label "internal 0 identity((Bytes[1], Bytes[1]))_runtime";
        Var "%0"; Var "%1"] []]
Proof
  EVAL_TAC
QED

(* This particular argument staging already has a literal-address read.
   Its rejection is a child obstruction, not a counterexample to the target. *)
Theorem structlit_identity_argument_copy_rejected:
  !G fn s w. ~in_revert_forward fn s /\ lookup_var "%1" s = SOME w ==>
    ~access_ok 0 G fn
      (EL 2 (SND structlit_identity_call_compiled).cs_current_insts) s
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[structlit_identity_call_instructions] >>
  simp[access_ok_def, mk_inst_def, source_memory_read_ranges_def,
    memory_range_of_operands_def, eval_operand_def, mem_read_ops_def]
QED
