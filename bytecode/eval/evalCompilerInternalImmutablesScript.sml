(* Integration regression: constructor internal locals and immutable staging.
   No bytecode oracle: check the unoptimized lowering IR directly. *)
Theory evalCompilerInternalImmutables
Ancestors
  compileVyper moduleLowering vyperCompiler compileEnv venomInst vyperAST
Libs finite_mapLib computeLib wordsLib

val () = computeLib.upd_compset add_finite_map_compset

Definition internal_immutable_body_def:
  internal_immutable_body =
    [AnnAssign "local" (BaseT (UintT 256))
       (TopLevelName (BaseT (UintT 256)) (NONE, "second"))]
End

Definition internal_immutable_lowered_def:
  internal_immutable_lowered =
    let cenv = build_compile_env
      [VariableDecl Private Immutable "first" (BaseT (UintT 256)) NONE;
       VariableDecl Private Immutable "second" (BaseT (UintT 256)) NONE]
      Internal Nonpayable "stage" [] NoneT internal_immutable_body F in
    SND (compile_internal_function (cenv with ce_is_ctor := T)
      [] F F 0 F F T 64 internal_immutable_body NONE
      (initial_compile_state "entry"))
End

(* The incoming internal env has ce_alloca_locals = F and ce_imm_alloca = NONE.
   compile_internal_function must set BOTH: the local receives its own ALLOCA,
   and loading the second immutable adds offset 32 to the fixed-region base.
   RETPC_PARAM remains the physical entry prefix, ahead of materialization. *)
Theorem constructor_internal_local_reads_staged_immutable:
  internal_immutable_lowered.cs_blocks = [] /\
  MAP (\i. (i.inst_opcode, i.inst_operands, i.inst_outputs))
    internal_immutable_lowered.cs_current_insts =
    [(RETPC_PARAM, [Lit 0w], ["%0"]);
     (ASSIGN, [Lit 0w], ["%1"]);
     (ALLOCA, [Lit 32w], ["%2"]);
     (ADD, [Lit 32w; Var "%1"], ["%3"]);
     (ILOAD, [Var "%3"], ["%4"]);
     (MSTORE, [Var "%2"; Var "%4"], []);
     (RET, [Var "%0"], [])]
Proof
  EVAL_TAC
QED
