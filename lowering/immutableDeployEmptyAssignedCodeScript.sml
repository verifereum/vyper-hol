(* Code compatibility probe with the assignment inside the real constructor. *)
Theory immutableDeployEmptyAssignedCode
Ancestors
  immutableDeployEmptyValidMachine immutableDeployEmptySource vyperCompiler
  stmtLowering compileVyper

Definition assigned_immutable_stmt_def:
  assigned_immutable_stmt =
    Assign (BaseTarget (TopLevelNameTarget (NONE,"dst"))) empty_immutable_expr
End

Definition assigned_immutable_tops_def:
  assigned_immutable_tops =
    [StructDecl "Empty" [];
     VariableDecl Private Immutable "dst" (StructT (NONE,"Empty")) NONE;
     VariableDecl Private Immutable "neighbor" (BaseT (UintT 256)) NONE;
     FunctionDecl Deploy Payable F F "__init__" [] [] NoneT [assigned_immutable_stmt]]
End

Definition assigned_immutable_unit_def:
  assigned_immutable_unit = THE
    (lower_vyper_deploy_unit assigned_immutable_tops empty_immutable_policy [])
End

Theorem assigned_immutable_lowering_succeeds:
  IS_SOME (lower_vyper_deploy_unit assigned_immutable_tops empty_immutable_policy [])
Proof
  EVAL_TAC >>
  simp[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256]
QED

Definition assigned_immutable_fn_def:
  assigned_immutable_fn = HD assigned_immutable_unit.cu_context.ctx_functions
End

Theorem assigned_immutable_fn_member:
  lookup_function assigned_immutable_fn.fn_name
    assigned_immutable_unit.cu_context.ctx_functions = SOME assigned_immutable_fn
Proof
  EVAL_TAC >>
  simp[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256] >> EVAL_TAC >> simp[]
QED

Definition assigned_immutable_ce_def:
  assigned_immutable_ce =
    (build_compile_env assigned_immutable_tops Deploy Payable "__init__"
       [] NoneT [assigned_immutable_stmt] F) with
      <|ce_imm_alloca := SOME (Var "%0"); ce_ctor_exit_label := SOME "@ctor_exit_0"|>
End

Definition assigned_immutable_sa_def:
  assigned_immutable_sa = (initial_compile_state "__deploy") with
    <|cs_next_var := 1; cs_next_label := 1; cs_next_id := 1;
      cs_current_insts :=
        [<|inst_id := 0; inst_opcode := ASSIGN; inst_operands := [Lit 0w];
           inst_outputs := ["%0"]|>]|>
End


Theorem assigned_immutable_fn_shape:
  assigned_immutable_fn = mk_raw_function "__deploy"
    [<|bb_label := "__deploy"; bb_instructions :=
       [mk_inst 0 ASSIGN [Lit 0w] ["%0"];
        mk_inst 1 ALLOCA [Lit 0w] ["%1"];
        mk_inst 2 MLOAD [Var "%1"] ["%2"];
        mk_inst 3 ADD [Var "%0"; Lit 0w] ["%3"];
        mk_inst 4 ISTORE [Var "%3"; Var "%2"] [];
        mk_inst 5 JMP [Label "@ctor_exit_0"] []]|>;
     <|bb_label := "@ctor_exit_0"; bb_instructions :=
       [mk_inst 6 ALLOCA [Lit 32w] ["%4"];
        mk_inst 7 ADD [Var "%4"; Lit 0w] ["%5"];
        mk_inst 8 MCOPY [Var "%5"; Var "%0"; Lit 32w] [];
        mk_inst 9 CODECOPY [Var "%4"; Label "runtime_begin"; Lit 0w] [];
        mk_inst 10 RETURN [Var "%4"; Lit 32w] []]|>]
Proof
  CONV_TAC (LAND_CONV EVAL) >>
  simp[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256] >> EVAL_TAC
QED

Theorem assigned_immutable_stmt_shape:
  SND (stmt_env assigned_immutable_ce NoLoop NoneT assigned_immutable_stmt
    assigned_immutable_sa) =
   <|cs_next_var := 4; cs_next_label := 1; cs_next_id := 5;
     cs_current_bb := "__deploy";
     cs_current_insts :=
       [mk_inst 0 ASSIGN [Lit 0w] ["%0"];
        mk_inst 1 ALLOCA [Lit 0w] ["%1"];
        mk_inst 2 MLOAD [Var "%1"] ["%2"];
        mk_inst 3 ADD [Var "%0"; Lit 0w] ["%3"];
        mk_inst 4 ISTORE [Var "%3"; Var "%2"] []];
     cs_blocks := []; cs_data_sections := []|>
Proof
  CONV_TAC (LAND_CONV EVAL) >> CONV_TAC (RAND_CONV EVAL) >> simp[]
QED

Theorem assigned_immutable_fragment_code:
  fn_has_code assigned_immutable_sa
    (SND (stmt_env assigned_immutable_ce NoLoop NoneT assigned_immutable_stmt
            assigned_immutable_sa)) assigned_immutable_fn /\
  fn_inst_ids_distinct assigned_immutable_fn /\
  local_ptrs_reserved assigned_immutable_ce assigned_immutable_sa /\
  (!s. ret_pc_ok assigned_immutable_ce assigned_immutable_sa s) /\
  ~block_is_terminated assigned_immutable_sa
Proof
  rewrite_tac[assigned_immutable_stmt_shape, assigned_immutable_fn_shape] >>
  conj_tac
  >- (simp[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def,
           assigned_immutable_sa_def, initial_compile_state_def,
           venomInstTheory.mk_raw_function_def, venomInstTheory.lookup_block_def] >>
      EVAL_TAC >> simp[]) >>
  conj_tac
  >- simp[venomWfTheory.fn_inst_ids_distinct_def,
          venomInstTheory.mk_raw_function_def, venomInstTheory.mk_inst_def] >>
  conj_tac
  >- (simp[compileEnvTheory.local_ptrs_reserved_def, assigned_immutable_ce_def,
           compileVyperTheory.build_compile_env_def, assigned_immutable_sa_def,
           assigned_immutable_tops_def, compileVyperTheory.build_flag_info_def,
           compileVyperTheory.allocate_args_def, initial_compile_state_def,
           compileEnvTheory.not_fresh_at_def] >>
      rpt strip_tac >>
      `toString (0:num) = "0"` by EVAL_TAC >>
      `toString n <> toString (0:num)` by simp[] >>
      metis_tac[]) >>
  conj_tac
  >- (simp[loweringPostsTheory.ret_pc_ok_def, assigned_immutable_ce_def,
           compileVyperTheory.build_compile_env_def] >> EVAL_TAC >> simp[]) >>
  EVAL_TAC >> simp[]
QED
