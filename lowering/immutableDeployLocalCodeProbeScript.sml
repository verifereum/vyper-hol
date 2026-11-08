(* A scalar constructor as code source for a hypothetical empty-local store. *)
Theory immutableDeployLocalCodeProbe
Ancestors
  immutableDeployEmptyAssignedCode immutableDeployEmptyValid
  immutableDeployEmptyStacked immutableDeployEmptySource immutableDeployEmptyDeployment
  vyperContext
  stmtLowering loweringPosts compileVyper vyperCompiler vyperTypeInitialState

Definition local_probe_decl_def:
  local_probe_decl = AnnAssign "x" (BaseT (UintT 256))
    (Literal (BaseT (UintT 256)) (IntL 0))
End
Definition local_probe_real_stmt_def:
  local_probe_real_stmt = Assign (BaseTarget (TopLevelNameTarget (NONE,"neighbor")))
    (Name (BaseT (UintT 256)) "x")
End
Definition local_probe_empty_stmt_def:
  local_probe_empty_stmt = Assign (BaseTarget (TopLevelNameTarget (NONE,"dst")))
    (Name (StructT (NONE,"Empty")) "x")
End
Definition local_probe_tops_def:
  local_probe_tops =
    [StructDecl "Empty" [];
     VariableDecl Private Immutable "dst" (StructT (NONE,"Empty")) NONE;
     VariableDecl Private Immutable "neighbor" (BaseT (UintT 256)) NONE;
     FunctionDecl Deploy Payable F F "__init__" [] [] NoneT
       [local_probe_decl; local_probe_real_stmt]]
End
Definition local_probe_unit_def:
  local_probe_unit = THE
    (lower_vyper_deploy_unit local_probe_tops empty_immutable_policy [])
End
Definition local_probe_fn_def:
  local_probe_fn = HD local_probe_unit.cu_context.ctx_functions
End
Definition local_probe_ce_def:
  local_probe_ce =
    (build_compile_env local_probe_tops Deploy Payable "__init__"
       [] NoneT [local_probe_decl; local_probe_real_stmt] F) with
      <|ce_imm_alloca := SOME (Var "%0"); ce_ctor_exit_label := SOME "@ctor_exit_0"|>
End
Definition local_probe_decl_result_def:
  local_probe_decl_result = stmt_env local_probe_ce NoLoop NoneT local_probe_decl
    assigned_immutable_sa
End
Definition local_probe_sa_def:
  local_probe_sa = SND local_probe_decl_result
End
Definition local_probe_real_ce_def:
  local_probe_real_ce = FST local_probe_decl_result
End
Definition local_probe_empty_ce_def:
  local_probe_empty_ce = local_probe_real_ce with
    <|ce_vars := local_probe_real_ce.ce_vars |+ ("x",PtrVar (Var "%1") 0);
      ce_var_type := (\id. if id = "x" then SOME (StructT (NONE,"Empty"))
                        else local_probe_real_ce.ce_var_type id)|>
End

Theorem local_probe_lowering_succeeds:
  IS_SOME (lower_vyper_deploy_unit local_probe_tops empty_immutable_policy [])
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256]
QED

Theorem local_probe_code_collision:
  SND (stmt_env local_probe_real_ce NoLoop NoneT local_probe_real_stmt local_probe_sa) =
  SND (stmt_env local_probe_empty_ce NoLoop NoneT local_probe_empty_stmt local_probe_sa)
Proof
  CONV_TAC (LAND_CONV EVAL) >> CONV_TAC (RAND_CONV EVAL) >> simp[]
QED

Theorem local_probe_sa_shape:
  local_probe_sa = (assigned_immutable_sa with
    <|cs_next_var := 2; cs_next_id := 3;
      cs_current_insts :=
        [mk_inst 0 ASSIGN [Lit 0w] ["%0"];
         mk_inst 1 ALLOCA [Lit 32w] ["%1"];
         mk_inst 2 MSTORE [Var "%1"; Lit 0w] []]|>)
Proof
  CONV_TAC (LAND_CONV EVAL) >> CONV_TAC (RAND_CONV EVAL) >> simp[]
QED

Theorem local_probe_fn_shape:
  local_probe_fn = mk_raw_function "__deploy"
    [<|bb_label := "__deploy"; bb_instructions :=
       [mk_inst 0 ASSIGN [Lit 0w] ["%0"];
        mk_inst 1 ALLOCA [Lit 32w] ["%1"];
        mk_inst 2 MSTORE [Var "%1"; Lit 0w] [];
        mk_inst 3 MLOAD [Var "%1"] ["%2"];
        mk_inst 4 ADD [Var "%0"; Lit 0w] ["%3"];
        mk_inst 5 ISTORE [Var "%3"; Var "%2"] [];
        mk_inst 6 JMP [Label "@ctor_exit_0"] []]|>;
     <|bb_label := "@ctor_exit_0"; bb_instructions :=
       [mk_inst 7 ALLOCA [Lit 32w] ["%4"];
        mk_inst 8 ADD [Var "%4"; Lit 0w] ["%5"];
        mk_inst 9 MCOPY [Var "%5"; Var "%0"; Lit 32w] [];
        mk_inst 10 CODECOPY [Var "%4"; Label "runtime_begin"; Lit 0w] [];
        mk_inst 11 RETURN [Var "%4"; Lit 32w] []]|>]
Proof
  CONV_TAC (LAND_CONV EVAL) >>
  simp[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256] >> EVAL_TAC
QED

Theorem local_probe_fn_member:
  lookup_function local_probe_fn.fn_name
    local_probe_unit.cu_context.ctx_functions = SOME local_probe_fn
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256] >>
  EVAL_TAC >> simp[]
QED

Theorem local_probe_empty_fragment_code:
  fn_has_code local_probe_sa
    (SND (stmt_env local_probe_empty_ce NoLoop NoneT local_probe_empty_stmt
       local_probe_sa)) local_probe_fn
Proof
  rewrite_tac[local_probe_fn_shape] >>
  EVAL_TAC >> simp[]
QED

Definition local_probe_cx_def:
  local_probe_cx = empty_immutable_valid_cx with
    sources := [(0w,[(NONE,local_probe_tops)])]
End

Theorem local_probe_body_typed:
  IS_SOME (type_stmts (empty_immutable_env with type_defs := type_env local_probe_tops)
    NoneT [local_probe_decl; local_probe_real_stmt])
Proof
  EVAL_TAC >> simp[finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem local_probe_functions_typed:
  functions_well_typed local_probe_cx
Proof
  rewrite_tac[vyperTypeInvariantsTheory.functions_well_typed_def] >>
  rpt gen_tac >> disch_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `get_module_code _ _ = SOME _` mp_tac >>
  simp[local_probe_cx_def, empty_immutable_valid_cx_def,
       empty_immutable_stacked_cx_def, empty_immutable_cx_def,
       vyperContextTheory.get_module_code_def,
       vyperContextTheory.empty_evaluation_context_def,
       vyperContextTheory.empty_call_txn_def] >> strip_tac >>
  qpat_x_assum `lookup_callable_function _ _ _ = SOME _` mp_tac >>
  simp[vyperInterpreterTheory.lookup_callable_function_def,
       vyperInterpreterTheory.lookup_function_def, local_probe_tops_def] >>
  strip_tac >> Cases_on `fn = "__init__"` >> gvs[] >>
  qexists `empty_immutable_env with
    <|type_defs := get_tenv local_probe_cx;
      fn_sigs := fn_sigs; bare_globals := bare_globals;
      bare_global_assignable := bare_global_assignable;
      toplevel_vtypes := toplevel_vtypes; flag_members := flag_members|>` >>
  simp[empty_immutable_env_def, local_probe_decl_def, local_probe_real_stmt_def,
       vyperTypeSystemTheory.type_stmt_def,
       vyperTypeSystemTheory.well_typed_expr_def] >>
  EVAL_TAC >>
  `get_module_code local_probe_cx NONE = SOME local_probe_tops` by EVAL_TAC >>
  `FLOOKUP bare_global_assignable (NONE,"neighbor") = SOME (BaseT (UintT 256))` by
    (qpat_x_assum `bare_global_assignable_complete _ _` mp_tac >>
     simp[vyperTypeInvariantsTheory.bare_global_assignable_complete_def] >>
     strip_tac >> first_x_assum irule >>
     goal_assum (drule_at Any) >> simp[local_probe_tops_def]) >>
  simp[finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem local_probe_empty_local_metadata:
  FLOOKUP local_probe_empty_ce.ce_vars "x" = SOME (PtrVar (Var "%1") 0) /\
  local_probe_empty_ce.ce_var_type "x" = SOME (StructT (NONE,"Empty")) /\
  local_probe_empty_ce.ce_module_vars = local_probe_real_ce.ce_module_vars /\
  local_probe_empty_ce.ce_module_var_type = local_probe_real_ce.ce_module_var_type /\
  local_probe_empty_ce.ce_imm_alloca = local_probe_real_ce.ce_imm_alloca
Proof
  simp[local_probe_empty_ce_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem local_probe_assignment_shape:
  SND (stmt_env local_probe_empty_ce NoLoop NoneT local_probe_empty_stmt local_probe_sa) =
    (local_probe_sa with
      <|cs_next_var := 4; cs_next_id := 6;
        cs_current_insts := local_probe_sa.cs_current_insts ++
          [mk_inst 3 MLOAD [Var "%1"] ["%2"];
           mk_inst 4 ADD [Var "%0"; Lit 0w] ["%3"];
           mk_inst 5 ISTORE [Var "%3"; Var "%2"] []]|>)
Proof
  CONV_TAC (LAND_CONV EVAL) >> CONV_TAC (RAND_CONV EVAL) >> simp[]
QED
