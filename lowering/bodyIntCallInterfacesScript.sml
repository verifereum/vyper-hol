(* Boundary probes for the internal-call simulation interfaces. *)
Theory bodyIntCallInterfaces
Ancestors
  bodySim supportedDecls vyperInterpreter exprSimHyps allocLimits
  compileVyper exprLoweringProps exprLowering compileEnv exprSim

Theorem body_inv_func_info_update:
  !tops ctx cenv cx info.
    body_inv tops ctx (cenv with ce_func_info := info) cx <=>
    body_inv tops ctx cenv cx
Proof
  simp[body_inv_def]
QED

Theorem expr_sim_inv_func_info_update:
  !cenv cx env es info.
    expr_sim_inv (cenv with ce_func_info := info) cx env es <=>
    expr_sim_inv cenv cx env es
Proof
  simp[expr_sim_inv_def]
QED

Theorem expr_body_pre_func_info_update:
  !cenv cx env ty fid es info.
    expr_body_pre (cenv with ce_func_info := info) cx env
      (Call ty (IntCall fid) [] NONE) es <=>
    expr_body_pre cenv cx env (Call ty (IntCall fid) [] NONE) es
Proof
  simp[expr_body_pre_def, expr_sim_inv_func_info_update,
       alloc_limits_expr_def]
QED

Theorem scalar_internal_abi_probe:
  build_func_info (K [])
    [FunctionDecl Internal Pure F F "f" [] [] (BaseT (UintT 256))
       [Return (SOME (Literal (BaseT (UintT 256)) (IntL 1)))]] "f" =
  (1, 0, [])
Proof
  EVAL_TAC
QED

Theorem scalar_internal_supported_probe:
  supported_program
    [FunctionDecl Internal Pure F F "f" [] [] (BaseT (UintT 256))
       [Return (SOME (Literal (BaseT (UintT 256)) (IntL 1)))]]
Proof
  EVAL_TAC
QED

Theorem compile_call_zero_metadata_probe:
  !cfn cenv ret ty fid st.
    compile_call cfn (cenv with ce_func_info := K (0,0,[])) ret ty
      (IntCall fid) [] NONE st =
    (StackValue ret (Lit 0w),
     SND (emit_void INVOKE
       [Label (internal_fn_label (cenv.ce_func_ids (nsid_to_string fid))
         (nsid_to_string fid)
         (cenv.ce_func_param_types (nsid_to_string fid)) cenv.ce_is_ctor)] st))
Proof
  simp[compile_call_def, compile_multi_vvs_def,
       compile_stage_intcall_args_def, comp_return_def] >>
  rpt gen_tac >> pairarg_tac >> simp[]
QED

Theorem zero_stack_value_not_one_probe:
  !cenv cx es s.
    ~vv_holds cenv cx (BaseT (UintT 256)) (Value (IntV 1))
      (StackValue (BaseT (UintT 256)) (Lit 0w)) es s
Proof
  simp[vv_holds_def, expr_val_rel_def, vyperStateTheory.read_result_def] >>
  EVAL_TAC >> rpt strip_tac >> gvs[] >>
  EVAL_TAC >> simp[]
QED
