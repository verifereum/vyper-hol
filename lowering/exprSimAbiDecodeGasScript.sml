(* ABI decoding's invalid-input prefix retains the concrete child's
   complete postcondition. The caller keeps the existing exemption gate. *)
Theory exprSimAbiDecodeGas
Ancestors
  gasSummary exprSim exprLowering compileEnv
  vyperInterpreter vyperContext vyperState vyperValue vyperAST

Theorem abi_decode_invalid_source:
  !cx ann unwrap ty e st v st'.
    bind (eval_expr cx e) (read_result cx) st = (INL v, st') /\
    evaluate_type_builtin cx (AbiDecode unwrap) ty [expr_type e] [v] =
      INR (RuntimeError "abi_decode invalid") ==>
    bind (eval_expr cx (TypeBuiltin ann (AbiDecode unwrap) ty [e]))
         (read_result cx) st =
      (INR (Error (RuntimeError "abi_decode invalid")), st')
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (child_result, child_state)` >>
  Cases_on `child_result` >>
  gvs[bind_def] >>
  simp[Once evaluate_def, type_builtin_args_length_ok_def,
       ignore_bind_def, type_check_def, assert_def, bind_def] >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, return_def, bind_def, lift_sum_def, raise_def]
QED

Theorem abi_decode_invalid_gas_prefix:
  !ctx func cenv cx ann unwrap ty e es sa s1 x s0 marks v ee t.
    lower_value compile_expr cenv (expr_type e) e sa = (x, s1) /\
    gas_marked_exec (ctx, func)
      (bind (eval_expr cx e) (read_result cx))
      (es, s0) marks (INL v) ee (OK t) /\
    expr_post ctx func cenv cx e es sa s1 s0
      (ee with gas_obs := []) v x t /\
    t.vs_current_bb = s1.cs_current_bb /\
    t.vs_inst_idx = LENGTH s1.cs_current_insts /\
    evaluate_type_builtin cx (AbiDecode unwrap) ty [expr_type e] [v] =
      INR (RuntimeError "abi_decode invalid") ==>
    gas_marked_exec (ctx, func)
      (bind (eval_expr cx (TypeBuiltin ann (AbiDecode unwrap) ty [e]))
            (read_result cx))
      (es, s0) marks
      (INR (Error (RuntimeError "abi_decode invalid"))) ee (OK t) /\
    expr_post ctx func cenv cx e es sa s1 s0
      (ee with gas_obs := []) v x t /\
    t.vs_current_bb = s1.cs_current_bb /\
    t.vs_inst_idx = LENGTH s1.cs_current_insts
Proof
  rpt strip_tac >>
  gvs[gas_marked_exec_def] >>
  gen_tac >>
  irule abi_decode_invalid_source >>
  simp[]
QED
