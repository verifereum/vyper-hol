(* The empty-signed-conversion exemption is decided only after the
   concrete child's source value and target landing have been related. *)
Theory exprSimConvertGas
Ancestors
  gasSummary exprSimConvert  exprLowering compileEnv
  vyperInterpreter vyperState vyperValue vyperAST

Theorem convert_empty_gas_prefix:
  !memory ctx func cenv cx ann ty e es sa s1 sb x op s0 marks v ee t.
    lower_value compile_expr cenv (expr_type e) e sa = (x, s1) /\
    compile_type_convert x (mk_convert_op (expr_type e) ty) s1 = (op, sb) /\
    gas_marked_exec memory (ctx, func)
      (bind (eval_expr cx e) (read_result cx))
      (es, s0) marks (INL v) ee (OK t) /\
    expr_post ctx func cenv cx e es sa s1 s0
      (ee with gas_obs := []) v x t /\
    t.vs_current_bb = s1.cs_current_bb /\
    t.vs_inst_idx = LENGTH s1.cs_current_insts /\
    convert_result cx (expr_type e) ty v =
      INR (Error (RuntimeError "convert empty bytes to signed")) ==>
    gas_marked_exec memory (ctx, func)
      (bind (eval_expr cx (TypeBuiltin ann Convert ty [e])) (read_result cx))
      (es, s0) marks
      (INR (Error (RuntimeError "convert empty bytes to signed"))) ee (OK t) /\
    expr_post ctx func cenv cx e es sa s1 s0
      (ee with gas_obs := []) v x t /\
    t.vs_current_bb = s1.cs_current_bb /\
    t.vs_inst_idx = LENGTH s1.cs_current_insts
Proof
  rpt strip_tac >> simp[] >>
  fs[gas_marked_exec_def] >>
  gen_tac >> first_x_assum (qspec_then `tail` assume_tac) >>
  drule eval_expr_convert_of_child >> simp[]
QED
