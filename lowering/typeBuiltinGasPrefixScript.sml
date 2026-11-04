(* A source type-builtin error keeps the concrete normal child prefix.
   No execution of the target conversion/decoder suffix is asserted. *)
Theory typeBuiltinGasPrefix
Ancestors
  gasNormalPrefix gasSummary typeBuiltinSource
  vyperInterpreter vyperContext vyperState vyperValue vyperAST

Theorem type_builtin_error_gas_prefix:
  !memory ctx func cenv cx child_ty e sa sb op es s0 marks v ee t
    ann tb ty err.
    gas_value_prefix memory (ctx, func, cenv, cx) (child_ty, e)
      (sa, sb, op) (es, s0) marks (v, ee, t) /\
    type_builtin_args_length_ok tb 1 /\
    evaluate_type_builtin cx tb ty [expr_type e] [v] = INR err ==>
    gas_marked_exec memory (ctx, func)
      (eval_expr cx (TypeBuiltin ann tb ty [e]))
      (es, s0) marks (INR (Error err)) ee (OK t) /\
    gas_value_prefix memory (ctx, func, cenv, cx) (child_ty, e)
      (sa, sb, op) (es, s0) marks (v, ee, t)
Proof
  rpt strip_tac >> simp[] >>
  fs[gas_value_prefix_def, gas_marked_exec_def] >>
  gen_tac >> first_x_assum (qspec_then `tail` assume_tac) >>
  drule_all eval_type_builtin_singleton_error >> simp[]
QED
