(* Concrete refutation of the frozen type-builtin obligation.
   No repair to the compiler, pointer discipline or target is made here. *)
Theory bodyPtrTypeBuiltinsPaddingCounterexample
Ancestors
  bodyPtrTypeBuiltinsPaddingOutcome bodyPtrTypeBuiltinsPaddingFrame
  bodyPtrTypeBuiltinsPaddingWitness bodyPtrTypeBuiltinsPaddingTarget
  bodyPtrDefs bodyPtrPreds exprLoweringProps compileEnv finite_map list
  exprSimDefs

Theorem padding_actual_expr_sim_ptr_false:
  ~expr_sim_ptr NONE padding_runtime.cu_context PG padding_runtime_function
    padding_actual_cenv padding_actual_context (BaseT (IntT 256))
    padding_expr padding_source
Proof
  strip_tac >> fs[expr_sim_ptr_def] >>
  first_x_assum (qspec_then `padding_actual_start` mp_tac) >>
  simp[padding_actual_lower_value] >>
  qexistsl_tac [`padding_actual_machine`, `FEMPTY |+ ("%5",(0,64))`,
               `entry_taint with t_mem := {63}`] >>
  mp_tac padding_actual_fn_has_code >>
  simp[padding_actual_end_def, padding_actual_lower_value] >> strip_tac >>
  simp[padding_actual_entry_static, padding_actual_gas_admissible,
       padding_actual_stmt_state_rel, padding_actual_ghost_entry,
       padding_actual_cenv_static, padding_actual_cenv_projections,
       padding_actual_reserved_names] >>
  irule padding_actual_no_pointer_outcome >>
  rpt strip_tac >>
  `LENGTH (TAKE 12 (fn_insts padding_runtime_function)) = 12` by
    (rewrite_tac[padding_runtime_function_equation] >> EVAL_TAC) >> gvs[]
QED

Theorem padding_body_expr_ptr_ok_false:
  ~body_expr_ptr_ok padding_actual_context padding_expr
Proof
  simp[body_expr_ptr_ok_def] >>
  qexistsl_tac [`NONE`, `[]`, `padding_program`, `padding_runtime.cu_context`,
               `padding_runtime_function`, `padding_actual_cenv`,
               `padding_actual_env`, `BaseT (IntT 256)`, `padding_source`] >>
  simp[padding_actual_body_inv, padding_actual_body_pre,
       padding_actual_expr_sim_ptr_false]
QED

Theorem type_builtin_expr_ptr_ok_counterexample:
  (Convert = Empty \/ Convert = MaxValue \/ Convert = MinValue \/
   Convert = Epsilon \/ Convert = Convert \/ Convert = Extract32) /\
  (type_builtin_args_length_ok Convert
     (LENGTH [Name (BaseT (BytesT (Dynamic 1))) "x"]) ==>
   body_exprs_ptr_ok padding_actual_context
     [Name (BaseT (BytesT (Dynamic 1))) "x"]) /\
  ~body_expr_ptr_ok padding_actual_context
    (TypeBuiltin (BaseT (IntT 256)) Convert (BaseT (IntT 256))
      [Name (BaseT (BytesT (Dynamic 1))) "x"])
Proof
  simp[padding_operand_universal,
       GSYM padding_expr_def, padding_body_expr_ptr_ok_false]
QED
