(* Finite compiler-state collision candidate; these abbreviations separate
   compiler computation from the still-required simulation frame. *)
Theory bodyPtrWordBuiltinsIntervalProbe
Ancestors exprLowering moduleLowering compileEnv compileVyper vyperCompiler fragExec
  venomInst venomWf list
Libs finite_mapLib intReduce

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset intReduce.add_int_compset

Definition word_interval_expr_def:
  word_interval_expr = Builtin (BaseT (IntT 256)) Abs
    [IfExp (BaseT (IntT 256)) (Name (BaseT BoolT) "b")
      (Literal (BaseT (IntT 256)) (IntL 1))
      (Literal (BaseT (IntT 256)) (IntL 2))]
End

Definition word_interval_env_def:
  word_interval_env = build_compile_env [] External Nonpayable "foo"
    [("b", BaseT BoolT)] NoneT [Expr word_interval_expr] F
End

Definition word_interval_start_def:
  word_interval_start =
    compile_register_positional_args word_interval_env
      [("b", T, F, 32, type_to_abi_dec_info word_interval_env.ce_struct_fields
        word_interval_env (BaseT BoolT))] 4
      (initial_compile_state "entry")
End

Theorem word_interval_start_counter:
  (SND word_interval_start).cs_next_id = 7
Proof
  EVAL_TAC
QED

Definition word_interval_result_def:
  word_interval_result = lower_value compile_expr (FST word_interval_start)
    (BaseT (IntT 256)) word_interval_expr (SND word_interval_start)
End

Theorem word_interval_result_labels:
  MAP (\bb. bb.bb_label) (SND word_interval_result).cs_blocks =
    ["@else_1"; "@then_0"; "entry"]
Proof
  EVAL_TAC
QED

(* Finish the actual external body, retaining the ordinary code generator. *)
Definition word_interval_final_def:
  word_interval_final = SND (compile_external_function_body word_interval_env
    [("b", T, F, 32, type_to_abi_dec_info word_interval_env.ce_struct_fields
      word_interval_env (BaseT BoolT))] F 0 F F
    [Expr word_interval_expr] NONE (initial_compile_state "entry"))
End

Definition word_interval_function_def:
  word_interval_function =
    HD (FST (extract_context "entry" word_interval_final)).ctx_functions
End

Definition word_interval_forged_def:
  word_interval_forged lbl =
    (SND word_interval_start) with cs_current_bb := lbl
End

Definition word_interval_forged_result_def:
  word_interval_forged_result lbl =
    lower_value compile_expr (FST word_interval_start) (BaseT (IntT 256))
      word_interval_expr (word_interval_forged lbl)
End

Theorem word_interval_collision_rejected:
  !lbl. MEM lbl ["@then_0"; "@else_1"] ==>
  ~fn_has_code (word_interval_forged lbl)
    (SND (word_interval_forged_result lbl)) word_interval_function
Proof
  rpt strip_tac >> fs[fn_has_code_def] >>
  first_x_assum (qspec_then
    `LAST (emitted_blocks (word_interval_forged lbl)
       (SND (word_interval_forged_result lbl)))` mp_tac) >>
  gvs[] >> EVAL_TAC
QED

Theorem word_interval_real_code:
  fn_has_code (SND word_interval_start) (SND word_interval_result)
    word_interval_function /\ fn_inst_ids_distinct word_interval_function
Proof
  simp[fn_has_code_def] >>
  CONV_TAC (DEPTH_CONV (REWRITE_CONV [emitted_blocks_def])) >>
  EVAL_TAC >> rpt strip_tac >> gvs[] >> EVAL_TAC
QED
