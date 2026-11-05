Theory extRetCompilerBoundProbe
Ancestors
  exprLowering fragExec compileEnv venomInst venomState list rich_list
  vyperTypeSystem

(* ExpMod is outside compile_binop's supported dispatch.  The expression
   still has a word annotation: the frame quantifies arbitrary expressions. *)
Definition recycled_bound_expr_def:
  recycled_bound_expr =
    Builtin (BaseT (UintT 256)) (Bop ExpMod)
      [IfExp (BaseT (UintT 256))
         (Literal (BaseT BoolT) (BoolL T))
         (Literal (BaseT (UintT 256)) (IntL 0))
         (Literal (BaseT (UintT 256)) (IntL 0));
       Literal (BaseT (UintT 256)) (IntL 0)]
End

Definition recycled_bound_start_def:
  recycled_bound_start cs = cs with
    <| cs_blocks := []; cs_current_bb := "@exit_2";
       cs_current_insts := [mk_inst 5 INVALID [] []; mk_inst 77 ADD [] []];
       cs_next_id := 0; cs_next_var := 0; cs_next_label := 0 |>
End

Theorem recycled_bound_compile_probe:
  (SND (lower_value compile_expr cenv (BaseT (UintT 256))
    recycled_bound_expr (recycled_bound_start cs))).cs_current_insts =
  [mk_inst 5 INVALID [] []]
Proof
  EVAL_TAC >> simp[] >> rpt strip_tac >> gvs[] >> EVAL_TAC
QED

Definition recycled_bound_end_def:
  recycled_bound_end cenv cs = SND
    (lower_value compile_expr cenv (BaseT (UintT 256))
      recycled_bound_expr (recycled_bound_start cs))
End

Definition recycled_bound_fn_def:
  recycled_bound_fn cenv cs fn = fn with
    fn_blocks := (recycled_bound_end cenv cs).cs_blocks
End

Theorem lower_value_initial_bound_counterexample:
  let sa = recycled_bound_start cs in
  let sm = recycled_bound_end cenv cs in
  let func = recycled_bound_fn cenv cs fn in
    lower_value compile_expr cenv (BaseT (UintT 256))
      recycled_bound_expr sa = (Lit 0w,sm) /\
    ~block_is_terminated sa /\ fn_has_code sa sm func /\
    block_is_terminated sm /\ sa.cs_current_bb = sm.cs_current_bb /\
    ~(LENGTH sa.cs_current_insts < LENGTH sm.cs_current_insts) /\
    is_word_type (expr_type recycled_bound_expr)
Proof
  EVAL_TAC >> simp[] >> rpt strip_tac >> gvs[] >> EVAL_TAC
QED

(* The word annotation alone does not rule out the probe, but the exact
   frame's type_stmt premise does.  This is NOT a frozen-frame counterexample. *)
Theorem recycled_bound_expr_not_typed:
  type_stmt env ret_ty (Return (SOME recycled_bound_expr)) = NONE
Proof
  simp[recycled_bound_expr_def, type_stmt_def, well_typed_expr_def,
       well_typed_builtin_app_def, well_typed_binop_def]
QED
