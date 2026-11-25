(* External code Slice evaluates the two word operands before its address. *)
Theory entryCreateBuiltinExternalCodeSlice
Ancestors
  bodyFullBuiltinSliceCodeExternalCompose exprSimSliceExtcodeTyped bodyFullPreds
  exprSimSliceSource entryCreateFocusSpec entryCreateIntervalLayout
  exprSimSource exprSimWordArgs vyperInterpreter vyperContext vyperState

Theorem external_code_slice_source_order:
  ~is_self_code (Builtin ct (Acc Code) [addr]) ==>
  eval_expr cx (Builtin ann (Slice n) [Builtin ct (Acc Code) [addr];start;len]) =
  do vs <- eval_exprs cx [start;len];
     av <- bind (eval_expr cx addr) (read_result cx);
     code_acc <- get_accounts;
     code_v <- lift_sum (evaluate_builtin cx code_acc ct (Acc Code) [expr_type addr] [av]);
     acc <- get_accounts;
     v <- lift_sum (evaluate_builtin cx acc ann (Slice n)
           (MAP expr_type [Builtin ct (Acc Code) [addr];start;len]) (code_v::vs));
     return (Value v)
  od
Proof
  strip_tac >> drule slice_extcode_actions >> simp[] >>
  rewrite_tac[eval_exprs_cons_action] >>
  `eval_exprs cx [] = return []` by simp[FUN_EQ_THM,eval_exprs_nil,return_def] >>
  simp[bind_assoc,bind_return]
QED

Theorem external_code_slice_address_guard:
  code_slice_source (Slice n) args = SOME (ct,addr) /\
  (builtin_args_length_ok (Slice n) (LENGTH args) ==>
      case code_slice_source (Slice n) args of
        NONE => body_exprs_full_ok cx args
      | SOME (code_ty,a) =>
          body_exprs_full_ok cx (TL args) /\
          (!s vs t. eval_exprs cx (TL args) s = (INL vs,t) ==>
                body_exprs_full_ok cx [a])) /\
  eval_exprs cx (TL args) raw = (INL vals,mid) ==>
  body_expr_full_ok cx addr
Proof
  strip_tac >>
  qpat_assum `code_slice_source _ _ = SOME _`
    (strip_assume_tac o REWRITE_RULE [code_slice_source_SOME]) >>
  gvs[] >> fs[builtin_args_length_ok_def, body_exprs_full_ok_def] >>
  metis_tac[]
QED
