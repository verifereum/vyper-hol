(* Builtin congruence retains the reachable operand guards of evaluate_ind. *)
Theory selfCodeFreeBuiltins
Ancestors
  selfCodeFreeInvariant selfCodeFreeContext selfCodeFreeSyntax vyperInterpreter
  vyperContext supportedExprTraverse
Libs monadsyntax

val _ = monadsyntax.enable_monad "vyper_evaluation";

Theorem self_code_free_builtin:
  ~supported_expr_exists is_self_code (Builtin ty bt es) /\
  (!s x t. type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s = (INL x,t) /\ bt = Len ==>
    eval_expr (cx with txn := (cx.txn with code := c)) (HD es) = eval_expr cx (HD es)) /\
  (!s x t. type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s = (INL x,t) /\
    bt <> Len /\ (bt = Bop In \/ bt = Bop NotIn) ==>
    eval_exprs (cx with txn := (cx.txn with code := c)) es = eval_exprs cx es) /\
  (!s x t. type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s = (INL x,t) /\
    bt <> Len /\ bt <> Bop In /\ bt <> Bop NotIn /\ bt <> Env MsgGas /\ code_slice_source bt es = NONE ==>
    eval_exprs (cx with txn := (cx.txn with code := c)) es = eval_exprs cx es) /\
  (!s x t ct addr. type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s = (INL x,t) /\
    bt <> Len /\ bt <> Bop In /\ bt <> Bop NotIn /\ bt <> Env MsgGas /\ code_slice_source bt es = SOME (ct,addr) ==>
    eval_exprs (cx with txn := (cx.txn with code := c)) (TL es) = eval_exprs cx (TL es)) /\
  (!s x t ct addr tail u. type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s = (INL x,t) /\
    bt <> Len /\ bt <> Bop In /\ bt <> Bop NotIn /\ bt <> Env MsgGas /\ code_slice_source bt es = SOME (ct,addr) /\
    eval_exprs cx (TL es) t = (INL tail,u) ==>
    eval_exprs (cx with txn := (cx.txn with code := c)) [addr] = eval_exprs cx [addr]) ==>
  eval_expr (cx with txn := (cx.txn with code := c)) (Builtin ty bt es) =
  eval_expr cx (Builtin ty bt es)
Proof
  strip_tac >> once_rewrite_tac[evaluate_def] >> simp[] >>
  irule ignore_bind_cong_implicit >> simp[] >> rpt strip_tac >>
  Cases_on `bt = Len`
  >- (gvs[] >> first_x_assum (drule_all_then assume_tac) >> simp[]) >>
  Cases_on `bt = Bop In \/ bt = Bop NotIn`
  >- (first_x_assum (drule_all_then assume_tac) >> simp[]) >>
  gvs[] >> Cases_on `bt = Env MsgGas` >- simp[] >>
  Cases_on `code_slice_source bt es`
  >- (gvs[] >> first_x_assum (drule_all_then assume_tac) >> simp[]) >>
  rename1 `code_slice_source bt es = SOME pair` >> PairCases_on `pair` >>
  drule_all self_code_free_slice_source >> strip_tac >> gvs[] >>
  first_x_assum (drule_all_then assume_tac) >> simp[evaluate_code_source_txn_code] >>
  irule bind_cong >> simp[] >> rpt strip_tac >>
  irule bind_cong >> simp[] >> rpt strip_tac >>
  irule bind_cong >> simp[] >> rpt strip_tac >>
  first_x_assum (drule_all_then assume_tac) >> simp[evaluate_code_source_txn_code]
QED
