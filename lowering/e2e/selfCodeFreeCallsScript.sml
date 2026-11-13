(* Guarded congruences for non-internal call branches. *)
Theory selfCodeFreeCalls
Ancestors
  selfCodeFreeInvariant selfCodeFreeContext selfCodeFreeSyntax vyperInterpreter
  vyperContext supportedExprTraverse
Libs monadsyntax

val _ = monadsyntax.enable_monad "vyper_evaluation";

Theorem self_code_free_send:
  (!s v t. type_check (LENGTH es = if has_gas then 3 else 2) "Send args" s = (INL v,t) ==>
    eval_exprs (cx with txn := (cx.txn with code := c)) es = eval_exprs cx es) ==>
  eval_expr (cx with txn := (cx.txn with code := c)) (Call ty (Send has_gas) es kws) =
  eval_expr cx (Call ty (Send has_gas) es kws)
Proof
  strip_tac >> once_rewrite_tac[evaluate_def] >> simp[] >>
  irule ignore_bind_cong_implicit >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem self_code_free_raw_call:
  eval_exprs (cx with txn := (cx.txn with code := c)) es = eval_exprs cx es ==>
  eval_expr (cx with txn := (cx.txn with code := c)) (Call ty (RawCallTarget flags) es kws) =
  eval_expr cx (Call ty (RawCallTarget flags) es kws)
Proof
  strip_tac >> once_rewrite_tac[evaluate_def] >> simp[]
QED

Theorem self_code_free_raw_call_calldata:
  eval_exprs (cx with txn := (cx.txn with code := c)) es = eval_exprs cx es ==>
  eval_expr (cx with txn := (cx.txn with code := c)) (Call ty (RawCallCalldataTarget flags) es kws) =
  eval_expr cx (Call ty (RawCallCalldataTarget flags) es kws)
Proof
  strip_tac >> once_rewrite_tac[evaluate_def] >> simp[]
QED

Theorem self_code_free_raw_log:
  eval_exprs (cx with txn := (cx.txn with code := c)) es = eval_exprs cx es ==>
  eval_expr (cx with txn := (cx.txn with code := c)) (Call ty RawLog es kws) =
  eval_expr cx (Call ty RawLog es kws)
Proof
  strip_tac >> once_rewrite_tac[evaluate_def] >> simp[]
QED

Theorem self_code_free_raw_revert:
  eval_exprs (cx with txn := (cx.txn with code := c)) es = eval_exprs cx es ==>
  eval_expr (cx with txn := (cx.txn with code := c)) (Call ty RawRevert es kws) =
  eval_expr cx (Call ty RawRevert es kws)
Proof
  strip_tac >> once_rewrite_tac[evaluate_def] >> simp[]
QED

Theorem self_code_free_selfdestruct:
  eval_exprs (cx with txn := (cx.txn with code := c)) es = eval_exprs cx es ==>
  eval_expr (cx with txn := (cx.txn with code := c)) (Call ty SelfDestructTarget es kws) =
  eval_expr cx (Call ty SelfDestructTarget es kws)
Proof
  strip_tac >> once_rewrite_tac[evaluate_def] >> simp[]
QED

Theorem self_code_free_ext_call:
  eval_exprs (cx with txn := (cx.txn with code := c)) (TAKE 1 es) = eval_exprs cx (TAKE 1 es) /\
  (!s target t. eval_exprs cx (TAKE 1 es) s = (INL target,t) ==>
    eval_exprs (cx with txn := (cx.txn with code := c)) (TAKE (LENGTH (FST (SND sig))) (DROP 1 es)) =
    eval_exprs cx (TAKE (LENGTH (FST (SND sig))) (DROP 1 es))) /\
  (!s target t vs u.
    eval_exprs cx (TAKE 1 es) s = (INL target,t) /\
    eval_exprs cx (TAKE (LENGTH (FST (SND sig))) (DROP 1 es)) t = (INL vs,u) ==>
    eval_exprs (cx with txn := (cx.txn with code := c)) (DROP (1 + LENGTH (FST (SND sig))) es) =
    eval_exprs cx (DROP (1 + LENGTH (FST (SND sig))) es)) ==>
  eval_expr (cx with txn := (cx.txn with code := c)) (Call ty (ExtCall static skip sig opts) es kws) =
  eval_expr cx (Call ty (ExtCall static skip sig opts) es kws)
Proof
  strip_tac >> once_rewrite_tac[evaluate_def] >> simp[] >>
  irule bind_cong_implicit >> simp[] >> rpt strip_tac >>
  first_x_assum (drule_then assume_tac) >> simp[] >>
  irule bind_cong >> simp[] >> rpt strip_tac >>
  first_x_assum (drule_all_then assume_tac) >> gvs[]
QED

Theorem self_code_free_create_blueprint:
  eval_exprs (cx with txn := (cx.txn with code := c)) (TAKE (if salt then 4 else 3) es) =
  eval_exprs cx (TAKE (if salt then 4 else 3) es) /\
  (!s prefix t size u.
    eval_exprs cx (TAKE (if salt then 4 else 3) es) s = (INL prefix,t) /\
    check_create_blueprint salt prefix t = (INL size,u) ==>
    eval_expr_results (cx with txn := (cx.txn with code := c)) (DROP (if salt then 4 else 3) es) =
    eval_expr_results cx (DROP (if salt then 4 else 3) es)) ==>
  eval_expr (cx with txn := (cx.txn with code := c)) (Call ty (CreateTarget (CreateFromBlueprint raw) salt rof unused) es kws) =
  eval_expr cx (Call ty (CreateTarget (CreateFromBlueprint raw) salt rof unused) es kws)
Proof
  strip_tac >> once_rewrite_tac[evaluate_def] >> simp[] >>
  irule bind_cong_implicit >> simp[] >> rpt strip_tac >>
  irule bind_cong >> simp[] >> rpt strip_tac >>
  first_x_assum (drule_all_then assume_tac) >> simp[]
QED

Theorem self_code_free_raw_create:
  eval_exprs (cx with txn := (cx.txn with code := c)) (TAKE 2 es) = eval_exprs cx (TAKE 2 es) /\
  (!s prefix t. eval_exprs cx (TAKE 2 es) s = (INL prefix,t) ==>
    eval_expr_results (cx with txn := (cx.txn with code := c))
      (TAKE (LENGTH (DROP 2 es) - (if salt then 1 else 0)) (DROP 2 es)) =
    eval_expr_results cx (TAKE (LENGTH (DROP 2 es) - (if salt then 1 else 0)) (DROP 2 es))) /\
  (!s prefix t results u args v.
    eval_exprs cx (TAKE 2 es) s = (INL prefix,t) /\
    eval_expr_results cx (TAKE (LENGTH (DROP 2 es) - (if salt then 1 else 0)) (DROP 2 es)) t = (INL results,u) /\
    read_results cx results u = (INL args,v) ==>
    eval_exprs (cx with txn := (cx.txn with code := c))
      (DROP (LENGTH (DROP 2 es) - (if salt then 1 else 0)) (DROP 2 es)) =
    eval_exprs cx (DROP (LENGTH (DROP 2 es) - (if salt then 1 else 0)) (DROP 2 es))) ==>
  eval_expr (cx with txn := (cx.txn with code := c)) (Call ty (CreateTarget RawCreate salt rof unused) es kws) =
  eval_expr cx (Call ty (CreateTarget RawCreate salt rof unused) es kws)
Proof
  strip_tac >> once_rewrite_tac[evaluate_def] >> simp[] >>
  irule bind_cong_implicit >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!s prefix t. _ ==> eval_expr_results _ _ = _` (drule_then assume_tac) >> gvs[] >>
  irule bind_cong >> simp[] >> rpt strip_tac >>
  irule bind_cong >> simp[] >> rpt strip_tac >>
  first_x_assum (drule_all_then assume_tac) >> gvs[]
QED

Theorem self_code_free_create_simple:
  (kind = CreateMinimalProxy \/ kind = CreateCopyOf) /\
  eval_exprs (cx with txn := (cx.txn with code := c)) es = eval_exprs cx es ==>
  eval_expr (cx with txn := (cx.txn with code := c)) (Call ty (CreateTarget kind salt rof unused) es kws) =
  eval_expr cx (Call ty (CreateTarget kind salt rof unused) es kws)
Proof
  strip_tac >> gvs[] >> once_rewrite_tac[evaluate_def] >> simp[]
QED
