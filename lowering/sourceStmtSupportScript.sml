(* #543: exact statement whitelist remainder. Recursive expressions and
   the redundant Exp AugAssign literal gate are replaced. Ordered assignment
   targets and copy-layout gates are shared with supportedStmts. *)
Theory sourceStmtSupport
Ancestors
  sourceExprSupport supportedStmts supportedTargets supportedStmtTraverse supportedExprs
  supportedExprForms supportedTypes supportedDecls vyperTypeSystem vyperAST
  list alist integer option

Definition source_assignment_remainder_def:
  source_assignment_remainder tops bindings target e <=>
    source_expr_remainder tops e /\
    case target of
      BaseTarget target_base =>
        supported_target tops bindings target_base \/
        (case supported_target_info tops bindings target_base of
           SOME (ValPT ty) => supported_place_type tops ty /\
             supported_copy_types ty (expr_type e)
         | _ => F)
    | TupleTarget targets =>
        EVERY (\g. case g of
          BaseTarget target_base => supported_target tops bindings target_base
        | TupleTarget _ => F) targets
End

Definition source_string_reason_remainder_def:
  source_string_reason_remainder tops (Literal _ (StringL text)) = T /\
  source_string_reason_remainder tops e =
    (source_pure_expr_remainder tops e /\
     case expr_type e of BaseT (StringT _) => T | _ => F)
End

Definition source_assert_reason_remainder_def:
  source_assert_reason_remainder tops AssertBare = T /\
  source_assert_reason_remainder tops AssertUnreachable = T /\
  source_assert_reason_remainder tops (AssertReason e) = source_string_reason_remainder tops e /\
  source_assert_reason_remainder tops (AssertCustomError err) = F
End

Definition source_raise_reason_remainder_def:
  source_raise_reason_remainder tops RaiseBare = T /\
  source_raise_reason_remainder tops RaiseUnreachable = T /\
  source_raise_reason_remainder tops (RaiseReason e) = source_string_reason_remainder tops e /\
  source_raise_reason_remainder tops (RaiseCustomError err) = F
End

Definition source_log_remainder_def:
  source_log_remainder tops id es <=>
    source_pure_exprs_remainder tops es /\
    case supported_event_fields tops id of
      SOME fields => MAP expr_type es = MAP (SND o FST) fields
    | NONE => F
End

Definition source_iterator_remainder_def:
  source_iterator_remainder tops ty (Range a b) n =
    (case (a,b) of
       (Literal _ (IntL start), Literal _ (IntL finish_n)) =>
         supported_integer_type ty /\ start <= finish_n /\ n = Num (finish_n - start)
     | _ => source_pure_expr_remainder tops a /\ source_pure_expr_remainder tops b /\ 0 < n) /\
  source_iterator_remainder tops ty (Array e) n =
    (case e of
       Name (ArrayT elem (Fixed m)) name => elem = ty /\ n = m
     | _ => F)
End

Definition source_aug_binop_remainder_def:
  source_aug_binop_remainder op ty e <=>
    if op = Exp then supported_integer_type ty
    else supported_binop op ty (expr_type e) F (supported_nonnegative_literal e)
End

Definition source_stmt_remainder_def:
  source_stmt_remainder tops bindings Pass = T /\
  source_stmt_remainder tops bindings Break = T /\
  source_stmt_remainder tops bindings Continue = T /\
  source_stmt_remainder tops bindings (Expr e) = source_expr_remainder tops e /\
  source_stmt_remainder tops bindings (Return NONE) = T /\
  source_stmt_remainder tops bindings (Return (SOME e)) = source_expr_remainder tops e /\
  source_stmt_remainder tops bindings (AnnAssign name ty e) =
    (supported_place_type tops ty /\ supported_copy_types ty (expr_type e) /\
     source_expr_remainder tops e) /\
  source_stmt_remainder tops bindings (Assign target e) =
    source_assignment_remainder tops bindings target e /\
  source_stmt_remainder tops bindings (AugAssign ty target op e) =
    ((supported_target tops bindings target \/ supported_aug_target tops bindings target) /\
     source_expr_remainder tops e /\ source_aug_binop_remainder op ty e) /\
  source_stmt_remainder tops bindings (Append target e) =
    (supported_append_target tops target /\ source_pure_expr_remainder tops e) /\
  source_stmt_remainder tops bindings (If c yes no) =
    (source_pure_expr_remainder tops c /\ source_stmts_remainder tops bindings yes /\
     source_stmts_remainder tops bindings no) /\
  source_stmt_remainder tops bindings (Assert c reason) =
    (source_pure_expr_remainder tops c /\ source_assert_reason_remainder tops reason) /\
  source_stmt_remainder tops bindings (Raise reason) = source_raise_reason_remainder tops reason /\
  source_stmt_remainder tops bindings (Log id es) = source_log_remainder tops id es /\
  source_stmt_remainder tops bindings (For name ty iter n body) =
    (supported_type_namespace ty /\ source_iterator_remainder tops ty iter n /\
     source_stmts_remainder tops bindings body /\
     ~supported_stmts_expr_exists expr_internal_call_root body) /\
  source_stmts_remainder tops bindings [] = T /\
  source_stmts_remainder tops bindings (s::ss) =
    (source_stmt_remainder tops bindings s /\ source_stmts_remainder tops bindings ss)
Termination
  WF_REL_TAC `measure (\x. case x of
    INL (_,_,s) => stmt_size s | INR (_,_,ss) => list_size stmt_size ss)` >>
  simp[stmt_size_def, list_size_def]
End

(* Acceptance may widen the assigned value. Ordered target and copy-layout
   restrictions are shared unchanged with main support; only RHS typing is
   needed to replace its expression remainder. *)
Theorem checked_assignment_remainder:
  atarget_accepts env target ty /\ well_typed_expr env e ==>
  (source_assignment_remainder tops bindings target e <=>
   supported_assignment tops bindings target e)
Proof
  strip_tac >> imp_res_tac checked_expr_remainder >>
  imp_res_tac checked_pure_remainder >>
  Cases_on `target` >>
  simp[source_assignment_remainder_def, supported_assignment_def]
QED

Theorem checked_string_reason_remainder:
  well_typed_expr env e ==>
  (source_string_reason_remainder tops e <=> supported_string_reason tops e)
Proof
  strip_tac >> drule (CONJUNCT1 checked_pure_remainder) >> strip_tac >>
  Cases_on `e` >>
  simp[source_string_reason_remainder_def, supported_string_reason_def] >>
  rename1 `Literal ty lit` >> Cases_on `lit` >>
  simp[source_string_reason_remainder_def, supported_string_reason_def,
       source_pure_expr_remainder_def, supported_pure_expr_def]
QED

Theorem checked_iterator_remainder:
  well_typed_iterator env ty iter ==>
  (source_iterator_remainder tops ty iter n <=> supported_iterator tops ty iter n)
Proof
  Cases_on `iter` >> simp[well_typed_iterator_def] >> strip_tac >>
  imp_res_tac checked_pure_remainder >>
  simp[source_iterator_remainder_def, supported_iterator_def]
QED

Theorem checked_aug_binop_remainder:
  IS_SOME (type_stmt env ret (AugAssign ty target op e)) ==>
  (source_aug_binop_remainder op ty e <=>
   supported_binop op ty (expr_type e) F (supported_nonnegative_literal e))
Proof
  Cases_on `op = Exp` >> simp[source_aug_binop_remainder_def] >>
  gvs[IS_SOME_EXISTS] >> strip_tac >>
  drule type_stmt_power_augassign_exponent >> strip_tac >>
  gvs[supported_binop_def, supported_nonnegative_literal_def]
QED

Theorem checked_stmt_remainder:
  (!tops bindings s. !env ret. IS_SOME (type_stmt env ret s) ==>
    (source_stmt_remainder tops bindings s <=> supported_stmt tops bindings s)) /\
  (!tops bindings ss. !env ret. IS_SOME (type_stmts env ret ss) ==>
    (source_stmts_remainder tops bindings ss <=> supported_stmts tops bindings ss))
Proof
  ho_match_mp_tac source_stmt_remainder_ind >> rw[] >>
  TRY (drule checked_aug_binop_remainder >> strip_tac) >>
  fs[source_stmt_remainder_def, supported_stmt_def] >>
  fs[IS_SOME_EXISTS, Once type_stmt_def, AllCaseEqs()] >>
  imp_res_tac checked_expr_remainder >> imp_res_tac checked_pure_remainder >>
  imp_res_tac checked_assignment_remainder >>
  imp_res_tac checked_iterator_remainder >>
  gvs[source_log_remainder_def, supported_log_def] >>
  TRY (rename1 `Assert c reason` >> Cases_on `reason` >>
       gvs[IS_SOME_EXISTS, type_stmt_def, AllCaseEqs(), source_assert_reason_remainder_def,
           supported_assert_reason_def] >>
       imp_res_tac checked_string_reason_remainder >>
       imp_res_tac checked_pure_remainder >> simp[]) >>
  TRY (rename1 `Raise reason` >> Cases_on `reason` >>
       gvs[IS_SOME_EXISTS, type_stmt_def, AllCaseEqs(), source_raise_reason_remainder_def,
           supported_raise_reason_def] >>
       imp_res_tac checked_string_reason_remainder >> simp[]) >>
  metis_tac[]
QED

val () = List.app (fn (name,th) => let
    val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null (hyp th) andalso null axioms andalso
    List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail ("source statement support kernel audit: " ^ name) end)
  (DB.thms "sourceStmtSupport");
