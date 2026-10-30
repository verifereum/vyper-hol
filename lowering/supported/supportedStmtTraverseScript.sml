(* Syntactic traversals over ALL statement/target forms, including unsupported
   syntax. Reuses TASK_020 expression traversals; no evaluator/type checker.
   TOP-LEVEL: supported_stmt_expr_exists, supported_stmts_expr_exists,
   supported_assignment_exists, supported_assignments_exists,
   supported_iterator_exists, supported_assert_exists, supported_raise_exists;
   supported_stmt_bindings, supported_stmts_bindings (locals or loop variables);
   supported_internal_stmt_shape, supported_internal_stmts_shape;
   supported_type_namespace, supported_types_namespace, expr_nonmain_type_root. *)
Theory supportedStmtTraverse
Ancestors
  supportedExprTraverse supportedTypes vyperAST list pair

(* The global main-module rule also covers identifiers in type annotations.
   This is ONLY a namespace traversal, not value/storage type admission. *)
Definition supported_type_namespace_def:
  supported_type_namespace (BaseT bt) = T /\
  supported_type_namespace NoneT = T /\
  supported_type_namespace (StructT id) = supported_main_nsid id /\
  supported_type_namespace (FlagT id) = supported_main_nsid id /\
  supported_type_namespace (ArrayT elem bd) = supported_type_namespace elem /\
  supported_type_namespace (TupleT ts) = supported_types_namespace ts /\
  supported_types_namespace [] = T /\
  supported_types_namespace (ty::ts) =
    (supported_type_namespace ty /\ supported_types_namespace ts)
Termination
  WF_REL_TAC `measure (\x. case x of
    INL ty => type_size ty | INR ts => list_size type_size ts)` >>
  simp[type_size_def, list_size_def]
End

Definition expr_nonmain_type_root_def:
  expr_nonmain_type_root e <=>
    ~supported_type_namespace (expr_type e) \/
    case e of
      TypeBuiltin ty blt target es => ~supported_type_namespace target
    | _ => F
End

Definition supported_assignment_exists_def:
  supported_assignment_exists p (BaseTarget target) =
    supported_target_exists p target /\
  supported_assignment_exists p (TupleTarget targets) =
    supported_assignments_exists p targets /\
  supported_assignments_exists p [] = F /\
  supported_assignments_exists p (target::targets) =
    (supported_assignment_exists p target \/
     supported_assignments_exists p targets)
Termination
  WF_REL_TAC `measure (\x. case x of
    INL (_,t) => assignment_target_size t
  | INR (_,ts) => list_size assignment_target_size ts)` >>
  simp[assignment_target_size_def, list_size_def]
End

Definition supported_iterator_exists_def:
  supported_iterator_exists p (Array e) = supported_expr_exists p e /\
  supported_iterator_exists p (Range a b) =
    (supported_expr_exists p a \/ supported_expr_exists p b)
End

Definition supported_assert_exists_def:
  supported_assert_exists p AssertBare = F /\
  supported_assert_exists p AssertUnreachable = F /\
  supported_assert_exists p (AssertReason e) = supported_expr_exists p e /\
  supported_assert_exists p (AssertCustomError err) =
    EXISTS (supported_expr_exists p) (custom_error_exprs err)
End

Definition supported_raise_exists_def:
  supported_raise_exists p RaiseBare = F /\
  supported_raise_exists p RaiseUnreachable = F /\
  supported_raise_exists p (RaiseReason e) = supported_expr_exists p e /\
  supported_raise_exists p (RaiseCustomError err) =
    EXISTS (supported_expr_exists p) (custom_error_exprs err)
End

Definition supported_stmt_expr_exists_def:
  supported_stmt_expr_exists p Pass = F /\
  supported_stmt_expr_exists p Break = F /\
  supported_stmt_expr_exists p Continue = F /\
  supported_stmt_expr_exists p (Expr e) = supported_expr_exists p e /\
  supported_stmt_expr_exists p (Return opt) = supported_opt_exists p opt /\
  supported_stmt_expr_exists p (AnnAssign name ty e) = supported_expr_exists p e /\
  supported_stmt_expr_exists p (Assign target e) =
    (supported_assignment_exists p target \/ supported_expr_exists p e) /\
  supported_stmt_expr_exists p (AugAssign ty target op e) =
    (supported_target_exists p target \/ supported_expr_exists p e) /\
  supported_stmt_expr_exists p (Append target e) =
    (supported_target_exists p target \/ supported_expr_exists p e) /\
  supported_stmt_expr_exists p (Log id es) = supported_exprs_exists p es /\
  supported_stmt_expr_exists p (Assert c reason) =
    (supported_expr_exists p c \/ supported_assert_exists p reason) /\
  supported_stmt_expr_exists p (Raise reason) = supported_raise_exists p reason /\
  supported_stmt_expr_exists p (If c yes no) =
    (supported_expr_exists p c \/ supported_stmts_expr_exists p yes \/
     supported_stmts_expr_exists p no) /\
  supported_stmt_expr_exists p (For name ty iter bound body) =
    (supported_iterator_exists p iter \/ supported_stmts_expr_exists p body) /\
  supported_stmts_expr_exists p [] = F /\
  supported_stmts_expr_exists p (s::ss) =
    (supported_stmt_expr_exists p s \/ supported_stmts_expr_exists p ss)
Termination
  WF_REL_TAC `measure (\x. case x of
    INL (_,s) => stmt_size s | INR (_,ss) => list_size stmt_size ss)` >>
  simp[stmt_size_def, list_size_def]
End

(* keep duplicates, all branches and nesting, and their declared types;
   locals=T collects AnnAssign, locals=F collects For. *)
Definition supported_stmt_bindings_def:
  supported_stmt_bindings locals (AnnAssign name ty e) =
    (if locals then [(name,ty)] else []) /\
  supported_stmt_bindings locals (For name ty iter bound body) =
    (if locals then [] else [(name,ty)]) ++
      supported_stmts_bindings locals body /\
  supported_stmt_bindings locals (If c yes no) =
    supported_stmts_bindings locals yes ++ supported_stmts_bindings locals no /\
  supported_stmt_bindings locals Pass = [] /\
  supported_stmt_bindings locals Break = [] /\
  supported_stmt_bindings locals Continue = [] /\
  supported_stmt_bindings locals (Expr e) = [] /\
  supported_stmt_bindings locals (Return opt) = [] /\
  supported_stmt_bindings locals (Assign target e) = [] /\
  supported_stmt_bindings locals (AugAssign ty target op e) = [] /\
  supported_stmt_bindings locals (Append target e) = [] /\
  supported_stmt_bindings locals (Log id es) = [] /\
  supported_stmt_bindings locals (Assert c reason) = [] /\
  supported_stmt_bindings locals (Raise reason) = [] /\
  supported_stmts_bindings locals [] = [] /\
  supported_stmts_bindings locals (s::ss) =
    supported_stmt_bindings locals s ++ supported_stmts_bindings locals ss
Termination
  WF_REL_TAC `measure (\x. case x of
    INL (_,s) => stmt_size s | INR (_,ss) => list_size stmt_size ss)` >>
  simp[stmt_size_def, list_size_def]
End

Definition supported_internal_stmt_shape_def:
  supported_internal_stmt_shape (AnnAssign name ty e) = F /\
  supported_internal_stmt_shape (For name ty iter bound body) = F /\
  supported_internal_stmt_shape (If c yes no) =
    (supported_internal_stmts_shape yes /\ supported_internal_stmts_shape no) /\
  supported_internal_stmt_shape Pass = T /\
  supported_internal_stmt_shape Break = T /\
  supported_internal_stmt_shape Continue = T /\
  supported_internal_stmt_shape (Expr e) = T /\
  supported_internal_stmt_shape (Return opt) = T /\
  supported_internal_stmt_shape (Assign target e) = T /\
  supported_internal_stmt_shape (AugAssign ty target op e) = T /\
  supported_internal_stmt_shape (Append target e) = T /\
  supported_internal_stmt_shape (Log id es) = T /\
  supported_internal_stmt_shape (Assert c reason) = T /\
  supported_internal_stmt_shape (Raise reason) = T /\
  supported_internal_stmts_shape [] = T /\
  supported_internal_stmts_shape (s::ss) =
    (supported_internal_stmt_shape s /\ supported_internal_stmts_shape ss)
Termination
  WF_REL_TAC `measure (\x. case x of
    INL s => stmt_size s | INR ss => list_size stmt_size ss)` >>
  simp[stmt_size_def, list_size_def]
End

(* Exact structural restriction, including declarations in either If arm. *)
Theorem supported_internal_shape_bindings:
  (!s. supported_internal_stmt_shape s <=>
       supported_stmt_bindings T s = [] /\ supported_stmt_bindings F s = []) /\
  (!ss. supported_internal_stmts_shape ss <=>
        supported_stmts_bindings T ss = [] /\ supported_stmts_bindings F ss = [])
Proof
  ho_match_mp_tac supported_internal_stmt_shape_ind >>
  simp[supported_internal_stmt_shape_def, supported_stmt_bindings_def] >>
  metis_tac[]
QED

Theorem supported_stmts_expr_exists_list:
  supported_stmts_expr_exists p ss <=> EXISTS (supported_stmt_expr_exists p) ss
Proof
  Induct_on `ss` >> simp[supported_stmt_expr_exists_def]
QED

Theorem supported_stmts_bindings_append:
  supported_stmts_bindings locals (xs ++ ys) =
    supported_stmts_bindings locals xs ++ supported_stmts_bindings locals ys
Proof
  Induct_on `xs` >> simp[supported_stmt_bindings_def]
QED

Theorem supported_internal_stmts_shape_list:
  supported_internal_stmts_shape ss <=> EVERY supported_internal_stmt_shape ss
Proof
  Induct_on `ss` >> simp[supported_internal_stmt_shape_def]
QED
