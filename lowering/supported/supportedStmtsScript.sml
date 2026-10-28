(* Statement whitelist with ordered assignment targets. Types/names are syntactic
   bindings, not source typing. Effects use supported_expr's existing root forms.
   TOP-LEVEL: supported_stmt, supported_stmts; supported_iterator,
   supported_assignment, supported_target, supported_append_target,
   supported_assert_reason, supported_raise_reason, supported_log. *)
Theory supportedStmts
Ancestors
  supportedStmtTraverse supportedExprs supportedExprForms supportedExprTraverse
  supportedTypes supportedDecls vyperAST list alist integer

Definition supported_local_word_def:
  supported_local_word bindings name <=>
    case ALOOKUP bindings name of SOME ty => supported_word_type ty | NONE => F
End

Definition supported_scalar_target_def:
  supported_scalar_target tops id <=>
    case supported_variable_decl tops id of
      SOME (Private, Storage, ty, SOME slot) => supported_full_word_type ty
    | SOME (Private, Transient, ty, SOME slot) => supported_full_word_type ty
    | _ => F
End

Definition supported_storage_field_write_def:
  supported_storage_field_write tops id fname <=>
    case supported_storage_fields tops id of
      SOME fields => MEM fname (MAP FST fields)
    | NONE => F
End

Definition supported_target_def:
  supported_target tops bindings target <=>
    case target of
      NameTarget name =>
        (case ALOOKUP bindings name of
           SOME ty => supported_value_type tops ty
         | NONE => F)
    | TopLevelNameTarget id => supported_scalar_target tops id
    | SubscriptTarget (TopLevelNameTarget id) key =>
        supported_subscript_base tops id /\ supported_expr tops key
    | AttributeTarget (TopLevelNameTarget id) fname =>
        supported_storage_field_write tops id fname
    | _ => F
End

(* Tuple lowering loads all RHS elements, then resolves and stores each flat
   target in order. Its INVALID branch for nested TupleTargets remains outside
   the supported compiler domain. *)
Definition supported_assignment_def:
  supported_assignment tops bindings target e <=>
    supported_expr tops e /\
    case target of
    | BaseTarget bt => supported_target tops bindings bt
    | TupleTarget targets =>
        EVERY (\g. case g of
          BaseTarget bt => supported_target tops bindings bt
        | TupleTarget _ => F) targets
End

Definition supported_append_target_def:
  supported_append_target tops (TopLevelNameTarget id) =
    supported_storage_dynamic_array tops id /\
  supported_append_target tops (NameTarget name) = F /\
  supported_append_target tops (SubscriptTarget target key) = F /\
  supported_append_target tops (AttributeTarget target fname) = F
End

Definition supported_string_reason_def:
  supported_string_reason tops (Literal _ (StringL text)) = T /\
  supported_string_reason tops e =
    (supported_pure_expr tops e /\
     case expr_type e of BaseT (StringT _) => T | _ => F)
End

Definition supported_assert_reason_def:
  supported_assert_reason tops AssertBare = T /\
  supported_assert_reason tops AssertUnreachable = T /\
  supported_assert_reason tops (AssertReason e) = supported_string_reason tops e
End

Definition supported_raise_reason_def:
  supported_raise_reason tops RaiseBare = T /\
  supported_raise_reason tops RaiseUnreachable = T /\
  supported_raise_reason tops (RaiseReason e) = supported_string_reason tops e
End

Definition supported_log_def:
  supported_log tops id es <=>
    supported_pure_exprs tops es /\
    case supported_event_fields tops id of
      SOME fields => MAP expr_type es = MAP (SND o FST) fields
    | NONE => F
End

(* Literal ranges have exactly Num(b-a), including zero. The other range
   branch requires a positive checked bound. Array iteration is precisely a
   Name of a fixed array with the loop type and AST bound equal to its shape.
   Source typing (including nonliteral endpoint types) remains separate. *)
Definition supported_iterator_def:
  supported_iterator tops ty (Range a b) n =
    (case (a,b) of
       (Literal _ (IntL start), Literal _ (IntL finish)) =>
         supported_integer_type ty /\ start <= finish /\ n = Num (finish - start)
     | _ => supported_pure_expr tops a /\ supported_pure_expr tops b /\ 0 < n) /\
  supported_iterator tops ty (Array e) n =
    (case e of
       Name (ArrayT elem (Fixed m)) name => elem = ty /\ n = m
     | _ => F)
End

Definition supported_stmt_def:
  supported_stmt tops bindings Pass = T /\
  supported_stmt tops bindings Break = T /\
  supported_stmt tops bindings Continue = T /\
  supported_stmt tops bindings (Expr e) = supported_expr tops e /\
  supported_stmt tops bindings (Return NONE) = T /\
  supported_stmt tops bindings (Return (SOME e)) = supported_expr tops e /\
  supported_stmt tops bindings (AnnAssign name ty e) =
    (supported_value_type tops ty /\ supported_expr tops e) /\
  supported_stmt tops bindings (Assign target e) =
    supported_assignment tops bindings target e /\
  supported_stmt tops bindings (AugAssign ty target op e) =
    (supported_target tops bindings target /\ supported_expr tops e /\
     supported_binop op ty (expr_type e) F (supported_nonnegative_literal e)) /\
  supported_stmt tops bindings (Append target e) =
    (supported_append_target tops target /\ supported_pure_expr tops e) /\
  supported_stmt tops bindings (If c yes no) =
    (supported_pure_expr tops c /\ supported_stmts tops bindings yes /\
     supported_stmts tops bindings no) /\
  supported_stmt tops bindings (Assert c reason) =
    (supported_pure_expr tops c /\ supported_assert_reason tops reason) /\
  supported_stmt tops bindings (Raise reason) = supported_raise_reason tops reason /\
  supported_stmt tops bindings (Log id es) = supported_log tops id es /\
  supported_stmt tops bindings (For name ty iter n body) =
    (supported_type_namespace ty /\ supported_iterator tops ty iter n /\
     supported_stmts tops bindings body /\
     ~supported_stmts_expr_exists expr_internal_call_root body) /\
  supported_stmts tops bindings [] = T /\
  supported_stmts tops bindings (s::ss) =
    (supported_stmt tops bindings s /\ supported_stmts tops bindings ss)
Termination
  WF_REL_TAC `measure (\x. case x of
    INL (_,_,s) => stmt_size s | INR (_,_,ss) => stmt1_size ss)` >>
  simp[stmt_size_def, supported_stmt_list_size]
End

(* ===== Consumer contracts ===== *)

Theorem supported_stmts_list:
  supported_stmts tops bindings ss <=> EVERY (supported_stmt tops bindings) ss
Proof
  Induct_on `ss` >> simp[supported_stmt_def]
QED

Theorem supported_literal_range_contract:
  supported_iterator tops ty
    (Range (Literal a_ty (IntL a)) (Literal b_ty (IntL b))) n <=>
  supported_integer_type ty /\ a <= b /\ n = Num (b - a)
Proof
  simp[supported_iterator_def]
QED

Theorem supported_array_iteration_contract:
  supported_iterator tops ty (Array (Name (ArrayT elem (Fixed m)) xs)) n <=>
    elem = ty /\ n = m
Proof
  simp[supported_iterator_def]
QED

Theorem supported_loop_body_contract:
  supported_stmt tops bindings (For name ty iter n body) ==>
    supported_stmts tops bindings body /\
    ~supported_stmts_expr_exists expr_internal_call_root body
Proof
  simp[supported_stmt_def]
QED

Theorem supported_augassign_contract:
  supported_stmt tops bindings (AugAssign ty target op e) ==>
    supported_expr tops e /\
    (op = Exp ==> supported_integer_type ty /\ supported_nonnegative_literal e)
Proof
  Cases_on `op` >> simp[supported_stmt_def, supported_binop_def]
QED
