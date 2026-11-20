(* Statement whitelist with ordered assignment targets. Types/names are syntactic
   bindings, not source typing. Effects use supported_expr's existing root forms.
   TOP-LEVEL: supported_stmt, supported_stmts; supported_iterator,
   supported_assignment, supported_target, supported_append_target,
   supported_assert_reason, supported_raise_reason, supported_log. *)
Theory supportedStmts
Ancestors
  vyperTypeContract vyperEventArgCompat vyperExprEffects
  supportedStmtTraverse supportedExprs supportedExprForms supportedExprTraverse
  supportedTypes supportedDecls supportedTargets vyperTypeSystem exprLowering vyperAST list alist integer

Definition supported_local_word_def:
  supported_local_word bindings name <=>
    case ALOOKUP bindings name of SOME ty => supported_word_type ty | NONE => F
End

Definition supported_scalar_target_def:
  supported_scalar_target tops id <=>
    case supported_variable_decl tops id of
      (* SCRATCH SEQ-8389: any visibility, any storage type *)
      SOME (vis, Storage, ty, SOME slot) => supported_storage_type tops ty
    | SOME (vis, Transient, ty, SOME slot) => supported_storage_type tops ty
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
      (* SCRATCH SEQ-8389: every bound local and every resolving place path;
         binding types are not consulted (sibling-scope redeclaration) *)
      NameTarget name => IS_SOME (ALOOKUP bindings name)
    | TopLevelNameTarget id =>
        supported_scalar_target tops id \/
        IS_SOME (supported_immutable_type tops id)
    | _ => IS_SOME (supported_target_info tops bindings target)
End

(* Tuple lowering loads all RHS elements, then resolves and stores each flat
   target in order. Its INVALID branch for nested TupleTargets remains outside
   the supported compiler domain. *)
Definition supported_assignment_def:
  supported_assignment tops bindings target e <=>
    supported_expr tops e /\
    case target of
    (* SCRATCH SEQ-8389: tuple targets stay flat (checker) *)
    | BaseTarget bt => supported_target tops bindings bt
    | TupleTarget targets =>
        EVERY (\g. case g of
          BaseTarget bt => supported_target tops bindings bt
        | TupleTarget _ => F) targets
End

(* Nested augmented places retain the word-type guard from target analysis. *)
Definition supported_aug_target_def:
  supported_aug_target tops bindings target <=>
    case supported_target_info tops bindings target of
      SOME (ValPT ty) => supported_word_type ty
    | _ => F
End

Definition supported_append_target_def:
  (* SCRATCH SEQ-8389: every dynamic-array target *)
  supported_append_target tops (TopLevelNameTarget id) =
    supported_storage_dynamic_array tops id /\
  supported_append_target tops (NameTarget name) = T /\
  supported_append_target tops (SubscriptTarget target key) = T /\
  supported_append_target tops (AttributeTarget target fname) = T
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
  supported_assert_reason tops (AssertReason e) = supported_string_reason tops e /\
  (* SCRATCH SEQ-8389: resolved custom errors (checker fact) *)
  supported_assert_reason tops (AssertCustomError err) =
    custom_error_resolved [(NONE, tops)] err
End

Definition supported_raise_reason_def:
  supported_raise_reason tops RaiseBare = T /\
  supported_raise_reason tops RaiseUnreachable = T /\
  supported_raise_reason tops (RaiseReason e) = supported_string_reason tops e /\
  (* SCRATCH SEQ-8389: resolved custom errors (checker fact) *)
  supported_raise_reason tops (RaiseCustomError err) =
    custom_error_resolved [(NONE, tops)] err
End

(* Exact argument types select the original Log proofs. *)
Definition supported_log_exact_def:
  supported_log_exact tops id es <=>
    supported_pure_exprs tops es /\
    case supported_event_fields tops id of
      SOME fields => MAP expr_type es = MAP (SND o FST) fields
    | NONE => F
End

Definition supported_log_def:
  supported_log tops id es <=>
    supported_pure_exprs tops es /\
    case supported_event_fields tops id of
      SOME fields => LIST_REL (\e ((_,fty),_). event_arg_compatible fty (expr_type e)) es fields
    | NONE => F
End

(* Literal ranges have exactly Num(b-a), including zero. The other range
   branch requires a positive checked bound. An array iterable has the loop
   type as its element type and its bound at most the AST bound (exactly it
   for a local fixed array): a local array, an immutable array, a storage or
   transient array declared at the iterated type, or another supported array
   expression that is not a place rooted at a top-level name and has no
   ternary in it.
   - A storage or transient array is read like the compiled loop reads it:
     the length once at entry and element i from its slot in iteration i
     (#1268).
   - A ternary of same-layout arms lowers to a pointer into one arm, so a
     ternary over locals would alias a local the body may write (#1254).
   - An internal call's declared return type is the annotated type: a
     narrower one would lay out the result buffer with another stride (#767).
   Source typing (including nonliteral endpoint types) remains separate. *)
Definition supported_iterator_def:
  supported_iterator tops ty (Range a b) n =
    (case (a,b) of
       (Literal _ (IntL start), Literal _ (IntL range_end)) =>
         supported_integer_type ty /\ start <= range_end /\ n = Num (range_end - start)
     | _ => supported_pure_expr tops a /\ supported_pure_expr tops b /\ 0 < n) /\
  supported_iterator tops ty (Array e) n =
    (case e of
       Name (ArrayT elem (Fixed m)) name => elem = ty /\ n = m
     | Name (ArrayT elem (Dynamic c)) name => elem = ty /\ c <= n
     | Name _ _ => F
     | TopLevelName (ArrayT elem bd) nid =>
         elem = ty /\ bound_length bd <= n /\
         (IS_SOME (supported_immutable_type tops nid) \/
          supported_storage_value tops nid (ArrayT elem bd))
     | TopLevelName _ _ => F
     (* SCRATCH SEQ-8389: ternary and storage-place iterables *)
     | _ => supported_expr tops e /\
            (!t fid args drv. e = Call t (IntCall fid) args drv ==>
               ?m nr rr ps ds b.
                 supported_function_decl tops fid Internal =
                   SOME (m,nr,rr,ps,ds,t,b)) /\
            ?bd. expr_type e = ArrayT ty bd /\ bound_length bd <= n)
End

Definition supported_stmt_def:
  supported_stmt tops bindings Pass = T /\
  supported_stmt tops bindings Break = T /\
  supported_stmt tops bindings Continue = T /\
  supported_stmt tops bindings (Expr e) = supported_expr tops e /\
  supported_stmt tops bindings (Return NONE) = T /\
  supported_stmt tops bindings (Return (SOME e)) = supported_expr tops e /\
  supported_stmt tops bindings (AnnAssign name ty e) =
    (supported_place_type tops ty /\ supported_expr tops e) /\
  supported_stmt tops bindings (Assign target e) =
    supported_assignment tops bindings target e /\
  supported_stmt tops bindings (AugAssign ty target op e) =
    ((supported_target tops bindings target \/ supported_aug_target tops bindings target) /\
     supported_expr tops e /\
     supported_binop op ty (expr_type e) F (supported_nonnegative_literal e)) /\
  supported_stmt tops bindings (Append target e) =
    (* SCRATCH SEQ-8389: every element and target shape *)
    (supported_append_target tops target /\ supported_pure_expr tops e) /\
  supported_stmt tops bindings (If c yes no) =
    (supported_pure_expr tops c /\ supported_stmts tops bindings yes /\
     supported_stmts tops bindings no) /\
  supported_stmt tops bindings (Assert c reason) =
    (supported_pure_expr tops c /\ supported_assert_reason tops reason) /\
  supported_stmt tops bindings (Raise reason) = supported_raise_reason tops reason /\
  supported_stmt tops bindings (Log id es) = supported_log tops id es /\
  supported_stmt tops bindings (For name ty iter n loop_body) =
    (supported_type_namespace ty /\ supported_iterator tops ty iter n /\
     (* SCRATCH SEQ-8389: internal calls in loop bodies *)
     supported_stmts tops bindings loop_body) /\
  supported_stmts tops bindings [] = T /\
  supported_stmts tops bindings (s::ss) =
    (supported_stmt tops bindings s /\ supported_stmts tops bindings ss)
Termination
  WF_REL_TAC `measure (\x. case x of
    INL (_,_,s) => stmt_size s | INR (_,_,ss) => list_size stmt_size ss)` >>
  simp[stmt_size_def, list_size_def]
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
  supported_stmt tops bindings (For name ty iter n loop_body) ==>
    (* SCRATCH SEQ-8389: restated; loop bodies may call internal functions now *)
    supported_stmts tops bindings loop_body
Proof
  simp[supported_stmt_def]
QED

Theorem supported_augassign_contract:
  supported_stmt tops bindings (AugAssign ty target op e) ==>
    (* SCRATCH SEQ-8389: restated; the Exp operand guard is gone *)
    supported_expr tops e
Proof
  Cases_on `op` >> simp[supported_stmt_def, supported_binop_def]
QED
