(* NONE identifies the main module. Every resolved reference in an imported
   declaration must carry its source id, including references to the import
   itself. Local names and declaration names are not module references. *)
Theory vyperImportRefs
Ancestors
  vyperAST list option pair
Libs
  cv_transLib

Definition imported_type_refs_ok_def:
  imported_type_refs_ok (BaseT _) = T /\
  imported_type_refs_ok (TupleT tys) = imported_types_refs_ok tys /\
  imported_type_refs_ok (ArrayT ty _) = imported_type_refs_ok ty /\
  imported_type_refs_ok (StructT id) = (FST id <> NONE) /\
  imported_type_refs_ok (FlagT id) = (FST id <> NONE) /\
  imported_type_refs_ok NoneT = T /\
  imported_types_refs_ok [] = T /\
  imported_types_refs_ok (ty::tys) =
    (imported_type_refs_ok ty /\ imported_types_refs_ok tys)
End

Definition imported_builtin_refs_ok_def:
  imported_builtin_refs_ok (MakeArray (SOME ty) _) = imported_type_refs_ok ty /\
  imported_builtin_refs_ok _ = T
End

Definition imported_call_refs_ok_def:
  imported_call_refs_ok (IntCall id) = (FST id <> NONE) /\
  imported_call_refs_ok (ExtCall _ _ (_,args,ret) _) =
    (imported_types_refs_ok args /\ imported_type_refs_ok ret) /\
  imported_call_refs_ok _ = T
End

Definition imported_expr_refs_ok_def:
  imported_expr_refs_ok (Name ty _) = imported_type_refs_ok ty /\
  imported_expr_refs_ok (TopLevelName ty id) =
    (imported_type_refs_ok ty /\ FST id <> NONE) /\
  imported_expr_refs_ok (FlagMember ty id _) =
    (imported_type_refs_ok ty /\ FST id <> NONE) /\
  imported_expr_refs_ok (IfExp ty test yes no) =
    (imported_type_refs_ok ty /\ imported_expr_refs_ok test /\
     imported_expr_refs_ok yes /\ imported_expr_refs_ok no) /\
  imported_expr_refs_ok (Literal ty _) = imported_type_refs_ok ty /\
  imported_expr_refs_ok (StructLit ty id fields) =
    (imported_type_refs_ok ty /\ FST id <> NONE /\ imported_field_refs_ok fields) /\
  imported_expr_refs_ok (Subscript ty base index) =
    (imported_type_refs_ok ty /\ imported_expr_refs_ok base /\ imported_expr_refs_ok index) /\
  imported_expr_refs_ok (Attribute ty base _) =
    (imported_type_refs_ok ty /\ imported_expr_refs_ok base) /\
  imported_expr_refs_ok (Builtin ty kind args) =
    (imported_type_refs_ok ty /\ imported_builtin_refs_ok kind /\ imported_exprs_refs_ok args) /\
  imported_expr_refs_ok (TypeBuiltin ty _ target args) =
    (imported_type_refs_ok ty /\ imported_type_refs_ok target /\ imported_exprs_refs_ok args) /\
  imported_expr_refs_ok (Pop ty target) =
    (imported_type_refs_ok ty /\ imported_base_target_refs_ok target) /\
  imported_expr_refs_ok (Call ty target args default) =
    (imported_type_refs_ok ty /\ imported_call_refs_ok target /\
     imported_exprs_refs_ok args /\ imported_optional_expr_refs_ok default) /\
  imported_base_target_refs_ok (NameTarget _) = T /\
  imported_base_target_refs_ok (TopLevelNameTarget id) = (FST id <> NONE) /\
  imported_base_target_refs_ok (SubscriptTarget target index) =
    (imported_base_target_refs_ok target /\ imported_expr_refs_ok index) /\
  imported_base_target_refs_ok (AttributeTarget target _) = imported_base_target_refs_ok target /\
  imported_exprs_refs_ok [] = T /\
  imported_exprs_refs_ok (e::es) =
    (imported_expr_refs_ok e /\ imported_exprs_refs_ok es) /\
  imported_optional_expr_refs_ok NONE = T /\
  imported_optional_expr_refs_ok (SOME e) = imported_expr_refs_ok e /\
  imported_field_refs_ok [] = T /\
  imported_field_refs_ok ((_,e)::fields) =
    (imported_expr_refs_ok e /\ imported_field_refs_ok fields)
Termination
  qexists_tac `measure (\(x : expr + base_assignment_target + expr list +
      expr option + (identifier # expr) list).
    case x of
      INL e => expr_size e
    | INR (INL t) => base_assignment_target_size t
    | INR (INR (INL es)) => list_size expr_size es
    | INR (INR (INR (INL opt))) => option_size expr_size opt
    | INR (INR (INR (INR fs))) =>
        list_size (pair_size (list_size char_size) expr_size) fs)` >>
  conj_tac >- MATCH_ACCEPT_TAC prim_recTheory.WF_measure >>
  PURE_REWRITE_TAC [prim_recTheory.measure_thm, sumTheory.sum_case_def,
                    pairTheory.pair_case_def] >>
  simp[expr_size_def, list_size_def, basicSizeTheory.pair_size_def,
       basicSizeTheory.option_size_def, bnfPrelimsTheory.option_size_map,
       bnfPrelimsTheory.pair_size_map, list_size_map, SF ETA_ss]
End

Definition imported_target_refs_ok_def:
  imported_target_refs_ok (BaseTarget target) = imported_base_target_refs_ok target /\
  imported_target_refs_ok (TupleTarget targets) = imported_targets_refs_ok targets /\
  imported_targets_refs_ok [] = T /\
  imported_targets_refs_ok (t::ts) =
    (imported_target_refs_ok t /\ imported_targets_refs_ok ts)
End

Definition imported_iterator_refs_ok_def:
  imported_iterator_refs_ok (Array e) = imported_expr_refs_ok e /\
  imported_iterator_refs_ok (Range first last) =
    (imported_expr_refs_ok first /\ imported_expr_refs_ok last)
End

Definition imported_error_refs_ok_def:
  imported_error_refs_ok (CustomError id positional kwargs) =
    (FST id <> NONE /\ imported_exprs_refs_ok positional /\ imported_field_refs_ok kwargs)
End

Definition imported_assert_refs_ok_def:
  imported_assert_refs_ok (AssertReason e) = imported_expr_refs_ok e /\
  imported_assert_refs_ok (AssertCustomError err) = imported_error_refs_ok err /\
  imported_assert_refs_ok _ = T
End

Definition imported_raise_refs_ok_def:
  imported_raise_refs_ok (RaiseReason e) = imported_expr_refs_ok e /\
  imported_raise_refs_ok (RaiseCustomError err) = imported_error_refs_ok err /\
  imported_raise_refs_ok _ = T
End

Definition imported_stmt_refs_ok_def:
  imported_stmt_refs_ok Pass = T /\
  imported_stmt_refs_ok Continue = T /\
  imported_stmt_refs_ok Break = T /\
  imported_stmt_refs_ok (Expr e) = imported_expr_refs_ok e /\
  imported_stmt_refs_ok (For _ ty iter _ body) =
    (imported_type_refs_ok ty /\ imported_iterator_refs_ok iter /\ imported_stmts_refs_ok body) /\
  imported_stmt_refs_ok (If guard yes no) =
    (imported_expr_refs_ok guard /\ imported_stmts_refs_ok yes /\ imported_stmts_refs_ok no) /\
  imported_stmt_refs_ok (Assert e reason) =
    (imported_expr_refs_ok e /\ imported_assert_refs_ok reason) /\
  imported_stmt_refs_ok (Log id args) = (FST id <> NONE /\ imported_exprs_refs_ok args) /\
  imported_stmt_refs_ok (Raise reason) = imported_raise_refs_ok reason /\
  imported_stmt_refs_ok (Return value) = imported_optional_expr_refs_ok value /\
  imported_stmt_refs_ok (Assign target e) =
    (imported_target_refs_ok target /\ imported_expr_refs_ok e) /\
  imported_stmt_refs_ok (AugAssign ty target _ e) =
    (imported_type_refs_ok ty /\ imported_base_target_refs_ok target /\ imported_expr_refs_ok e) /\
  imported_stmt_refs_ok (Append target e) =
    (imported_base_target_refs_ok target /\ imported_expr_refs_ok e) /\
  imported_stmt_refs_ok (AnnAssign _ ty e) =
    (imported_type_refs_ok ty /\ imported_expr_refs_ok e) /\
  imported_stmts_refs_ok [] = T /\
  imported_stmts_refs_ok (s::ss) =
    (imported_stmt_refs_ok s /\ imported_stmts_refs_ok ss)
End

Definition imported_value_type_refs_ok_def:
  imported_value_type_refs_ok (Type ty) = imported_type_refs_ok ty /\
  imported_value_type_refs_ok (HashMapT key value) =
    (imported_type_refs_ok key /\ imported_value_type_refs_ok value)
End

Definition imported_toplevel_refs_ok_def:
  imported_toplevel_refs_ok (FunctionDecl _ _ _ _ _ args defaults ret body) =
    (EVERY (imported_type_refs_ok o SND) args /\ imported_exprs_refs_ok defaults /\
     imported_type_refs_ok ret /\ imported_stmts_refs_ok body) /\
  imported_toplevel_refs_ok (VariableDecl _ mut _ ty _) =
    (imported_type_refs_ok ty /\
     case mut of Constant e => imported_expr_refs_ok e | _ => T) /\
  imported_toplevel_refs_ok (HashMapDecl _ _ _ key value _) =
    (imported_type_refs_ok key /\ imported_value_type_refs_ok value) /\
  imported_toplevel_refs_ok (StructDecl _ fields) =
    EVERY (imported_type_refs_ok o SND) fields /\
  imported_toplevel_refs_ok (EventDecl _ fields) =
    EVERY (imported_type_refs_ok o SND o FST) fields /\
  imported_toplevel_refs_ok (ErrorDecl _ fields) =
    EVERY (imported_type_refs_ok o SND) fields /\
  imported_toplevel_refs_ok (FlagDecl _ _) = T /\
  imported_toplevel_refs_ok (InterfaceDecl _ signatures) =
    EVERY (\(_,args,ret,_). EVERY (imported_type_refs_ok o SND) args /\
                           imported_type_refs_ok ret) signatures
End

val () = cv_auto_trans imported_type_refs_ok_def;
val () = cv_auto_trans imported_builtin_refs_ok_def;
val () = cv_auto_trans imported_call_refs_ok_def;
val () = cv_auto_trans imported_expr_refs_ok_def;
val () = cv_auto_trans imported_target_refs_ok_def;
val () = cv_auto_trans imported_iterator_refs_ok_def;
val () = cv_auto_trans imported_error_refs_ok_def;
val () = cv_auto_trans imported_assert_refs_ok_def;
val () = cv_auto_trans imported_raise_refs_ok_def;
val () = cv_auto_trans imported_stmt_refs_ok_def;
val () = cv_auto_trans imported_value_type_refs_ok_def;
val () = cv_auto_trans imported_toplevel_refs_ok_def;
