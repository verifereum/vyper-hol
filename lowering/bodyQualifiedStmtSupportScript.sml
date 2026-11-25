(* Resolve qualified event and error declarations at the statement boundary. *)
Theory bodyQualifiedStmtSupport
Ancestors
  supportedDecls vyperTypeContract vyperEventArgCompat vyperTypeSystem
  vyperAST list alist

Definition qualified_custom_error_ok_def[simp]:
  qualified_custom_error_ok mods (CustomError id pos kw) <=>
    FST id = NONE \/ custom_error_resolved mods (CustomError id pos kw)
End

Definition qualified_stmt_decls_ok_def[simp]:
  qualified_stmt_decls_ok mods (Raise (RaiseCustomError err)) =
    qualified_custom_error_ok mods err /\
  qualified_stmt_decls_ok mods (Assert e (AssertCustomError err)) =
    qualified_custom_error_ok mods err /\
  qualified_stmt_decls_ok mods (Log id args) =
    (FST id = NONE \/
     ?tops fields. ALOOKUP mods (FST id) = SOME tops /\
       supported_event_fields tops (NONE,SND id) = SOME fields /\
       LIST_REL (\e ((_,fty),_). event_arg_compatible fty (expr_type e)) args fields) /\
  qualified_stmt_decls_ok mods (If e yes no) =
    (qualified_stmts_decls_ok mods yes /\ qualified_stmts_decls_ok mods no) /\
  qualified_stmt_decls_ok mods (For id ty it n body) =
    qualified_stmts_decls_ok mods body /\
  qualified_stmt_decls_ok mods _ = T /\
  qualified_stmts_decls_ok mods [] = T /\
  qualified_stmts_decls_ok mods (s::ss) =
    (qualified_stmt_decls_ok mods s /\ qualified_stmts_decls_ok mods ss)
Termination
  WF_REL_TAC `measure (\x. case x of
    INL (_,s) => stmt_size s | INR (_,ss) => list_size stmt_size ss)` >>
  simp[]
End
