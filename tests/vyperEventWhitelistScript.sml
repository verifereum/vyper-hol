(* Issue #570: event validation belongs to the certified checker. The
   whitelist retains its existing expression restrictions only.
   Checker rejection counterparts live in vyperEventRegression and
   vyperImportedEventRegression. *)
Theory vyperEventWhitelist
Ancestors
  supportedProgram supportedStmts supportedNames supportedDecls supportedExprs
  vyperAST list integer

Theorem event_header_whitelist_unrestricted:
  !tops name fields. supported_declaration_header tops (EventDecl name fields)
Proof
  simp[supported_declaration_header_def]
QED

Theorem log_whitelist_expression_restrictions_only:
  !tops bindings id args.
    supported_stmt tops bindings (Log id args) <=> supported_pure_exprs tops args
Proof
  simp[supported_stmt_def, supported_log_def]
QED

Theorem event_bytes20_and_aggregate_headers:
  EVERY (supported_declaration_header [])
    [EventDecl "Word" [(("a",BaseT (BytesT (Fixed 20))),T)];
     EventDecl "Array" [(("a",ArrayT (BaseT (UintT 256)) (Fixed 2)),F)];
     EventDecl "Tuple" [(("a",TupleT [BaseT BoolT]),F)]]
Proof
  simp[supported_declaration_header_def]
QED

Theorem event_duplicate_names_checker_owned:
  supported_program [EventDecl "E" []; EventDecl "E" []]
Proof
  EVAL_TAC
QED

Theorem log_lookup_checker_owned:
  supported_stmt [] [] (Log (NONE,"missing") []) /\
  supported_stmt [] [] (Log (SOME 0,"E") [])
Proof
  EVAL_TAC
QED

Theorem log_arity_and_type_checker_owned:
  supported_stmt [EventDecl "E" [(("a",BaseT (UintT 256)),T)]] []
    (Log (NONE,"E") [Literal (BaseT BoolT) (BoolL T)]) /\
  supported_stmt [EventDecl "E" [(("a",BaseT (UintT 256)),T)]] []
    (Log (NONE,"E") [Literal (BaseT (UintT 256)) (IntL 0);
                     Literal (BaseT (UintT 256)) (IntL 1)])
Proof
  EVAL_TAC
QED
