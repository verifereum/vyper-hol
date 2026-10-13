(* Permanent occurrence/collection checks over supported AND unsupported AST.
   TASK_020's expression traversal handles recursion beneath each leaf. *)
Theory supportedStmtTraverseProps
Ancestors
  supportedStmtTraverse supportedProgram supportedExprProps supportedExprFormProps
  supportedExprTraverse vyperAST list integer
Libs
  intLib

Definition traversal_test_statements_def:
  traversal_test_statements e =
    [Expr e; Return (SOME e); AnnAssign "x" NoneT e;
     Assign (BaseTarget (NameTarget "x")) e;
     Assign (TupleTarget [TupleTarget [BaseTarget
       (SubscriptTarget (AttributeTarget (NameTarget "x") "f") e)]]) expr_test_uint;
     AugAssign NoneT (NameTarget "x") Add e;
     AugAssign NoneT (SubscriptTarget (NameTarget "x") e) Add expr_test_uint;
     Append (NameTarget "x") e;
     Append (SubscriptTarget (NameTarget "x") e) expr_test_uint;
     Log (SOME 1,"E") [expr_test_uint;e];
     Assert e AssertBare; Assert expr_test_uint (AssertReason e);
     Raise (RaiseReason e);
     If e [] []; If expr_test_uint [Expr e] []; If expr_test_uint [] [Expr e];
     For "i" NoneT (Range e expr_test_uint) 0 [];
     For "i" NoneT (Range expr_test_uint e) 0 [];
     For "i" NoneT (Array e) 0 [];
     For "i" NoneT (Array expr_test_uint) 0 [If expr_test_uint [] [Expr e]];
     Expr (Call NoneT Send [expr_test_uint] (SOME e));
     Expr (Pop NoneT (SubscriptTarget (NameTarget "x") e))]
End

Theorem supported_internal_occurrence_all_statement_positions:
  EVERY (supported_stmt_expr_exists expr_internal_call_root)
    (traversal_test_statements expr_test_internal) /\
  ~supported_stmts_expr_exists expr_internal_call_root
    [Pass; Break; Continue; Return NONE; Assert expr_test_uint AssertUnreachable;
     Raise RaiseBare; Raise RaiseUnreachable; Log (NONE,"E") [];
     Assign (TupleTarget []) expr_test_uint;
     If expr_test_uint [Expr expr_test_uint] []]
Proof
  EVAL_TAC
QED

Theorem supported_dynamic_decode_all_statement_positions:
  EVERY (supported_stmt_expr_exists (expr_dynamic_decode_root []))
    (traversal_test_statements expr_test_decode) /\
  ~supported_stmts_expr_exists (expr_dynamic_decode_root [])
    [Expr (TypeBuiltin (TupleT [BaseT (UintT 256);BaseT BoolT]) (AbiDecode F)
       (TupleT [BaseT (UintT 256);BaseT BoolT]) [expr_test_uint])]
Proof
  EVAL_TAC
QED

Theorem supported_exact_decode_occurrence_api:
  occurs_abi_decode_target (TupleT [BaseT (UintT 256);BaseT (StringT 32)])
    [FunctionDecl Internal Pure T T "unsupported" [] [] NoneT
      (traversal_test_statements expr_test_decode)] /\
  ~occurs_abi_decode_target (BaseT (StringT 32))
    [FunctionDecl Internal Pure F F "helper" [] [] NoneT [Expr expr_test_decode]] /\
  occurs_abi_decode_target (TupleT [BaseT (UintT 256);BaseT BoolT])
    [FunctionDecl Deploy Nonpayable F F "__init__" [] [] NoneT
      [Expr (TypeBuiltin NoneT (AbiDecode T)
         (TupleT [BaseT (UintT 256);BaseT BoolT]) [expr_test_uint])]] /\
  ~occurs_abi_decode_target (TupleT [BaseT (UintT 256);BaseT (StringT 32)])
    [FunctionDecl External Pure F F "f" [] [expr_test_decode] NoneT [];
     VariableDecl Private (Constant expr_test_decode) "constant" NoneT NONE;
     StructDecl "S" []; EventDecl "E" []; InterfaceDecl "I" []; FlagDecl "F" []]
Proof
  EVAL_TAC
QED

Theorem supported_bindings_all_branches_and_nesting:
  supported_stmts_bindings T
    [AnnAssign "a" NoneT expr_test_uint;
     If expr_test_uint [AnnAssign "b" (BaseT BoolT) expr_test_uint]
       [For "i" (BaseT (UintT 256)) (Array expr_test_uint) 0
          [AnnAssign "a" (BaseT (UintT 8)) expr_test_uint;
           For "j" (BaseT (IntT 256)) (Array expr_test_uint) 0 []]];
     For "i" NoneT (Array expr_test_uint) 0 []] =
    [("a",NoneT); ("b",BaseT BoolT); ("a",BaseT (UintT 8))] /\
  supported_stmts_bindings F
    [AnnAssign "a" NoneT expr_test_uint;
     If expr_test_uint [AnnAssign "b" (BaseT BoolT) expr_test_uint]
       [For "i" (BaseT (UintT 256)) (Array expr_test_uint) 0
          [AnnAssign "a" (BaseT (UintT 8)) expr_test_uint;
           For "j" (BaseT (IntT 256)) (Array expr_test_uint) 0 []]];
     For "i" NoneT (Array expr_test_uint) 0 []] =
    [("i",BaseT (UintT 256)); ("j",BaseT (IntT 256)); ("i",NoneT)] /\
  supported_stmts_bindings T
    [Pass; Break; Continue; Expr expr_test_uint; Return NONE;
     Assign (BaseTarget (NameTarget "x")) expr_test_uint;
     AugAssign NoneT (NameTarget "x") Add expr_test_uint;
     Append (NameTarget "x") expr_test_uint; Log (NONE,"E") [];
     Assert expr_test_uint AssertBare; Raise RaiseBare] = [] /\
  supported_stmts_bindings F
    [Pass; Break; Continue; Expr expr_test_uint; Return NONE;
     Assign (BaseTarget (NameTarget "x")) expr_test_uint;
     AugAssign NoneT (NameTarget "x") Add expr_test_uint;
     Append (NameTarget "x") expr_test_uint; Log (NONE,"E") [];
     Assert expr_test_uint AssertBare; Raise RaiseBare] = []
Proof
  EVAL_TAC
QED
