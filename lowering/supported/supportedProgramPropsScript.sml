(* Permanent whole-program and per-body context checks, NOT TASK_022's 101
   fixture proofs. Plain EVAL on tops; source typing stays a separate premise. *)
Theory supportedProgramProps
Ancestors
  supportedProgram supportedStmts supportedStmtTraverse supportedNames
  supportedExprTraverse supportedExprProps supportedExprFormProps
  vyperTypeContract vyperAST list integer
Libs
  intLib

Definition program_test_deploy_def:
  program_test_deploy stmts = FunctionDecl Deploy Nonpayable F F
    "__init__" [] [] NoneT stmts
End

Definition program_test_internal_def:
  program_test_internal stmts = FunctionDecl Internal Pure F F
    "helper" [("arg",BaseT (UintT 256))] [] (BaseT (UintT 256)) stmts
End

Definition program_test_range_def:
  program_test_range stmts = For "i" (BaseT (UintT 256))
    (Range (Literal (BaseT (UintT 256)) (IntL 0))
           (Literal (BaseT (UintT 256)) (IntL 2))) 2 stmts
End

Theorem supported_program_positive:
  supported_program [] /\
  supported_program
    [program_test_internal [Return (SOME (Name (BaseT (UintT 256)) "arg"))];
     program_test_deploy
       [AnnAssign "x" (BaseT (UintT 256)) expr_test_internal;
        Assign (BaseTarget (NameTarget "x")) expr_test_internal;
        program_test_range [AugAssign (BaseT (UintT 256)) (NameTarget "x") Add expr_test_uint];
        If expr_test_uint [Expr expr_test_internal] [Pass]]]
Proof
  EVAL_TAC
QED

(* One real external-selector calculation, kept separate from other EVALs. *)
Theorem supported_external_program_positive:
  supported_program
    [FunctionDecl External Pure F F "answer" [] [] (BaseT (UintT 256))
      [Return (SOME (Literal (BaseT (UintT 256)) (IntL 42)))]]
Proof
  EVAL_TAC
QED

Theorem supported_storage_event_program_positive:
  supported_program
    [StructDecl "Record" [("first",BaseT (UintT 256)); ("second",BaseT (IntT 256))];
     VariableDecl Private Storage "record" (StructT (NONE,"Record")) (SOME 0);
     VariableDecl Private Storage "items" (ArrayT (BaseT (UintT 256)) (Dynamic 4)) (SOME 2);
     HashMapDecl Private F "map" (BaseT AddressT) (Type (BaseT (UintT 256))) (SOME 7);
     EventDecl "Updated" [(("value",BaseT (UintT 256)),F)];
     program_test_deploy
       [Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (NONE,"record")) "second")) expr_test_int;
        Append (TopLevelNameTarget (NONE,"items")) expr_test_uint;
        Assign (BaseTarget (SubscriptTarget (TopLevelNameTarget (NONE,"map")) expr_test_address)) expr_test_uint;
        Log (NONE,"Updated") [expr_test_uint]]]
Proof
  EVAL_TAC
QED

Theorem supported_internal_locals_and_loops:
  EVERY (\stmts. supported_program [program_test_internal stmts])
    [[AnnAssign "local" (BaseT (UintT 256)) expr_test_uint];
     [If expr_test_uint [] [AnnAssign "local" (BaseT (UintT 256)) expr_test_uint]];
     [program_test_range []];
     [If expr_test_uint [program_test_range []] []]]
Proof
  EVAL_TAC
QED

Theorem supported_internal_context_rejections:
  EVERY (\stmts. ~supported_program [program_test_internal stmts])
    [[Expr expr_test_internal];
     [Return (SOME expr_test_internal)];
     [Assign (BaseTarget (NameTarget "arg")) expr_test_internal];
     [If expr_test_uint [] [Expr expr_test_internal]]]
Proof
  EVAL_TAC
QED

(* External calls, send and pop ARE allowed in Internal and For bodies:
   the restriction is IntCall, not every effect. *)
Theorem supported_other_effects_in_internal_and_loop:
  supported_function_body expr_test_tops Internal []
    [Expr expr_test_pop;
     Expr (Call NoneT (Send F) [expr_test_address; expr_test_uint] NONE);
     Expr (Call (BaseT (UintT 256))
       (ExtCall T F ("remote",[BaseT (UintT 256)],BaseT (UintT 256)) [])
       [expr_test_address; expr_test_uint] NONE)] /\
  supported_stmt expr_test_tops []
    (program_test_range
      [Expr expr_test_pop; Expr (Call NoneT (Send F) [expr_test_address; expr_test_uint] NONE)])
Proof
  EVAL_TAC
QED

Theorem supported_loop_internal_call_rejections:
  EVERY (\stmts. ~supported_function_body expr_test_tops Deploy []
    [program_test_range stmts])
    [[Expr expr_test_internal];
     [Return (SOME expr_test_internal)];
     [If expr_test_uint [] [Expr expr_test_internal]];
     [AnnAssign "local" (BaseT (UintT 256)) expr_test_internal];
     [program_test_range [Expr expr_test_internal]];
     [Assign (BaseTarget (SubscriptTarget (TopLevelNameTarget (NONE,"fixed"))
        expr_test_internal)) expr_test_uint]] /\
  supported_function_body expr_test_tops Deploy []
    [Expr expr_test_internal; program_test_range [Pass]; Expr expr_test_internal]
Proof
  EVAL_TAC
QED

Theorem supported_local_type_environment:
  supported_function_body [] Deploy [("arg",BaseT (UintT 8))]
    [Assign (BaseTarget (NameTarget "arg")) expr_test_uint;
     If expr_test_uint [AnnAssign "local" (BaseT (UintT 256)) expr_test_uint] [];
     Assign (BaseTarget (NameTarget "local")) expr_test_uint;
     program_test_range [Assign (BaseTarget (NameTarget "i")) expr_test_uint]] /\
  supported_function_body [] Deploy [("arg",TupleT [BaseT (UintT 256)])]
    [Assign (BaseTarget (NameTarget "arg"))
       (Name (TupleT [BaseT (UintT 256)]) "arg")] /\
  supported_function_body [] Deploy []
    [AnnAssign "local" (ArrayT (BaseT (UintT 256)) (Fixed 2))
       (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2))
         (MakeArray (SOME (BaseT (UintT 256))) (Fixed 2)) [expr_test_uint;expr_test_uint]);
     Assign (BaseTarget (NameTarget "local"))
       (Name (ArrayT (BaseT (UintT 256)) (Fixed 2)) "local")] /\
  ~supported_function_body [] Deploy []
    [Assign (BaseTarget (NameTarget "missing")) expr_test_uint]
Proof
  EVAL_TAC
QED

Theorem supported_local_bytestring_assignment_and_reasons:
  supported_function_body [] Deploy
    [("s",BaseT (StringT 10)); ("b",BaseT (BytesT (Dynamic 40)))]
    [Assign (BaseTarget (NameTarget "s"))
       (Literal (BaseT (StringT 3)) (StringL "abc"));
     Assign (BaseTarget (NameTarget "b"))
       (Name (BaseT (BytesT (Dynamic 40))) "b");
     Assert (Literal (BaseT BoolT) (BoolL T))
       (AssertReason (Name (BaseT (StringT 10)) "s"));
     Raise (RaiseReason (Name (BaseT (StringT 10)) "s"))]
Proof
  EVAL_TAC
QED

Theorem supported_binding_duplicates_rejected:
  EVERY (\stmts. ~supported_program [program_test_deploy stmts])
    [[AnnAssign "x" (BaseT (UintT 256)) expr_test_uint;
      AnnAssign "x" (BaseT (UintT 256)) expr_test_uint];
     [If expr_test_uint [AnnAssign "x" (BaseT (UintT 256)) expr_test_uint]
       [AnnAssign "x" (BaseT (UintT 256)) expr_test_uint]];
     [program_test_range []; program_test_range []];
     [program_test_range [program_test_range []]];
     [AnnAssign "i" (BaseT (UintT 256)) expr_test_uint; program_test_range []]] /\
  ~supported_function_body [] Deploy [("arg",BaseT (UintT 256))]
    [If expr_test_uint [] [AnnAssign "arg" (BaseT (UintT 256)) expr_test_uint]] /\
  ~supported_function_body [] Deploy [("i",BaseT (UintT 256))]
    [program_test_range []] /\
  ~supported_function_body [] Deploy
    [("arg",BaseT (UintT 256)); ("arg",BaseT (UintT 256))] []
Proof
  EVAL_TAC
QED

Theorem supported_module_bindings_accepted:
  supported_program
    [VariableDecl Private Storage "x" (BaseT (UintT 256)) (SOME 0);
     program_test_deploy [AnnAssign "x" (BaseT (UintT 256)) expr_test_uint]] /\
  supported_program
    [HashMapDecl Private F "i" (BaseT AddressT) (Type (BaseT (UintT 256))) (SOME 0);
     program_test_deploy [program_test_range []]]
Proof
  EVAL_TAC
QED

Theorem supported_declaration_exclusions_assembled:
  EVERY (\top. ~supported_program [top])
    [FunctionDecl Deploy Nonpayable F T "__init__" [] [] NoneT [];
     VariableDecl Private Immutable "x" (BaseT (UintT 256)) (SOME 0);
     VariableDecl Private (Constant expr_test_uint) "x" (BaseT (UintT 256)) NONE;
     VariableDecl Public Storage "x" (BaseT (UintT 256)) (SOME 0);
     VariableDecl Private Storage "x" (BaseT (UintT 256)) NONE;
     VariableDecl Private Storage "x" (BaseT (UintT 8)) (SOME 0);
     FlagDecl "Flag" ["a"];
     StructDecl "S" [("f",StructT (SOME 0,"S"))];
     InterfaceDecl "I" [("f",[("a",StructT (SOME 0,"S"))],NoneT,View)]]
Proof
  EVAL_TAC
QED

(* Entry/header validity is checked by check_contract, not the whitelist. *)
Theorem supported_entry_header_context:
  supported_program [FunctionDecl Deploy Nonpayable T F "__init__" [] [] NoneT []] /\
  supported_program [FunctionDecl Deploy Nonpayable F F "__init__" [] [expr_test_uint] NoneT []] /\
  ~function_header_ok Deploy Nonpayable F F "__init__" [] [expr_test_uint] NoneT
Proof
  EVAL_TAC
QED

Theorem supported_fallback_context:
  supported_program [FunctionDecl External Payable F F "__default__" [] [] NoneT [Pass]] /\
  supported_program [FunctionDecl External Payable F F "__default__"
    [("arg",BaseT (UintT 256))] [] NoneT []] /\
  ~function_header_ok External Payable F F "__default__"
    [("arg",BaseT (UintT 256))] [] NoneT
Proof
  EVAL_TAC
QED

Theorem supported_name_checks_assembled:
  ~supported_program [program_test_internal []; program_test_internal []] /\
  ~contract_namespaces_ok F
    [(NONE,[program_test_internal []; program_test_internal []])] /\
  ~supported_program [EventDecl "E" []; EventDecl "E" []] /\
  supported_program
    [VariableDecl Private Storage "field_name" (BaseT (UintT 256)) (SOME 0);
     StructDecl "S" [("field_name",BaseT (UintT 256))]]
Proof
  EVAL_TAC
QED

(* Source-shape uniqueness is internal-only, not a global namespace check. *)
Theorem supported_function_name_sharing:
  supported_program
    [FunctionDecl External Pure F F "helper" [] [] NoneT [];
     program_test_internal []] /\
  supported_program [program_test_deploy []; program_test_deploy []]
Proof
  EVAL_TAC
QED

Theorem supported_default_expression_checks:
  supported_program
    [FunctionDecl External Pure F F "answer" [("x",BaseT (UintT 256))]
       [expr_test_uint] NoneT []] /\
  EVERY (\e. ~supported_program
    [FunctionDecl Deploy Nonpayable F F "__init__" [] [e] NoneT []])
    [Builtin (BaseT (UintT 256)) (Env MsgGas) [];
     Builtin (BaseT (UintT 256)) (Bop Add) [];
     Name (StructT (SOME 0,"S")) "x"]
Proof
  EVAL_TAC
QED

Theorem supported_annotation_module_exclusions:
  supported_type_namespace (TupleT [StructT (NONE,"S");
    ArrayT (FlagT (NONE,"F")) (Fixed 1)]) /\
  ~supported_type_namespace (TupleT [StructT (NONE,"S");
    ArrayT (FlagT (SOME 0,"F")) (Fixed 1)]) /\
  EVERY (\stmts. ~supported_program [program_test_deploy stmts])
    [[Expr (Name (StructT (SOME 0,"S")) "x")];
     [Expr (Subscript (BaseT (UintT 256))
       (TopLevelName (StructT (SOME 0,"S")) (NONE,"missing")) expr_test_uint)];
     [For "i" (StructT (SOME 0,"S"))
       (Range expr_test_uint (Name (BaseT (UintT 256)) "end")) 1 []]]
Proof
  EVAL_TAC
QED

(* D10: supported_program is deliberately NOT a source typing judgement.
   Shape/name lookup can accept this ill-typed initializer, without consulting
   a type checker. No source-correctness claim is made by this test. *)
Theorem supported_syntax_not_typing:
  supported_program [program_test_deploy
    [AnnAssign "x" (BaseT (UintT 256)) (Literal (BaseT BoolT) (BoolL T))]]
Proof
  EVAL_TAC
QED
