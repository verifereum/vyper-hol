(* Permanent PLAN 5.6 statement-row acceptance/rejection checks.
   All concrete checks use plain EVAL_TAC (10s build contract). *)
Theory supportedStmtProps
Ancestors
  supportedStmts supportedStmtTraverse supportedProgram supportedExprProps
  supportedExprFormProps supportedExprTraverse vyperAST list integer
Libs
  intLib

Definition stmt_test_bindings_def:
  stmt_test_bindings =
    [("word",BaseT (UintT 256)); ("narrow",BaseT (UintT 8));
     ("aggregate",TupleT [BaseT (UintT 256)]);
     ("array",ArrayT (BaseT (UintT 256)) (Fixed 2))]
End

Theorem supported_simple_statement_rows:
  supported_stmts expr_test_tops stmt_test_bindings
    [Pass; Break; Continue; Expr expr_test_uint; Expr expr_test_internal;
     Expr expr_test_pop; Return NONE; Return (SOME expr_test_uint);
     Return (SOME expr_test_internal);
     AnnAssign "new" (BaseT (UintT 256)) expr_test_internal;
     AnnAssign "tuple" (TupleT [BaseT (UintT 256)]) expr_test_uint;
     Assign (BaseTarget (NameTarget "word")) expr_test_internal;
     Assign (BaseTarget (NameTarget "narrow")) expr_test_uint]
Proof
  EVAL_TAC
QED

Theorem supported_all_effect_root_positions:
  EVERY (\e. supported_stmts expr_test_tops stmt_test_bindings
    [Expr e; Return (SOME e); AnnAssign "new" (BaseT (UintT 256)) e;
     Assign (BaseTarget (NameTarget "word")) e;
     Assign (TupleTarget [BaseTarget (NameTarget "word")]) e;
     Assign (BaseTarget (TopLevelNameTarget (NONE,"scalar"))) e;
     Assign (BaseTarget (SubscriptTarget (TopLevelNameTarget (NONE,"map"))
       expr_test_address)) e;
     Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (NONE,"record"))
       "second")) e;
     AugAssign (BaseT (UintT 256)) (NameTarget "word") Add e;
     AugAssign (BaseT (UintT 256)) (TopLevelNameTarget (NONE,"scalar")) Add e;
     AugAssign (BaseT (UintT 256))
       (SubscriptTarget (TopLevelNameTarget (NONE,"fixed")) expr_test_uint) Add e;
     AugAssign (BaseT (IntT 256))
       (AttributeTarget (TopLevelNameTarget (NONE,"record")) "second") Add e])
    [expr_test_internal; expr_test_pop;
     Call NoneT (Send F) [expr_test_address;expr_test_uint] NONE;
     Call (BaseT (UintT 256))
       (ExtCall T F ("remote",[BaseT (UintT 256)],BaseT (UintT 256)) [])
       [expr_test_address;expr_test_uint] NONE]
Proof
  EVAL_TAC
QED

Theorem supported_storage_statement_rows:
  supported_stmts expr_test_tops stmt_test_bindings
    [Assign (BaseTarget (TopLevelNameTarget (NONE,"scalar"))) expr_test_uint;
     Assign (BaseTarget (TopLevelNameTarget (NONE,"transient"))) expr_test_int;
     Assign (BaseTarget (SubscriptTarget (TopLevelNameTarget (NONE,"map"))
       expr_test_address)) expr_test_uint;
     Assign (BaseTarget (SubscriptTarget (TopLevelNameTarget (NONE,"fixed"))
       expr_test_uint)) expr_test_uint;
     Assign (BaseTarget (SubscriptTarget (TopLevelNameTarget (NONE,"dynamic"))
       expr_test_uint)) expr_test_int;
     Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (NONE,"record"))
       "first")) expr_test_uint;
     Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (NONE,"record"))
       "second")) expr_test_int;
     Append (TopLevelNameTarget (NONE,"dynamic")) expr_test_int]
Proof
  EVAL_TAC
QED

(* Assignment admission is syntactic: RHS shape/type compatibility is a
   separate typing obligation, including the singleton scalar-RHS check. *)
Theorem supported_tuple_assignment_rows:
  supported_stmts expr_test_tops stmt_test_bindings
    [Assign (TupleTarget []) expr_test_uint;
     Assign (TupleTarget [BaseTarget (NameTarget "word")]) expr_test_uint;
     Assign (TupleTarget [BaseTarget (NameTarget "word");
       BaseTarget (NameTarget "narrow")])
       (Builtin (TupleT [BaseT (UintT 256); BaseT (UintT 8)])
         (MakeArray NONE (Fixed 2)) [expr_test_uint; expr_test_uint]);
     Assign (TupleTarget [BaseTarget (NameTarget "word");
       BaseTarget (TopLevelNameTarget (NONE,"scalar"));
       BaseTarget (SubscriptTarget (TopLevelNameTarget (NONE,"fixed")) expr_test_internal);
       BaseTarget (AttributeTarget (TopLevelNameTarget (NONE,"record")) "second");
       BaseTarget (NameTarget "word")]) expr_test_internal;
     Assign (BaseTarget (NameTarget "aggregate")) expr_test_uint;
     Assign (BaseTarget (NameTarget "array")) expr_test_uint]
Proof
  EVAL_TAC
QED

Theorem supported_target_exclusions:
  EVERY (\s. ~supported_stmt expr_test_tops stmt_test_bindings s)
    [Assign (BaseTarget (NameTarget "missing")) expr_test_uint;
     Assign (TupleTarget [TupleTarget []]) expr_test_uint;
     Assign (TupleTarget [BaseTarget (NameTarget "word");
       TupleTarget [BaseTarget (NameTarget "narrow")]]) expr_test_uint;
     Assign (TupleTarget [BaseTarget (NameTarget "missing")]) expr_test_uint;
     Assign (TupleTarget [BaseTarget (NameTarget "word");
       BaseTarget (TopLevelNameTarget (NONE,"fixed"))]) expr_test_internal;
     Assign (BaseTarget (TopLevelNameTarget (NONE,"fixed"))) expr_test_uint;
     Assign (BaseTarget (TopLevelNameTarget (NONE,"record"))) expr_test_uint;
     Assign (BaseTarget (TopLevelNameTarget (NONE,"map"))) expr_test_uint;
     Assign (BaseTarget (TopLevelNameTarget (SOME 0,"scalar"))) expr_test_uint;
     Assign (BaseTarget (SubscriptTarget (NameTarget "array") expr_test_uint)) expr_test_uint;
     Assign (BaseTarget (SubscriptTarget
       (SubscriptTarget (TopLevelNameTarget (NONE,"map")) expr_test_uint)
       expr_test_uint)) expr_test_uint;
     Assign (BaseTarget (AttributeTarget (NameTarget "record") "first")) expr_test_uint;
     Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (NONE,"record")) "absent")) expr_test_uint;
     Append (NameTarget "array") expr_test_uint;
     Append (TopLevelNameTarget (NONE,"fixed")) expr_test_uint;
     Append (TopLevelNameTarget (SOME 0,"dynamic")) expr_test_uint;
     Append (SubscriptTarget (TopLevelNameTarget (NONE,"dynamic")) expr_test_uint) expr_test_uint;
     Append (AttributeTarget (TopLevelNameTarget (NONE,"record")) "first") expr_test_uint]
Proof
  EVAL_TAC
QED

Theorem supported_storage_effect_statement_rows:
  supported_stmts expr_test_tops stmt_test_bindings
    [Assign (BaseTarget (TopLevelNameTarget (NONE,"scalar"))) expr_test_internal;
     Assign (BaseTarget (SubscriptTarget (TopLevelNameTarget (NONE,"map"))
       expr_test_address)) expr_test_internal;
     Assign (BaseTarget (SubscriptTarget (TopLevelNameTarget (NONE,"fixed"))
       expr_test_internal)) expr_test_uint;
     Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (NONE,"record"))
       "second")) expr_test_internal;
     Assign (BaseTarget (SubscriptTarget (TopLevelNameTarget (NONE,"dynamic"))
       expr_test_pop)) expr_test_internal;
     AugAssign (BaseT (UintT 256))
       (SubscriptTarget (TopLevelNameTarget (NONE,"fixed")) expr_test_internal)
       Add expr_test_pop]
Proof
  EVAL_TAC
QED

(* Effect roots are allowed for assignment RHSs and subscript targets, but
   nested expression effects and effectful append values remain excluded. *)
Theorem supported_storage_effects_rejected:
  EVERY (\s. ~supported_stmt expr_test_tops stmt_test_bindings s)
    [Assign (BaseTarget (TopLevelNameTarget (NONE,"scalar")))
       (Builtin (BaseT (UintT 256)) (Bop Add) [expr_test_internal; expr_test_uint]);
     Assign (TupleTarget [BaseTarget (NameTarget "word")])
       (Builtin (TupleT [BaseT (UintT 256)]) (MakeArray NONE (Fixed 1))
         [expr_test_internal]);
     Assign (BaseTarget (SubscriptTarget (TopLevelNameTarget (NONE,"fixed"))
       (Builtin (BaseT (UintT 256)) (Bop Add) [expr_test_pop; expr_test_uint])))
       expr_test_uint;
     AugAssign (BaseT (UintT 256)) (NameTarget "word") Add
       (Builtin (BaseT (UintT 256)) (Bop Add) [expr_test_internal; expr_test_uint]);
     AugAssign (BaseT (UintT 256))
       (SubscriptTarget (TopLevelNameTarget (NONE,"fixed"))
         (Builtin (BaseT (UintT 256)) (Bop Add) [expr_test_internal; expr_test_uint]))
       Add expr_test_uint;
     Append (TopLevelNameTarget (NONE,"dynamic")) expr_test_pop;
     AnnAssign "bad" NoneT expr_test_uint;
     AnnAssign "bad" (ArrayT (BaseT (UintT 256)) (Fixed 0)) expr_test_uint]
Proof
  EVAL_TAC
QED

Theorem supported_augmented_statement_row:
  supported_stmts expr_test_tops stmt_test_bindings
    [AugAssign (BaseT (UintT 8)) (NameTarget "narrow") Add expr_test_uint;
     AugAssign (BaseT (UintT 256)) (TopLevelNameTarget (NONE,"scalar")) Add expr_test_uint;
     AugAssign (BaseT (IntT 256)) (TopLevelNameTarget (NONE,"transient")) Sub expr_test_int;
     AugAssign (BaseT (UintT 256)) (NameTarget "word") Exp
       (Literal (BaseT (UintT 256)) (IntL 0));
     AugAssign (BaseT (UintT 256)) (NameTarget "word") ShL expr_test_uint;
     AugAssign (BaseT (UintT 256)) (NameTarget "word") Add expr_test_internal;
     AugAssign (BaseT (UintT 256)) (NameTarget "aggregate") Add expr_test_uint;
     AugAssign (BaseT (UintT 256))
       (SubscriptTarget (TopLevelNameTarget (NONE,"fixed")) expr_test_uint) Add expr_test_uint;
     AugAssign (BaseT (UintT 256))
       (AttributeTarget (TopLevelNameTarget (NONE,"record")) "first") Add expr_test_uint] /\
  EVERY (\s. ~supported_stmt expr_test_tops stmt_test_bindings s)
    [AugAssign (BaseT (UintT 256)) (NameTarget "word") Exp
       (Literal (BaseT (IntT 256)) (IntL (~1)));
     AugAssign (BaseT (UintT 256)) (NameTarget "word") Exp
       (Name (BaseT (UintT 256)) "power");
     AugAssign (BaseT (UintT 8)) (NameTarget "narrow") ShL expr_test_uint;
     AugAssign (BaseT (UintT 256)) (NameTarget "word") ShR expr_test_int;
     AugAssign (BaseT (UintT 256)) (NameTarget "word") ExpMod expr_test_uint;
     AugAssign (BaseT (UintT 256)) (NameTarget "word") In expr_test_uint;
     AugAssign (BaseT (UintT 256)) (NameTarget "missing") Add expr_test_uint;
     AugAssign (BaseT (UintT 256)) (TopLevelNameTarget (NONE,"fixed")) Add expr_test_uint;
     AugAssign (BaseT (UintT 256))
       (SubscriptTarget (NameTarget "array") expr_test_uint) Add expr_test_uint;
     AugAssign (BaseT (UintT 256))
       (SubscriptTarget (TopLevelNameTarget (SOME 0,"fixed")) expr_test_uint) Add expr_test_uint;
     AugAssign (BaseT (UintT 256))
       (AttributeTarget (TopLevelNameTarget (NONE,"record")) "absent") Add expr_test_uint]
Proof
  EVAL_TAC
QED

Theorem supported_control_reason_rows:
  supported_stmts expr_test_tops stmt_test_bindings
    [If expr_test_uint [Expr expr_test_internal] [Return (SOME expr_test_pop)];
     Assert expr_test_uint AssertBare; Assert expr_test_uint AssertUnreachable;
     Assert expr_test_uint (AssertReason (Literal (BaseT (StringT 16)) (StringL "why")));
     Raise RaiseBare; Raise RaiseUnreachable;
     Raise (RaiseReason (Literal (BaseT (StringT 16)) (StringL "UNREACHABLE")))] /\
  EVERY (\s. ~supported_stmt expr_test_tops stmt_test_bindings s)
    [If expr_test_internal [] []; Assert expr_test_pop AssertBare;
     Assert expr_test_uint (AssertReason expr_test_internal);
     Raise (RaiseReason expr_test_uint);
     Raise (RaiseReason (Builtin (BaseT (StringT 16)) (Concat 16) []))]
Proof
  EVAL_TAC
QED

Definition stmt_test_events_def:
  stmt_test_events =
    [EventDecl "Event" [(("value",BaseT (UintT 256)),T);
                         (("text",BaseT (StringT 16)),F)]]
End

Theorem supported_log_statement_row:
  supported_stmt stmt_test_events []
    (Log (NONE,"Event") [expr_test_uint; Name (BaseT (StringT 16)) "text"]) /\
  EVERY (\s. ~supported_stmt stmt_test_events [] s)
    [Log (NONE,"missing") []; Log (SOME 0,"Event") [];
     Log (NONE,"Event") [expr_test_uint];
     Log (NONE,"Event") [expr_test_uint; expr_test_uint];
     Log (NONE,"Event") [expr_test_uint; Name (BaseT (StringT 16)) "text"; expr_test_uint]] /\
  ~supported_stmt (stmt_test_events ++ expr_test_tops) []
    (Log (NONE,"Event") [expr_test_internal; Name (BaseT (StringT 16)) "text"])
Proof
  EVAL_TAC
QED

Theorem supported_literal_range_statement_row:
  supported_stmts [] []
    [For "i" (BaseT (UintT 256))
       (Range (Literal (BaseT (UintT 256)) (IntL 2))
              (Literal (BaseT (UintT 256)) (IntL 5))) 3 [Pass];
     For "i" (BaseT (IntT 256))
       (Range (Literal (BaseT (IntT 256)) (IntL (~2)))
              (Literal (BaseT (IntT 256)) (IntL 1))) 3 [];
     For "i" (BaseT (UintT 256))
       (Range (Literal (BaseT (UintT 256)) (IntL 2))
              (Literal (BaseT (UintT 256)) (IntL 2))) 0 []] /\
  ~supported_iterator [] (BaseT (UintT 256))
    (Range (Literal (BaseT (UintT 256)) (IntL 2))
           (Literal (BaseT (UintT 256)) (IntL 5))) 4 /\
  ~supported_iterator [] (BaseT (IntT 256))
    (Range (Literal (BaseT (IntT 256)) (IntL 5))
           (Literal (BaseT (IntT 256)) (IntL 2))) 0 /\
  ~supported_iterator [] (BaseT DecimalT)
    (Range (Literal (BaseT (UintT 256)) (IntL 2))
           (Literal (BaseT (UintT 256)) (IntL 5))) 3
Proof
  EVAL_TAC
QED

Theorem supported_checked_range_statement_row:
  supported_iterator expr_test_tops (BaseT (UintT 256))
    (Range (Name (BaseT (UintT 256)) "a") expr_test_uint) 1 /\
  supported_iterator expr_test_tops (BaseT (UintT 256))
    (Range expr_test_uint (Name (BaseT (UintT 256)) "b")) 2 /\
  ~supported_iterator expr_test_tops (BaseT (UintT 256))
    (Range expr_test_uint (Name (BaseT (UintT 256)) "b")) 0 /\
  ~supported_iterator expr_test_tops (BaseT (UintT 256))
    (Range expr_test_internal expr_test_uint) 1 /\
  ~supported_iterator expr_test_tops (BaseT (UintT 256))
    (Range expr_test_uint expr_test_pop) 1
Proof
  EVAL_TAC
QED

Theorem supported_fixed_array_iteration_row:
  supported_stmt [] stmt_test_bindings
    (For "i" (BaseT (UintT 256))
      (Array (Name (ArrayT (BaseT (UintT 256)) (Fixed 2)) "array")) 2 [Pass]) /\
  EVERY (\iter. ~supported_iterator expr_test_tops (BaseT (UintT 256)) iter 2)
    [Array (Name (ArrayT (BaseT (UintT 256)) (Dynamic 2)) "array");
     Array (Name (ArrayT (BaseT (IntT 256)) (Fixed 2)) "array");
     Array (TopLevelName (ArrayT (BaseT (UintT 256)) (Fixed 2)) (NONE,"fixed"));
     Array (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2))
       (MakeArray (SOME (BaseT (UintT 256))) (Fixed 2)) [expr_test_uint; expr_test_uint])] /\
  ~supported_iterator [] (BaseT (UintT 256))
    (Array (Name (ArrayT (BaseT (UintT 256)) (Fixed 2)) "array")) 3
Proof
  EVAL_TAC
QED
