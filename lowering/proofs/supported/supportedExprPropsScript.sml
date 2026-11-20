(* Permanent expression/occurrence coverage for PLAN 5.6 and 6.2.
   All concrete checks use plain EVAL (with standard integer reductions). *)
Theory supportedExprProps
Ancestors
  supportedExprs supportedExprTraverse supportedExprForms supportedExprFormProps
  supportedTypes supportedDecls vyperAST list integer
Libs
  intLib

Definition expr_test_tops_def:
  expr_test_tops =
    [VariableDecl Private Storage "scalar" (BaseT (UintT 256)) (SOME 0);
     VariableDecl Private Transient "transient" (BaseT (IntT 256)) (SOME 1);
     VariableDecl Private Storage "fixed" (ArrayT (BaseT (UintT 256)) (Fixed 2)) (SOME 2);
     VariableDecl Private Storage "dynamic" (ArrayT (BaseT (IntT 256)) (Dynamic 4)) (SOME 4);
     StructDecl "Pair" [("first", BaseT (UintT 256)); ("second", BaseT (IntT 256))];
     VariableDecl Private Storage "record" (StructT (NONE,"Pair")) (SOME 9);
     HashMapDecl Private F "map" (BaseT AddressT) (Type (BaseT (UintT 256))) (SOME 11);
     HashMapDecl Private F "nested" (BaseT (UintT 256))
       (HashMapT (BaseT (UintT 256)) (Type (BaseT (UintT 256)))) (SOME 12);
     HashMapDecl Private F "recordmap" (BaseT (UintT 256))
       (Type (StructT (NONE,"Pair"))) (SOME 13);
     FunctionDecl Internal Pure F F "helper" [("u",BaseT (UintT 256))] []
       (BaseT (UintT 256)) [];
     InterfaceDecl "I" [("remote", [("u",BaseT (UintT 256))], BaseT (UintT 256), View)]]
End

Definition expr_test_address_def:
  expr_test_address = Name (BaseT AddressT) "address"
End

Definition expr_test_internal_def:
  expr_test_internal = Call (BaseT (UintT 256)) (IntCall (NONE,"helper"))
    [expr_test_uint] NONE
End

Definition expr_test_pop_def:
  expr_test_pop = Pop (BaseT (IntT 256)) (TopLevelNameTarget (NONE,"dynamic"))
End

Definition expr_test_decode_def:
  expr_test_decode = TypeBuiltin
    (TupleT [BaseT (UintT 256); BaseT (StringT 32)]) (AbiDecode F)
    (TupleT [BaseT (UintT 256); BaseT (StringT 32)])
    [Name (BaseT (BytesT (Dynamic 256))) "data"]
End

Theorem supported_pure_expression_rows:
  EVERY (supported_pure_expr expr_test_tops)
    [expr_test_uint; Literal (BaseT (IntT 8)) (IntL (~1));
     TopLevelName (BaseT (UintT 256)) (NONE,"scalar");
     TopLevelName (BaseT (IntT 256)) (NONE,"transient");
     TopLevelName (ArrayT (BaseT (UintT 256)) (Fixed 2)) (NONE,"fixed");
     TopLevelName (StructT (NONE,"Pair")) (NONE,"record");
     IfExp (BaseT (UintT 256)) (Name (BaseT BoolT) "c") expr_test_uint expr_test_uint;
     IfExp (BaseT (StringT 10)) (Name (BaseT BoolT) "c")
       (Name (BaseT (StringT 10)) "s") (Name (BaseT (StringT 10)) "t");
     IfExp (ArrayT (BaseT (UintT 256)) (Fixed 2)) (Name (BaseT BoolT) "c")
       (Name (ArrayT (BaseT (UintT 256)) (Fixed 2)) "a")
       (Name (ArrayT (BaseT (UintT 256)) (Fixed 2)) "b");
     IfExp (StructT (NONE,"Pair")) (Name (BaseT BoolT) "c")
       (Name (StructT (NONE,"Pair")) "p") (Name (StructT (NONE,"Pair")) "q");
     StructLit (StructT (NONE,"Pair")) (NONE,"Pair")
       [("first",expr_test_uint); ("second",expr_test_int)];
     Builtin (TupleT [BaseT (UintT 256)]) (MakeArray NONE (Fixed 1)) [expr_test_uint];
     Subscript (BaseT (UintT 256)) (TopLevelName NoneT (NONE,"map")) expr_test_address;
     Subscript (BaseT (UintT 256))
       (TopLevelName (ArrayT (BaseT (UintT 256)) (Fixed 2)) (NONE,"fixed")) expr_test_uint;
     Subscript (BaseT (IntT 256))
       (TopLevelName (ArrayT (BaseT (IntT 256)) (Dynamic 4)) (NONE,"dynamic")) expr_test_uint;
     Subscript (BaseT (UintT 256))
       (Name (ArrayT (BaseT (UintT 256)) (Fixed 2)) "fixed") expr_test_uint;
     Subscript (BaseT (UintT 256))
       (Subscript NoneT (TopLevelName NoneT (NONE,"nested")) expr_test_uint) expr_test_uint;
     Attribute (BaseT (UintT 256))
       (TopLevelName (StructT (NONE,"Pair")) (NONE,"record")) "first";
     Attribute (BaseT (IntT 256))
       (TopLevelName (StructT (NONE,"Pair")) (NONE,"record")) "second";
     Attribute (BaseT (UintT 256))
       (Name (StructT (NONE,"Pair")) "record") "first";
     Builtin (BaseT (UintT 256)) (Bop Add) [expr_test_uint; expr_test_uint];
     TypeBuiltin (BaseT (IntT 8)) Convert (BaseT (IntT 8)) [expr_test_uint];
     expr_test_decode;
     FlagMember (FlagT (NONE,"Flags")) (NONE,"Flags") "A"]
Proof
  EVAL_TAC
QED

Theorem supported_nested_map_transient_and_bytes_roots:
  supported_subscript_base
    [VariableDecl Private Transient "a" (ArrayT (BaseT (UintT 256)) (Fixed 2)) (SOME 0)]
    (NONE,"a") /\
  supported_subscript_base
    [HashMapDecl Private T "a" (BaseT AddressT) (Type (BaseT (UintT 256))) (SOME 0)]
    (NONE,"a") /\
  supported_subscript_base
    [HashMapDecl Private F "a" (BaseT (BytesT (Fixed 32)))
       (Type (BaseT (UintT 256))) (SOME 0)] (NONE,"a") /\
  supported_subscript_base
    [HashMapDecl Private F "a" (BaseT AddressT)
       (HashMapT (BaseT AddressT) (Type (BaseT (UintT 256)))) (SOME 0)] (NONE,"a")
Proof
  EVAL_TAC
QED

(* Effects may occur in place keys while P retains its effect-free meaning. *)
(* No declaration decides admission: the lowering hashes the call-site
   signature, as the source semantics does. *)
Theorem supported_external_declaration_independent:
  EVERY (\tops. supported_effect_expr tops
    (Call (BaseT (UintT 256)) (ExtCall T F ("remote",[BaseT (UintT 256)],BaseT (UintT 256)) [])
      [expr_test_address; expr_test_uint] NONE))
    [[FunctionDecl External View F F "remote" [("u",BaseT (UintT 256))] []
        (BaseT (UintT 256)) [];
      InterfaceDecl "I" [("remote",[("u",BaseT (UintT 256))],BaseT (UintT 256),View)]];
     [InterfaceDecl "Bad" [("remote",[("i",BaseT (IntT 256))],BaseT (UintT 256),View)];
      InterfaceDecl "Good" [("remote",[("u",BaseT (UintT 256))],BaseT (UintT 256),View)]];
     [InterfaceDecl "I"
       [("remote",[("i",BaseT (IntT 256))],BaseT (UintT 256),View);
        ("remote",[("u",BaseT (UintT 256))],BaseT (UintT 256),View)]];
     []]
Proof
  EVAL_TAC
QED
(* Effectful place keys have their own E cases. Other effectful children and
   call arguments retain the independent evaluation-order restrictions. *)
Theorem supported_occurrence_traversal_coverage:
  EVERY expr_has_internal_call
    [expr_test_internal;
     IfExp (BaseT (UintT 256)) expr_test_uint expr_test_internal expr_test_uint;
     StructLit (StructT (NONE,"Pair")) (NONE,"Pair") [("first",expr_test_internal)];
     Subscript NoneT expr_test_internal expr_test_uint;
     Subscript NoneT expr_test_uint expr_test_internal;
     Attribute NoneT expr_test_internal "field";
     Builtin NoneT Len [expr_test_internal];
     TypeBuiltin NoneT Extract32 NoneT [expr_test_uint; expr_test_internal];
     Pop NoneT (AttributeTarget (SubscriptTarget (NameTarget "x") expr_test_internal) "f");
     Call NoneT RawLog [expr_test_internal] NONE;
     Call NoneT RawLog [] (SOME expr_test_internal)] /\
  target_has_internal_call (AttributeTarget
    (SubscriptTarget (TopLevelNameTarget (NONE,"x")) expr_test_internal) "f") /\
  ~expr_has_internal_call expr_test_pop /\
  ~expr_has_internal_call expr_test_decode /\
  ~expr_has_internal_call (FlagMember NoneT (NONE,"Flag") "f") /\
  expr_has_effect expr_test_pop /\
  expr_has_effect (Call NoneT RawRevert [] NONE) /\
  expr_has_effect (Builtin NoneT Len [expr_test_pop]) /\
  ~expr_has_effect (TopLevelName NoneT (NONE,"x")) /\
  ~expr_has_effect (Literal (BaseT (IntT 8)) (IntL (~1))) /\
  ~expr_has_effect expr_test_decode
Proof
  EVAL_TAC
QED

Theorem supported_dynamic_decode_traversal_coverage:
  supported_pure_expr expr_test_tops expr_test_decode /\
  EVERY (expr_has_dynamic_decode expr_test_tops)
    [expr_test_decode;
     IfExp NoneT expr_test_uint expr_test_uint expr_test_decode;
     StructLit NoneT (NONE,"x") [("f",expr_test_decode)];
     Subscript NoneT expr_test_decode expr_test_uint;
     Subscript NoneT expr_test_uint expr_test_decode;
     Attribute NoneT expr_test_decode "f";
     Builtin NoneT Len [expr_test_decode];
     TypeBuiltin NoneT Extract32 NoneT [expr_test_decode];
     Call NoneT RawLog [expr_test_decode] NONE;
     Call NoneT RawLog [] (SOME expr_test_decode);
     Pop NoneT (SubscriptTarget (NameTarget "x") expr_test_decode)] /\
  target_has_dynamic_decode expr_test_tops
    (AttributeTarget (SubscriptTarget (NameTarget "x") expr_test_decode) "f") /\
  expr_has_dynamic_decode [] (TypeBuiltin NoneT (AbiDecode T)
    (TupleT [BaseT (BytesT (Dynamic 0)); BaseT BoolT]) []) /\
  ~expr_has_dynamic_decode expr_test_tops (TypeBuiltin
    (TupleT [BaseT (UintT 256); BaseT BoolT]) (AbiDecode F)
    (TupleT [BaseT (UintT 256); BaseT BoolT]) [expr_test_uint]) /\
  ~expr_has_dynamic_decode expr_test_tops expr_test_internal /\
  ~expr_has_dynamic_decode expr_test_tops expr_test_pop /\
  ~expr_has_dynamic_decode [] (Name (BaseT (StringT 32)) "x") /\
  expr_has_dynamic_decode [StructDecl "S" [("s",BaseT (StringT 32))]]
    (TypeBuiltin NoneT (AbiDecode F) (StructT (NONE,"S")) []) /\
  expr_has_dynamic_decode [] (TypeBuiltin NoneT (AbiDecode F)
    (ArrayT (BaseT (UintT 256)) (Dynamic 2)) []) /\
  expr_has_dynamic_decode [] (TypeBuiltin NoneT (AbiDecode F)
    (ArrayT (BaseT (StringT 32)) (Fixed 2)) []) /\
  ~expr_has_dynamic_decode [] (TypeBuiltin NoneT (AbiDecode F)
    (ArrayT (BaseT (UintT 256)) (Fixed 2)) [])
Proof
  EVAL_TAC
QED
