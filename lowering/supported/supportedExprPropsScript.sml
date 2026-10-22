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
     IfExp (BaseT (UintT 256)) (Name (BaseT BoolT) "c") expr_test_uint expr_test_uint;
     StructLit (StructT (NONE,"Pair")) (NONE,"Pair")
       [("first",expr_test_uint); ("second",expr_test_int)];
     Builtin (TupleT [BaseT (UintT 256)]) (MakeArray NONE (Fixed 1)) [expr_test_uint];
     Subscript (BaseT (UintT 256)) (TopLevelName NoneT (NONE,"map")) expr_test_address;
     Subscript (BaseT (UintT 256))
       (TopLevelName (ArrayT (BaseT (UintT 256)) (Fixed 2)) (NONE,"fixed")) expr_test_uint;
     Subscript (BaseT (IntT 256))
       (TopLevelName (ArrayT (BaseT (IntT 256)) (Dynamic 4)) (NONE,"dynamic")) expr_test_uint;
     Attribute (BaseT (UintT 256))
       (TopLevelName (StructT (NONE,"Pair")) (NONE,"record")) "first";
     Builtin (BaseT (UintT 256)) (Bop Add) [expr_test_uint; expr_test_uint];
     TypeBuiltin (BaseT (IntT 8)) Convert (BaseT (IntT 8)) [expr_test_uint];
     expr_test_decode]
Proof
  EVAL_TAC
QED

Theorem supported_storage_base_exclusions:
  EVERY (\e. ~supported_expr expr_test_tops e)
    [TopLevelName (ArrayT (BaseT (UintT 256)) (Fixed 2)) (NONE,"fixed");
     TopLevelName (StructT (NONE,"Pair")) (NONE,"record");
     TopLevelName (BaseT (UintT 256)) (NONE,"missing");
     TopLevelName (BaseT (UintT 256)) (SOME 0,"scalar");
     TopLevelName (BaseT (IntT 256)) (NONE,"scalar");
     Subscript (BaseT (UintT 256))
       (Name (ArrayT (BaseT (UintT 256)) (Fixed 2)) "fixed") expr_test_uint;
     Subscript (BaseT (UintT 256))
       (Subscript (ArrayT (BaseT (UintT 256)) (Fixed 2))
         (TopLevelName NoneT (NONE,"map")) expr_test_uint) expr_test_uint;
     Subscript (BaseT (UintT 256)) (TopLevelName NoneT (SOME 0,"map")) expr_test_uint;
     Attribute (BaseT (IntT 256))
       (TopLevelName (StructT (NONE,"Pair")) (NONE,"record")) "second";
     Attribute (BaseT (UintT 256))
       (Name (StructT (NONE,"Pair")) "record") "first";
     Attribute (BaseT (UintT 256))
       (TopLevelName (StructT (NONE,"Pair")) (SOME 0,"record")) "first";
     IfExp (TupleT [BaseT (UintT 256)]) (Name (BaseT BoolT) "c") expr_test_uint expr_test_uint;
     StructLit (StructT (NONE,"Pair")) (SOME 0,"Pair") [];
     FlagMember (FlagT (NONE,"Flags")) (NONE,"Flags") "A"]
Proof
  EVAL_TAC
QED

Theorem supported_bad_storage_declarations_excluded:
  ~supported_subscript_base
    [VariableDecl Private Transient "a" (ArrayT (BaseT (UintT 256)) (Fixed 2)) (SOME 0)]
    (NONE,"a") /\
  ~supported_subscript_base
    [VariableDecl Private Storage "a" (ArrayT (BaseT (UintT 8)) (Fixed 2)) (SOME 0)]
    (NONE,"a") /\
  ~supported_subscript_base
    [VariableDecl Private Storage "a" (ArrayT (BaseT (UintT 256)) (Fixed 0)) (SOME 0)]
    (NONE,"a") /\
  ~supported_subscript_base
    [HashMapDecl Private T "a" (BaseT AddressT) (Type (BaseT (UintT 256))) (SOME 0)]
    (NONE,"a") /\
  ~supported_subscript_base
    [HashMapDecl Private F "a" (BaseT (BytesT (Fixed 32)))
       (Type (BaseT (UintT 256))) (SOME 0)] (NONE,"a") /\
  ~supported_subscript_base
    [HashMapDecl Private F "a" (BaseT AddressT)
       (HashMapT (BaseT AddressT) (Type (BaseT (UintT 256)))) (SOME 0)] (NONE,"a") /\
  ~supported_storage_scalar
    [VariableDecl Private Storage "a" (BaseT (UintT 256)) NONE]
    (NONE,"a") (BaseT (UintT 256)) /\
  ~supported_storage_scalar
    [VariableDecl Private Immutable "a" (BaseT (UintT 256)) (SOME 0)]
    (NONE,"a") (BaseT (UintT 256)) /\
  ~supported_storage_scalar
    [VariableDecl Private (Constant expr_test_uint) "a" (BaseT (UintT 256)) (SOME 0)]
    (NONE,"a") (BaseT (UintT 256)) /\
  ~supported_storage_scalar
    [VariableDecl Public Storage "a" (BaseT (UintT 256)) (SOME 0)]
    (NONE,"a") (BaseT (UintT 256))
Proof
  EVAL_TAC
QED

Theorem supported_internal_send_pop_rows:
  supported_effect_expr expr_test_tops expr_test_internal /\
  supported_effect_expr expr_test_tops (Call NoneT (Send F) [expr_test_address; expr_test_uint] NONE) /\
  supported_effect_expr expr_test_tops
    (Call NoneT (Send T) [expr_test_address; expr_test_uint; expr_test_uint] NONE) /\
  supported_effect_expr expr_test_tops expr_test_pop /\
  EVERY (\e. ~supported_pure_expr expr_test_tops e /\ supported_expr expr_test_tops e)
    [expr_test_internal; expr_test_pop] /\
  ~supported_expr expr_test_tops
    (Call (BaseT (UintT 256)) (IntCall (NONE,"remote")) [expr_test_uint] NONE) /\
  ~supported_expr expr_test_tops
    (Call (BaseT (UintT 256)) (IntCall (SOME 0,"helper")) [expr_test_uint] NONE) /\
  ~supported_expr [FunctionDecl External Pure F F "helper" [] [] NoneT []]
    (Call NoneT (IntCall (NONE,"helper")) [] NONE) /\
  ~supported_expr [FunctionDecl Deploy Pure F F "helper" [] [] NoneT []]
    (Call NoneT (IntCall (NONE,"helper")) [] NONE) /\
  ~supported_expr expr_test_tops (Call (BaseT (UintT 256)) (Send F) [expr_test_address; expr_test_uint] NONE) /\
  ~supported_expr expr_test_tops (Call NoneT (Send F) [expr_test_address] NONE) /\
  ~supported_expr expr_test_tops (Call NoneT (Send T) [expr_test_address; expr_test_uint] NONE) /\
  ~supported_expr expr_test_tops (Pop (BaseT (UintT 256)) (TopLevelNameTarget (NONE,"fixed"))) /\
  ~supported_expr expr_test_tops (Pop (BaseT (IntT 256)) (NameTarget "dynamic")) /\
  ~supported_expr expr_test_tops (Pop (BaseT (IntT 256)) (TopLevelNameTarget (SOME 0,"dynamic"))) /\
  ~supported_expr expr_test_tops
    (Pop (BaseT (IntT 256)) (SubscriptTarget (TopLevelNameTarget (NONE,"dynamic")) expr_test_uint))
Proof
  EVAL_TAC
QED

Theorem supported_external_expression_row:
  supported_effect_expr expr_test_tops
    (Call (BaseT (UintT 256)) (ExtCall T F ("remote",[BaseT (UintT 256)],BaseT (UintT 256)) [])
      [expr_test_address; expr_test_uint] NONE) /\
  supported_effect_expr expr_test_tops
    (Call (TupleT [BaseT (UintT 256); BaseT BoolT])
      (ExtCall F F ("remote",[BaseT (UintT 256)],TupleT [BaseT (UintT 256); BaseT BoolT]) [EKValue])
      [expr_test_address; expr_test_uint; expr_test_uint] NONE) /\
  ~supported_expr expr_test_tops
    (Call NoneT (ExtCall T F ("remote",[BaseT (UintT 256)],NoneT) [])
      [expr_test_address; expr_test_uint] NONE) /\
  ~supported_expr expr_test_tops
    (Call (BaseT (UintT 256)) (ExtCall T F ("remote",[BaseT (UintT 256)],BaseT (UintT 256)) [])
      [expr_test_address] NONE) /\
  ~supported_expr expr_test_tops
    (Call (BaseT (UintT 256)) (ExtCall F F ("remote",[BaseT (UintT 256)],BaseT (UintT 256)) [EKValue])
      [expr_test_address; expr_test_uint] NONE) /\
  ~supported_expr expr_test_tops
    (Call (BaseT (UintT 256)) (ExtCall T F ("remote",[BaseT (UintT 256)],BaseT (UintT 256)) [])
      [expr_test_address; expr_test_uint; expr_test_uint] NONE) /\
  (* The selector comes from the call-site signature: no declaration lookup. *)
  supported_effect_expr expr_test_tops
    (Call (BaseT (UintT 256)) (ExtCall T F ("remote",[BaseT (IntT 256)],BaseT (UintT 256)) [])
      [expr_test_address; expr_test_int] NONE) /\
  supported_effect_expr expr_test_tops
    (Call (BaseT (UintT 256)) (ExtCall T F ("missing",[BaseT (UintT 256)],BaseT (UintT 256)) [])
      [expr_test_address; expr_test_uint] NONE) /\
  (* A default_return_value= is an operand like the others: any pure default
     is admitted, an effectful one is not. *)
  EVERY (\d. supported_effect_expr expr_test_tops
    (Call (BaseT (UintT 256)) (ExtCall T F ("remote",[BaseT (UintT 256)],BaseT (UintT 256)) [EKDefault])
      [expr_test_address; expr_test_uint; d] NONE))
    [expr_test_uint; Literal (BaseT (UintT 256)) (IntL 7);
     IfExp (BaseT (UintT 256)) (Literal (BaseT BoolT) (BoolL T))
       expr_test_uint expr_test_uint] /\
  ~supported_expr expr_test_tops
    (Call (BaseT (UintT 256)) (ExtCall T F ("remote",[BaseT (UintT 256)],BaseT (UintT 256)) [EKDefault])
      [expr_test_address; expr_test_uint; expr_test_internal] NONE) /\
  ~supported_expr expr_test_tops
    (Call (BaseT (UintT 256)) (ExtCall T F ("remote",[BaseT (UintT 256)],BaseT (UintT 256)) [])
      [expr_test_address; expr_test_uint] (SOME expr_test_uint)) /\
  (* Keyword operands: each kind at most once, no value= on a staticcall. *)
  supported_effect_expr expr_test_tops
    (Call (BaseT (UintT 256)) (ExtCall F F ("remote",[BaseT (UintT 256)],BaseT (UintT 256)) [EKGas; EKValue])
      [expr_test_address; expr_test_uint; expr_test_uint; expr_test_uint] NONE) /\
  ~supported_expr expr_test_tops
    (Call (BaseT (UintT 256)) (ExtCall F F ("remote",[BaseT (UintT 256)],BaseT (UintT 256)) [EKValue; EKValue])
      [expr_test_address; expr_test_uint; expr_test_uint; expr_test_uint] NONE) /\
  ~supported_expr expr_test_tops
    (Call (BaseT (UintT 256)) (ExtCall T F ("remote",[BaseT (UintT 256)],BaseT (UintT 256)) [EKValue])
      [expr_test_address; expr_test_uint; expr_test_uint] NONE) /\
  EVERY (\ret. supported_effect_expr expr_test_tops
    (Call ret (ExtCall T F ("remote",[BaseT (UintT 256)],ret) [])
      [expr_test_address; expr_test_uint] NONE))
    [BaseT (StringT 32); BaseT (BytesT (Dynamic 32));
     TupleT [BaseT (UintT 256); BaseT (StringT 32)];
     ArrayT (BaseT (UintT 256)) (Fixed 2); ArrayT (BaseT (UintT 256)) (Dynamic 3);
     StructT (NONE,"Pair")] /\
  EVERY (\ret. ~supported_expr expr_test_tops
    (Call ret (ExtCall T F ("remote",[BaseT (UintT 256)],ret) [])
      [expr_test_address; expr_test_uint] NONE))
    [TupleT []; BaseT (BytesT (Fixed 20)); StructT (NONE,"Missing");
     TupleT [TupleT [BaseT (UintT 256)]]]
Proof
  EVAL_TAC
QED

Theorem supported_external_nonword_arguments_rejected:
  EVERY (\arg_ty. ~supported_effect_expr
    [InterfaceDecl "I" [("remote",[("arg",arg_ty)],BaseT (UintT 256),View)]]
    (Call (BaseT (UintT 256)) (ExtCall T F ("remote",[arg_ty],BaseT (UintT 256)) [])
      [expr_test_address; Name arg_ty "arg"] NONE))
    [BaseT (StringT 32); BaseT (BytesT (Dynamic 32)); BaseT (BytesT (Fixed 20));
     BaseT (UintT 7); TupleT [BaseT (UintT 256)];
     ArrayT (BaseT (UintT 256)) (Fixed 2); StructT (NONE,"Pair"); NoneT]
Proof
  EVAL_TAC
QED

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
(* No effectful child may hide in a P constructor or an E argument. This
   rejects the argument-location and external evaluation-order witnesses. *)
Theorem supported_effect_nesting_counterexamples:
  EVERY (\e. ~supported_expr expr_test_tops e)
    [Builtin (BaseT (UintT 256)) (Bop Add) [expr_test_internal; expr_test_uint];
     IfExp (BaseT (UintT 256)) expr_test_internal expr_test_uint expr_test_uint;
     IfExp (BaseT (UintT 256)) (Name (BaseT BoolT) "c") expr_test_internal expr_test_uint;
     IfExp (BaseT (UintT 256)) (Name (BaseT BoolT) "c") expr_test_uint expr_test_internal;
     StructLit (StructT (NONE,"Pair")) (NONE,"Pair") [("first",expr_test_internal)];
     Builtin (TupleT [BaseT (UintT 256)]) (MakeArray NONE (Fixed 1)) [expr_test_internal];
     TypeBuiltin (BaseT (IntT 256)) Convert (BaseT (IntT 256)) [expr_test_internal];
     Subscript (BaseT (UintT 256)) (TopLevelName NoneT (NONE,"map")) expr_test_internal;
     Call (BaseT (UintT 256)) (IntCall (NONE,"helper")) [expr_test_pop] NONE;
     Call (BaseT (UintT 256)) (IntCall (NONE,"helper")) [expr_test_internal] NONE;
     Call (BaseT (UintT 256)) (ExtCall T F ("remote",[BaseT (UintT 256)],BaseT (UintT 256)) [])
       [expr_test_internal; expr_test_uint] NONE;
     Call (BaseT (UintT 256)) (ExtCall F F ("remote",[BaseT (UintT 256)],BaseT (UintT 256)) [EKValue])
       [expr_test_address; expr_test_uint; expr_test_internal] NONE;
     Call (BaseT (UintT 256)) (ExtCall T F ("remote",[BaseT (UintT 256)],BaseT (UintT 256)) [])
       [expr_test_address; expr_test_internal] NONE;
     Call NoneT (Send F) [expr_test_internal; expr_test_uint] NONE;
     Call NoneT (Send F) [expr_test_address; expr_test_pop] NONE;
     Call (BaseT (UintT 256)) (IntCall (NONE,"helper")) [expr_test_uint] (SOME expr_test_uint)]
Proof
  EVAL_TAC
QED

Theorem supported_raw_call_forms_excluded:
  EVERY (\target. ~supported_expr expr_test_tops (Call NoneT target [] NONE))
    [RawCallTarget <| rcf_max_outsize := 0; rcf_is_delegate := F;
                     rcf_is_static := F; rcf_revert_on_failure := T |>;
     RawLog; RawRevert; SelfDestructTarget;
     CreateTarget CreateMinimalProxy F T; CreateTarget CreateCopyOf F T;
     CreateTarget (CreateFromBlueprint F) T T; CreateTarget RawCreate F T]
Proof
  EVAL_TAC
QED

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
