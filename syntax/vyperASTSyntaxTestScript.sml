Theory vyperASTSyntaxTest
Ancestors
  vyperAST
Libs
  vyperASTSyntax

fun same_term a b = Term.aconv a b;

val u256 =
  vyperASTSyntax.mk_BaseT_tm
    (vyperASTSyntax.mk_UintT_tm (numSyntax.term_of_int 256));
val name_tm = vyperASTSyntax.mk_Name (u256, "x");
val _ =
  case vyperASTSyntax.dest_Name name_tm of
  | (ty, "x") => if same_term ty u256 then () else raise Fail "dest_Name ty"
  | _ => raise Fail "dest_Name";

val lit_tm =
  vyperASTSyntax.mk_Literal_tm
    (u256, vyperASTSyntax.mk_IntL_tm
      (intSyntax.term_of_int (Arbint.fromInt 1)));
val call_tm = vyperASTSyntax.mk_Call
  (u256, vyperASTSyntax.Send_tm, [name_tm, lit_tm], SOME name_tm);
val _ =
  case vyperASTSyntax.dest_Call call_tm of
  | (ty, target, [arg1, arg2], SOME drv) =>
      if same_term ty u256 andalso
         same_term target vyperASTSyntax.Send_tm andalso
         same_term arg1 name_tm andalso
         same_term arg2 lit_tm andalso
         same_term drv name_tm
      then ()
      else raise Fail "dest_Call components"
  | _ => raise Fail "dest_Call";

val for_tm = vyperASTSyntax.mk_For
  ("i", u256, vyperASTSyntax.mk_Range_tm (lit_tm, name_tm),
   numSyntax.term_of_int 10, [vyperASTSyntax.Pass_tm]);
val _ =
  case vyperASTSyntax.dest_For for_tm of
  | ("i", ty, iter, bound, [body]) =>
      if same_term ty u256 andalso
         vyperASTSyntax.is_Range iter andalso
         same_term bound (numSyntax.term_of_int 10) andalso
         same_term body vyperASTSyntax.Pass_tm
      then ()
      else raise Fail "dest_For components"
  | _ => raise Fail "dest_For";

val _ =
  case vyperASTSyntax.view_expr name_tm of
  | vyperASTSyntax.VName (ty, "x") =>
      if same_term ty u256 then () else raise Fail "view_expr ty"
  | _ => raise Fail "view_expr";

val _ = if not (vyperASTSyntax.is_Name lit_tm) then ()
        else raise Fail "is_Name negative";

val body_tm = listSyntax.mk_list ([vyperASTSyntax.Pass_tm], vyperASTSyntax.stmt_ty);
val empty_args_tm = listSyntax.mk_list ([], vyperASTSyntax.argument_ty);
val empty_defaults_tm = listSyntax.mk_list ([], vyperASTSyntax.expr_ty);
val fn_tm = vyperASTSyntax.mk_FunctionDecl_tm
  (vyperASTSyntax.External_tm,
   vyperASTSyntax.Nonpayable_tm,
   boolSyntax.F,
   boolSyntax.F,
   stringSyntax.fromMLstring "f",
   empty_args_tm,
   empty_defaults_tm,
   u256,
   body_tm);
val _ =
  case vyperASTSyntax.view_toplevel fn_tm of
  | vyperASTSyntax.VFunctionDecl (vis, mut, nonre, rawret, name, args, defaults, ret, body) =>
      if same_term vis vyperASTSyntax.External_tm andalso
         same_term mut vyperASTSyntax.Nonpayable_tm andalso
         same_term nonre boolSyntax.F andalso
         same_term rawret boolSyntax.F andalso
         stringSyntax.fromHOLstring name = "f" andalso
         same_term args empty_args_tm andalso
         same_term defaults empty_defaults_tm andalso
         same_term ret u256 andalso
         same_term body body_tm
      then ()
      else raise Fail "view_toplevel FunctionDecl components"
  | _ => raise Fail "view_toplevel FunctionDecl";

(* Exhaust every recursive AST view constructor. The individual raw constructor
   and destructor functions are generated from the same checked constants; these
   tests guard the hand-written list/option/string adapters and view dispatch. *)
val nsid = pairSyntax.mk_pair
  (optionSyntax.mk_none numSyntax.num, stringSyntax.fromMLstring "member");
val fields = listSyntax.mk_list
  ([pairSyntax.mk_pair (stringSyntax.fromMLstring "field", name_tm)],
   pairSyntax.mk_prod (stringSyntax.string_ty, vyperASTSyntax.expr_ty));
val expr_samples =
  [ vyperASTSyntax.mk_TopLevelName_tm (u256, nsid)
  , vyperASTSyntax.mk_FlagMember (u256, nsid, "member")
  , vyperASTSyntax.mk_IfExp_tm (u256, name_tm, name_tm, name_tm)
  , vyperASTSyntax.mk_StructLit (u256, nsid, [("field", name_tm)])
  , vyperASTSyntax.mk_Subscript_tm (u256, name_tm, lit_tm)
  , vyperASTSyntax.mk_Attribute (u256, name_tm, "field")
  , vyperASTSyntax.mk_Builtin (u256,
      vyperASTSyntax.mk_Bop_tm vyperASTSyntax.Add_tm,
      [name_tm, lit_tm])
  , vyperASTSyntax.mk_TypeBuiltin
      (u256, vyperASTSyntax.Convert_tm, u256, [name_tm])
  , vyperASTSyntax.mk_Pop_tm
      (u256, vyperASTSyntax.mk_NameTarget "xs")
  ];
val _ = List.app (fn tm => ignore (vyperASTSyntax.view_expr tm)) expr_samples;

val base_target = vyperASTSyntax.mk_BaseTarget_tm
  (vyperASTSyntax.mk_NameTarget "x");
val tuple_target = vyperASTSyntax.mk_TupleTarget [base_target];
val base_target_samples =
  [ vyperASTSyntax.mk_NameTarget "x"
  , vyperASTSyntax.mk_TopLevelNameTarget_tm nsid
  , vyperASTSyntax.mk_SubscriptTarget_tm
      (vyperASTSyntax.mk_NameTarget "xs", lit_tm)
  , vyperASTSyntax.mk_AttributeTarget
      (vyperASTSyntax.mk_NameTarget "s", "field")
  ];
val _ = List.app
  (fn tm => ignore (vyperASTSyntax.view_base_assignment_target tm))
  base_target_samples;
val _ = List.app
  (fn tm => ignore (vyperASTSyntax.view_assignment_target tm))
  [base_target, tuple_target];
val _ = List.app
  (fn tm => ignore (vyperASTSyntax.view_iterator tm))
  [vyperASTSyntax.mk_Array_tm name_tm,
   vyperASTSyntax.mk_Range_tm (lit_tm, name_tm)];
val _ = List.app
  (fn tm => ignore (vyperASTSyntax.view_assert_reason tm))
  [vyperASTSyntax.AssertBare_tm,
   vyperASTSyntax.AssertUnreachable_tm,
   vyperASTSyntax.mk_AssertReason_tm name_tm];
val _ = List.app
  (fn tm => ignore (vyperASTSyntax.view_raise_reason tm))
  [vyperASTSyntax.RaiseBare_tm,
   vyperASTSyntax.RaiseUnreachable_tm,
   vyperASTSyntax.mk_RaiseReason_tm name_tm];
val stmt_samples =
  [ vyperASTSyntax.Continue_tm
  , vyperASTSyntax.Break_tm
  , vyperASTSyntax.mk_Expr_tm name_tm
  , vyperASTSyntax.mk_If (name_tm, [vyperASTSyntax.Pass_tm], [])
  , vyperASTSyntax.mk_Assert_tm
      (name_tm, vyperASTSyntax.AssertBare_tm)
  , vyperASTSyntax.mk_Log (nsid, [name_tm])
  , vyperASTSyntax.mk_Raise_tm vyperASTSyntax.RaiseBare_tm
  , vyperASTSyntax.mk_Return (SOME name_tm)
  , vyperASTSyntax.mk_Assign_tm (tuple_target, name_tm)
  , vyperASTSyntax.mk_AugAssign_tm
      (u256, vyperASTSyntax.mk_NameTarget "x",
       vyperASTSyntax.Add_tm, name_tm)
  , vyperASTSyntax.mk_Append_tm
      (vyperASTSyntax.mk_NameTarget "xs", name_tm)
  , vyperASTSyntax.mk_AnnAssign ("x", u256, name_tm)
  ];
val _ = List.app (fn tm => ignore (vyperASTSyntax.view_stmt tm)) stmt_samples;

val flags = vyperASTSyntax.mk_raw_call_flags
  { max_outsize = numSyntax.term_of_int 32
  , is_delegate = boolSyntax.F
  , is_static = boolSyntax.T
  , revert_on_failure = boolSyntax.T
  };
val call_target_samples =
  [ vyperASTSyntax.mk_IntCall_tm nsid
  , vyperASTSyntax.mk_ExtCall_tm
      (boolSyntax.T,
       pairSyntax.mk_pair
         (stringSyntax.fromMLstring "f",
          pairSyntax.mk_pair
            (listSyntax.mk_list ([u256], vyperASTSyntax.type_ty), u256)))
  , vyperASTSyntax.Send_tm
  , vyperASTSyntax.mk_RawCallTarget_tm flags
  , vyperASTSyntax.RawLog_tm
  , vyperASTSyntax.RawRevert_tm
  , vyperASTSyntax.SelfDestructTarget_tm
  , vyperASTSyntax.mk_CreateTarget_tm
      (vyperASTSyntax.CreateMinimalProxy_tm, boolSyntax.T)
  ];
val _ = List.app
  (fn tm => ignore (vyperASTSyntax.view_call_target tm))
  call_target_samples;
val _ =
  if vyperASTSyntax.is_raw_call_flags flags then
    let val decoded = vyperASTSyntax.dest_raw_call_flags flags in
      if same_term (#max_outsize decoded) (numSyntax.term_of_int 32) andalso
         same_term (#is_delegate decoded) boolSyntax.F andalso
         same_term (#is_static decoded) boolSyntax.T andalso
         same_term (#revert_on_failure decoded) boolSyntax.T
      then () else raise Fail "raw_call_flags fields"
    end
  else raise Fail "raw_call_flags recognizer";

val no_slot = optionSyntax.mk_none numSyntax.num;
val empty_fields = listSyntax.mk_list ([], vyperASTSyntax.argument_ty);
val empty_event_fields = listSyntax.mk_list
  ([], pairSyntax.mk_prod (vyperASTSyntax.argument_ty, bool));
val empty_members = listSyntax.mk_list ([], stringSyntax.string_ty);
val empty_interfaces = listSyntax.mk_list
  ([], vyperASTSyntax.interface_func_ty);
val toplevel_samples =
  [ vyperASTSyntax.mk_VariableDecl_tm
      (vyperASTSyntax.Private_tm,
       vyperASTSyntax.Storage_tm,
       stringSyntax.fromMLstring "x", u256, no_slot)
  , vyperASTSyntax.mk_HashMapDecl_tm
      (vyperASTSyntax.Private_tm, boolSyntax.F,
       stringSyntax.fromMLstring "m", u256,
       vyperASTSyntax.mk_Type_tm u256, no_slot)
  , vyperASTSyntax.mk_StructDecl_tm
      (stringSyntax.fromMLstring "S", empty_fields)
  , vyperASTSyntax.mk_EventDecl_tm
      (stringSyntax.fromMLstring "E", empty_event_fields)
  , vyperASTSyntax.mk_FlagDecl_tm
      (stringSyntax.fromMLstring "F", empty_members)
  , vyperASTSyntax.mk_InterfaceDecl_tm
      (stringSyntax.fromMLstring "I", empty_interfaces)
  ];
val _ = List.app
  (fn tm => ignore (vyperASTSyntax.view_toplevel tm))
  toplevel_samples;

val _ =
  (ignore (vyperASTSyntax.dest_Name lit_tm);
   raise Fail "dest_Name accepted Literal")
  handle HOL_ERR _ => ();
