Theory sourceOrdinaryExprProps
Ancestors
  sourceOrdinaryExprElaborate sourceOrdinaryExprDefs sourceOrdinaryBridge
  sourceExprWitnessDefs sourceExprElaborate sourceExprDefs sourceConstBuiltinTest
  sourceSyntax sourceResolve sourceConstEval sourceConstAST jsonToVyperExpr
  jsonAST vyperTypeSystem vyperAST finite_map list pair option
Libs
  intLib wordsLib

Theorem source_ordinary_expected_type:
  source_const_then result (source_ordinary_expected expected) = SC_Value e ==>
  expr_type e = expected
Proof
  Cases_on `result` >> simp[source_const_then_def,source_ordinary_expected_def] >>
  rw[] >> gvs[]
QED

Theorem source_ordinary_expr_type:
  source_ordinary_expr fuel env scopes table constants bindings ctx expected original annotated = SC_Value e ==>
  expr_type e = expected
Proof
  Cases_on `fuel` >- simp[source_ordinary_expr_def] >>
  rename1 `SUC n` >>
  Cases_on `source_ordinary_projection (SUC n) annotated <> SOME original` >>
  simp[Once source_ordinary_expr_def] >>
  MATCH_ACCEPT_TAC source_ordinary_expected_type
QED

Theorem source_ordinary_expr_mismatch:
  source_ordinary_projection (SUC fuel) annotated <> SOME original ==>
  source_ordinary_expr (SUC fuel) env scopes table constants bindings ctx expected original annotated =
  SC_Invalid SCErr_Domain
Proof
  simp[Once source_ordinary_expr_def]
QED

Theorem source_ordinary_expr_replacement_irrelevant:
  source_ordinary_expr fuel env scopes table constants bindings ctx expected original
    (JE_Folded retained replacement1) =
  source_ordinary_expr fuel env scopes table constants bindings ctx expected original
    (JE_Folded retained replacement2)
Proof
  Cases_on `fuel` >> simp[source_ordinary_expr_def,source_ordinary_projection_def]
QED

Theorem source_ordinary_fold_invalid:
  source_resolve_candidate scopes table original = SOME candidate /\
  source_ordinary_evaluable candidate /\
  source_const_eval constants candidate = SC_Invalid err ==>
  source_ordinary_fold fuel env scopes table constants bindings expected original = SC_Invalid err
Proof
  simp[source_ordinary_fold_def]
QED

Theorem source_ordinary_fold_unsupported:
  source_resolve_candidate scopes table original = SOME candidate /\
  source_ordinary_evaluable candidate /\
  source_const_eval constants candidate = SC_Unsupported why ==>
  source_ordinary_fold fuel env scopes table constants bindings expected original = SC_Unsupported why
Proof
  simp[source_ordinary_fold_def]
QED

Theorem source_ordinary_nonmigrated_classification:
  ~source_ordinary_evaluable (SCE_Builtin SCB_Concat args kws) /\
  ~source_ordinary_evaluable (SCE_Builtin SCB_Sha256 args kws) /\
  ~source_ordinary_evaluable (SCE_Builtin SCB_Convert args kws) /\
  ~source_ordinary_evaluable (SCE_Call callee args kws)
Proof
  simp[source_ordinary_evaluable_def,sourceConstBuiltinTheory.source_const_builtin_arity_def]
QED

(* Callable identity deliberately ignores index contents. They are normalized
   only later by the recursive child, then occur once in expr_base_target. *)
Theorem source_ordinary_pop_receiver_subscript:
  source_ordinary_pop_receiver scopes table bindings (SX_Subscript receiver index) =
  source_ordinary_pop_receiver scopes table bindings receiver
Proof
  simp[Once source_ordinary_pop_receiver_def,
       source_expr_variable_def,source_expr_path_def]
QED

(* Test-only adapter. All originals and expected results are the existing 37
   retained rows (36 successes and the deliberately rejected method_id_var).
   Explicit JSON claims below are a separate input, not a source-to-JSON
   conversion and not the runtime result of a normalization. *)
Definition source_ordinary_test_def:
  source_ordinary_test env runtime constants ty original annotated =
    source_ordinary_expr 24 (source_expr_witness_env env runtime)
      [MAP (\(path,e). (HD path,path)) (FILTER (\(path,e). LENGTH path = 1) runtime) ++
       MAP (\(path,v). (HD path,path)) constants ++
       [("self",["self"]);("msg",["msg"])] ++
       MAP (\(name,kind). (name,["builtin";name]))
         (("concat",SR_Builtin SCB_Concat)::("floor",SR_Function)::source_expr_witness_builtins)]
      (MAP (\(path,e). (path,SR_Dynamic)) runtime ++
       MAP (\(path,v). (path,SR_Constant)) constants ++
       [(["self"],SR_Module);(["msg"],SR_Module)] ++
       MAP (\(name,kind). (["builtin";name],kind))
         (("concat",SR_Builtin SCB_Concat)::("floor",SR_Function)::source_expr_witness_builtins))
      (MAP (\(path,v). (path,SC_Constant v)) constants)
      (MAP (\(path,e). (path,SE_Runtime e)) runtime ++ source_expr_witness_bindings)
      (0,NONE,[],[],[],[],[]) ty original annotated
End

Definition source_ordinary_retained_claims_def:
  source_ordinary_retained_claims =
    let u = JT_Integer 256 F; i = JT_Integer 256 T;
        b = JT_Named NONE "bool"; a = JT_Named NONE "address";
        ni = \n. JE_Int n u; nb = JE_Bool;
        nm = \n ty. JE_Name n NONE JMissingSource ty;
        fnm = \n. JE_Name n NONE JMissingSource JT_None;
        bin = \ty l op r. JE_BinOp l op r ty;
        call = \n args ty. JE_Call (fnm n) args [] ty JMissingSource;
        fixed = \e. JE_Call (fnm "method_id") [e]
          [JKeyword "output_type" (fnm "bytes4")] (JT_BytesM 4) JMissingSource;
        mid = \s. call "method_id" [JE_GenericStr s] (JT_Bytes 4);
        enc = \e ks n. JE_Call (fnm "abi_encode") [e] ks (JT_Bytes n) JMissingSource;
        dead = JE_Hex "0xdeadbeef" (JT_BytesM 4);
        ks = [JKeyword "ensure_tuple" (nb F);JKeyword "method_id" dead];
        x = nm "x" u; y = nm "y" i; av = nm "a" u;
        neg = \n. JE_UnaryOp JUop_USub (JE_Int n i) i;
        tt = JT_Tuple [JT_Integer 128 T;b]
    in
    [bin u x JBop_Pow (bin u (ni 1) JBop_Add (ni 2));
     bin i (bin i (JE_Int 0 i) JBop_Sub (JE_Int 2 i)) JBop_Pow y;
     bin u x JBop_Add (bin u (ni 1) JBop_Add (ni 2));
     bin u x JBop_Mult (bin u (ni 2) JBop_Pow (ni 8));
     JE_Compare (ni 1) JBop_Lt (ni 2);
     JE_BoolOp JBoolop_And [nm "x" b;JE_UnaryOp JUop_Not (nb T) b];
     bin u x JBop_BitAnd (bin u (ni 1) JBop_LShift (ni 4));
     bin u x JBop_Add (call "min" [ni 3;ni 5] u);
     call "pow_mod256" [ni 2;ni 10] u;
     call "uint256_addmod" [ni 5;ni 6;ni 7] u;
     call "abs" [neg 5] i;
     call "keccak256" [JE_GenericStr "hello"] (JT_BytesM 32);
     call "len" [JE_GenericStr "abcd"] u;
     fixed (JE_GenericStr "transfer(address,uint256)");
     mid "transfer(address,uint256)";
     fixed (nm "SIG" (JT_String 5));
     fixed (JE_GenericStr "foo()");
     fixed (nm "s" (JT_String 30));
     enc av [JKeyword "ensure_tuple" (nb F);JKeyword "method_id" (nm "M" (JT_BytesM 4))] 36;
     enc av [JKeyword "ensure_tuple" (nb F);JKeyword "method_id" (mid "foo()")] 36;
     enc (nm "v" tt) [JKeyword "ensure_tuple" (nb F);JKeyword "method_id" (JE_Bytes 4 "0xdeadbeef")] 68;
     enc (nm "a" (JT_String 40)) ks 132;
     enc av ks 36;
     enc av [JKeyword "ensure_tuple" (nm "E" b);JKeyword "method_id" dead] 36;
     JE_Call (fnm "abi_decode") [nm "d" (JT_Bytes 64);JE_Tuple [fnm "uint256";fnm "bool"]]
       [JKeyword "unwrap_tuple" (nm "U" b)] (JT_Tuple [u;b]) JMissingSource;
     enc x [JKeyword "method_id" (mid "f(uint256)")] 36;
     enc (nm "a" a) [JKeyword "method_id" dead] 36;
     bin i (nm "x" i) JBop_Add (neg 5);
     bin i (neg 2) JBop_Pow y;
     JE_Compare av JBop_Lt (ni 5);
     JE_BoolOp JBoolop_Or [JE_BoolOp JBoolop_And [nm "a" b;nm "b" b];nm "c" b];
     bin u (bin u (nm "X" u) JBop_Add
       (JE_Attribute (fnm "self") "s" NONE NONE NONE JMissingSource u)) JBop_Add (nm "N" u);
     nm "C" (JT_BytesM 32);
     call "len" [nm "S" (JT_String 3)] u;
     bin u (nm "A" u) JBop_Mult (ni 7);
     call "raw_call" [nm "t" a;enc x [JKeyword "method_id" (mid "f(uint256)")] 36] JT_None;
     call "raw_revert" [enc x [JKeyword "method_id" (mid "E(uint256)")] 36] JT_None]
End

val () = computeLib.add_funs [source_const_keccak_hello, source_const_keccak_foo_full,
  source_expr_hash_transfer,
  source_expr_hash_f, source_expr_hash_E, source_expr_hash_x];

Definition source_ordinary_retained_row_def:
  source_ordinary_retained_row env n =
    case (EL n source_expr_witnesses,EL n source_ordinary_retained_claims) of
      ((name,runtime,constants,ty,original,expected),annotated) =>
        source_ordinary_test env runtime constants ty original annotated = expected
End

(* Expand fixture constructors ONCE, not the entire 37-row list at every
   recursive EVAL. These are still 37 separate kernel proofs of explicit paired
   source/JSON inputs; there is no source-to-JSON or runtime-to-JSON adapter. *)
val ordinary_witness_terms = fst (listSyntax.dest_list
  (rhs (concl (EVAL ``source_expr_witnesses``))));
val ordinary_claim_terms = fst (listSyntax.dest_list
  (rhs (concl (EVAL ``source_ordinary_retained_claims``))));
val source_ordinary_retained_rows = List.tabulate (37, fn n =>
  let val [name,runtime,constants,ty,original,expected] =
        pairSyntax.strip_pair (List.nth (ordinary_witness_terms,n))
      val annotated = List.nth (ordinary_claim_terms,n)
      val goal = ``source_ordinary_test env ^runtime ^constants ^ty ^original ^annotated = ^expected``
      val () = print ("ordinary retained row " ^ Int.toString n ^ "\n")
      val th = prove (goal,
        EVAL_TAC >> simp[source_expr_exists_equal] >>
        EVAL_TAC >> simp[source_expr_exists_equal] >> EVAL_TAC >> simp[source_expr_exists_equal])
  in save_thm ("source_ordinary_retained_" ^ Int.toString n,th) end);

Theorem source_ordinary_all_retained_expressions:
  LENGTH source_ordinary_retained_claims = LENGTH source_expr_witnesses /\
  LENGTH source_ordinary_retained_claims = 37 /\
  EVERY (\((name,runtime,constants,ty,original,expected),annotated).
    source_ordinary_test env runtime constants ty original annotated = expected)
    (ZIP (source_expr_witnesses,source_ordinary_retained_claims))
Proof
  simp_tac (srw_ss()) (source_ordinary_retained_rows @
    [source_ordinary_retained_claims_def,source_expr_witnesses_def,
     LET_THM,listTheory.ZIP,listTheory.EVERY_DEF,listTheory.LENGTH,
     pairTheory.pair_case_def,pairTheory.UNCURRY_DEF]) >>
  EVAL_TAC
QED

Theorem source_ordinary_concat_retained:
  source_ordinary_test env
    [(["s"],Name (BaseT (StringT 5)) "s")] [] (BaseT (StringT 6))
    (SX_Call (SX_Name "concat") [SX_Name "s";SX_Literal (SCL_String "x")] [])
    (JE_Call (JE_Name "concat" NONE JMissingSource JT_None)
      [JE_Name "s" NONE JMissingSource (JT_String 5);JE_Str 1 "x"] []
      (JT_String 6) JMissingSource) =
    SC_Value (Builtin (BaseT (StringT 6)) (Concat 6)
      [Name (BaseT (StringT 5)) "s";Literal (BaseT (StringT 1)) (StringL "x")])
Proof
  EVAL_TAC
QED

Theorem source_ordinary_concat_invalid_subtree:
  source_ordinary_test env [(["s"],Name (BaseT (StringT 5)) "s")] [] (BaseT (StringT 6))
    (SX_Call (SX_Name "concat") [SX_Name "s";
      SX_Call (SX_Name "len")
        [SX_Binary SCB_FloorDiv (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 0))] []] [])
    (JE_Call (JE_Name "concat" NONE JMissingSource JT_None)
      [JE_Name "s" NONE JMissingSource (JT_String 5);
       JE_Call (JE_Name "len" NONE JMissingSource JT_None)
         [JE_BinOp (JE_Int 1 (JT_Integer 256 F)) JBop_FloorDiv
           (JE_Int 0 (JT_Integer 256 F)) (JT_Integer 256 F)] []
         (JT_Integer 256 F) JMissingSource] [] (JT_String 6) JMissingSource) =
    SC_Invalid SCErr_ZeroDivisor
Proof
  EVAL_TAC
QED

Theorem source_ordinary_tuple_index_required:
  source_ordinary_test env
    [(["v"],Name (TupleT [BaseT (UintT 256);BaseT (UintT 256)]) "v");
     (["i"],Name (BaseT (UintT 256)) "i")] [] (BaseT (UintT 256))
    (SX_Subscript (SX_Name "v") (SX_Name "i"))
    (JE_Subscript (JE_Name "v" NONE JMissingSource
      (JT_Tuple [JT_Integer 256 F;JT_Integer 256 F]))
      (JE_Name "i" NONE JMissingSource (JT_Integer 256 F)) (JT_Integer 256 F)) =
    SC_Invalid SCErr_Domain
Proof
  EVAL_TAC
QED

Theorem source_ordinary_array_index_dynamic:
  source_ordinary_test env
    [(["v"],Name (ArrayT (BaseT (UintT 256)) (Fixed 2)) "v");
     (["i"],Name (BaseT (UintT 256)) "i")] [] (BaseT (UintT 256))
    (SX_Subscript (SX_Name "v") (SX_Name "i"))
    (JE_Subscript (JE_Name "v" NONE JMissingSource
      (JT_StaticArray (JT_Integer 256 F) 2))
      (JE_Name "i" NONE JMissingSource (JT_Integer 256 F)) (JT_Integer 256 F)) =
    SC_Value (Subscript (BaseT (UintT 256))
      (Name (ArrayT (BaseT (UintT 256)) (Fixed 2)) "v") (Name (BaseT (UintT 256)) "i"))
Proof
  EVAL_TAC
QED

Theorem source_ordinary_tuple_literal_index:
  source_ordinary_test env [] [] (BaseT (UintT 256))
    (SX_Subscript (SX_Tuple [SX_Literal (SCL_Int 4);SX_Literal (SCL_Int 5)])
      (SX_Literal (SCL_Int 1)))
    (JE_Subscript (JE_Tuple [JE_Int 4 (JT_Integer 256 F);JE_Int 5 (JT_Integer 256 F)])
      (JE_Int 1 (JT_Integer 256 F)) (JT_Integer 256 F)) =
    SC_Value (Subscript (BaseT (UintT 256))
      (Builtin (TupleT [BaseT (UintT 256);BaseT (UintT 256)]) (MakeArray NONE (Fixed 2))
        [Literal (BaseT (UintT 256)) (IntL 4);Literal (BaseT (UintT 256)) (IntL 5)])
      (Literal (BaseT (UintT 256)) (IntL 1)))
Proof
  EVAL_TAC >> simp[source_expr_exists_equal] >> EVAL_TAC
QED

Theorem source_ordinary_missing_name:
  source_ordinary_test env [] [] (BaseT (UintT 256)) (SX_Name "missing")
    (JE_Name "missing" NONE JMissingSource (JT_Integer 256 F)) =
  SC_Unsupported (SCS_UnresolvedName ["missing"])
Proof
  EVAL_TAC
QED

Theorem source_ordinary_abi_flag_required:
  source_ordinary_test env
    [(["x"],Name (BaseT (UintT 256)) "x");(["flag"],Name (BaseT BoolT) "flag")] []
    (BaseT (BytesT (Dynamic 32)))
    (SX_Call (SX_Name "abi_encode") [SX_Name "x"] [("ensure_tuple",SX_Name "flag")])
    (JE_Call (JE_Name "abi_encode" NONE JMissingSource JT_None)
      [JE_Name "x" NONE JMissingSource (JT_Integer 256 F)]
      [JKeyword "ensure_tuple" (JE_Name "flag" NONE JMissingSource (JT_Named NONE "bool"))]
      (JT_Bytes 32) JMissingSource) = SC_Invalid SCErr_Domain
Proof
  EVAL_TAC
QED

Theorem source_ordinary_residual_invalid_child:
  source_ordinary_test env [] [] (BaseT (UintT 256))
    (SX_Call (SX_Name "floor")
      [SX_Binary SCB_FloorDiv (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 0))] [])
    (JE_Call (JE_Name "floor" NONE JMissingSource JT_None)
      [JE_BinOp (JE_Int 1 (JT_Integer 256 F)) JBop_FloorDiv
        (JE_Int 0 (JT_Integer 256 F)) (JT_Integer 256 F)] []
      (JT_Integer 256 F) JMissingSource) = SC_Invalid SCErr_ZeroDivisor
Proof
  EVAL_TAC
QED

(* The existing nested_pop fixture: HashMap root is a place with NoneT,
   while the normalized receiver is a dynamic array. The ordinary bridge must
   not demand standalone source typing of that root. *)
Definition source_ordinary_nested_pop_test_def:
  source_ordinary_nested_pop_test env index annotated_index =
    source_ordinary_test env
      [(["self";"items"],TopLevelName NoneT (NONE,"items"));
       (["bucket"],Name (BaseT (UintT 256)) "bucket")] [] (BaseT (UintT 256))
      (SX_Call (SX_Attribute
        (SX_Subscript (SX_Attribute (SX_Name "self") "items") index) "pop") [] [])
      (JE_Call (JE_Attribute
        (JE_Subscript
          (JE_Attribute (JE_Name "self" NONE JMissingSource JT_None) "items"
            NONE NONE NONE JMissingSource JT_None)
          annotated_index (JT_DynArray (JT_Integer 256 F) 4))
        "pop" NONE NONE NONE JMissingSource JT_None)
        [] [] (JT_Integer 256 F) JMissingSource)
End

Theorem source_ordinary_nested_pop_dynamic:
  source_ordinary_nested_pop_test env (SX_Name "bucket")
    (JE_Name "bucket" NONE JMissingSource (JT_Integer 256 F)) =
  SC_Value (Pop (BaseT (UintT 256))
    (SubscriptTarget (TopLevelNameTarget (NONE,"items"))
      (Name (BaseT (UintT 256)) "bucket")))
Proof
  EVAL_TAC
QED

Theorem source_ordinary_nested_pop_normalized_index:
  source_ordinary_nested_pop_test env
    (SX_Binary SCB_Add (SX_Literal (SCL_Int 3)) (SX_Literal (SCL_Int 4)))
    (JE_BinOp (JE_Int 3 (JT_Integer 256 F)) JBop_Add
      (JE_Int 4 (JT_Integer 256 F)) (JT_Integer 256 F)) =
  SC_Value (Pop (BaseT (UintT 256))
    (SubscriptTarget (TopLevelNameTarget (NONE,"items"))
      (Literal (BaseT (UintT 256)) (IntL 7))))
Proof
  EVAL_TAC
QED

Theorem source_ordinary_nested_pop_poison_index:
  source_ordinary_nested_pop_test env
    (SX_Binary SCB_Add (SX_Literal (SCL_Int 3)) (SX_Literal (SCL_Int 4)))
    (JE_Folded (JE_BinOp (JE_Int 3 (JT_Integer 256 F)) JBop_Add
      (JE_Int 4 (JT_Integer 256 F)) (JT_Integer 256 F))
      (JE_Name "poison" NONE JMissingSource JT_None)) =
  SC_Value (Pop (BaseT (UintT 256))
    (SubscriptTarget (TopLevelNameTarget (NONE,"items"))
      (Literal (BaseT (UintT 256)) (IntL 7))))
Proof
  EVAL_TAC
QED

Theorem source_ordinary_nested_pop_invalid_index:
  source_ordinary_nested_pop_test env
    (SX_Binary SCB_FloorDiv (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 0)))
    (JE_BinOp (JE_Int 1 (JT_Integer 256 F)) JBop_FloorDiv
      (JE_Int 0 (JT_Integer 256 F)) (JT_Integer 256 F)) =
  SC_Invalid SCErr_ZeroDivisor
Proof
  EVAL_TAC
QED

Theorem source_ordinary_nested_method_not_generalized:
  ~source_ordinary_callable [[("items",["items"])]] [(["items"],SR_Dynamic)]
    [(["items"],SE_Runtime (Name NoneT "items"))]
    (SX_Attribute (SX_Subscript (SX_Name "items") (SX_Literal (SCL_Int 7))) "other")
Proof
  EVAL_TAC
QED

Theorem source_ordinary_nested_pop_missing_root:
  ~source_ordinary_callable [] [] []
    (SX_Attribute (SX_Subscript (SX_Name "items") (SX_Literal (SCL_Int 7))) "pop") /\
  ~source_ordinary_callable [[("items",["shadow"])]]
    [(["shadow"],SR_Constant);(["items"],SR_Dynamic)]
    [(["items"],SE_Runtime (Name NoneT "items"))]
    (SX_Attribute (SX_Subscript (SX_Name "items") (SX_Literal (SCL_Int 7))) "pop")
Proof
  EVAL_TAC
QED

(* Inherited dispatch only: the very same child is Source-normalized, and
   rejected on invalid constants. No scalar builtin evaluation is added. *)
Definition source_ordinary_residual_test_def:
  source_ordinary_residual_test env sending original annotated =
    let name = if sending then "send" else "unsafe_add";
        ty = if sending then NoneT else BaseT (UintT 256);
        jt = if sending then JT_None else JT_Integer 256 F;
        argty = if sending then BaseT AddressT else BaseT (UintT 256);
        jat = if sending then JT_Named NONE "address" else JT_Integer 256 F in
    source_ordinary_test env [(["x"],Name argty "x")] [] ty
      (SX_Call (SX_Name name) [SX_Name "x";original] [])
      (JE_Call (JE_Name name (SOME "builtin_function") JMissingSource JT_None)
        [JE_Name "x" NONE JMissingSource jat;annotated] [] jt JMissingSource)
End

Theorem source_ordinary_residual_normalized_child:
  source_ordinary_residual_test env F
    (SX_Binary SCB_Add (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 2)))
    (JE_BinOp (JE_Int 1 (JT_Integer 256 F)) JBop_Add
      (JE_Int 2 (JT_Integer 256 F)) (JT_Integer 256 F)) =
    SC_Value (Builtin (BaseT (UintT 256)) (Bop UnsafeAdd)
      [Name (BaseT (UintT 256)) "x";Literal (BaseT (UintT 256)) (IntL 3)]) /\
  source_ordinary_residual_test env T
    (SX_Binary SCB_Add (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 2)))
    (JE_BinOp (JE_Int 1 (JT_Integer 256 F)) JBop_Add
      (JE_Int 2 (JT_Integer 256 F)) (JT_Integer 256 F)) =
    SC_Value (Call NoneT (Send F)
      [Name (BaseT AddressT) "x";Literal (BaseT (UintT 256)) (IntL 3)] NONE)
Proof
  EVAL_TAC
QED

Theorem source_ordinary_residual_poison_child:
  source_ordinary_residual_test env sending
    (SX_Binary SCB_Add (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 2)))
    (JE_Folded (JE_BinOp (JE_Int 1 (JT_Integer 256 F)) JBop_Add
      (JE_Int 2 (JT_Integer 256 F)) (JT_Integer 256 F)) replacement) =
  source_ordinary_residual_test env sending
    (SX_Binary SCB_Add (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 2)))
    (JE_BinOp (JE_Int 1 (JT_Integer 256 F)) JBop_Add
      (JE_Int 2 (JT_Integer 256 F)) (JT_Integer 256 F))
Proof
  Cases_on `sending` >> EVAL_TAC
QED

Theorem source_ordinary_residual_invalid_constant:
  source_ordinary_residual_test env sending
    (SX_Binary SCB_FloorDiv (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 0)))
    (JE_BinOp (JE_Int 1 (JT_Integer 256 F)) JBop_FloorDiv
      (JE_Int 0 (JT_Integer 256 F)) (JT_Integer 256 F)) =
    SC_Invalid SCErr_ZeroDivisor
Proof
  Cases_on `sending` >> EVAL_TAC
QED

Theorem source_ordinary_residual_identity_boundary:
  ~source_ordinary_residual_callable scopes (SX_Name "send")
    (JE_Name "unsafe_add" (SOME "builtin_function") src ty) /\
  ~source_ordinary_residual_callable scopes (SX_Name "send")
    (JE_Name "send" NONE src ty) /\
  ~source_ordinary_residual_callable scopes (SX_Name "unknown")
    (JE_Name "unknown" (SOME "builtin_function") src ty) /\
  (source_resolve_lexical scopes "send" = SOME path ==>
    ~source_ordinary_residual_callable scopes (SX_Name "send")
      (JE_Name "send" (SOME "builtin_function") src ty))
Proof
  simp[source_ordinary_residual_callable_def,source_ordinary_residual_builtins_def]
QED

Theorem source_ordinary_residual_shadow_and_unknown:
  source_ordinary_test env [(["unsafe_add"],Name NoneT "unsafe_add")] [] NoneT
    (SX_Call (SX_Name "unsafe_add") [] [])
    (JE_Call (JE_Name "unsafe_add" (SOME "builtin_function") JMissingSource JT_None)
      [] [] JT_None JMissingSource) = SC_Invalid SCErr_Domain /\
  source_ordinary_test env [] [] NoneT (SX_Call (SX_Name "unknown") [] [])
    (JE_Call (JE_Name "unknown" (SOME "builtin_function") JMissingSource JT_None)
      [] [] JT_None JMissingSource) = SC_Invalid SCErr_Domain
Proof
  EVAL_TAC
QED

Theorem source_ordinary_residual_excludes_migrated_names:
  EVERY (\name. ~MEM name source_ordinary_residual_builtins)
    ["method_id";"abi_encode";"abi_decode";"_abi_encode";"_abi_decode";
     "raw_call";"raw_revert";"len";"concat";"keccak256";"sha256";"convert";
     "min";"max";"abs";"pow_mod256";"uint256_addmod";"uint256_mulmod";
     "slice";"empty";"min_value";"max_value";"range"]
Proof
  EVAL_TAC
QED

(* These are inherited designators, not new Source builtin/type semantics. *)
Definition source_ordinary_epsilon_test_def:
  source_ordinary_epsilon_test env descriptor =
    source_ordinary_expr 12 (source_expr_witness_env env ([]:(string list # expr) list))
      [[("decimal",["decimal"])]] [(["decimal"],SR_Type)] []
      [(["decimal"],SE_Type (BaseT DecimalT))] (0,NONE,[],[],[],[],[])
      (BaseT DecimalT) (SX_Call (SX_Name "epsilon") [SX_Name "decimal"] [])
      (JE_Call (JE_Name "epsilon" (SOME "builtin_function") JMissingSource JT_None)
        [descriptor] [] (JT_Named NONE "decimal") JMissingSource)
End

Theorem source_ordinary_epsilon_descriptor:
  source_ordinary_epsilon_test env (JE_Name "decimal" (SOME "decimal") JMissingSource JT_None) =
    SC_Value (TypeBuiltin (BaseT DecimalT) Epsilon (BaseT DecimalT) []) /\
  source_ordinary_epsilon_test env
    (JE_Folded (JE_Name "decimal" (SOME "decimal") JMissingSource JT_None) replacement) =
    SC_Value (TypeBuiltin (BaseT DecimalT) Epsilon (BaseT DecimalT) [])
Proof
  EVAL_TAC
QED

Theorem source_ordinary_epsilon_descriptor_mismatch:
  source_ordinary_epsilon_test env
    (JE_Name "uint256" (SOME "integer") JMissingSource JT_None) = SC_Invalid SCErr_Domain
Proof
  EVAL_TAC
QED

Definition source_ordinary_environment_test_def:
  source_ordinary_environment_test env runtime root attr ty jt =
    source_ordinary_test env runtime [] ty (SX_Attribute (SX_Name root) attr)
      (JE_Attribute (JE_Name root NONE JMissingSource (JT_Named NONE root))
        attr NONE (SOME root) NONE JMissingSource jt)
End

Theorem source_ordinary_environment_retained:
  source_ordinary_environment_test env [] "block" "number" (BaseT (UintT 256)) (JT_Integer 256 F) =
    SC_Value (Builtin (BaseT (UintT 256)) (Env BlockNumber) []) /\
  source_ordinary_environment_test env [] "tx" "origin" (BaseT AddressT) (JT_Named NONE "address") =
    SC_Value (Builtin (BaseT AddressT) (Env TxOrigin) []) /\
  source_ordinary_environment_test env [] "chain" "id" (BaseT (UintT 256)) (JT_Integer 256 F) =
    SC_Value (Builtin (BaseT (UintT 256)) (Env ChainId) [])
Proof
  EVAL_TAC
QED

Theorem source_ordinary_environment_identity_boundary:
  ~source_ordinary_environment_designator scopes (SX_Name "block")
    (JE_Name "tx" NONE src (JT_Named NONE "block")) /\
  ~source_ordinary_environment_designator scopes (SX_Name "block")
    (JE_Name "block" (SOME "module") src (JT_Named NONE "block")) /\
  ~source_ordinary_environment_designator scopes (SX_Name "block")
    (JE_Name "block" NONE src JT_None) /\
  ~source_ordinary_environment_designator scopes (SX_Name "unknown")
    (JE_Name "unknown" NONE src (JT_Named NONE "unknown")) /\
  (source_resolve_lexical scopes "block" = SOME path ==>
    ~source_ordinary_environment_designator scopes (SX_Name "block")
      (JE_Name "block" NONE src (JT_Named NONE "block")))
Proof
  simp[source_ordinary_environment_designator_def,source_ordinary_environment_root_def]
QED

(* No lexical binding, even a dangling one, can fall through to spelling-only
   legacy Attribute dispatch. This guard applies to all three namespace roots. *)
Theorem source_ordinary_environment_guard:
  source_ordinary_environment_root receiver /\
  ~source_ordinary_environment_designator scopes receiver abase ==>
  source_ordinary_layer build fuel env scopes table constants bindings ctx expected
    (SX_Attribute receiver name) (JE_Attribute abase attr tc btn btc src ty) =
    SC_Invalid SCErr_Domain
Proof
  simp[source_ordinary_layer_def]
QED

Theorem source_ordinary_environment_shadow_unknown_and_bare:
  source_ordinary_environment_test env [( ["block"],Name NoneT "block")]
    "block" "number" (BaseT (UintT 256)) (JT_Integer 256 F) = SC_Invalid SCErr_Domain /\
  source_ordinary_environment_test env [] "unknown" "number"
    (BaseT (UintT 256)) (JT_Integer 256 F) =
    SC_Unsupported (SCS_UnresolvedName ["unknown"]) /\
  source_ordinary_test env [] [] NoneT (SX_Name "block")
    (JE_Name "block" NONE JMissingSource (JT_Named NONE "block")) =
    SC_Unsupported (SCS_UnresolvedName ["block"])
Proof
  EVAL_TAC
QED

(* Constant siblings are still normalized from originals. Replacement poison
   below cannot enter either the environment designator or the parent AST. *)
Definition source_ordinary_environment_parent_test_def:
  source_ordinary_environment_parent_test env original annotated =
    source_ordinary_test env [] [] (BaseT (UintT 256))
      (SX_Binary SCB_Add (SX_Attribute (SX_Name "block") "number") original)
      (JE_BinOp (JE_Attribute
        (JE_Name "block" NONE JMissingSource (JT_Named NONE "block")) "number"
        (SOME "integer") (SOME "block") NONE JMissingSource (JT_Integer 256 F))
        JBop_Add annotated (JT_Integer 256 F))
End

Theorem source_ordinary_environment_parent_poison:
  source_ordinary_environment_parent_test env
    (SX_Binary SCB_Add (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 2)))
    (JE_Folded (JE_BinOp (JE_Int 1 (JT_Integer 256 F)) JBop_Add
      (JE_Int 2 (JT_Integer 256 F)) (JT_Integer 256 F)) replacement) =
    SC_Value (Builtin (BaseT (UintT 256)) (Bop Add)
      [Builtin (BaseT (UintT 256)) (Env BlockNumber) [];
       Literal (BaseT (UintT 256)) (IntL 3)])
Proof
  EVAL_TAC
QED

Theorem source_ordinary_environment_parent_invalid:
  source_ordinary_environment_parent_test env
    (SX_Binary SCB_FloorDiv (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 0)))
    (JE_Folded (JE_BinOp (JE_Int 1 (JT_Integer 256 F)) JBop_FloorDiv
      (JE_Int 0 (JT_Integer 256 F)) (JT_Integer 256 F)) replacement) =
    SC_Invalid SCErr_ZeroDivisor
Proof
  EVAL_TAC
QED

fun audit_source_ordinary thy =
  List.app (fn (name,th) =>
    let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
    in if null (Thm.hyp th) andalso null axioms andalso
          List.all (fn s => s = "DISK_THM") oracles then ()
       else raise Fail ("ordinary expression kernel audit: " ^ thy ^ "." ^ name)
    end) (DB.thms thy);

val () = List.app audit_source_ordinary
  ["sourceOrdinaryExprDefs","sourceOrdinaryExprElaborate","sourceOrdinaryExprProps"];
