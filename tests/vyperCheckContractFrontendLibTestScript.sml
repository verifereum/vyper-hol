Theory vyperCheckContractFrontendLibTest
Ancestors
  jsonToVyper jsonToVyperExpr jsonAST vyperAST vyperTypeContract
  jsonNominalSources vyperStorage
Libs
  vyperCheckContractFrontendLib vyperConstEvalLib cv_transLib

(* Declare fixtures relative to this source file so holbuild stages them at
   the same relative path and includes their contents in the cache key. *)
fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../tests/fixtures/check_contract"]

(* Branch checks for guarded call dispatch; fixture checks below also exercise
   these paths through the contract checker. Deliberately conflicting metadata
   checks that syntax shortcuts and self/pop keep their original priority. *)
val call_ctx = ``(0, SOME 9, [("lib", 7)], [], [], [], [], [], [], []) :
  int # num option # (string # num) list # string list #
  (string # type) list # ((num option # string) # type) list #
  (((num option # string) # (num option # string)) list) #
  ((num option # string) # literal) list #
  (num # (string # num) list) list #
  ((num option # string) # (expr # json_expr)) list``;
val call_arg = ``Literal (BaseT BoolT) (BoolL T)``;
(* An interface constructor yields its address as a stack value. *)
val iface_result = ``Builtin (BaseT AddressT) (Acc Address) [^call_arg]``;
fun call_name id tc = ``JE_Name ^id ^tc (JExplicitSource 1) JT_None``;
fun call_attr base name tc =
  ``JE_Attribute ^base ^name ^tc NONE NONE JMissingSource JT_None``;
val lib_name = call_name ``"lib"`` ``SOME "module"``;
val self_name = call_name ``"self"`` ``SOME "module"``;
val local_name = call_name ``"xs"`` ``NONE : string option``;
fun check_call_with ctx source_ref label func ret_ty pop_target expected = let
  val translated = bossLib.EVAL
    ``translate_call ^ctx ^func [^call_arg] [] ^ret_ty
        ^source_ref ^pop_target``
in
  if aconv (rhs (concl translated)) expected then ()
  else raise Fail ("translate_call dispatch: " ^ label)
end;
fun check_call label func ret_ty pop_target expected =
  check_call_with call_ctx ``JMissingSource`` label func ret_ty pop_target expected;
fun check_bool_call label func expected =
  check_call label func ``JT_Named NONE "bool"`` ``NONE : (expr # base_assignment_target) option`` expected;
fun internal_call nsid name =
  ``Call (BaseT BoolT) (IntCall (^nsid, ^name)) [^call_arg] NONE``;
val override_call_ctx =
  ``(0, SOME 0, [], [], [], [],
      [((SOME 0, "compute"), (NONE, "compute"))], [], [], []) :
    int # num option # (string # num) list # string list #
    (string # type) list # ((num option # string) # type) list #
    (((num option # string) # (num option # string)) list) #
    ((num option # string) # literal) list #
    (num # (string # num) list) list #
  ((num option # string) # (expr # json_expr)) list``;
val _ = check_call_with override_call_ctx ``JExplicitSource 0``
  "abstract call links to concrete override"
  (call_attr self_name ``"compute"`` ``NONE : string option``)
  ``JT_Named NONE "bool"`` ``NONE : (expr # base_assignment_target) option``
  (internal_call ``NONE : num option`` ``"compute"``);
val _ = check_bool_call "interface before builtin"
  (call_name ``"len"`` ``SOME "interface"``) iface_result;
val _ = app (fn tc => check_bool_call "builtin with negative interface tag"
  (call_name ``"len"`` tc) ``Builtin (BaseT BoolT) Len [^call_arg]``)
  [``NONE : string option``, ``SOME "interfaces"``];
val rejected = rhs (concl (EVAL ``rejected_expr``));
(* A bare-name call is always a builtin in Vyper (functions are called through
   self), so an unknown name is rejected rather than read as an internal call. *)
val _ = app (fn tc => check_bool_call "non-interface name"
  (call_name ``"unknown"`` tc) rejected)
  [``NONE : string option``, ``SOME "interfaces"``, ``SOME "module"``];
val _ = app (fn name => check_bool_call "unsupported builtin" (call_name name
  ``SOME "builtin_function"``) rejected)
  [``"print"``, ``"breakpoint"``, ``"shift"``];
val _ = app (fn shortcut => check_bool_call "interface shortcut before self"
  (call_attr self_name shortcut ``NONE : string option``) iface_result)
  [``"__at__"``, ``"__interface__"``];
val _ = check_bool_call "near shortcut name"
  (call_attr self_name ``"__at"`` ``SOME "interface"``)
  (internal_call ``SOME 9`` ``"__at"``);
(* A tuple literal takes its type from the node's annotation (Vyper types it
   by its context, so a member may be wider than its element), and falls back
   to the element types when the annotation is missing or doesn't fit. *)
fun check_tuple_type label ty expected = let
  val translated = bossLib.EVAL
    ``expr_type (translate_expr ^call_ctx
        (JE_Tuple [JE_Str 1 "x"; JE_Int 1 (JT_Integer 256 F)] ^ty))``
in
  if aconv (rhs (concl translated)) expected then ()
  else raise Fail ("tuple literal type: " ^ label)
end;
val _ = check_tuple_type "annotated"
  ``JT_Tuple [JT_String 10; JT_Integer 256 F]``
  ``TupleT [BaseT (StringT 10); BaseT (UintT 256)]``;
val _ = check_tuple_type "missing annotation" ``JT_None``
  ``TupleT [BaseT (StringT 1); BaseT (UintT 256)]``;
val _ = check_tuple_type "wrong arity" ``JT_Tuple [JT_String 10]``
  ``TupleT [BaseT (StringT 1); BaseT (UintT 256)]``;
fun pop_call base = call_attr base ``"pop"`` ``SOME "interface"``;
fun check_pop label base expected = let
  val func = pop_call base
  val translated = bossLib.EVAL
    ``translate_expr ^call_ctx
        (JE_Call ^func [JE_Bool T] [] (JT_Named NONE "bool") JMissingSource)``
in
  if aconv (rhs (concl translated)) expected then ()
  else raise Fail ("pop receiver translation: " ^ label)
end;
val _ = check_pop "pop before interface"
  local_name ``Pop (BaseT BoolT) (NameTarget "xs")``;
val _ = check_pop "pop self uses current module"
  (call_attr self_name ``"xs"`` ``NONE : string option``)
  ``Pop (BaseT BoolT) (TopLevelNameTarget (SOME 9, "xs"))``;
val _ = check_pop "pop module uses canonical alias"
  (call_attr lib_name ``"xs"`` ``NONE : string option``)
  ``Pop (BaseT BoolT) (TopLevelNameTarget (SOME 7, "xs"))``;
val _ = app (fn tc => check_pop "pop ordinary attribute negative tag/name"
  (call_attr (call_name ``"selfish"`` tc) ``"xs"`` ``NONE : string option``)
  ``Pop (BaseT BoolT) (AttributeTarget (NameTarget "selfish") "xs")``)
  [``NONE : string option``, ``SOME "modules"``];
val subscript_base =
  ``JE_Subscript ^local_name (JE_Int 7 (JT_Integer 256 F)) JT_None``;
val subscript_target =
  ``SubscriptTarget (NameTarget "xs") (Literal (BaseT (UintT 256)) (IntL 7))``;
val _ = check_call "pop translated target" (pop_call subscript_base)
  ``JT_Named NONE "bool"``
  ``SOME (Name (BaseT BoolT) "xs", ^subscript_target)``
  ``Pop (BaseT BoolT) ^subscript_target``;
val _ = check_pop "pop translates subscript index" subscript_base
  ``Pop (BaseT BoolT) ^subscript_target``;
val _ = check_pop "pop nested subscript"
  ``JE_Subscript ^subscript_base (JE_Int 2 (JT_Integer 256 F)) JT_None``
  ``Pop (BaseT BoolT) (SubscriptTarget ^subscript_target
      (Literal (BaseT (UintT 256)) (IntL 2)))``;
val _ = check_pop "pop attribute of subscript"
  (call_attr subscript_base ``"items"`` ``NONE : string option``)
  ``Pop (BaseT BoolT) (AttributeTarget ^subscript_target "items")``;
val _ = check_pop "pop fallback" ``JE_Bool T``
  (internal_call ``NONE : num option`` ``"pop"``);
val _ = check_bool_call "self call before interface fallback"
  (call_attr self_name ``"foo"`` ``SOME "interface"``)
  (internal_call ``SOME 9`` ``"foo"``);
val _ = check_bool_call "module interface fallback"
  (call_attr lib_name ``"Foo"`` ``SOME "interface"``) iface_result;
val _ = check_bool_call "module alias fallback"
  (call_attr lib_name ``"foo"`` ``SOME "interfaces"``)
  (internal_call ``SOME 7`` ``"foo"``);
val _ = app (fn tc => check_bool_call "module negative tag"
  (call_attr (call_name ``"lib"`` tc) ``"foo"`` ``NONE : string option``)
  (internal_call ``SOME 9`` ``"foo"``))
  [``NONE : string option``, ``SOME "modules"``];
val nested_module = call_attr lib_name ``"nested"`` ``SOME "module"``;
val _ = check_bool_call "unmapped module alias source fallback"
  (call_attr (call_name ``"other"`` ``SOME "module"``)
    ``"foo"`` ``NONE : string option``)
  (internal_call ``SOME 3`` ``"foo"``);
val _ = check_bool_call "nested module fallback"
  (call_attr nested_module ``"foo"`` ``NONE : string option``)
  (internal_call ``SOME 9`` ``"foo"``);
val _ = check_bool_call "non-attribute fallback" ``JE_Bool T``
  (internal_call ``SOME 9`` ``""``);
val _ = check_call "module struct constructor source recovery"
  (call_attr lib_name ``"Record"`` ``NONE : string option``)
  ``JT_Struct NONE "Record"`` ``NONE : (expr # base_assignment_target) option``
  ``StructLit (StructT (SOME 3, "Record")) (SOME 3, "Record") []``;
val _ = check_call "module struct constructor explicit source"
  (call_attr lib_name ``"Record"`` ``NONE : string option``)
  ``JT_Struct (SOME 2) "Record"`` ``NONE : (expr # base_assignment_target) option``
  ``StructLit (StructT (SOME 4, "Record")) (SOME 4, "Record") []``;
val _ = check_call "module function returning struct"
  (call_attr lib_name ``"foo"`` ``NONE : string option``)
  ``JT_Struct NONE "Record"`` ``NONE : (expr # base_assignment_target) option``
  ``Call (StructT (SOME 9, "Record")) (IntCall (SOME 7, "foo")) [^call_arg] NONE``;

(* Abstract functions are compile-time holes. Translation must link calls to
   the concrete override, remove the ellipsis body from executable modules,
   and reject malformed override declarations before contract checking. *)
val abstract_u256_fn =
  ``JTL_FunctionDef "compute" ["abstract"] []
      [JArg "x" (JT_Integer 256 F) (JTA_Integer 256 F)] []
      (JFuncType [JT_Integer 256 F] (JT_Integer 256 F))
      (JTA_Integer 256 F) [JS_Expr JE_Ellipsis]``;
val concrete_u256_fn =
  ``JTL_FunctionDef "compute" ["override"] ["base"]
      [JArg "x" (JT_Integer 256 F) (JTA_Integer 256 F)] []
      (JFuncType [JT_Integer 256 F] (JT_Integer 256 F))
      (JTA_Integer 256 F)
      [JS_Return (SOME (JE_Name "x" NONE JMissingSource
        (JT_Integer 256 F)))]``;
val mismatched_u256_fn =
  ``JTL_FunctionDef "compute" ["override"] ["base"]
      [JArg "y" (JT_Integer 256 F) (JTA_Integer 256 F)] []
      (JFuncType [JT_Integer 256 F] (JT_Integer 256 F))
      (JTA_Integer 256 F)
      [JS_Return (SOME (JE_Name "y" NONE JMissingSource
        (JT_Integer 256 F)))]``;
val import_base =
  ``JTL_Import [JImportInfo "base" 0 "base" "base.vy"]``;
val initialize_base =
  ``JTL_InitializesDecl
      (JE_Name "base" (SOME "module") (JExplicitSource 0) JT_None)``;
fun abstract_link_ast main_body imported_body =
  ``JAnnotatedAST (JModule (-1) F ^main_body)
      [JImportedModule 0 "base.vy" "base.vy" F ^imported_body]``;
fun assert_translation label expect_some ast = let
  val th = bossLib.EVAL ``translate_annotated_ast ^ast``
  val translated = rhs (concl th)
  val actual_some = optionSyntax.is_some translated
in
  if actual_some = expect_some then ()
  else raise Fail ("abstract frontend disposition: " ^ label)
end;
val valid_abstract_ast =
  abstract_link_ast
    ``[^import_base; ^initialize_base; ^concrete_u256_fn]``
    ``[^abstract_u256_fn]``;
val _ = assert_translation "valid override" true valid_abstract_ast;
val _ = assert_translation "override without initializes" false
  (abstract_link_ast ``[^import_base; ^concrete_u256_fn]``
    ``[^abstract_u256_fn]``);
val _ = assert_translation "parameter-name mismatch" false
  (abstract_link_ast
    ``[^import_base; ^initialize_base; ^mismatched_u256_fn]``
    ``[^abstract_u256_fn]``);
val _ = assert_translation "unimplemented abstract function" false
  (abstract_link_ast ``[^import_base]`` ``[^abstract_u256_fn]``);

(* Override variance is recursive, including tuple members and nested arrays. *)
Theorem abstract_override_tuple_variance:
  json_type_supertype
    (JT_Tuple [JT_String 10; JT_DynArray (JT_Tuple [JT_Bytes 8]) 4])
    (JT_Tuple [JT_String 5; JT_DynArray (JT_Tuple [JT_Bytes 4]) 2]) ∧
  ¬json_type_supertype
    (JT_Tuple [JT_String 5]) (JT_Tuple [JT_String 10]) ∧
  ¬json_type_supertype
    (JT_Tuple [JT_String 10]) (JT_Tuple [JT_String 5; JT_Integer 256 F])
Proof
  EVAL_TAC
QED

fun tuple_return_fn decs aliases bound =
  ``JTL_FunctionDef "compute" ^decs ^aliases [] []
      (JFuncType [] (JT_Tuple [JT_String ^bound; JT_Integer 256 F]))
      (JTA_Tuple [JTA_String (JE_Int (&^bound) (JT_Integer 256 F));
        JTA_Integer 256 F])
      [JS_Return (SOME (JE_Tuple [JE_Str 1 "x";
        JE_Int 1 (JT_Integer 256 F)] JT_None))]``;
val tuple_abstract = tuple_return_fn ``["abstract"]`` ``[] : string list`` ``10``;
val tuple_override = tuple_return_fn ``["override"]`` ``["base"]`` ``5``;
val _ = assert_translation "covariant tuple return" true
  (abstract_link_ast ``[^import_base; ^initialize_base; ^tuple_override]``
    ``[^tuple_abstract]``);
val _ = assert_translation "incompatible tuple return" false
  (abstract_link_ast
    ``[^import_base; ^initialize_base;
       ^(tuple_return_fn ``["override"]`` ``["base"]`` ``20``)]``
    ``[^tuple_abstract]``);

fun default_u256_fn decs aliases default =
  ``JTL_FunctionDef "compute" ^decs ^aliases
      [JArg "x" (JT_Integer 256 F) (JTA_Integer 256 F)] [^default]
      (JFuncType [JT_Integer 256 F] (JT_Integer 256 F))
      (JTA_Integer 256 F)
      [JS_Return (SOME (JE_Name "x" NONE JMissingSource
        (JT_Integer 256 F)))]``;
fun constant_default alias =
  ``JE_Attribute
      (JE_Name ^alias (SOME "module") JMissingSource JT_None)
      "VALUE" NONE NONE NONE JMissingSource (JT_Integer 256 F)``;
val default_constants =
  ``[JTL_VariableDecl "VALUE" (JT_Integer 256 F) (JTA_Integer 256 F)
      F F F F (SOME (JE_Int 7 (JT_Integer 256 F)))]``;
val alias_abstract = default_u256_fn ``["abstract"]`` ``[] : string list``
  (constant_default ``"c1"``);
val alias_override = default_u256_fn ``["override"]`` ``["base"]``
  (constant_default ``"c2"``);
fun alias_default_ast override_constant_src =
  ``JAnnotatedAST
      (JModule (-1) F
        [JTL_Import [JImportInfo "base" 1 "base" "base.vy";
          JImportInfo "c2" ^override_constant_src "constants"
            (if ^override_constant_src = 0 then "constants.vy" else "other.vy")];
         ^initialize_base; ^alias_override])
      [JImportedModule 0 "constants.vy" "constants.vy" F ^default_constants;
       JImportedModule 2 "other.vy" "other.vy" F ^default_constants;
       JImportedModule 1 "base.vy" "base.vy" F
         [JTL_Import [JImportInfo "c1" 0 "constants" "constants.vy"];
          ^alias_abstract]]``;
val _ = assert_translation "same default declaration through different aliases"
  true (alias_default_ast ``0 : int``);
val _ = assert_translation "different declarations with identical default spelling"
  false (alias_default_ast ``2 : int``);
val expression_default =
  ``JE_BinOp (JE_Int 1 (JT_Integer 256 F)) JBop_Add
      (JE_Int 1 (JT_Integer 256 F)) (JT_Integer 256 F)``;
val expression_default_abstract = default_u256_fn ``["abstract"]`` ``[] : string list``
  expression_default;
val expression_default_override = default_u256_fn ``["override"]`` ``["base"]``
  expression_default;
val literal_default_override = default_u256_fn ``["override"]`` ``["base"]``
  ``JE_Int 2 (JT_Integer 256 F)``;
val _ = assert_translation "same default expression"
  true (abstract_link_ast
    ``[^import_base; ^initialize_base; ^expression_default_override]``
    ``[^expression_default_abstract]``);
val _ = assert_translation "equal default values with different syntax"
  false (abstract_link_ast
    ``[^import_base; ^initialize_base; ^literal_default_override]``
    ``[^expression_default_abstract]``);

Theorem abstract_override_resolution_is_transitive:
  resolve_override_aux 3
    [((SOME 2,"compute"),(SOME 1,"compute"));
     ((SOME 1,"compute"),(NONE,"compute"))]
    (SOME 2,"compute") = (NONE,"compute")
Proof
  EVAL_TAC
QED

val address = ``0w : address``;
val fixture_dir = "../tests/fixtures/check_contract/";

val empty_layout = ``<| storage := []; transient := []; code := [] |> :
  json_storage_layout``;
fun prepare_sources sources =
  vyperCheckContractFrontendLib.prepare_translated_input
    {in_deploy = false, address = address, sources = sources,
     import_map = ``[] : (string # num) list``, storage_layout = empty_layout};
fun prepare_ast ast =
  vyperCheckContractFrontendLib.prepare_check_input
    {in_deploy = false, address = address, annotated_ast = ast,
     storage_layout = empty_layout};
fun assert_modules label expected (input : vyperCheckContractLib.check_input) =
  if aconv (#modules input) expected then ()
  else raise Fail ("source normalization: " ^ label ^ "\nexpected " ^
    term_to_string expected ^ "\nactual " ^ term_to_string (#modules input));
fun expect_source_conflict label prepare =
  ((prepare (); raise Fail ("source conflict accepted: " ^ label))
   handle Fail message =>
     if String.isSubstring "conflicting definitions for source ID" message
     then () else raise Fail message);

val nominal_declarations =
  ``[EventDecl "Ping" [(("x", BaseT (UintT 256)), F)];
     StructDecl "Record" [("x", BaseT (UintT 256))];
     FlagDecl "Mode" ["A"; "B"]]``;
val distinct_sources =
  ``[(NONE, []); (SOME 7, ^nominal_declarations); (SOME 2, []);
     (SOME 9, ^nominal_declarations)]``;
val _ = assert_modules "first occurrence order and distinct nominal identities"
  distinct_sources
  (prepare_sources
    ``[(NONE, []); (SOME 7, ^nominal_declarations); (SOME 2, []);
       (SOME 7, ^nominal_declarations); (SOME 9, ^nominal_declarations);
       (SOME 2, []); (NONE, [])]``);
val _ = assert_modules "normalization is idempotent" distinct_sources
  (prepare_sources (#modules (prepare_sources distinct_sources)));
val _ = assert_modules "closed source expressions still evaluate"
  ``[(NONE, []); (SOME 7, ^nominal_declarations)]``
  (prepare_sources
    ``APPEND [(NONE, []); (SOME 7, ^nominal_declarations)]
        [(SOME 7, ^nominal_declarations)]``);
val _ = expect_source_conflict "different declaration bodies" (fn () =>
  prepare_sources
    ``[(NONE, []); (SOME 7, ^nominal_declarations);
       (SOME 7, [FlagDecl "Mode" ["C"]])]``);
val _ = expect_source_conflict "main module collision" (fn () =>
  prepare_sources ``[(NONE, []); (NONE, ^nominal_declarations)]``);
val _ = expect_source_conflict "slot annotation must not erase a conflict"
  (fn () => prepare_sources
    ``[(NONE, []);
       (SOME 7, [VariableDecl (Public F) Storage "x" (BaseT (UintT 256)) (SOME 1)]);
       (SOME 7, [VariableDecl (Public F) Storage "x" (BaseT (UintT 256)) (SOME 2)])]``);

fun repeated_interface_ast first_body second_body =
  ``JAnnotatedAST (JModule 0 F [])
      [JImportedModule 1 "IPing.vyi" "utils/IPing.vyi" F ^first_body;
       JImportedModule 1 "../utils/IPing.vyi" "utils/IPing.vyi" F ^second_body]``;
val interface_event =
  ``[JTL_EventDef "Ping"
      [(JArg "x" (JT_Integer 256 F) (JTA_Integer 256 F), F)]]``;
val interface_stub =
  ``JTL_FunctionDef "ping" ["external"] [] [] []
      (JFuncType [] JT_None) JTA_None [JS_Expr JE_Ellipsis]``;
val _ = expect_source_conflict "annotated interface bodies" (fn () =>
  prepare_ast (repeated_interface_ast interface_event
    ``[JTL_FlagDef "Mode" ["A"]]``));
val _ = expect_source_conflict "empty interface filtering must not erase a conflict"
  (fn () => prepare_ast
    (repeated_interface_ast ``[] : json_toplevel list`` interface_event));
val _ = assert_modules "stub-only interfaces are removed"
  ``[(NONE, [])] : (num option # toplevel list) list``
  (prepare_ast (repeated_interface_ast ``[^interface_stub]``
    ``[^interface_stub]``));
(* Called directly, as by callers that skip prepare_translated_input,
   remove_interface_sources returns one listing per source ID. Listings of
   one module that differ only in their nonreentrancy default both survive
   translation, with equal translated sources. *)
val twice_listed_ast =
  ``JAnnotatedAST (JModule 0 F [])
      [JImportedModule 1 "IPing.vyi" "utils/IPing.vyi" F ^interface_event;
       JImportedModule 1 "IPing.vyi" "utils/IPing.vyi" T ^interface_event]``;
val twice_listed_translation = optionSyntax.dest_some
  (rhs (concl (bossLib.EVAL ``translate_annotated_ast ^twice_listed_ast``)));
fun source_ids translated =
  map (fst o pairSyntax.dest_pair)
    (fst (listSyntax.dest_list (fst (pairSyntax.dest_pair translated))));
val _ = if length (source_ids twice_listed_translation) = 3 then ()
  else raise Fail "twice-listed interface: translation no longer repeats it";
val _ = if length (source_ids
    (vyperCheckContractFrontendLib.remove_interface_sources twice_listed_ast
       twice_listed_translation)) = 2 then ()
  else raise Fail "remove_interface_sources kept a repeated source ID";
val builtin_interfaces =
  ``JAnnotatedAST (JModule 0 F [])
      [JImportedModule (-2) "IERC20.vyi" "builtin/IERC20.vyi" F
         [^interface_stub];
       JImportedModule (-2) "IERC721.vyi" "builtin/IERC721.vyi" F
         [^interface_stub]]``;
val _ = assert_modules "builtin sentinel interfaces remain removable"
  ``[(NONE, [])] : (num option # toplevel list) list``
  (prepare_ast builtin_interfaces);
val _ = assert_modules "builtin sentinel paths keep distinct canonical identities"
  ``[(NONE, []); (SOME 5, ^nominal_declarations);
     (SOME 6, ^nominal_declarations)]``
  (prepare_ast
    ``JAnnotatedAST (JModule 0 F [])
        [JImportedModule (-2) "First.vyi" "builtin/First.vyi" F
           (^interface_event ++
            [JTL_StructDef "Record" [JArg "x" (JT_Integer 256 F) (JTA_Integer 256 F)];
             JTL_FlagDef "Mode" ["A"; "B"]]);
         JImportedModule (-2) "Second.vyi" "builtin/Second.vyi" F
           (^interface_event ++
            [JTL_StructDef "Record" [JArg "x" (JT_Integer 256 F) (JTA_Integer 256 F)];
             JTL_FlagDef "Mode" ["A"; "B"]])]``);

(* Test the body marker independently of declaration-time default types. *)
fun math_function name body =
  ``JTL_FunctionDef ^name ["internal"] []
      [JArg "x" (JT_Integer 256 F) (JTA_Integer 256 F)]
      [JE_Int 1 (JT_Integer 256 F)]
      (JFuncType [JT_Integer 256 F] JT_None) JTA_None ^body``;
fun math_body ty =
  ``[JS_If (JE_Bool T)
      [JS_AnnAssign "y" ^ty (JTA_Integer 256 F) (JE_Int 2 ^ty)] []]``;
val math_declarations =
  ``[^(math_function ``"typed"`` (math_body ``JT_Integer 256 F``));
     ^(math_function ``"untyped"`` (math_body ``JT_None``));
     ^(math_function ``"noop"`` ``[JS_Pass]``)]``;
fun check_math_import path expected =
  let
    val {modules, ...} = prepare_ast
      ``JAnnotatedAST (JModule 0 F [])
          [JImportedModule (-2) ^path ^path F ^math_declarations]``
    val names = rhs (concl (EVAL
      ``MAP (λtop. case top of FunctionDecl _ _ _ _ name _ _ _ _ => name
                    | _ => "") (FLAT (MAP SND ^modules))``))
  in
    if aconv names expected then ()
    else raise Fail ("imported math function filtering: " ^ term_to_string names)
  end;
val _ = check_math_import ``"vyper/builtins/stdlib/math.vy"`` ``["typed"; "noop"]``;
val _ = check_math_import ``"/compiler/vyper/builtins/stdlib/math.vy"``
  ``["typed"; "noop"]``;
val _ = check_math_import ``"local/math.vy"`` ``["typed"; "untyped"; "noop"]``;

(* Generated at VYPER_PIN with `vyper -f annotated_ast,layout
   duplicate_interface/main/c.vy`; resolved paths are relative to the fixture
   root. The compiler repeats IPing, including its nonempty event declaration. *)
val duplicate_path = fixture_dir ^ "duplicate_interface/main/c.json";
val duplicate_ast = JSONDecode.decodeFile jsonASTLib.annotated_ast duplicate_path;
val duplicate_translation = optionSyntax.dest_some
  (rhs (concl (bossLib.EVAL ``translate_annotated_ast ^duplicate_ast``)));
val (duplicate_sources, duplicate_rest) = pairSyntax.dest_pair duplicate_translation;
val (_, duplicate_import_map) = pairSyntax.dest_pair duplicate_rest;
val (duplicate_entries, duplicate_source_ty) = listSyntax.dest_list duplicate_sources;
(* Translation keeps one listing of the repeated interface, in import order. *)
val duplicate_ids = listSyntax.mk_list
  (map (fst o pairSyntax.dest_pair) duplicate_entries,
   fst (pairSyntax.dest_prod duplicate_source_ty));
val expected_duplicate_sources =
  if aconv duplicate_ids ``[NONE; SOME 3; SOME 4]`` then duplicate_sources
  else raise Fail ("duplicate interface fixture has unexpected sources " ^
    term_to_string duplicate_ids);
val duplicate_input = prepare_ast duplicate_ast;
val _ = assert_modules "annotated repro keeps one listing per module"
  expected_duplicate_sources duplicate_input;
val duplicate_translated_input =
  vyperCheckContractFrontendLib.prepare_translated_input
    {in_deploy = false, address = address, sources = duplicate_sources,
     import_map = duplicate_import_map, storage_layout = empty_layout};
val _ = assert_modules "translated repro agrees with annotated frontend"
  expected_duplicate_sources duplicate_translated_input;
val _ = vyperCheckContractLib.check_contract duplicate_translated_input;

fun check_fixture in_deploy path = let
  val checked = vyperCheckContractFrontendLib.check_contract_file
    {in_deploy = in_deploy, address = address,
     path = fixture_dir ^ path}
  val (_, result) = dest_eq (concl checked)
in
  if optionSyntax.is_some result then ()
  else raise Fail ("frontend contract checker rejected " ^ path)
end;

val _ = check_fixture false "scoped_locals/main.json";
val _ = check_fixture false "simple.json";
(* Generated at VYPER_PIN with vyper -f annotated_ast,layout stdlib_math.vy,
   keeping the builtin path relative to the Vyper installation. The call to
   isqrt leaves sqrt's body untyped in the standalone JSON. *)
val _ = check_fixture false "stdlib_math.json";
val _ = check_fixture true "stdlib_math.json";
(* Named constants fold to literals; slice start bounds remain runtime checks. *)
val _ = check_fixture false "slice_named_start.json";
(* Constant slice lengths fold to literals: a code slice and a narrowing byte
   slice are accepted, as is a runtime length within the source's bound. *)
val _ = check_fixture false "slice_folded_length.json";
val _ = check_fixture false "address_bytes20.json";
val _ = check_fixture true "address_bytes20.json";
val _ = check_fixture false "address_bytes32.json";
val _ = check_fixture true "address_bytes32.json";
val _ = check_fixture false "mutability.json";
val _ = check_fixture false "assert_view_reason.json";
val _ = check_fixture false "raise_view_custom_error.json";
(* The operator forms Vyper accepts next to the ones the checker rejects. *)
val _ = check_fixture false "operator_forms.json";
val _ = check_fixture false "storage.json";
val _ = check_fixture false "decimal_map_key.json";

(* Pinned legacy and Venom bytecode write these slots for decimal_map_key.vy.
   The map's layout slot is 0 and the keys are 1.5 and -1.25. *)
Theorem decimal_map_key_matches_pinned_slots:
  hashmap_slot 0w (encode_hashmap_key (BaseT DecimalT) (DecimalV 15000000000)) =
    0xe57318393fbc3527c4c66c6d13a85c170b8dfa130f80dde3557bf02a721ce1b3w /\
  hashmap_slot 0w (encode_hashmap_key (BaseT DecimalT) (DecimalV (-12500000000))) =
    0x8814a88af2daef0f3a47b81774a1a2e18ae61f89ba56a319073b65ba9b14b6daw
Proof
  CONV_TAC cv_eval
QED
val _ = check_fixture false "imported_struct/main.json";
val _ = check_fixture false "imported_flag/main.json";
(* lib2 reads lib1's constant and main reads lib2's. *)
val _ = check_fixture false "imported_constants/main.json";
val _ = check_fixture true "imported_constants/main.json";
val _ = check_fixture false "imported_interface/main.json";
(* A .vyi stub's defaults (`= []`, `= ""`) are never analysed, so untyped. *)
val _ = check_fixture false "interface_defaults/main.json";
val _ = check_fixture false "duplicate_interface/main/c.json";
val _ = check_fixture false "multimodule_storage/main.json";
val _ = check_fixture false "defaults_control/main.json";
val _ = check_fixture false "transient_storage/main.json";
val _ = check_fixture false "nonreentrant/main.json";
val _ = check_fixture false "nonreentrancy_pragma/main.json";
val _ = check_fixture true "deployment/main.json";
val _ = check_fixture false "imported_deploy/main.json";
val _ = check_fixture true "imported_deploy/main.json";
val _ = check_fixture false "third_party/flex/daddy/daddy.json";
val _ = check_fixture true "third_party/flex/daddy/daddy.json";
val _ = check_fixture false "interface_struct_return/main.json";
val _ = check_fixture false "abi_encode/main.json";
(* Struct and flag declared in an interface and used as I.S / I.Mode in
   storage, HashMap values, empty(), literals and returns. *)
val _ = check_fixture false "interface_struct/main.json";
(* main initializes token, which initializes ownable; main has its own owner. *)
val _ = check_fixture false "nested_initializes/main.json";
val _ = check_fixture true "nested_initializes/main.json";
(* lib_a is reached as `..lib_a` from main and `.lib_a` from lib_b. *)
val _ = check_fixture false "relative_uses/pkg/mocks/main.json";
val _ = check_fixture true "relative_uses/pkg/mocks/main.json";
(* main initializes token and, as `token.ownable`, the module token imports;
   ownable has a variable named `slot`. *)
val _ = check_fixture false "attribute_initializes/main.json";
val _ = check_fixture true "attribute_initializes/main.json";
(* Nothing initializes lib, so it has no storage in the layout; main calls
   its pure helper directly and through mid, which main initializes. *)
val _ = check_fixture false "uninitialized_import/main.json";
val _ = check_fixture true "uninitialized_import/main.json";

(* A code slice needs a compile-time length. *)
val _ =
  ((check_fixture false "slice_code_runtime.json";
    raise Fail "frontend contract checker accepted a runtime-length code slice")
   handle Fail message =>
     if String.isSubstring "check_contract returned NONE" message then ()
     else raise Fail message);

fun check_fixture_rejected path =
  ((check_fixture false path;
    raise Fail ("frontend contract checker accepted " ^ path))
   handle Fail message =>
     if String.isSubstring "check_contract returned NONE" message then ()
     else raise Fail message);

(* Both code generators at the pin reject mutating calls in revert reasons.
   The nested calls check traversal through arguments as well as roots. *)
val _ = app check_fixture_rejected
  ["assert_mutating_reason.json", "raise_mutating_reason.json",
   "assert_mutating_custom_error.json", "raise_mutating_custom_error.json"];

(* A same-named internal function doesn't capture a bare builtin call: Vyper
   compiles these to the builtin (a console call, INVALID, a runtime shift),
   which the frontend doesn't support. *)
val _ = check_fixture_rejected "builtin_shadow_print.json";
val _ = check_fixture_rejected "builtin_shadow_breakpoint.json";
val _ = check_fixture_rejected "builtin_shadow_shift.json";

(* A Decimal node's value is its source span, signs Vyper folded and comments
   included; the values are those the pinned compiler stores. *)
val _ = app (fn (span, expected) =>
    if aconv (rhs (concl (EVAL ``decimal_string_to_int ^(stringSyntax.fromMLstring span)``)))
             expected then ()
    else raise Fail ("decimal span " ^ span))
  [("--1.5", ``15000000000 : int``),
   ("-(-2.25)", ``22500000000 : int``),
   ("-( # e9\n        3.0)", ``-30000000000 : int``),
   ("1.5", ``15000000000 : int``),
   ("-15e-10", ``-15 : int``)];

(* A runtime length bounds the result by the source: Bytes[64] fits a
   Bytes[64] result but not a Bytes[63] one. *)
Theorem slice_runtime_length_source_bound:
  slice_operands_ok (Slice 64)
    [Name (BaseT (BytesT (Dynamic 64))) "b"; Literal (BaseT (UintT 256)) (IntL 0);
     Name (BaseT (UintT 256)) "n"] /\
  ~slice_operands_ok (Slice 63)
    [Name (BaseT (BytesT (Dynamic 64))) "b"; Literal (BaseT (UintT 256)) (IntL 0);
     Name (BaseT (UintT 256)) "n"]
Proof
  EVAL_TAC
QED

(* An inferred struct name declared in two modules keeps no source. *)
Theorem nominal_source_needs_one_declaration:
  resolve_json_type [((StructKind, "S"), 1); ((StructKind, "S"), 1)]
    (JT_Struct NONE "S") = JT_Struct (SOME 1) "S" ∧
  resolve_json_type [((StructKind, "S"), 0); ((StructKind, "S"), 1)]
    (JT_Struct NONE "S") = JT_Struct NONE "S" ∧
  resolve_json_type [((StructKind, "S"), 1)]
    (JT_Flag NONE "S") = JT_Flag NONE "S"
Proof
  EVAL_TAC
QED

fun fixture_input path = vyperCheckContractFrontendLib.prepare_check_input
  {in_deploy = false, address = address,
   annotated_ast = JSONDecode.decodeFile jsonASTLib.annotated_ast
     (fixture_dir ^ path),
   storage_layout = JSONDecode.decodeFile jsonASTLib.storage_layout
     (fixture_dir ^ path)};

(* Vyper reads the denomination from a constant's folded value; the frontend
   substitutes the constant before resolving it, so this one is ether. *)
val _ = check_fixture false "aswei_constant_denomination.json";
val _ = if null (find_terms (aconv ``AsWeiValue Ether``)
                  (#modules (fixture_input "aswei_constant_denomination.json")))
  then raise Fail "as_wei_value constant denomination not read as ether"
  else ();
(* A denomination the frontend can't resolve is rejected, not read as wei. *)
val _ = if aconv (rhs (concl (EVAL
    ``make_builtin_call (BaseT (UintT 256)) "as_wei_value"
        [Name (BaseT (UintT 256)) "amount"; Name (BaseT (StringT 5)) "unit"]
        [] (JT_Integer 256 F)``))) rejected then ()
  else raise Fail "unresolved as_wei_value denomination not rejected";

fun assert_fixture_has path label tm =
  if null (find_terms (aconv tm) (#modules (fixture_input path)))
  then raise Fail (path ^ ": " ^ label) else ();

(* convert(x, T) and abi_decode(x, T) produce a T, not the wider return type
   Vyper annotates the call with: an input longer than T's bound reverts. *)
val _ = check_fixture false "convert_type_argument.json";
val _ = assert_fixture_has "convert_type_argument.json" "convert not at its type argument"
  ``TypeBuiltin (BaseT (StringT 10)) Convert (BaseT (StringT 10))``;
val _ = assert_fixture_has "convert_type_argument.json" "abi_decode not at its type argument"
  ``TypeBuiltin (ArrayT (BaseT (UintT 256)) (Dynamic 3)) (AbiDecode T)
      (ArrayT (BaseT (UintT 256)) (Dynamic 3))``;

(* A field, element or popped value read into a wider context keeps its own
   type; each of these was rejected while typed at the context's. *)
val _ = check_fixture false "member_own_type.json";
val _ = assert_fixture_has "member_own_type.json" "field not at its own type"
  ``Attribute (ArrayT (BaseT (BytesT (Dynamic 5))) (Dynamic 2))``;
val _ = check_fixture false "pop_element_type.json";
val _ = assert_fixture_has "pop_element_type.json" "pop not at the element type"
  ``Pop (BaseT (BytesT (Dynamic 10)))``;

(* Vyper folds a shift amount and annotates a small literal ecrecover v as
   int8; both are accepted. *)
val _ = check_fixture false "shift_folded_amount.json";
val _ = check_fixture false "ecrecover_literal_v.json";

(* A constant may refer to one declared after it: constants are emitted in
   dependency order. *)
val _ = check_fixture false "constant_forward_reference.json";

(* initializes: lib1.lib2 keys its layout "lib2", beside the main module's
   own alias lib2 for lib3. *)
val _ = check_fixture false "initializes_alias_shadow/main.json";

(* lib exports a JSON ABI interface it imports; the JSON source isn't among
   the annotated AST's imports, so the translation is rejected rather than
   exporting a made-up function. *)
val _ = (check_fixture false "export_json_interface/main.json";
         raise Fail "JSON interface export accepted")
  handle Fail message =>
    if String.isSubstring "annotated AST translation rejected" message then ()
    else raise Fail message;

(* token (source 1) nests ownable (source 2) under its own alias; the
   main module's owner keeps its own key. *)
val expected_nested_layout =
  ``[(0w : address,
      ([((NONE, "owner"), 2); ((SOME 4, "owner"), 0);
        ((SOME 3, "supply"), 1)] : storage_layout,
       [] : storage_layout))]``;
val _ = if aconv (#layouts (fixture_input "nested_initializes/main.json"))
                 expected_nested_layout then ()
  else raise Fail "nested storage layout did not resolve the module path";

(* ownable is initialized by main as `token.ownable`, so its variables sit at
   the top of the layout under `ownable`. *)
val attribute_layout = #layouts (fixture_input "attribute_initializes/main.json");
val _ = if aconv attribute_layout
  ``[(0w : address,
      ([((SOME 4, "owner"), 1); ((SOME 4, "slot"), 2); ((NONE, "owner"), 3);
        ((SOME 3, "supply"), 0)] : storage_layout,
       [] : storage_layout))]`` then ()
  else raise Fail ("attribute initializes layout: " ^
    term_to_string attribute_layout);

(* lib_a keeps its source ID 1 (module 3) and is listed once. *)
val relative_uses_modules = #modules (fixture_input "relative_uses/pkg/mocks/main.json");
val _ = if aconv (listSyntax.mk_list
                   (map (fst o pairSyntax.dest_pair)
                     (fst (listSyntax.dest_list relative_uses_modules)),
                    ``:num option``))
                 ``[NONE; SOME 3; SOME 4]`` then ()
  else raise Fail "repeated relative import changed module identity";

val multimodule_path = fixture_dir ^ "multimodule_storage/main.json";
val multimodule_input = vyperCheckContractFrontendLib.prepare_check_input
  {in_deploy = false, address = address,
   annotated_ast = JSONDecode.decodeFile jsonASTLib.annotated_ast
     multimodule_path,
   storage_layout = JSONDecode.decodeFile jsonASTLib.storage_layout
     multimodule_path};
val expected_multimodule_layout =
  ``[(0w : address,
      ([((SOME 3, "stored"), 0)] : storage_layout,
       [] : storage_layout))]``;
val _ = if aconv (#layouts multimodule_input) expected_multimodule_layout then ()
  else raise Fail "multi-module storage layout did not preserve source identity";

val structured = vyperCheckContractFrontendLib.check_contract_result
  {in_deploy = false, address = address,
   annotated_ast = JSONDecode.decodeFile jsonASTLib.annotated_ast
     (fixture_dir ^ "simple.json"),
   storage_layout = JSONDecode.decodeFile jsonASTLib.storage_layout
     (fixture_dir ^ "simple.json")};
val _ = if aconv (#modules structured) (#modules (#input structured)) andalso
               aconv (#layouts structured) (#layouts (#input structured)) andalso
               null (free_vars (#artifact structured))
  then () else raise Fail "structured frontend result is inconsistent";

val missing_layout_input =
  {in_deploy = false, address = address, modules = #modules multimodule_input,
   layouts = ``([] : (address # (storage_layout # storage_layout)) list)``};
val _ =
  ((vyperCheckContractLib.check_contract missing_layout_input;
    raise Fail "checker accepted a contract with a missing imported layout")
   handle Fail message =>
     if String.isSubstring "check_contract returned NONE" message then ()
     else raise Fail message);

(* An ordinary slice keeps the Slice node and folds its closed start and
   length operands. The length determines the result capacity. *)
val slice_uint_json =
  "{\"typeclass\":\"integer\",\"bits\":256,\"is_signed\":false}";
val slice_sum_json =
  "{\"ast_type\":\"BinOp\",\"left\":{\"ast_type\":\"Int\",\"value\":1,\"type\":" ^
  slice_uint_json ^ "},\"op\":{\"ast_type\":\"Add\"},\"right\":{\"ast_type\":\"Int\"," ^
  "\"value\":1,\"type\":" ^ slice_uint_json ^ "},\"type\":" ^ slice_uint_json ^ "}";
val ordinary_slice_ast = JSONDecode.decodeString jsonASTLib.annotated_ast
  ("{\"ast\":{\"body\":[{\"ast_type\":\"FunctionDef\",\"name\":\"test\",\"decorator_list\":[]," ^
   "\"args\":{\"ast_type\":\"arguments\",\"args\":[]},\"func_type\":{\"argument_types\":[],\"return_type\":null}," ^
   "\"body\":[{\"ast_type\":\"Expr\",\"value\":{\"ast_type\":\"Call\",\"func\":{\"ast_type\":\"Name\",\"id\":\"slice\"}," ^
   "\"args\":[{\"ast_type\":\"Name\",\"id\":\"b\",\"type\":{\"name\":\"Bytes\",\"length\":10}}," ^
   slice_sum_json ^ "," ^ slice_sum_json ^ "],\"keywords\":[]," ^
   "\"type\":{\"name\":\"Bytes\",\"length\":2}}}]}]}}");
val expected_ordinary_slice =
  ``JE_Call (JE_Name "slice" NONE JMissingSource JT_None)
      [JE_Name "b" NONE JMissingSource (JT_Bytes 10);
       JE_BinOp (JE_Int 1 (JT_Integer 256 F)) JBop_Add (JE_Int 1 (JT_Integer 256 F))
         (JT_Integer 256 F);
       JE_BinOp (JE_Int 1 (JT_Integer 256 F)) JBop_Add (JE_Int 1 (JT_Integer 256 F))
         (JT_Integer 256 F)] [] (JT_Bytes 2) JMissingSource``;
val () = if not (null (find_terms (aconv expected_ordinary_slice) ordinary_slice_ast))
  then () else raise Fail "ordinary slice decoded unexpectedly";
val () = if aconv (rhs (concl (bossLib.EVAL
    ``translate_expr (module_expr_ctx [] (0:int) NONE [] [] [] []) ^expected_ordinary_slice``)))
  ``Builtin (BaseT (BytesT (Dynamic 2))) (Slice 2)
      [Name (BaseT (BytesT (Dynamic 10))) "b";
       Literal (BaseT (UintT 256)) (IntL 2);
       Literal (BaseT (UintT 256)) (IntL 2)]``
  then () else raise Fail "ordinary slice did not preserve its folded operands";

(* Issue 565: the public getter flag follows the pragma, except for explicit
   reentrant, constant and immutable declarations (g37/g38/g39 controls). *)
Theorem translated_public_variable_getter_flag:
  (case translate_toplevel ni im ec tc nr_default
     (JTL_VariableDecl name ty ann T imm trans reentrant const_val) of
     SOME (VariableDecl vis _ _ _ _) => vis
   | _ => Private) =
  Public (nr_default /\ ~reentrant /\ ~imm /\ const_val = NONE)
Proof
  simp[jsonToVyperTopLevelTheory.translate_toplevel_def]
QED

Theorem translated_public_hashmap_getter_flag:
  (case translate_toplevel ni im ec tc nr_default
     (JTL_HashMapDecl name kt vt T trans reentrant) of
     SOME (HashMapDecl vis _ _ _ _ _) => vis
   | _ => Private) = Public (nr_default /\ ~reentrant)
Proof
  simp[jsonToVyperTopLevelTheory.translate_toplevel_def]
QED

Theorem range_static_folded_endpoints:
  !ctx.
    translate_iter ctx (BaseT (IntT 8))
      (JIter_Range
         [JE_BinOp (JE_Int (-5) (JT_Integer 8 T)) JBop_Add
            (JE_Int 2 (JT_Integer 8 T)) (JT_Integer 8 T);
          JE_Int 127 (JT_Integer 8 T)] NONE) =
    Range (Literal (BaseT (IntT 8)) (IntL (-3)))
          (Literal (BaseT (IntT 8)) (IntL 127))
Proof
  gen_tac >> CONV_TAC EVAL
QED

Theorem range_bounded_folded_endpoint:
  translate_stmt [] [] ^call_ctx
    (JS_For "i" (JT_Integer 8 T) (JTA_Integer 8 T)
       (JIter_Range
          [JE_Name "n" NONE JMissingSource (JT_Integer 8 T);
           JE_BinOp (JE_Int 2 (JT_Integer 8 T)) JBop_Add
             (JE_Int 3 (JT_Integer 8 T)) (JT_Integer 8 T)]
          (SOME (JE_Int 4 (JT_Integer 256 F)))) [JS_Pass]) =
    For "i" (BaseT (IntT 8))
      (Range (Name (BaseT (IntT 8)) "n") (Literal (BaseT (IntT 8)) (IntL 5)))
      4 [Pass]
Proof
  EVAL_TAC
QED
