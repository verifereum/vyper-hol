Theory vyperCheckContractFrontendLibTest
Ancestors
  jsonToVyper jsonToVyperExpr jsonAST vyperAST vyperTypeContract
Libs
  vyperCheckContractFrontendLib

(* Declare fixtures relative to this source file so holbuild stages them at
   the same relative path and includes their contents in the cache key. *)
fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../tests/fixtures/check_contract"]

(* Branch checks for guarded call dispatch; fixture checks below also exercise
   these paths through the contract checker. Deliberately conflicting metadata
   checks that syntax shortcuts and self/pop keep their original priority. *)
val call_ctx = ``(0, SOME 9, [("lib", 7)], [], [], [], []) :
  int # num option # (string # num) list # string list #
  (string # type) list # ((num option # string) # type) list #
  (((num option # string) # (num option # string)) list)``;
val call_arg = ``Literal (BaseT BoolT) (BoolL T)``;
fun call_name id tc = ``JE_Name ^id ^tc (JExplicitSource 1) JT_None``;
fun call_attr base name tc =
  ``JE_Attribute ^base ^name ^tc NONE NONE JMissingSource JT_None``;
val lib_name = call_name ``"lib"`` ``SOME "module"``;
val self_name = call_name ``"self"`` ``SOME "module"``;
val local_name = call_name ``"xs"`` ``NONE : string option``;
fun check_call_with ctx source_ref label func ret_ty pop_idx expected = let
  val translated = bossLib.EVAL
    ``translate_call ^ctx ^func [^call_arg] [] ^ret_ty
        ^source_ref ^pop_idx``
in
  if aconv (rhs (concl translated)) expected then ()
  else raise Fail ("translate_call dispatch: " ^ label)
end;
fun check_call label func ret_ty pop_idx expected =
  check_call_with call_ctx ``JMissingSource`` label func ret_ty pop_idx expected;
fun check_bool_call label func expected =
  check_call label func ``JT_Named NONE "bool"`` ``NONE : expr option`` expected;
fun internal_call nsid name =
  ``Call (BaseT BoolT) (IntCall (^nsid, ^name)) [^call_arg] NONE``;
val override_call_ctx =
  ``(0, SOME 0, [], [], [], [],
      [((SOME 0, "compute"), (NONE, "compute"))]) :
    int # num option # (string # num) list # string list #
    (string # type) list # ((num option # string) # type) list #
    (((num option # string) # (num option # string)) list)``;
val _ = check_call_with override_call_ctx ``JExplicitSource 0``
  "abstract call links to concrete override"
  (call_attr self_name ``"compute"`` ``NONE : string option``)
  ``JT_Named NONE "bool"`` ``NONE : expr option``
  (internal_call ``NONE : num option`` ``"compute"``);
val _ = check_bool_call "interface before builtin"
  (call_name ``"len"`` ``SOME "interface"``) call_arg;
val _ = app (fn tc => check_bool_call "builtin with negative interface tag"
  (call_name ``"len"`` tc) ``Builtin (BaseT BoolT) Len [^call_arg]``)
  [``NONE : string option``, ``SOME "interfaces"``];
val _ = app (fn tc => check_bool_call "non-interface name"
  (call_name ``"unknown"`` tc) (internal_call ``NONE : num option`` ``"unknown"``))
  [``NONE : string option``, ``SOME "interfaces"``, ``SOME "module"``];
val _ = app (fn shortcut => check_bool_call "interface shortcut before self"
  (call_attr self_name shortcut ``NONE : string option``) call_arg)
  [``"__at__"``, ``"__interface__"``];
val _ = check_bool_call "near shortcut name"
  (call_attr self_name ``"__at"`` ``SOME "interface"``)
  (internal_call ``SOME 9`` ``"__at"``);
fun pop_call base = call_attr base ``"pop"`` ``SOME "interface"``;
val _ = check_bool_call "pop before interface"
  (pop_call local_name) ``Pop (BaseT BoolT) (NameTarget "xs")``;
val _ = check_bool_call "pop self before module"
  (pop_call (call_attr self_name ``"xs"`` ``NONE : string option``))
  ``Pop (BaseT BoolT) (TopLevelNameTarget (NONE, "xs"))``;
val _ = check_bool_call "pop module uses raw source, not alias"
  (pop_call (call_attr lib_name ``"xs"`` ``NONE : string option``))
  ``Pop (BaseT BoolT) (TopLevelNameTarget (SOME 3, "xs"))``;
val _ = app (fn tc => check_bool_call "pop ordinary attribute negative tag/name"
  (pop_call (call_attr (call_name ``"selfish"`` tc) ``"xs"`` ``NONE : string option``))
  ``Pop (BaseT BoolT) (AttributeTarget (NameTarget "selfish") "xs")``)
  [``NONE : string option``, ``SOME "modules"``];
val subscript_base = ``JE_Subscript ^local_name (JE_Int 7 JT_None) JT_None``;
val _ = check_bool_call "pop subscript missing index" (pop_call subscript_base)
  ``Pop (BaseT BoolT) (SubscriptTarget (NameTarget "xs") ^call_arg)``;
val _ = check_call "pop subscript translated index" (pop_call subscript_base)
  ``JT_Named NONE "bool"`` ``SOME (Literal (BaseT (UintT 256)) (IntL 7))``
  ``Pop (BaseT BoolT) (SubscriptTarget (NameTarget "xs")
      (Literal (BaseT (UintT 256)) (IntL 7)))``;
val _ = check_bool_call "pop fallback" (pop_call ``JE_Bool T``)
  (internal_call ``NONE : num option`` ``"pop"``);
val _ = check_bool_call "self call before interface fallback"
  (call_attr self_name ``"foo"`` ``SOME "interface"``)
  (internal_call ``SOME 9`` ``"foo"``);
val _ = check_bool_call "module interface fallback"
  (call_attr lib_name ``"Foo"`` ``SOME "interface"``) call_arg;
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
  ``JT_Struct NONE "Record"`` ``NONE : expr option``
  ``StructLit (StructT (SOME 3, "Record")) (SOME 3, "Record") []``;
val _ = check_call "module struct constructor explicit source"
  (call_attr lib_name ``"Record"`` ``NONE : string option``)
  ``JT_Struct (SOME 2) "Record"`` ``NONE : expr option``
  ``StructLit (StructT (SOME 4, "Record")) (SOME 4, "Record") []``;
val _ = check_call "module function returning struct"
  (call_attr lib_name ``"foo"`` ``NONE : string option``)
  ``JT_Struct NONE "Record"`` ``NONE : expr option``
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
      (JTA_Tuple [JTA_String ^bound; JTA_Integer 256 F])
      [JS_Return (SOME (JE_Tuple [JE_Str 1 "x";
        JE_Int 1 (JT_Integer 256 F)]))]``;
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
      F F F (SOME (JE_Int 7 (JT_Integer 256 F)))]``;
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
val folded_default_abstract = default_u256_fn ``["abstract"]`` ``[] : string list``
  ``JE_Folded ^expression_default (JE_Int 2 (JT_Integer 256 F))``;
val expression_default_override = default_u256_fn ``["override"]`` ``["base"]``
  expression_default;
val literal_default_override = default_u256_fn ``["override"]`` ``["base"]``
  ``JE_Int 2 (JT_Integer 256 F)``;
val _ = assert_translation "folding metadata preserves original default structure"
  true (abstract_link_ast
    ``[^import_base; ^initialize_base; ^expression_default_override]``
    ``[^folded_default_abstract]``);
val _ = assert_translation "equal default values with different syntax"
  false (abstract_link_ast
    ``[^import_base; ^initialize_base; ^literal_default_override]``
    ``[^folded_default_abstract]``);

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

fun check_fixture in_deploy path = let
  val checked = vyperCheckContractFrontendLib.check_contract_file
    {in_deploy = in_deploy, address = address,
     path = fixture_dir ^ path}
  val (_, result) = dest_eq (concl checked)
in
  if optionSyntax.is_some result then ()
  else raise Fail ("frontend contract checker rejected " ^ path)
end;

val _ = check_fixture false "simple.json";
val _ = check_fixture false "address_bytes20.json";
val _ = check_fixture true "address_bytes20.json";
val _ = check_fixture false "storage.json";
val _ = check_fixture false "imported_struct/main.json";
val _ = check_fixture false "imported_flag/main.json";
val _ = check_fixture false "imported_interface/main.json";
val _ = check_fixture false "multimodule_storage/main.json";
val _ = check_fixture false "defaults_control/main.json";
val _ = check_fixture false "transient_storage/main.json";
val _ = check_fixture false "nonreentrant/main.json";
val _ = check_fixture true "deployment/main.json";
val _ = check_fixture false "imported_deploy/main.json";
val _ = check_fixture true "imported_deploy/main.json";
val _ = check_fixture false "third_party/flex/daddy/daddy.json";
val _ = check_fixture true "third_party/flex/daddy/daddy.json";
val _ = check_fixture false "interface_struct_return/main.json";
val _ = check_fixture false "abi_encode/main.json";

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
