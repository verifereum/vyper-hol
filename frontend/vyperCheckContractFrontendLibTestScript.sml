Theory vyperCheckContractFrontendLibTest
Ancestors
  jsonToVyper jsonToVyperExpr jsonAST vyperAST vyperTypeContract
  jsonNominalSources
  sourceModuleElaborate sourceModuleDefs sourceSyntax sourceConstAST
  sourceConstAnnotation finite_map sourceModuleLinkTest sourceModuleFrontendLibTest
  sourceConstBuiltinCompute sourceConstBuiltinTest
  sourceMeaningCallTest sourceMeaningCallExampleDefs sourceMeaningCompile
  sourceMeaningCallDefs vyperInterpreter vyperState vyperValue
Libs
  vyperCheckContractFrontendLib cv_transLib

(* Declare fixtures relative to this source file so holbuild stages them at
   the same relative path and includes their contents in the cache key. *)
fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../tests/fixtures/check_contract",
  "../tests/sourceShiftCountFixtures",
  "../lowering/defs/bytecode/folded-value-witnesses.txt"]

(* Branch checks for guarded call dispatch; fixture checks below also exercise
   these paths through the contract checker. Deliberately conflicting metadata
   checks that syntax shortcuts and self/pop keep their original priority. *)
val call_ctx = ``(0, SOME 9, [("lib", 7)], [], [], [], []) :
  int # num option # (string # num) list # string list #
  (string # type) list # ((num option # string) # type) list #
  (((num option # string) # (num option # string)) list)``;
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
  check_call label func ``JT_Named NONE "bool"`` ``NONE : base_assignment_target option`` expected;
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
  ``JT_Named NONE "bool"`` ``NONE : base_assignment_target option``
  (internal_call ``NONE : num option`` ``"compute"``);
val _ = check_bool_call "interface before builtin"
  (call_name ``"len"`` ``SOME "interface"``) iface_result;
val _ = app (fn tc => check_bool_call "builtin with negative interface tag"
  (call_name ``"len"`` tc) ``Builtin (BaseT BoolT) Len [^call_arg]``)
  [``NONE : string option``, ``SOME "interfaces"``];
val _ = app (fn tc => check_bool_call "non-interface name"
  (call_name ``"unknown"`` tc) (internal_call ``NONE : num option`` ``"unknown"``))
  [``NONE : string option``, ``SOME "interfaces"``, ``SOME "module"``];
val _ = app (fn shortcut => check_bool_call "interface shortcut before self"
  (call_attr self_name shortcut ``NONE : string option``) iface_result)
  [``"__at__"``, ``"__interface__"``];
val _ = check_bool_call "near shortcut name"
  (call_attr self_name ``"__at"`` ``SOME "interface"``)
  (internal_call ``SOME 9`` ``"__at"``);
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
  ``JT_Named NONE "bool"`` ``SOME ^subscript_target``
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
  ``JT_Struct NONE "Record"`` ``NONE : base_assignment_target option``
  ``StructLit (StructT (SOME 3, "Record")) (SOME 3, "Record") []``;
val _ = check_call "module struct constructor explicit source"
  (call_attr lib_name ``"Record"`` ``NONE : string option``)
  ``JT_Struct (SOME 2) "Record"`` ``NONE : base_assignment_target option``
  ``StructLit (StructT (SOME 4, "Record")) (SOME 4, "Record") []``;
val _ = check_call "module function returning struct"
  (call_attr lib_name ``"foo"`` ``NONE : string option``)
  ``JT_Struct NONE "Record"`` ``NONE : base_assignment_target option``
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

val empty_layout = ``<| storage := []; transient := []; code := [] |> :
  json_storage_layout``;
fun prepare_sources sources =
  vyperCheckContractFrontendLib.prepare_translated_input
    {in_deploy = false, address = address, sources = sources,
     import_map = ``[] : (string # num) list``, storage_layout = empty_layout};
fun prepare_ast ast =
  vyperCheckContractFrontendLib.prepare_check_input_legacy
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
       (SOME 7, [VariableDecl Public Storage "x" (BaseT (UintT 256)) (SOME 1)]);
       (SOME 7, [VariableDecl Public Storage "x" (BaseT (UintT 256)) (SOME 2)])]``);

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
  val checked = vyperCheckContractFrontendLib.check_contract_file_legacy
    {in_deploy = in_deploy, address = address,
     path = fixture_dir ^ path}
  val (_, result) = dest_eq (concl checked)
in
  if optionSyntax.is_some result then ()
  else raise Fail ("frontend contract checker rejected " ^ path)
end;

val _ = check_fixture false "scoped_locals/main.json";
val _ = check_fixture false "simple.json";
val _ = check_fixture false "address_bytes20.json";
val _ = check_fixture true "address_bytes20.json";
val _ = check_fixture false "address_bytes32.json";
val _ = check_fixture true "address_bytes32.json";
val _ = check_fixture false "storage.json";
val _ = check_fixture false "imported_struct/main.json";
val _ = check_fixture false "imported_flag/main.json";
(* lib2 reads lib1's constant and main reads lib2's. *)
val _ = check_fixture false "imported_constants/main.json";
val _ = check_fixture true "imported_constants/main.json";
val _ = check_fixture false "imported_interface/main.json";
val _ = check_fixture false "duplicate_interface/main/c.json";
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

fun fixture_input path = vyperCheckContractFrontendLib.prepare_check_input_legacy
  {in_deploy = false, address = address,
   annotated_ast = JSONDecode.decodeFile jsonASTLib.annotated_ast
     (fixture_dir ^ path),
   storage_layout = JSONDecode.decodeFile jsonASTLib.storage_layout
     (fixture_dir ^ path)};

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
val multimodule_input = vyperCheckContractFrontendLib.prepare_check_input_legacy
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

val structured = vyperCheckContractFrontendLib.check_contract_result_legacy
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

(* Do not expand legacy folded-value consumption (#135). Operator/call nodes
   decode identically with absent, poisoned or malformed replacements. Exercise
   the recursive module decoder, not only a standalone expression decoder. *)
fun fold_obj kind fields = JSON.OBJECT (("ast_type", JSON.STRING kind)::fields);
val fold_one = fold_obj "Int" [("value", JSON.INT 1)];
val fold_true = fold_obj "NameConstant" [("value", JSON.BOOL true)];
fun check_fold_decode value expected = let
  val input = JSON.OBJECT [("ast", JSON.OBJECT [("body", JSON.ARRAY
    [fold_obj "ExportsDecl" [("annotation", value)]])])];
  val actual = JSONDecode.decode jsonASTLib.annotated_ast input;
  val want = ``JAnnotatedAST (JModule (~1) F [JTL_ExportsDecl ^expected]) []``
in if aconv actual want then () else (print (term_to_string actual ^ "\nEXPECTED: " ^ term_to_string want ^ "\n"); raise Fail "legacy expression syntax changed") end;
val fold_cases = [
  (fold_obj "BinOp" [("left", fold_one), ("op", fold_obj "Add" []),
     ("right", fold_one)], ``JE_BinOp (JE_Int 1 JT_None) JBop_Add (JE_Int 1 JT_None) JT_None``),
  (fold_obj "Compare" [("left", fold_one), ("op", fold_obj "Lt" []),
     ("right", fold_one)], ``JE_Compare (JE_Int 1 JT_None) JBop_Lt (JE_Int 1 JT_None)``),
  (fold_obj "BoolOp" [("op", fold_obj "And" []), ("values", JSON.ARRAY [fold_true, fold_true])],
     ``JE_BoolOp JBoolop_And [JE_Bool T; JE_Bool T]``),
  (fold_obj "UnaryOp" [("op", fold_obj "Not" []), ("operand", fold_true)],
     ``JE_UnaryOp JUop_Not (JE_Bool T) JT_None``),
  (fold_obj "Call" [("func", fold_obj "Name" [("id", JSON.STRING "abs")]),
     ("args", JSON.ARRAY [fold_one])],
     ``JE_Call (JE_Name "abs" NONE JMissingSource JT_None) [JE_Int 1 JT_None] [] JT_None JMissingSource``)];
val () = app (fn (original, expected) => (
  check_fold_decode original expected;
  case original of JSON.OBJECT fields =>
    app (fn replacement => check_fold_decode
      (JSON.OBJECT (("folded_value", replacement)::fields)) expected)
      [fold_one, fold_obj "Int" [("value", JSON.INT 777)],
       JSON.NULL, JSON.STRING "not an AST", fold_obj "Unsupported" []]
  | _ => raise Fail "test node is not an object")) fold_cases;

(* Even plausible Decimal replacements and source-text serialization quirks
   are irrelevant: no folded Decimal parser is needed on these legacy nodes. *)
val () = app (fn (JSON.OBJECT fields, original) =>
    app (fn text => check_fold_decode
      (JSON.OBJECT (("folded_value",
        fold_obj "Decimal" [("value", JSON.STRING text)])::fields)) original)
      ["min(3.0, 5.0)", "1.0 + 2.0", "-(1.0 + 2.0)",
       "max_value(decimal)", "1.5suffix", "1.2.3", "1e+", "",
       "_1", "-_1", "_1e1", "1_.5", "1._5", "1__5"]
  | _ => raise Fail "test node is not an object") fold_cases;

Theorem nested_folded_integer_ignored:
  json_expr_int_opt (JE_Folded (JE_Bool F)
    (JE_Folded (JE_Bool T) (JE_Int (~3) JT_None))) = NONE
Proof
  EVAL_TAC
QED

(* Existing legacy JE_Folded translation is unchanged, not a new decoder
   capability. The ordinary source route strips/ignores replacements instead. *)
Theorem folded_translation_boundary:
  translate_expr ctx (JE_Folded original (JE_Folded other folded)) =
  translate_expr ctx folded
Proof
  simp[translate_expr_def]
QED

(* Genuine literal syntax still decodes/translates. The same literal used as
   replacement metadata cannot replace an operator's original syntax. *)
val fold_literals = [
  (fold_one, ``JE_Int 1 JT_None``),
  (fold_obj "Decimal" [("value", JSON.STRING "1.5")], ``JE_Decimal "1.5"``),
  (fold_obj "Decimal" [("value", JSON.STRING "-1.25e-2")],
     ``JE_Decimal "-1.25e-2"``),
  (fold_obj "Decimal" [("value", JSON.STRING "+1_000.0E+1")],
     ``JE_Decimal "+1_000.0E+1"``),
  (fold_obj "Hex" [("value", JSON.STRING "0xdeadbeef"),
     ("type", JSON.OBJECT [("typeclass", JSON.STRING "bytes_m"), ("m", JSON.INT 4)])],
     ``JE_Hex "0xdeadbeef" (JT_BytesM 4)``),
  (fold_obj "Hex" [("value", JSON.STRING "0x0000000000000000000000000000000000000001"),
     ("type", JSON.OBJECT [("name", JSON.STRING "address")])],
     ``JE_Hex "0x0000000000000000000000000000000000000001" (JT_Named NONE "address")``),
  (fold_obj "Bytes" [("value", JSON.STRING "0xdeadbeef"),
     ("type", JSON.OBJECT [("name", JSON.STRING "Bytes"), ("length", JSON.INT 4)])],
     ``JE_Bytes 4 "0xdeadbeef"``),
  (fold_obj "Str" [("value", JSON.STRING "abc"),
     ("type", JSON.OBJECT [("length", JSON.INT 3)])], ``JE_Str 3 "abc"``),
  (fold_obj "Str" [("value", JSON.STRING "abc"),
     ("type", JSON.OBJECT [("generic", JSON.STRING "string")])], ``JE_GenericStr "abc"``),
  (fold_true, ``JE_Bool T``)];
val () = app (fn (literal, expected) => (
  check_fold_decode literal expected;
  app (fn (JSON.OBJECT fields, original) =>
      check_fold_decode (JSON.OBJECT (("folded_value", literal)::fields)) original
    | _ => raise Fail "test node is not an object") fold_cases)) fold_literals;

Theorem literal_kinds_probe:
  translate_expr ctx (JE_Decimal "1.5") =
    Literal (BaseT DecimalT) (DecimalL 15000000000) /\
  translate_expr ctx (JE_Hex "0xdeadbeef" (JT_BytesM 4)) =
    Literal (BaseT (BytesT (Fixed 4))) (BytesL [222w; 173w; 190w; 239w]) /\
  translate_expr ctx (JE_Hex "0x01" (JT_Named NONE "address")) =
    Literal (BaseT AddressT) (BytesL [1w]) /\
  translate_expr ctx (JE_Bytes 4 "0xdeadbeef") =
    Literal (BaseT (BytesT (Dynamic 4))) (BytesL [222w; 173w; 190w; 239w]) /\
  translate_expr ctx (JE_Str 3 "abc") =
    Literal (BaseT (StringT 3)) (StringL "abc") /\
  translate_expr ctx (JE_GenericStr "abc") =
    Literal (BaseT (StringT 3)) (StringL "abc") /\
  translate_expr ctx (JE_Bool T) =
    Literal (BaseT BoolT) (BoolL T)
Proof
  EVAL_TAC
QED

Theorem folded_range_bounds_ignored:
  range_bound_of_args [JE_Folded (JE_Bool F) (JE_Int 3 JT_None)] = NONE /\
  range_bound_of_args [JE_Folded (JE_Bool F) (JE_Int (~2) JT_None);
    JE_Folded (JE_Bool T) (JE_Int 3 JT_None)] = NONE
Proof
  EVAL_TAC
QED

(* Keep the newly asserted boundary facts kernel-closed even if a future
   frontend dependency accidentally introduces an admission. *)
val () = app (fn th =>
  if null (List.filter (fn name => name <> "DISK_THM")
    (#1 (Tag.dest_tag (Thm.tag th)))) then ()
  else raise Fail "fold boundary probe depends on an oracle")
  [nested_folded_integer_ignored, folded_translation_boundary,
   literal_kinds_probe, folded_range_bounds_ignored];


(* ABI keyword extraction must not turn malformed present values into defaults. *)
Theorem abi_keyword_extractors_eval:
  kwarg_bool_opt "k" [] T = SOME T /\
  kwarg_bool_opt "k" [("k", Literal (BaseT BoolT) (BoolL F))] T = SOME F /\
  kwarg_bool_opt "k" [("k", Name (BaseT BoolT) "b")] T = NONE /\
  kwarg_bool_opt "k" [("k", Literal (BaseT (UintT 256)) (IntL 1))] T = NONE /\
  kwarg_method_id "k" [] = NONE /\
  kwarg_method_id "k"
    [("k", Literal (BaseT (BytesT (Fixed 4))) (BytesL [1w;2w;3w;4w]))] =
      SOME [1w;2w;3w;4w] /\
  kwarg_method_id "k"
    [("k", Literal (BaseT (BytesT (Fixed 3))) (BytesL [1w;2w;3w]))] = SOME [] /\
  kwarg_method_id "k" [("k", Name (BaseT (BytesT (Fixed 4))) "m")] = SOME [] /\
  kwarg_method_id "k" [("k", Literal (BaseT BoolT) (BoolL T))] = SOME []
Proof
  EVAL_TAC
QED

(* The same well-formed zero-argument function surrounds each translated call.
   Valid controls ensure a rejection is due to the keyword, not the wrapper. *)
Definition abi_keyword_contract_def:
  abi_keyword_contract result_ty body =
    [(NONE, [FunctionDecl External Pure F F "f" [] [] result_ty
      [Return (SOME body)]])]
End

Definition abi_keyword_encode_def:
  abi_keyword_encode kwargs =
    make_builtin_call (BaseT (BytesT (Dynamic 36))) "abi_encode"
      [Literal (BaseT (UintT 256)) (IntL 1)] kwargs (JT_Bytes 36)
End

Definition abi_keyword_decode_def:
  abi_keyword_decode kwargs =
    make_builtin_call (BaseT (UintT 256)) "abi_decode"
      [Literal (BaseT (BytesT (Dynamic 32))) (BytesL (REPLICATE 32 0w))]
      kwargs (JT_Integer 256 F)
End

Theorem abi_keyword_encode_valid_control:
  IS_SOME (check_contract F [] (0w : address)
    (abi_keyword_contract (BaseT (BytesT (Dynamic 36)))
      (abi_keyword_encode [("ensure_tuple", Literal (BaseT BoolT) (BoolL F));
        ("method_id", Literal (BaseT (BytesT (Fixed 4)))
          (BytesL [1w;2w;3w;4w]))])))
Proof
  simp[abi_keyword_contract_def, abi_keyword_encode_def, make_builtin_call_def,
       kwarg_bool_opt_def, kwarg_method_id_def, expr_type_def] >>
  CONV_TAC (RAND_CONV vyperCheckContractLib.check_contract_conv) >> simp[]
QED

Theorem abi_keyword_decode_valid_control:
  IS_SOME (check_contract F [] (0w : address)
    (abi_keyword_contract (BaseT (UintT 256))
      (abi_keyword_decode [("unwrap_tuple", Literal (BaseT BoolT) (BoolL T))])))
Proof
  simp[abi_keyword_contract_def, abi_keyword_decode_def, make_builtin_call_def,
       kwarg_bool_opt_def] >>
  CONV_TAC (RAND_CONV vyperCheckContractLib.check_contract_conv) >> simp[]
QED

Theorem abi_keyword_invalid_method_id_rejected:
  check_contract F [] (0w : address)
    (abi_keyword_contract (BaseT (BytesT (Dynamic 36)))
      (abi_keyword_encode [("ensure_tuple", Literal (BaseT BoolT) (BoolL F));
        ("method_id", Literal (BaseT BoolT) (BoolL T))])) = NONE
Proof
  simp[abi_keyword_contract_def, abi_keyword_encode_def, make_builtin_call_def,
       kwarg_bool_opt_def, kwarg_method_id_def, expr_type_def] >>
  CONV_TAC (LHS_CONV vyperCheckContractLib.check_contract_conv) >> simp[]
QED

Theorem abi_keyword_invalid_ensure_tuple_rejected:
  check_contract F [] (0w : address)
    (abi_keyword_contract (BaseT (BytesT (Dynamic 36)))
      (abi_keyword_encode [("ensure_tuple", Literal (BaseT (UintT 256)) (IntL 1))])) = NONE
Proof
  simp[abi_keyword_contract_def, abi_keyword_encode_def, make_builtin_call_def,
       kwarg_bool_opt_def] >>
  CONV_TAC (LHS_CONV vyperCheckContractLib.check_contract_conv) >> simp[]
QED

Theorem abi_keyword_invalid_unwrap_tuple_rejected:
  check_contract F [] (0w : address)
    (abi_keyword_contract (BaseT (UintT 256))
      (abi_keyword_decode [("unwrap_tuple", Literal (BaseT (UintT 256)) (IntL 1))])) = NONE
Proof
  simp[abi_keyword_contract_def, abi_keyword_decode_def, make_builtin_call_def,
       kwarg_bool_opt_def] >>
  CONV_TAC (LHS_CONV vyperCheckContractLib.check_contract_conv) >> simp[]
QED

val () = app (fn th =>
  if null (List.filter (fn name => name <> "DISK_THM")
    (#1 (Tag.dest_tag (Thm.tag th)))) then ()
  else raise Fail "ABI keyword test depends on an oracle")
  [abi_keyword_extractors_eval, abi_keyword_encode_valid_control,
   abi_keyword_decode_valid_control, abi_keyword_invalid_method_id_rejected,
   abi_keyword_invalid_ensure_tuple_rejected, abi_keyword_invalid_unwrap_tuple_rejected];

(* ===== Public source path: originals, exact equations and shared checker ===== *)
val source_layouts = ``[(0w:address,([]:storage_layout,[]:storage_layout))]``;
val source_trust = ``<| smt_ids := [(["main"],NONE)]; smt_nominals := [];
  smt_type_defs := FEMPTY; smt_slots := [] |>``;
fun source_input program : vyperCheckContractFrontendLib.source_input =
  {fuel=``80:num``,trust=source_trust,keys=``[["main"]]``,program=program,
   layouts=source_layouts,address=address};
fun audit_source_thm th = let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null (hyp th) andalso null axioms andalso
    List.all (fn s => s = "DISK_THM") oracles then ()
    else raise Fail "public source frontend equation is not kernel-closed" end;
fun exact_equation label lhs_tm rhs_tm th =
  if aconv (concl th) (mk_eq (lhs_tm,rhs_tm)) then audit_source_thm th
  else raise Fail ("public source frontend equation mismatch: " ^ label);
fun save_source_result label (src:vyperCheckContractFrontendLib.source_input)
    (checked:vyperCheckContractFrontendLib.source_checked_result) = let
  val elab = #elaboration checked
  val modules = #modules elab
  val retained = #retained elab
  val artifact = #artifact checked
  val {fuel,trust,keys,program,layouts,address} = src
  val phase_args = #2 (strip_comb (lhs (concl (#equation elab))))
  val phase = if length phase_args = 4 then
      ``source_module_elaborate_simple ^fuel ^trust ^keys ^program``
    else let val policies = List.nth (phase_args,2) in
      ``source_module_elaborate ^fuel ^trust ^policies ^keys ^program`` end
  val composition = if length phase_args = 4 then
      ``source_module_check_simple ^fuel ^trust ^keys ^program ^layouts ^address``
    else let val policies = List.nth (phase_args,2) in
      ``source_module_check ^fuel ^trust ^policies ^keys ^program ^layouts ^address`` end
  val () = exact_equation "phase" phase ``SM_Ok ^retained`` (#equation elab)
  val () = exact_equation "retained original"
    ``retained_source ^retained`` program (#original elab)
  val () = exact_equation "checker artifact"
    ``check_contract T ^layouts ^address ^modules`` ``SOME ^artifact`` (#checking checked)
  val () = exact_equation "composition artifact" composition
    ``SM_Ok (^retained,^artifact)`` (#composition checked)
  val () = if #in_deploy (#input checked) andalso
      aconv (#modules (#input checked)) modules andalso
      aconv (#layouts (#input checked)) layouts andalso
      aconv (#address (#input checked)) address then ()
    else raise Fail "public source frontend checked different input"
  val () = app audit_source_thm [#linking elab,#equation elab,#original elab,
    #checking checked,#composition checked]
  val _ = save_thm (label ^ "_phase",#equation elab)
  val _ = save_thm (label ^ "_source",#original elab)
  val _ = save_thm (label ^ "_links",#linking elab)
  val _ = save_thm (label ^ "_check",#checking checked)
  val _ = save_thm (label ^ "_composition",#composition checked)
in () end;

(* Strict #135 bound input uses the SAME general source phase. Only the
   explicitly named _legacy entry retains the compatibility evaluator. *)
val strict_src = vyperCheckContractFrontendLib.prepare_constant_source_file
  {address=address,path=fixture_dir ^ "constant_bound.json"};
val strict_checked = vyperCheckContractFrontendLib.Source.check_contract_result strict_src;
val () = save_source_result "public_constant_bound" strict_src strict_checked;
val strict_expected = ``[(NONE,[
  VariableDecl Private (Constant (Literal (BaseT (UintT 256)) (IntL 3)))
    "N" (BaseT (UintT 256)) NONE;
  FunctionDecl External Pure F F "power"
    [("x",BaseT (UintT 256));("values",ArrayT (BaseT (UintT 256)) (Fixed 3))] []
    (BaseT (UintT 256)) [Return (SOME (Builtin (BaseT (UintT 256)) (Bop Exp)
      [Name (BaseT (UintT 256)) "x";Literal (BaseT (UintT 256)) (IntL 3)]))]])]
    : (num option # toplevel list) list``;
val () = if aconv (#modules (#elaboration strict_checked)) strict_expected then ()
  else raise Fail "public source constant array/exponent AST mismatch";
val () = exact_equation "strict adapter uses shared pipeline"
  (lhs (concl (#checking strict_checked))) (rhs (concl (#checking strict_checked)))
  (vyperCheckContractFrontendLib.Source.check_constant_contract_file
    {address=address,path=fixture_dir ^ "constant_bound.json"});

fun metadata_variant replacement (JSON.OBJECT fields) = JSON.OBJECT
    ((case replacement of NONE => [] | SOME value =>
      List.map (fn key => (key,value)) ["folded_value","type","is_constant","is_immutable"]) @
     List.map (fn (key,v) => (key,metadata_variant replacement v))
       (List.filter (fn (key,_) => not (List.exists (fn k => k = key)
         ["folded_value","type","is_constant","is_immutable"])) fields))
  | metadata_variant replacement (JSON.ARRAY values) =
      JSON.ARRAY (List.map (metadata_variant replacement) values)
  | metadata_variant _ value = value;
val source_path = fixture_dir ^ "source_syntax/c27_const_binop_fold.json";
val source_json = JSONDecode.decodeFile JSONDecode.raw source_path;
val source_program = JSONDecode.decode sourceSyntaxLib.annotated_ast source_json;
val public_source = vyperCheckContractFrontendLib.Source.check_contract_result
  (source_input source_program);
val () = save_source_result "public_source_original" (source_input source_program) public_source;
val () = app (fn variant => let
    val program = JSONDecode.decode sourceSyntaxLib.annotated_ast variant
    val () = if aconv program source_program then ()
      else raise Fail "public source decoder consumed metadata"
    val checked = vyperCheckContractFrontendLib.Source.check_contract_result (source_input program)
  in if aconv (concl (#checking checked)) (concl (#checking public_source)) andalso
    aconv (concl (#composition checked)) (concl (#composition public_source)) then ()
    else raise Fail "metadata changed source equation/artifact" end)
  [metadata_variant NONE source_json,
   metadata_variant (SOME (JSON.STRING "poisoned metadata")) source_json];
val () = exact_equation "source file entry point"
  (lhs (concl (#checking public_source))) (rhs (concl (#checking public_source)))
  (vyperCheckContractFrontendLib.check_source_contract_file
    {fuel=``80:num``,trust=source_trust,keys=``[["main"]]``,layouts=source_layouts,
     address=address,path=source_path});

(* Exercise extended internal/imported/export and external source call paths
   through the actual public API, not the legacy translator. *)
val linked_src : vyperCheckContractFrontendLib.source_input =
  {fuel=``30:num``,trust=``source_module_link_trust``,keys=``[["main"];["lib"]]``,
   program=``source_module_link_fixture``,layouts=source_layouts,address=address};
val linked_public = vyperCheckContractFrontendLib.Source.check_contract_result linked_src;
val () = save_source_result "public_imported_call" linked_src linked_public;
val () = if aconv
  (rhs (concl (EVAL (rhs (concl source_module_link_call_exact)))))
  (rhs (concl (#equation (#elaboration linked_public)))) then ()
  else raise Fail "public source imported-call exact AST mismatch";

val external_src : vyperCheckContractFrontendLib.source_input =
  {fuel=``40:num``,keys=``[["main"]]``,program=``source_module_external_fixture``,
   layouts=source_layouts,address=address,
   trust=``<| smt_ids := [(["main"],NONE)]; smt_nominals := [(["main";"I"],STI_Interface)];
     smt_type_defs := FEMPTY |+ ((NONE,"I"),InterfaceArgs
       [("read",[],BaseT (UintT 256),View)]); smt_slots := [] |>``};
val external_public = vyperCheckContractFrontendLib.Source.check_contract_result external_src;
val () = save_source_result "public_external_call" external_src external_public;
val () = if aconv (#modules (#elaboration external_public))
  (lhs (concl source_module_external_ast_exact)) then ()
  else raise Fail "public source external-call AST mismatch";

(* The captured pre-erasure version of an ORDINARY legacy fixture. Reuse the
   inherited canonical ID/layout, not the parser's colliding source_id claims. *)
val ordinary_loaded = sourceModuleLoaderLib.load_file
  (fixture_dir ^ "source_loader/multimodule_storage.json");
val ordinary_trust = ``<| smt_ids := [(["main"],NONE);(["lib"],SOME 3)];
  smt_nominals := []; smt_type_defs := FEMPTY; smt_slots := [((SOME 3,"stored"),0)] |>``;
val ordinary_public = vyperCheckContractFrontendLib.check_loaded_source_contract_result
  {fuel=``40:num``,trust=ordinary_trust,source=ordinary_loaded,
   layouts= #layouts multimodule_input,address=address};
val () = save_source_result "public_ordinary_multimodule"
  {fuel=``40:num``,trust=ordinary_trust,keys= #keys ordinary_loaded,
   program= #program ordinary_loaded,layouts= #layouts multimodule_input,address=address}
  ordinary_public;
(* Source explicitly annotates the imported storage slot inherited from the
   supplied layout. Legacy leaves this imported declaration's slot as NONE.
   Pin the actual source AST instead of asserting false legacy AST equality. *)
val ordinary_expected = ``[(NONE,[
  FunctionDecl External Nonpayable F F "set_value" [("x",BaseT (UintT 256))] [] NoneT
    [Expr (Call NoneT (IntCall (SOME 3,"set_value"))
      [Name (BaseT (UintT 256)) "x"] NONE)]]);
  (SOME 3,[VariableDecl Private Storage "stored" (BaseT (UintT 256)) (SOME 0);
    FunctionDecl Internal Nonpayable F F "set_value" [("x",BaseT (UintT 256))] [] NoneT
      [Assign (BaseTarget (TopLevelNameTarget (SOME 3,"stored")))
        (Name (BaseT (UintT 256)) "x")]])]``;
val () = if aconv (#modules (#elaboration ordinary_public)) ordinary_expected
  then () else raise Fail "ordinary pre-erasure source AST mismatch";
val ordinary_legacy_checked = vyperCheckContractLib.check_contract
  {in_deploy=true,address=address,modules= #modules multimodule_input,
   layouts= #layouts multimodule_input};
val () = audit_source_thm ordinary_legacy_checked;
val () = if aconv (rhs (concl ordinary_legacy_checked))
  (rhs (concl (#checking ordinary_public))) then ()
  else raise Fail "ordinary source/legacy checker artifacts differ";
val _ = save_thm ("public_ordinary_legacy_check",ordinary_legacy_checked);

fun source_rejects label src =
  if (vyperCheckContractFrontendLib.Source.check_contract src; false)
    handle HOL_ERR _ => true then ()
  else raise Fail ("public source frontend retried/accepted " ^ label);
val () = source_rejects "fuel exhaustion"
  {fuel=``0:num``,trust=source_trust,keys=``[["main"]]``,program=source_program,
   layouts=source_layouts,address=address};
val () = source_rejects "unknown source name" (source_input
  ``SourceProgram (SourceModule [SD_Function "f" [SX_Name "external"] [] []
    (SOME (SCA_Name ["uint256"])) [SS_Return (SOME (SX_Name "missing"))]]) []``);

(* The pin-valid #135 gate preserves BOTH old successes, but the public name
   must now be exactly Source, including deployment checking. A true original
   pre-erasure capture must produce the same AST/equations as the strict adapter.
   Legacy constant initializers remain unfurled (and are pinned in its own
   witness theory); Source reifies them. Checker artifacts agree, not whole
   legacy ASTs. The separate shift test pins exact function-AST agreement.
   This does not promote the adapter's qualifier flags to source provenance. *)
val () = app (fn name => let
  val file = {address=address,path=fixture_dir ^ name ^ ".json"}
  val src = vyperCheckContractFrontendLib.prepare_constant_source_file file
  val checked = vyperCheckContractFrontendLib.Source.check_contract_result src
  val legacy = vyperCheckContractFrontendLib.check_constant_contract_file_legacy file
  val public = vyperCheckContractFrontendLib.check_constant_contract_file file
  val strict = vyperCheckContractFrontendLib.Source.check_constant_contract_file file
  val original = JSONDecode.decodeFile sourceSyntaxLib.annotated_ast
    ("../tests/sourceShiftCountFixtures/" ^ name ^ ".json")
  val same = vyperCheckContractFrontendLib.Source.check_contract_result
    {fuel= #fuel src,trust= #trust src,keys= #keys src,program=original,
     layouts= #layouts src,address=address}
  val () = app audit_source_thm [legacy,public,strict,#checking same,#composition same]
  val () = if aconv (concl public) (concl strict) andalso
      aconv (concl public) (concl (#checking checked)) andalso
      aconv (concl public) (concl (#checking same)) andalso
      aconv (rhs (concl public)) (rhs (concl legacy)) then ()
    else raise Fail ("strict public/source/legacy AST mismatch: " ^ name)
  val () = save_source_result ("public_strict_" ^ name) src checked
  val _ = save_thm ("public_strict_" ^ name ^ "_legacy",legacy)
in () end) ["constant_bound","constant_shifts"];

(* Genuine public loader entry: the trusted capture protocol, not ordinary
   annotated JSON with qualifiers reconstructed from erased metadata. *)
val loader_file = {fuel=``40:num``,trust=ordinary_trust,
  layouts= #layouts multimodule_input,address=address,
  path=fixture_dir ^ "source_loader/multimodule_storage.json"};
val loader_checked = vyperCheckContractFrontendLib.Source.check_contract_file_result loader_file;
val () = exact_equation "public pre-erasure loader"
  (lhs (concl (#composition ordinary_public))) (rhs (concl (#composition ordinary_public)))
  (#composition loader_checked);
val () = exact_equation "public pre-erasure file checker"
  (lhs (concl (#checking ordinary_public))) (rhs (concl (#checking ordinary_public)))
  (vyperCheckContractFrontendLib.Source.check_contract_file loader_file);
val () = ((vyperCheckContractFrontendLib.Source.check_contract_file
    {fuel=``40:num``,trust=ordinary_trust,layouts= #layouts multimodule_input,
     address=address,path=multimodule_path};
    raise Fail "public loader accepted ordinary post-erasure JSON")
  handle JSONDecode.JSONError _ => ());

(* Preserved policies are now supported. Applying declaration-only to a real
   implementation is still rejected: its body is not an interface signature. *)
val nr_source : sourceModuleLoaderLib.loaded =
  {program= #program ordinary_loaded,keys= #keys ordinary_loaded,
   nonreentrant_defaults=``[T;F]``,declaration_only=``[F;F]``,provenance=JSON.NULL};
val nr_lock_name = stringSyntax.fromMLstring "$.nonreentrant_key";
val nr_layouts = ``[(^address,([((SOME 3,"stored"),0)],
  [((NONE,^nr_lock_name),0)]))] : (address # (storage_layout # storage_layout)) list``;
val nr_checked = vyperCheckContractFrontendLib.Source.check_loaded_contract_result
  {fuel=``40:num``,trust=ordinary_trust,source=nr_source,
   layouts=nr_layouts,address=address};
val () = audit_source_thm (#composition nr_checked);
val _ = save_thm ("public_loader_nonreentrant_policy",#composition nr_checked);
val false_interface : sourceModuleLoaderLib.loaded =
  {program= #program ordinary_loaded,keys= #keys ordinary_loaded,
   nonreentrant_defaults=``[F;F]``,declaration_only=``[F;T]``,provenance=JSON.NULL};
val () = if (vyperCheckContractFrontendLib.Source.check_loaded_contract_result
  {fuel=``40:num``,trust=ordinary_trust,source=false_interface,
   layouts= #layouts multimodule_input,address=address}; false)
  handle HOL_ERR _ => true then () else
  raise Fail "public loader fabricated an interface from implementation bodies";

(* Source defaults and full call/load semantic extraction for the actual checked
   artifact. Raw backend success, independent source derivations and nominal
   environment agreement remain visible; no bytecode theorem is asserted. *)
val meaning_src : vyperCheckContractFrontendLib.source_input =
  {fuel=``12:num``,trust=``source_meaning_call_trust``,keys=``[["main"]]``,
   program=``SourceProgram source_meaning_call_syntax []``,
   layouts=source_layouts,address=address};
val meaning_checked = vyperCheckContractFrontendLib.Source.check_contract_result meaning_src;
val () = save_source_result "public_meaning_defaults" meaning_src meaning_checked;
val meaning_artifact = vyperCheckContractFrontendLib.Source.artifact_semantics meaning_checked;
val () = audit_source_thm meaning_artifact;
val _ = save_thm ("public_meaning_artifact",meaning_artifact);
val (_,meaning_body) = strip_forall (concl meaning_artifact);
val (compiler_premise,_) = dest_imp meaning_body;
val (raw_compile,raw_bytes) = dest_eq compiler_premise;
val (raw_head,raw_args) = strip_comb raw_compile;
val meaning_tops = snd (pairSyntax.dest_pair
  (hd (#1 (listSyntax.dest_list (#modules (#elaboration meaning_checked))))));
val () = if same_const raw_head ``compile_vyper`` andalso length raw_args = 3 andalso
  aconv (List.last raw_args) meaning_tops andalso optionSyntax.is_some raw_bytes then ()
  else raise Fail "public semantics lost exact raw compiler premise";
val () = ((vyperCheckContractFrontendLib.Source.artifact_semantics ordinary_public;
  raise Fail "public semantics silently flattened imported modules")
  handle Fail message => if message = "source artifact semantics: backend-module-linking"
    then () else raise Fail message);
val () = app (fn constant =>
  if List.exists (same_const constant) (find_terms is_const (concl meaning_artifact)) then ()
  else raise Fail "public artifact lost independent call/load semantics")
  [``source_meaning_call``,``source_meaning_load``,``source_meaning_module``];
Theorem public_meaning_default_call:
  FST (call_external NONE source_meaning_call_machine
    (empty_call_txn with function_name := "f")) = INL (IntV 6)
Proof
  ACCEPT_TAC source_meaning_call_runtime_return
QED

(* Re-run every retained whole source through the PUBLIC full checker, not a
   certificate-only/translation-only test. All 36 pin-valid cases must succeed;
   method_id_var alone is pin-invalid. Metadata variants decode identically.
   This 37-row inventory does NOT cover the ordinary legacy fixture universe. *)
val () = app (fn s => let
  val bytes = listSyntax.mk_list (List.map (fn c => numSyntax.term_of_int (Char.ord c))
    (String.explode s),numSyntax.num)
  val th = cv_eval (mk_comb (``source_const_keccak``,bytes))
in computeLib.add_funs [th] end)
  ["hello","transfer(address,uint256)","foo()","f(uint256)","E(uint256)","x"];
val inventory_stream = TextIO.openIn "../lowering/defs/bytecode/folded-value-witnesses.txt";
val inventory_names = String.tokens Char.isSpace (TextIO.inputAll inventory_stream);
val () = TextIO.closeIn inventory_stream;
val () = if length inventory_names = 37 then () else raise Fail "public source inventory changed";
val () = app (fn name => let
  val raw = JSONDecode.decodeFile JSONDecode.raw
    (fixture_dir ^ "source_syntax/" ^ name ^ ".json")
  val program = JSONDecode.decode sourceSyntaxLib.annotated_ast raw
  val slots = if name = "method_id_storage" then ``[((NONE,"m"),0:num)]:storage_layout``
    else if name = "i12_immut_with_storage" then ``[((NONE,"s"),0:num)]:storage_layout``
    else ``[]:storage_layout``
  val src : vyperCheckContractFrontendLib.source_input =
    {fuel=``80:num``,keys=``[["main"]]``,program=program,address=address,
     trust=``<| smt_ids := [(["main"],NONE)]; smt_nominals := [];
       smt_type_defs := FEMPTY; smt_slots := ^slots |>``,
     layouts=``[(^address,(^slots,[]:storage_layout))]``}
  val () = app (fn variant =>
    if aconv program (JSONDecode.decode sourceSyntaxLib.annotated_ast variant) then ()
    else raise Fail ("public source consumed metadata: " ^ name))
    [metadata_variant NONE raw,metadata_variant (SOME (JSON.STRING "poison")) raw]
in if name = "method_id_var" then let
    val phase = EVAL ``source_module_elaborate_simple ^(#fuel src) ^(#trust src) ^(#keys src) ^program``
    val () = exact_equation "pin-invalid source domain rejection"
      ``source_module_elaborate_simple ^(#fuel src) ^(#trust src) ^(#keys src) ^program``
      ``SM_Error (SME_Constant SCErr_Domain) :
        (num option # toplevel list) list source_retained source_module_result`` phase
    val () = source_rejects name src
    val _ = save_thm ("public_inventory_method_id_var_reject",phase)
  in () end else let
    val checked = vyperCheckContractFrontendLib.Source.check_contract_result src
    val () = save_source_result ("public_inventory_" ^ name) src checked
    val expected = DB.fetch "sourceModuleFrontendLibTest" ("source_module_" ^ name ^ "_composition")
    val () = if aconv (concl (#composition checked)) (concl expected) then ()
      else raise Fail ("public source inventory artifact changed: " ^ name)
  in print ("PUBLIC_SOURCE_ACCEPT_CHECK " ^ name ^ "\n") end
end) inventory_names;
val () = app (fn (_,th) => audit_source_thm th)
  (DB.thms "vyperCheckContractFrontendLibTest");
