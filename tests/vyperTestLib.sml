structure vyperTestLib :> vyperTestLib = struct

open HolKernel boolLib bossLib cv_transLib wordsLib intLib
     pairSyntax listSyntax stringSyntax optionSyntax
     intSyntax wordsSyntax fcpSyntax
     vfmTypesSyntax contractABISyntax byteStringCacheLib
     vyperABITheory vyperASTSyntax vyperTestRunnerTheory
     jsonASTLib jsonToVyperTheory
open JSONDecode

(* ===== jsonAST Translation Pipeline ===== *)
(* Parse JSON to jsonAST, then translate to vyperAST using EVAL *)

val translate_annotated_ast_tm =
  prim_mk_const{Thy="jsonToVyper",Name="translate_annotated_ast"}

fun translate_jsonast_to_vyper jsonast_tm = let
  val app = mk_comb(translate_annotated_ast_tm, jsonast_tm)
  val thm = EVAL app
  val rhs = rhs (concl thm)
in
  (* translate_annotated_ast returns SOME (...) or NONE if imports not topsorted *)
  if optionSyntax.is_some rhs then optionSyntax.dest_some rhs
  else raise JSONError (Fail "imports not topologically sorted", JSON.OBJECT [])
end

(* Decoder that uses the jsonAST pipeline with full module support *)
val toplevels_via_jsonast : term decoder =
  JSONDecode.map translate_jsonast_to_vyper wrapped_annotated_ast

fun from_term_option ty = lift_option (mk_option ty) I

fun check cd pred err d =
  andThen cd (fn x => if pred x then d else fail err)

fun check_field lab req =
  check (field lab string) (equal req) (lab ^ " not " ^ req)

fun check_trace_type req = check_field "trace_type" req

fun check_ast_type req = check_field "ast_type" req

val numOfLargeInt =
  intSyntax.dest_injected o
  intSyntax.term_of_int o
  Arbint.fromLargeInt

fun achoose err ls = orElse(choose ls, fail err)

fun triml n s = String.extract(s,n,NONE)

val numtm = JSONDecode.map numOfLargeInt intInf
val stringtm = JSONDecode.map fromMLstring string
val booltm = JSONDecode.map mk_bool bool
val negbooltm = JSONDecode.map (mk_bool o not) bool

val address : term decoder = JSONDecode.map address_from_hex string
val bytes : term decoder = JSONDecode.map cached_bytes_from_hex string

val Call_tm = prim_mk_const{Thy="vyperTestRunner",Name="Call"}
val call_trace_ty = #1 $ dom_rng $ type_of Call_tm

local
  fun descending [] = true
    | descending [x] = true
    | descending (x::y::ls) = (x-1 = y) andalso descending (y::ls)

  fun ensure_not_empty s = if String.size s = 0 then "0" else s

  fun descending_key (k1, _) (k2, _) = k2 < k1
in
val blockHashes : term decoder =
  JSONDecode.map (fn ls => let
    fun f (k,v) = (Option.valOf (Int.fromString k),
                   decode (JSONDecode.map (bytes32_from_hex o ensure_not_empty) string) v)
    val ls = List.map f ls
    val ls = Lib.sort descending_key ls
    val true = descending (List.map #1 ls)
  in mk_list(List.map #2 ls, bytes32_ty) end) $ rawObject
val blobHashes : term decoder =
  JSONDecode.map (fn ls => mk_list(ls, bytes32_ty)) $
    array (JSONDecode.map (bytes32_from_hex o ensure_not_empty) string)
end

val call : term decoder =
  check_trace_type "call" $
  JSONDecode.map (fn ((a,c,v,t),(p,g,s,(h,bh)),(m,bn,bf,e)) =>
              TypeBase.mk_record (call_trace_ty, [
                ("sender", s),
                ("target", t),
                ("callData", c),
                ("value", v),
                ("timeStamp", m),
                ("blockNumber", bn),
                ("blockHashes", h),
                ("blobHashes", bh),
                ("blobBaseFee", bf),
                ("gasLimit", g),
                ("gasPrice", p),
                ("chainId", numSyntax.term_of_int 1),
                ("static", a),
                ("expectedOutput", e)]))
          (tuple3 (
            field "call_args" $
              tuple4 (field "is_modifying" negbooltm,
                      field "calldata" bytes,
                      field "value" numtm,
                      field "to" address),
            field "env" $
              tuple4 (field "tx" $ field "gas_price" numtm,
                      field "tx" $ field "gas" numtm,
                      field "tx" $ field "origin" address,
                      tuple2 (field "block" $ field "block_hashes" blockHashes,
                              field "tx" $ field "blob_hashes" blobHashes)),
            tuple4 (
              field "env" $ field "block" $ field "timestamp" numtm,
              field "env" $ field "block" $ field "number" numtm,
              field "env" $ field "block" $ field "blob_basefee" numtm,
              field "output" (JSONDecode.map (from_term_option bytes_ty) $
                              nullable bytes))))

fun theoptstring NONE = "" | theoptstring (SOME s) = s

val abiBaseType : term decoder =
  JSONDecode.map parse_abi_type string

fun tuple_brackets s =
  if Substring.isSuffix "]" s then let
    val (ps, ns) = Substring.splitr (not o equal #"[") s
    val bt = parse_optnum_ss ns
    val s = Substring.trimr 1 ps
    val a = mk_comb(contractABISyntax.Array_tm, bt)
  in
    curry mk_comb a o tuple_brackets s
  end else if Substring.isEmpty s
  then I else raise Fail "not brackets"

fun d_abiType () : term decoder = achoose "abiType" [
  check (field "type" string)
        (String.isPrefix "tuple")
        "not tuple" $
    JSONDecode.map (fn (t, ls) =>
      (tuple_brackets $
       Substring.extract
         (t, String.size "tuple", NONE)) $
      mk_comb(contractABISyntax.Tuple_tm, mk_list (ls, abi_type_ty))) $
    tuple2 (field "type" string,
            field "components" $ array $ delay d_abiType),
  field "type" abiBaseType
]
val abiType = delay d_abiType

val abiArg : term decoder =
  JSONDecode.map mk_pair $
  tuple2 (field "name" stringtm, abiType)

val abiMutability : term decoder =
  andThen string (fn s =>
    if s = "nonpayable" then succeed Nonpayable_tm else
    if s = "view" then succeed View_tm else
    if s = "payable" then succeed Payable_tm else
    if s = "pure" then succeed Pure_tm else
    fail ("abiMutability: " ^ s))

val Function_tm = prim_mk_const{Thy="vyperTestRunner",Name="Function"}
val Event_tm = prim_mk_const{Thy="vyperTestRunner",Name="Event"}
val (abi_function_ty, abi_entry_ty) = dom_rng $ type_of $ Function_tm
val abi_arg_ty = mk_prod(string_ty, abi_type_ty)

fun mk_Function (n,is,os,m) =
  mk_comb(Function_tm,
             TypeBase.mk_record (abi_function_ty, [
               ("name", n),
               ("inputs", mk_list(is, abi_arg_ty)),
               ("outputs", mk_list(os, abi_arg_ty)),
               ("mutability", m)]))

val abiEntry : term decoder = achoose "abiEntry" [
    check_field "type" "function" $
    JSONDecode.map mk_Function $
      tuple4 (field "name" stringtm,
              field "inputs" (array abiArg),
              field "outputs" (array abiArg),
              field "stateMutability" abiMutability),
    check_field "type" "constructor" $
    JSONDecode.map mk_Function $
      tuple4 (succeed $ fromMLstring "__init__",
              field "inputs" (array abiArg),
              field "outputs" (array abiArg),
              field "stateMutability" abiMutability),
    check_field "type" "fallback" $
    JSONDecode.map mk_Function $
      tuple4 (succeed $ fromMLstring "__default__",
              succeed $ [],
              succeed $ [],
              field "stateMutability" abiMutability),
    check_field "type" "event" $
    JSONDecode.map (fn s => mk_comb(Event_tm, s)) $
    field "name" stringtm
  ]

val Deployment_tm = prim_mk_const{Thy="vyperTestRunner",Name="Deployment"}
val deployment_trace_ty = #1 $ dom_rng $ type_of Deployment_tm

val SetBalance_tm = prim_mk_const{Thy="vyperTestRunner",Name="SetBalance"}
val ClearTransientStorage_tm =
  prim_mk_const{Thy="vyperTestRunner",Name="ClearTransientStorage"}

val unsupported_code = [
  "@raw_return\n" (* TODO: add *)
]

val unsupported_patterns = unsupported_code @ [
  "msg.mana", "msg.gas",
  "msg.data",
  "gas=",
  (* JSON ABI interface imports currently expose legacy ABI entries
     with constant/payable instead of stateMutability, and dynamic ABI bytes
     as length="..."; the frontend/ABI decoder does not support those yet. *)
  "import jsonabi as jsonabi",
  "import JSONInterface"
]

fun has_unsupported_patterns src =
  List.exists (fn x => String.isSubstring x src) unsupported_patterns

fun is_blank s =
  List.all Char.isSpace (String.explode s)

fun source_codes_json j =
  let
    fun gather (JSON.OBJECT kvs) =
          let
            val here =
              case List.find (fn (k, _) => k = "source_code") kvs of
                SOME (_, JSON.STRING s) => [s]
              | _ => []
            val nested = List.concat (List.map (fn (_, v) => gather v) kvs)
          in
            here @ nested
          end
      | gather (JSON.ARRAY xs) = List.concat (List.map gather xs)
      | gather _ = []
  in
    gather j
  end

fun first_some [] = NONE
  | first_some (NONE::xs) = first_some xs
  | first_some (SOME x::_) = SOME x

fun unsupported_source_reason_for jsons =
  case List.concat (List.map source_codes_json jsons) of
    [] => SOME "missing source_code"
  | srcs =>
      if List.exists (fn src => String.size src = 0 orelse is_blank src) srcs
      then SOME "blank source_code"
      else first_some
        (List.map (fn pat =>
           if List.exists (String.isSubstring pat) srcs
           then SOME ("unsupported source pattern: " ^ pat)
           else NONE)
         unsupported_patterns)

fun unsupported_source_reason j = unsupported_source_reason_for [j]

fun has_unsupported_source_json j =
  Option.isSome (unsupported_source_reason j)

fun has_unsupported_source_code (name, (err, j)) =
  has_unsupported_source_json j

(* ===== Test Selection ===== *)

val test_exports_root = "vyper-test-exports"
val generated_dir = "generated"

fun check_generate_dirs () = (
  if OS.FileSys.isDir test_exports_root then ()
  else raise Fail "vyper-test-exports not found - run from tests/ directory";
  if OS.FileSys.isDir generated_dir then ()
  else raise Fail "generated/ not found - run from tests/ directory"
)

(* Directory-level allowlist plus small explicit allowlist. *)
val allowed_test_prefixes = [
  "vyper-test-exports/functional/codegen/",
  "vyper-test-exports/functional/builtins/codegen/"
]

val allowed_test_patterns = [
  "vyper-test-exports/functional/builtins/codegen/test_blobhash.json"
]

val excluded_test_patterns = [
  "*/functional/codegen/abstract/*", (* @override semantics not implemented *)
  (* The clean export contains a top-level ErrorDef, for which
     frontend/jsonASTLib.sml's json_toplevel decoder has no branch. *)
  "vyper-test-exports/functional/codegen/features/test_custom_errors.json"
]

(* Individual test names that bypass unsupported pattern checks *)
val allowed_test_names = [
  (* extcall tests - staticcall now enabled globally *)
  "test_external_contract_call_state_change",
  "test_complicated_external_contract_calls"
]

(* Tests excluded by name - require architectural changes *)
val excluded_test_names = [
  (* These tests have a helper contract deployed via raw_bytecode with
     annotated_ast: null. The deployment decoder cannot handle null ASTs.
     Fix: add a RawDeployment trace type that only carries address +
     runtime bytecode + ABI, skipping source compilation entirely. *)
  "test_abi_arg_wrapped_complex_member_head",
  "test_abi_arg_wrapped_dynarray_head",
  "test_abi_decode_child_head_points_to_parent",
  "test_abi_decode_complex_arithmetic_overflow",
  "test_abi_decode_complex_empty_dynarray",
  "test_abi_decode_empty_toplevel_dynarray",
  "test_abi_decode_extcall_complex_empty_dynarray",
  "test_abi_decode_extcall_empty_array",
  "test_abi_decode_extcall_zero_len_array2",
  "test_abi_decode_invalid_toplevel_dynarray_head",
  "test_abi_decode_merge_head_and_length",
  "test_abi_decode_nonstrict_head",
  "test_abi_decode_nonstrict_head_oob",
  "test_create_from_blueprint_bad_code_offset",
  "test_immutables_initialized2",
  "test_revert_reason_typed",
  "test_revert_reason_typed_no_variable",
  "test_side_effects_evaluation",
  "test_checkable_raw_call",
  "test_nonreentrant_decorator_for_default",

  (* RawCreate now preserves bytecode, constructor args, value, and salt.
     Its eval-order and CREATE2 salt tests are enabled. Running initcode and
     installing the resulting runtime code remains out of scope (#379), so
     tests that inspect or call the deployed contract remain excluded. *)
  "test_raw_create",
  "test_raw_create_change_*",
  "test_raw_create_dynamic_arg",
  "test_raw_create_double_eval",
  "test_raw_create_memory_overlap",
  "test_raw_create_revert_value_kws*",
  "test_bubble_revert_data_raw_create",

  (* create_from_blueprint / create_copy_of / create_minimal_proxy_to tests:
     opaque create model doesn't run blueprint/raw initcode or register newly
     created contracts as callable, so calls to created contracts fail.
     TODO(#379): run initcode and register created contracts. *)
  "test_create_from_blueprint*",
  "test_blueprint_evals_once_side_effects",
  "test_bubble_revert_data_blueprint",
  (* Proxy/copy semantics install statically derivable runtime code, and the
     salted proxy CREATE2 address tests are enabled. Registration as a
     callable Vyper contract and constructor effects remain out of scope
     (#379), so tests that call or inspect created contract state stay out. *)
  "test_create_copy_of*",
  "test_create_minimal_proxy_to_call",
  "test_create_minimal_proxy_to_create",
  "test_minimal_proxy_exception",
  (* Tests using shift() builtin which is not yet translated.
     TODO: add shift builtin support *)
  "test_uint256_mulmod_complex",
  (* msg.data tests now excluded by unsupported_patterns *)
  (* skip_contract_check=True keyword not yet supported in ExtCall.
     TODO: add skip_contract_check flag to ExtCall AST *)
  "test_skip_contract_check",
  (* Out-of-gas test - we don't model gas *)
  "test_ecrecover_oog_handling",
  (* ABI decode strictness tests - Vyper's decoder is stricter than standard
     ABI, rejecting OOB heads, truncated data, etc. TODO: add Vyper-specific
     ABI decode validation on top of contractABI's standard valid_enc *)
  "test_abi_decode_extcall_array_oob*",
  "test_abi_decode_extcall_complex_empty_dynarray2",
  "test_abi_decode_extcall_invalid_head",
  "test_abi_decode_extcall_oob",
  "test_abi_decode_extcall_return_nodata",
  "test_abi_decode_extcall_runtimesz_oob",
  "test_abi_decode_extcall_truncate_returndata*",
  "test_abi_decode_dynarray_complex_insufficient_data",
  "test_abi_decode_nonstrict_head_oob2",
  "test_abi_decode_runtimesz_oob*",
  "test_abi_decode_top_level_head_oob",
  "test_nested_invalid_dynarray_head",
  "test_static_outer_type_invalid_heads",
  "test_abi_decode_arithmetic_overflow",
  "test_abi_decode_bytearray_clamp",
  "test_abi_decode_dynarray_complex2",
  "test_abi_decode_head_pointing_outside_buffer",
  "test_abi_decode_head_roundtrip",
  "test_abi_decode_max_size",
  "test_clamper*",
  "test_returndatasize_check"
]

fun glob_match pat str =
  let
    fun step [] [] = true
      | step (#"*"::ps) ss =
          step ps ss orelse
          (case ss of [] => false | _::ss' => step (#"*"::ps) ss')
      | step (#"?"::ps) (_::ss) = step ps ss
      | step (p::ps) (s::ss) = (p = s) andalso step ps ss
      | step _ _ = false
  in
    step (String.explode pat) (String.explode str)
  end

fun is_supported_test_file path =
  let
    val allowed =
      List.exists (fn prefix => String.isPrefix prefix path)
        allowed_test_prefixes orelse
      List.exists (fn pat => glob_match pat path) allowed_test_patterns
    val excluded =
      List.exists (fn pat => glob_match pat path) excluded_test_patterns
  in
    allowed andalso not excluded
  end

fun list_json_files dir = let
  val d = OS.FileSys.openDir dir
  fun loop acc =
    case OS.FileSys.readDir d of
      NONE => (OS.FileSys.closeDir d; acc)
    | SOME entry =>
        if entry = "." orelse entry = ".." then loop acc
        else let
          val path = OS.Path.concat(dir, entry)
        in
          if OS.FileSys.isDir path then loop (list_json_files path @ acc)
          else if String.isSuffix ".json" entry then loop (path :: acc)
          else loop acc
        end
in
  loop []
end

fun detect_path_sep () =
  case String.explode (OS.Path.concat ("a", "b")) of
    [#"a", sep, #"b"] => String.str sep
  | _ => "/"

val path_sep = detect_path_sep ()
val tests_prefix = String.concat ["tests", path_sep]
val exports_prefix = String.concat ["vyper-test-exports", path_sep]

fun strip_tests_prefix path =
  if String.isPrefix tests_prefix path
  then String.extract(path, String.size tests_prefix, NONE)
  else path

fun strip_exports_prefix path =
  if String.isPrefix exports_prefix path
  then String.extract(path, String.size exports_prefix, NONE)
  else path

fun collapse_underscores s =
  let
    fun step [] acc = String.implode (List.rev acc)
      | step (#"_"::cs) (#"_"::acc) = step cs acc
      | step (c::cs) acc = step cs (c::acc)
  in
    step (String.explode s) []
  end

fun json_path_to_id path = let
  val path = strip_exports_prefix path
  val base =
    if String.isSuffix ".json" path
    then String.extract(path, 0, SOME (String.size path - 5))
    else path
  val lower = String.map Char.toLower base
  fun sanitize c = if Char.isAlphaNum c then c else #"_"
  val cleaned = String.implode (List.map sanitize (String.explode lower))
  val collapsed = collapse_underscores cleaned
in
  if String.size collapsed = 0 then "empty" else collapsed
end

val deployment : term decoder =
  check_trace_type "deployment" $
  JSONDecode.map (fn (((((srcs_exps_imap,(i,h,bh),(s,m,a,g),(d,bn,bf,v)),e),bc),sl),bp) =>
             (* translate_annotated_ast returns (sources, exports, import_map) *)
             let val (srcs, exps_import_map) = pairSyntax.dest_pair srcs_exps_imap
                 val (exps, import_map) = pairSyntax.dest_pair exps_import_map in
             TypeBase.mk_record (deployment_trace_ty, [
               ("sourceAst", srcs),
               ("sourceExports", exps),
               ("importMap", import_map),
               ("contractAbi", mk_list(i, abi_entry_ty)),
               ("deployedAddress", a),
               ("deployer", s),
               ("deploymentSuccess", e),
               ("value", v),
               ("timeStamp", m),
               ("blockNumber", bn),
               ("blockHashes", h),
               ("blobHashes", bh),
               ("blobBaseFee", bf),
               ("gasPrice", g),
               ("chainId", numSyntax.term_of_int 1),
               ("callData", d),
               ("runtimeBytecode", bc),
               ("storageLayout", sl),
               ("isBlueprint", bp)
             ]) end)
          (tuple2 (tuple2 (tuple2 (tuple2 (tuple4 (toplevels_via_jsonast,
                           tuple3 (
                             field "contract_abi" (array abiEntry),
                             field "env" $ field "block" $
                               field "block_hashes" blockHashes,
                             field "env" $ field "tx" $
                               field "blob_hashes" blobHashes),
                           tuple4 (field "env" $ field "tx" $ field "origin" address,
                                   field "env" $ field "block" $ field "timestamp" numtm,
                                   field "deployed_address" address,
                                   field "env" $ field "tx" $ field "gas_price" numtm),
                           tuple4 (field "calldata" $
                                   JSONDecode.map (cached_bytes_from_hex o theoptstring)
                                     (nullable string),
                                   field "env" $ field "block" $ field "number" numtm,
                                   field "env" $ field "block" $ field "blob_basefee" numtm,
                                   field "value" numtm)),
                   field "deployment_succeeded" booltm),
                  field "runtime_bytecode" bytes),
                 field "storage_layout" storage_layout),
                JSONDecode.map (fn s => mk_bool (s = "blueprint"))
                  (field "deployment_type" string)))

val trace : term decoder =
  achoose "trace" [
    JSONDecode.map (curry mk_comb Call_tm) call,
    JSONDecode.map (curry mk_comb Deployment_tm) deployment,
    check_trace_type "clear_transient_storage" $
      succeed ClearTransientStorage_tm,
    JSONDecode.map (fn (a,b) => list_mk_comb(SetBalance_tm, [a,b])) $
    tuple2 (
      field "address" address,
      field "value" numtm)
  ]

(* ===== Fixture / dependency support ===== *)
(* Fixtures are shared setup items (item_type = "fixture") that tests depend
   on via their "deps" field. We resolve deps by prepending fixture traces
   to the test's own traces, so each test runs from a clean state with
   the fixture setup applied first. All current deps are same-file. *)

val fixture_decoder =
  check_field "item_type" "fixture" $
  field "traces" (array trace)

(* Decoder for test items with deps: reads both "deps" and "traces" fields. *)
val test_with_deps_decoder =
  check_field "item_type" "test" $
  tuple2 (field "deps" (array string),
          field "traces" (array trace))

(* Extract fixture name from a dep string.
   Dep format: "tests/export/functional/.../test_file.json/fixture_name"
   We take the part after the last '/' as the fixture name. *)
fun fixture_name_of_dep dep =
  case String.fields (fn c => c = #"/") dep of
    [] => ""
  | parts => List.last parts

(* Pass 1: collect fixtures from JSON items into a lookup dictionary.
   Keep the raw JSON for source eligibility checks as well as the decoded traces. *)
fun collect_fixture ((name, json), acc) =
  if decode (field "item_type" string) json = "fixture"
  then let
    val traces = decode fixture_decoder json
  in
    (name, json, traces) :: acc
  end
  else acc

(* Pass 2: decode test items, resolving the directly listed (already flattened)
   deps by prepending fixture traces in their declared order. *)
fun trydecode_with_fixtures fixtures
      ((name,json),(selected,failures,name_skips,source_skips,non_tests)) =
  if decode (field "item_type" string) json <> "test"
  then (selected,failures,name_skips,source_skips,non_tests + 1)
  else if List.exists (fn pat => glob_match pat name) excluded_test_names
  then (selected,failures,name::name_skips,source_skips,non_tests)
  else let
    val (dep_names, test_traces) = decode test_with_deps_decoder json
    fun resolve dn =
      case List.find
        (fn (fixture_name, _, _) => fixture_name = fixture_name_of_dep dn)
        fixtures of
        NONE => raise Fail ("unresolved fixture dependency: " ^ dn)
      | SOME fixture => fixture
    val resolved = List.map resolve dep_names
    val fixture_jsons =
      List.map (fn (_, fixture_json, _) => fixture_json) resolved
    val fixture_traces =
      List.concat (List.map (fn (_, _, traces) => traces) resolved)
    val source_reason = unsupported_source_reason_for (fixture_jsons @ [json])
  in
    if List.exists (equal name) allowed_test_names then
      ((name, fixture_traces @ test_traces) :: selected,
       failures,name_skips,source_skips,non_tests)
    else case source_reason of
      SOME reason =>
        (selected,failures,name_skips,(name,reason)::source_skips,non_tests)
    | NONE =>
        ((name, fixture_traces @ test_traces) :: selected,
         failures,name_skips,source_skips,non_tests)
  end
  handle JSONError e =>
           (selected,(name,JSONError e)::failures,
            name_skips,source_skips,non_tests)
       | e =>
           (selected,
            (name,JSONError (e,JSON.OBJECT [("source_code",JSON.STRING "")]))
              ::failures,
            name_skips,source_skips,non_tests)

fun read_test_json json_path = let
  val test_jsons = decodeFile rawObject json_path
  val fixtures = List.foldl collect_fixture [] test_jsons
  val (selected,failures,name_skips,source_skips,non_tests) =
    List.foldl (trydecode_with_fixtures fixtures) ([],[],[],[],0) test_jsons
in
  {selected = selected,
   failures = failures,
   name_skips = name_skips,
   source_skips = source_skips,
   total_items = List.length test_jsons,
   fixtures = List.length fixtures,
   non_tests = non_tests}
end

val trace_ty = mk_thy_type{Thy="vyperTestRunner",Tyop="trace",Args=[]}
val traces_ty = mk_list_type trace_ty

fun lexless a b = String.compare (a, b) = LESS

fun test_files () =
  list_json_files test_exports_root
  |> List.map strip_tests_prefix
  |> List.filter is_supported_test_file
  |> Lib.sort lexless
  |> List.map (fn path => (json_path_to_id path, path))

fun cleanup_generated_scripts files = let
  val keep =
    List.map (fn (id, _) => String.concat ["vyperTestDefs_", id, "Script.sml"]) files @
    List.map (fn (id, _) => String.concat ["vyperTest_", id, "Script.sml"]) files
  fun is_keep name = List.exists (fn k => k = name) keep
  fun is_gen name =
    (String.isPrefix "vyperTestDefs_" name orelse
     String.isPrefix "vyperTest_" name) andalso
    String.isSuffix "Script.sml" name
  val gen_dir = generated_dir
  fun loop d =
    case OS.FileSys.readDir d of
      NONE => ()
    | SOME entry =>
        if entry = "." orelse entry = ".." then loop d
        else let
          val path = OS.Path.concat(gen_dir, entry)
        in
          if is_gen entry andalso not (is_keep entry) then
            (OS.FileSys.remove path handle _ => ())
          else ();
          loop d
        end
  val d = OS.FileSys.openDir gen_dir
  val () = loop d
  val () = OS.FileSys.closeDir d
in
  ()
end

fun holbuild_extra_deps (_ : string list) = ()
fun holbuild_extra_outputs (_ : string list) = ()

fun print_file_coverage json_path report = let
  val tests = #selected report
  val decode_fails = #failures report
  val trace_count =
    List.foldl (fn ((_,traces),n) => List.length traces + n) 0 tests
  val () = TextIO.print (String.concat
    ["[vyper-coverage] file=", json_path,
     " items=", Int.toString (#total_items report),
     " fixtures=", Int.toString (#fixtures report),
     " non_tests=", Int.toString (#non_tests report),
     " selected=", Int.toString (List.length tests),
     " traces=", Int.toString trace_count,
     " excluded_name=", Int.toString (List.length (#name_skips report)),
     " excluded_source=", Int.toString (List.length (#source_skips report)),
     " decode_failures=", Int.toString (List.length decode_fails), "\n"])
  val () = List.app (fn name => TextIO.print (String.concat
    ["[vyper-coverage] excluded file=", json_path,
     " test=", name, " reason=excluded test name\n"]))
    (List.rev (#name_skips report))
  val () = List.app (fn (name,reason) => TextIO.print (String.concat
    ["[vyper-coverage] excluded file=", json_path,
     " test=", name, " reason=", reason, "\n"]))
    (List.rev (#source_skips report))
  val () =
    if List.null tests then TextIO.print (String.concat
      ["[vyper-coverage] warning file=", json_path,
       " has no selected tests\n"])
    else ()
in
  ()
end

(* Raw JSON inventory for standalone reporting.  Unlike read_test_json, this
   deliberately does not decode traces into HOL terms (byte decoding creates
   cached HOL definitions and therefore requires an active theory). *)
fun raw_string_field key (JSON.OBJECT fields) =
      (case List.find (fn (name,_) => name = key) fields of
         SOME (_,JSON.STRING value) => SOME value
       | _ => NONE)
  | raw_string_field _ _ = NONE

fun raw_array_length_field key (JSON.OBJECT fields) =
      (case List.find (fn (name,_) => name = key) fields of
         SOME (_,JSON.ARRAY values) => SOME (List.length values)
       | _ => NONE)
  | raw_array_length_field _ _ = NONE

fun raw_string_array_field key (JSON.OBJECT fields) =
      (case List.find (fn (name,_) => name = key) fields of
         SOME (_,JSON.ARRAY values) =>
           SOME (List.mapPartial
             (fn JSON.STRING value => SOME value | _ => NONE) values)
       | _ => NONE)
  | raw_string_array_field _ _ = NONE

fun read_coverage_json json_path = let
  val items = decodeFile rawObject json_path
  val fixtures = List.mapPartial (fn (name,json) =>
    if raw_string_field "item_type" json = SOME "fixture"
    then SOME (name,json) else NONE) items
  fun deps json = Option.getOpt (raw_string_array_field "deps" json,[])
  fun fixture_for dep =
    List.find (fn (name,_) => name = fixture_name_of_dep dep) fixtures
  fun fixture_trace_count dep =
    case fixture_for dep of
      NONE => 0
    | SOME (_,json) => Option.getOpt (raw_array_length_field "traces" json,0)
  val referenced_fixtures =
    List.concat (List.map (fn (_,json) => deps json) items)
  val unreferenced_traced_fixtures = List.mapPartial (fn (name,json) =>
    if Option.getOpt (raw_array_length_field "traces" json,0) > 0 andalso
       not (List.exists (fn dep => fixture_name_of_dep dep = name)
         referenced_fixtures)
    then SOME name else NONE) fixtures
  fun classify ((name,json),
      (non_tests,selected,direct_traces,expanded_traces,name_skips,
       pattern_skips,no_traces,fixture_source,missing_source,blank_source,
       unresolved_deps,malformed)) =
    case raw_string_field "item_type" json of
      SOME "fixture" =>
        (non_tests,selected,direct_traces,expanded_traces,name_skips,
         pattern_skips,no_traces,fixture_source,missing_source,blank_source,
         unresolved_deps,malformed)
    | SOME "test" => let
        val direct = Option.getOpt (raw_array_length_field "traces" json,0)
        val item_deps = deps json
        val resolved_fixture_jsons = List.mapPartial
          (fn dep => case fixture_for dep of
             NONE => NONE
           | SOME (_,fixture_json) => SOME fixture_json) item_deps
        val unresolved = List.mapPartial
          (fn dep => if Option.isSome (fixture_for dep)
                     then NONE else SOME (name,dep)) item_deps
        val unresolved_deps = unresolved @ unresolved_deps
        val expanded = direct + List.foldl
          (fn (dep,n) => fixture_trace_count dep + n) 0 item_deps
        val source_from_fixture =
          List.null (source_codes_json json) andalso
          not (List.null
            (List.concat (List.map source_codes_json resolved_fixture_jsons)))
        fun keep_selected () =
          (non_tests,selected + 1,direct + direct_traces,
           expanded + expanded_traces,name_skips,pattern_skips,no_traces,
           if source_from_fixture then name::fixture_source else fixture_source,
           missing_source,blank_source,unresolved_deps,malformed)
      in
        if List.exists (fn pat => glob_match pat name) excluded_test_names
        then (non_tests,selected,direct_traces,expanded_traces,
              name::name_skips,pattern_skips,no_traces,fixture_source,
              missing_source,blank_source,unresolved_deps,malformed)
        else if List.exists (equal name) allowed_test_names
        then keep_selected ()
        else
          case unsupported_source_reason_for (resolved_fixture_jsons @ [json]) of
            NONE => keep_selected ()
          | SOME reason =>
              if expanded = 0 then
                (non_tests,selected,direct_traces,expanded_traces,name_skips,
                 pattern_skips,name::no_traces,fixture_source,missing_source,
                 blank_source,unresolved_deps,malformed)
              else if reason = "missing source_code" then
                (non_tests,selected,direct_traces,expanded_traces,name_skips,
                 pattern_skips,no_traces,fixture_source,name::missing_source,
                 blank_source,unresolved_deps,malformed)
              else if reason = "blank source_code" then
                (non_tests,selected,direct_traces,expanded_traces,name_skips,
                 pattern_skips,no_traces,fixture_source,missing_source,
                 name::blank_source,unresolved_deps,malformed)
              else
                (non_tests,selected,direct_traces,expanded_traces,name_skips,
                 (name,reason)::pattern_skips,no_traces,fixture_source,
                 missing_source,blank_source,unresolved_deps,malformed)
      end
    | SOME _ =>
        (non_tests + 1,selected,direct_traces,expanded_traces,name_skips,
         pattern_skips,no_traces,fixture_source,missing_source,blank_source,
         unresolved_deps,malformed)
    | NONE =>
        (non_tests,selected,direct_traces,expanded_traces,name_skips,
         pattern_skips,no_traces,fixture_source,missing_source,blank_source,
         unresolved_deps,name::malformed)
  val (non_tests,selected,direct_traces,expanded_traces,name_skips,
       pattern_skips,no_traces,fixture_source,missing_source,blank_source,
       unresolved_deps,malformed) =
    List.foldl classify (0,0,0,0,[],[],[],[],[],[],[],[]) items
in
  {total_items = List.length items,
   fixtures = List.length fixtures,
   non_tests = non_tests,
   selected = selected,
   direct_traces = direct_traces,
   expanded_traces = expanded_traces,
   name_skips = name_skips,
   pattern_skips = pattern_skips,
   no_traces = no_traces,
   fixture_source = fixture_source,
   missing_source = missing_source,
   blank_source = blank_source,
   unresolved_deps = unresolved_deps,
   unreferenced_traced_fixtures = unreferenced_traced_fixtures,
   malformed = malformed}
end

fun print_raw_coverage output json_path report = let
  fun emit text = TextIO.output(output,text)
  val () = emit (String.concat
    ["[vyper-coverage] file=", json_path,
     " items=", Int.toString (#total_items report),
     " fixtures=", Int.toString (#fixtures report),
     " non_tests=", Int.toString (#non_tests report),
     " selected=", Int.toString (#selected report),
     " direct_traces=", Int.toString (#direct_traces report),
     " expanded_traces=", Int.toString (#expanded_traces report),
     " excluded_name=", Int.toString (List.length (#name_skips report)),
     " excluded_pattern=", Int.toString (List.length (#pattern_skips report)),
     " no_exported_traces=", Int.toString (List.length (#no_traces report)),
     " source_from_fixture=", Int.toString (List.length (#fixture_source report)),
     " missing_source=", Int.toString (List.length (#missing_source report)),
     " blank_source=", Int.toString (List.length (#blank_source report)),
     " unresolved_fixture_deps=",
       Int.toString (List.length (#unresolved_deps report)),
     " malformed_items=", Int.toString (List.length (#malformed report)), "\n"])
  val () = List.app (fn name => emit (String.concat
    ["[vyper-coverage] excluded file=", json_path,
     " test=", name, " reason=excluded test name\n"]))
    (List.rev (#name_skips report))
  val () = List.app (fn (name,reason) => emit (String.concat
    ["[vyper-coverage] excluded file=", json_path,
     " test=", name, " reason=", reason, "\n"]))
    (List.rev (#pattern_skips report))
  fun emit_named reason names = List.app (fn name => emit (String.concat
    ["[vyper-coverage] excluded file=", json_path,
     " test=", name, " reason=", reason, "\n"])) (List.rev names)
  val () = emit_named "no exported traces" (#no_traces report)
  val () = List.app (fn name => emit (String.concat
    ["[vyper-coverage] selected file=", json_path,
     " test=", name, " reason=source supplied by fixture\n"]))
    (List.rev (#fixture_source report))
  val () = emit_named "missing source_code in traceful item" (#missing_source report)
  val () = emit_named "blank source_code" (#blank_source report)
  val () = List.app (fn (name,dep) => emit (String.concat
    ["[vyper-coverage] unresolved fixture file=", json_path,
     " test=", name, " dep=", dep, "\n"]))
    (List.rev (#unresolved_deps report))
  val () = List.app (fn name => emit (String.concat
    ["[vyper-coverage] fixture file=", json_path,
     " name=", name, " reason=unreferenced fixture with traces\n"]))
    (List.rev (#unreferenced_traced_fixtures report))
  val () = List.app (fn name => emit (String.concat
    ["[vyper-coverage] malformed file=", json_path,
     " item=", name, " reason=missing item_type\n"]))
    (List.rev (#malformed report))
in
  if #selected report = 0 then emit (String.concat
    ["[vyper-coverage] warning file=", json_path,
     " has no selected tests\n"])
  else ()
end

fun write_coverage_report output_path = let
  val files = test_files ()
  val reports = List.map (fn (_,path) => (path,read_coverage_json path)) files
  fun sum field = List.foldl (fn ((_,report),n) => field report + n) 0 reports
  val total_items = sum #total_items
  val fixtures = sum #fixtures
  val non_tests = sum #non_tests
  val selected = sum #selected
  val direct_traces = sum #direct_traces
  val expanded_traces = sum #expanded_traces
  val excluded_name = sum (List.length o #name_skips)
  val excluded_pattern = sum (List.length o #pattern_skips)
  val no_traces = sum (List.length o #no_traces)
  val fixture_source = sum (List.length o #fixture_source)
  val missing_source = sum (List.length o #missing_source)
  val blank_source = sum (List.length o #blank_source)
  val unresolved_deps = sum (List.length o #unresolved_deps)
  val unreferenced_fixtures = sum
    (List.length o #unreferenced_traced_fixtures)
  val malformed = sum (List.length o #malformed)
  val zero_selected = sum (fn report => if #selected report = 0 then 1 else 0)
  val output = TextIO.openOut output_path
  fun emit text = TextIO.output(output,text)
  fun write () = let
    val () = emit (String.concat
      ["[vyper-coverage] admitted_files=", Int.toString (List.length files), "\n"])
    val () = List.app (fn (json_path,report) =>
      print_raw_coverage output json_path report) reports
  in
    emit (String.concat
      ["[vyper-coverage] summary admitted_files=", Int.toString (List.length files),
       " items=", Int.toString total_items,
       " fixtures=", Int.toString fixtures,
       " non_tests=", Int.toString non_tests,
       " selected=", Int.toString selected,
       " direct_traces=", Int.toString direct_traces,
       " expanded_traces=", Int.toString expanded_traces,
       " excluded_name=", Int.toString excluded_name,
       " excluded_pattern=", Int.toString excluded_pattern,
       " no_exported_traces=", Int.toString no_traces,
       " source_from_fixture=", Int.toString fixture_source,
       " missing_source=", Int.toString missing_source,
       " blank_source=", Int.toString blank_source,
       " unresolved_fixture_deps=", Int.toString unresolved_deps,
       " unreferenced_traced_fixtures=", Int.toString unreferenced_fixtures,
       " malformed_items=", Int.toString malformed,
       " zero_selected_files=", Int.toString zero_selected, "\n"])
  end
in
  (write () before TextIO.closeOut output)
  handle e => (TextIO.closeOut output; raise e)
end

fun make_definitions_for_file (id, json_path) = let
  val report = read_test_json json_path
  val tests = #selected report
  val decode_fails = #failures report
  val () = print_file_coverage json_path report
  val () =
    case decode_fails of
        [] => ()
      | (name, err)::_ =>
          raise Fail (
            String.concat ["decode failure in ", json_path, ": ", name,
                           " - ", exnMessage err, " (",
                           Int.toString (List.length decode_fails),
                           " tests failed to decode)"])
  val path_vn = String.concat["json_path_", id]
  val path_def = new_definition(path_vn ^ "_def",
                   mk_eq(mk_var(path_vn, string_ty),
                         fromMLstring json_path))
  val traces_prefix = String.concat ["traces_", id, "_"]
  val test_name_prefix = String.concat ["name_", id, "_"]
  fun define_traces i (name, traces) = let
    val trs = mk_list(traces, trace_ty)
    val tn = Int.toString i
    val vn = traces_prefix ^ tn
    val var = mk_var(vn, traces_ty)
    val def = new_definition(vn ^ "_def", mk_eq(var, trs))
    val () = cv_trans def
    val vn = test_name_prefix ^ tn
    val def = new_definition(vn ^ "_def",
      mk_eq(mk_var(vn, string_ty), fromMLstring name))
  in () end
in
  Lib.appi define_traces tests
end

fun generate_defn_scripts () = let
  val () = check_generate_dirs ()
  val files = test_files ()
  val gen_dir = generated_dir
  val () = cleanup_generated_scripts files
  val () = List.app (fn (id, jsonp) => let
    val thyname = String.concat["vyperTestDefs_", id]
    val fname = OS.Path.concat(gen_dir, String.concat[thyname, "Script.sml"])
    (* Path is relative to tests/generated/, so prepend ../ to reach tests/vyper-test-exports *)
    val jsonp_from_generated = OS.Path.concat("..", jsonp)
    val contents = String.concat [
      "Theory ", thyname, "[no_sig_docs]\nAncestors jsonToVyper\nLibs vyperTestLib\n",
      "val () = holbuild_extra_deps [\"", jsonp_from_generated, "\"];\n",
      "val () = make_definitions_for_file (\"", id, "\", \"", jsonp_from_generated, "\");\n"]
    val out = TextIO.openOut(fname)
    val () = TextIO.output(out, contents)
    val () = TextIO.closeOut out
  in () end) files
in
  ()
end

fun generate_test_scripts () = let
  val () = check_generate_dirs ()
  val files = test_files ()
  val gen_dir = generated_dir
  val () = cleanup_generated_scripts files
  val () = List.app (fn (id, _) => let
    val thyname = String.concat["vyperTest_", id]
    val defsname = String.concat["vyperTestDefs_", id]
    val fname = OS.Path.concat(gen_dir, String.concat[thyname, "Script.sml"])
    val contents = String.concat [
      "Theory ", thyname, "[no_sig_docs]\nAncestors ", defsname,
      "\nLibs vyperTestRunnerLib\nval () = List.app ",
      "run_test_on_traces $ all_traces \"", defsname, "\";\n"]
    val out = TextIO.openOut(fname)
    val () = TextIO.output(out, contents)
    val () = TextIO.closeOut out
  in () end) files
in
  ()
end

fun generate_tests () = (
  generate_defn_scripts ();
  generate_test_scripts ()
)

end
