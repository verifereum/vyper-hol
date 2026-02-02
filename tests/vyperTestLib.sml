structure vyperTestLib :> vyperTestLib = struct

open HolKernel boolLib bossLib cv_transLib wordsLib
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
  rhs
end

(* Decoder that uses the jsonAST pipeline with full module support *)
val toplevels_via_jsonast : term decoder =
  JSONDecode.map translate_jsonast_to_vyper annotated_ast

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
val stringToNumTm =
  numSyntax.term_of_int o
  Option.valOf o Int.fromString

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
  "def boo(a: DynArray[uint256, 12] =", (* TODO: default argument values *)
  "def addition(a: uint256, b: uint256 = 1)", (* TODO: ditto *)
  "def test(a: uint256, b: String[50] =", (* TODO: ditto *)
  "def test2(l: bytes2 =", (* TODO: ditto *)
  "def test2(l: Bytes[2] =", (* TODO: ditto *)
  "def test2(l: Bytes[3] =", (* TODO: ditto *)
  "def test2(l: Bytes[4] =", (* TODO: ditto *)
  "def test2(l: bytes3 =", (* TODO: ditto *)
  "def test2(l: bytes4 =", (* TODO: ditto *)
  "def foo(a: Bytes[65] =", (* TODO: ditto *)
  "def foo(a: String[65] =", (* TODO: ditto *)
  "def foo(a: uint256 =", (* TODO: ditto *)
  "def foo(a: uint256[3] =", (* TODO: ditto *)
  "def foo(a: DynArray[uint256, 3] =", (* TODO: ditto *)
  "def fooBar(a: int128 =", (* TODO: ditto *)
  "def outer(xs: Bytes[256] = ", (* TODO: default arguments on external fns *)
  "@raw_return\n" (* TODO: add *)
]

val unsupported_patterns = unsupported_code @ [
  "extcall ",
  "staticcall ",
  "raw_call(",
  "raw_log(",
  "raw_revert(",
  "selfdestruct",
  "msg.mana", "msg.gas",
  "exports",
  "import ",
  "create_minimal_proxy_to(",
  "create_copy_of("
]

fun has_default_arg src =
  let
    val n = String.size src
    fun find_sub sub i =
      let val m = String.size sub in
        if i + m > n then NONE
        else if String.substring (src, i, m) = sub then SOME i
        else find_sub sub (i + 1)
      end
    fun find_char c i =
      if i >= n then NONE
      else if String.sub (src, i) = c then SOME i
      else find_char c (i + 1)
    fun has_default_from i =
      case find_sub "def " i of
        NONE => false
      | SOME d =>
          (case find_char #"(" (d + 4) of
             NONE => false
           | SOME l =>
               (case find_char #")" (l + 1) of
                  NONE => false
                | SOME r =>
                    let
                      val args = String.substring (src, l + 1, r - l - 1)
                    in
                      String.isSubstring "=" args orelse has_default_from (r + 1)
                    end))
  in
    has_default_from 0
  end

fun has_sqrt_call src =
  let
    val n = String.size src
    fun loop i =
      if i + 5 > n then false
      else if String.substring (src, i, 5) = "sqrt(" andalso
              (i = 0 orelse String.sub (src, i - 1) <> #"i")
           then true
           else loop (i + 1)
  in
    loop 0
  end

fun has_unsupported_patterns src =
  has_default_arg src orelse
  has_sqrt_call src orelse
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

fun has_unsupported_source_json j =
  case source_codes_json j of
    [] => true
  | srcs =>
      List.exists (fn src =>
        String.size src = 0 orelse is_blank src orelse
        has_unsupported_patterns src) srcs

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
  "vyper-test-exports/functional/codegen/"
]

val allowed_test_patterns = [
  "vyper-test-exports/functional/builtins/codegen/test_blobhash.json"
]

val excluded_test_patterns = [
]

(* Individual test names that bypass unsupported pattern checks *)
val allowed_test_names = [
  "test_external_contract_calls_with_uint8[8]"
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
  check (field "source_code" string)
        (fn src => not (has_unsupported_patterns src))
        "has unsupported_pattern" $
  JSONDecode.map (fn ((((c,(i,h,bh),(s,m,a,g),(d,bn,bf,v)),e),bc),sl) =>
             TypeBase.mk_record (deployment_trace_ty, [
               ("sourceAst", c),
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
               ("callData", d),
               ("runtimeBytecode", bc),
               ("storageLayout", sl)
             ]))
          (tuple2 (tuple2 (tuple2 (tuple4 (toplevels_via_jsonast,
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
                 field "storage_layout" storage_layout))

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

val test_decoder =
  (check_field "item_type" "test" $
   field "traces" (array trace))

fun trydecode ((name,json),(s,f)) =
  if List.exists (fn n => n = name) allowed_test_names
     orelse not (has_unsupported_source_json json)
  then ((name, decode test_decoder json)::s, f)
       handle JSONError e => (s, (name, JSONError e)::f)
            | e => (s, (name, JSONError (e, JSON.OBJECT [("source_code", JSON.STRING "")]))::f)
  else (s,f)

fun read_test_json json_path = let
  val test_jsons = decodeFile rawObject json_path
in
  List.foldl trydecode ([],[]) test_jsons
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

fun make_definitions_for_file (id, json_path) = let
  val (tests, decode_fails) = read_test_json json_path
  val () =
    case decode_fails of
        [] => ()
      | (name, err)::_ =>
          TextIO.output(TextIO.stdErr,
            String.concat ["decode failure in ", json_path, ": ", name,
                           " - ", exnMessage err, " (skipping ",
                           Int.toString (List.length decode_fails),
                           " tests)\n"])
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

end
