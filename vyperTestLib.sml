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

val translate_module_tm = prim_mk_const{Thy="jsonToVyper",Name="translate_module"}

fun translate_jsonast_to_vyper jsonast_tm = let
  val app = mk_comb(translate_module_tm, jsonast_tm)
  val thm = EVAL app
  val rhs = rhs (concl thm)
in
  rhs
end

(* Decoder that uses the new jsonAST pipeline *)
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
  has_sqrt_call src orelse
  List.exists (fn x => String.isSubstring x src) unsupported_patterns

fun source_code_opt j =
  (decode (orElse(field "source_code" (nullable string),
                  succeed NONE)) j)
  handle JSONError _ => NONE
       | _ => NONE

fun has_unsupported_source_json j =
  case source_code_opt j of
    NONE => false
  | SOME src => has_unsupported_patterns src

fun has_unsupported_source_code (name, (err, j)) =
  case source_code_opt j of
    NONE => true
  | SOME src => has_unsupported_patterns src

val deployment : term decoder =
  check_trace_type "deployment" $
  check (field "source_code" string)
        (fn src => not (has_unsupported_patterns src))
        "has unsupported_pattern" $
  JSONDecode.map (fn ((c,(i,h,bh),(s,m,a,g),(d,bn,bf,v)),e) =>
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
               ("callData", d)
             ]))
          (tuple2 (tuple4 (toplevels_via_jsonast,
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
                   field "deployment_succeeded" booltm))

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
  if has_unsupported_source_json json then (s,f)
  else ((name, decode test_decoder json)::s, f)
       handle JSONError e => (s, (name, e)::f)
              | e => (s, (name, (e, JSON.OBJECT [("source_code", JSON.STRING "")]))::f)

fun read_test_json json_path = let
  val test_jsons = decodeFile rawObject json_path
in
  List.foldl trydecode ([],[]) test_jsons
end

val trace_ty = mk_thy_type{Thy="vyperTestRunner",Tyop="trace",Args=[]}
val traces_ty = mk_list_type trace_ty

val test_files_with_prefixes = [
  ("vyper-test-exports/functional/codegen",
   ["test_interfaces.json",
    "test_selector_table.json",
    "test_selector_table_stability.json"]),
  ("vyper-test-exports/functional/codegen/calling_convention",
   [
    "test_default_function.json",
    (* TODO: unsupported
    "test_default_parameters.json",
    *)
    (* TODO: uses test deps
    "test_erc20_abi.json",
    *)
    "test_external_contract_calls.json",
    "test_inlineable_functions.json",
    "test_internal_call.json",
    "test_modifiable_external_contract_calls.json",
    "test_new_call_convention.json",
    "test_return.json",
    "test_self_call_struct.json"]),
  ("vyper-test-exports/functional/codegen/environment_variables",
   ["test_blobbasefee.json",
    "test_block_number.json",
    "test_blockhash.json",
    "test_tx.json"]),
  ("vyper-test-exports/functional/codegen/modules",
   ["test_events.json",
    "test_exports.json",
    "test_flag_imports.json",
    "test_interface_imports.json",
    "test_module_constants.json",
    "test_module_variables.json",
    "test_nonreentrant.json",
    "test_stateless_functions.json"]),
  ("vyper-test-exports/functional/codegen/integration",
   ["test_basics.json",
    "test_crowdfund.json",
    "test_escrow.json"]),
  ("vyper-test-exports/functional/codegen/storage_variables",
   ["test_getters.json",
    "test_setters.json",
    "test_storage_variable.json"]),
  ("vyper-test-exports/functional/codegen/types/numbers",
   [
    "test_constants.json",
    "test_decimals.json",
    "test_division.json",
    "test_exponents.json",
    "test_isqrt.json",
    "test_modulo.json",
    "test_signed_ints.json",
    (* TODO: sqrt not yet supported, nor fixtures / imports
    "test_sqrt.json",*)
    "test_unsigned_ints.json"
   ]),
  ("vyper-test-exports/functional/codegen/types",
   [
    "test_array_indexing.json",
    "test_bytes.json",
    "test_bytes_literal.json",
    "test_dynamic_array.json",
    "test_flag.json",
    "test_identifier_naming.json",
    "test_lists.json",
    "test_node_types.json",
    "test_string.json",
    "test_string_literal.json",
    "test_struct.json"
   ]),
  ("vyper-test-exports/functional/codegen/features",
   [
    "test_address_balance.json",
    "test_assert.json",
    "test_assert_unreachable.json",
    "test_assignment.json",
    "test_bytes_map_keys.json",
    "test_clampers.json",
    "test_comments.json",
    "test_comparison.json",
    "test_conditionals.json",
    "test_constructor.json",
    "test_flag_pure_functions.json",
    "test_gas.json",
    "test_immutable.json",
    "test_init.json",
    "test_logging.json",
    "test_logging_bytes_extended.json",
    "test_logging_from_call.json",
    "test_mana.json",
    "test_memory_alloc.json",
    "test_memory_dealloc.json",
    "test_packing.json",
    "test_reverting.json",
    "test_selfdestruct.json",
    "test_short_circuiting.json",
    "test_string_map_keys.json",
    "test_ternary.json",
    "test_transient.json"]),
  ("vyper-test-exports/functional/codegen/features/decorators",
   ["test_nonreentrant.json",
    "test_payable.json",
    "test_private.json",
    "test_public.json",
    "test_pure.json",
    "test_raw_return.json",
    "test_view.json"]),
  ("vyper-test-exports/functional/codegen/features/iteration",
   ["test_break.json",
    "test_continue.json",
    "test_for_in_list.json",
    "test_for_range.json",
    "test_range_in.json"])
]

fun make_test_files [] acc = List.rev acc
  | make_test_files ((pfx,ls)::r) acc =
    make_test_files r $ List.revAppend
      (List.map (curry OS.Path.concat pfx) ls, acc)
val test_files = make_test_files test_files_with_prefixes []

fun make_definitions_for_file (n, json_path) = let
  val nstr = Int.toString n
  val (tests, decode_fails) = read_test_json json_path
  val firstDf = List.find (not o has_unsupported_source_code) decode_fails
  val () = case firstDf of NONE => () | SOME (name, (err, _)) => raise Fail
             (String.concat ["decode failure in ", json_path, ": ", name,
                             " - ", exnMessage err])
  val path_vn = String.concat["json_path_", nstr]
  val path_def = new_definition(path_vn ^ "_def",
                   mk_eq(mk_var(path_vn, string_ty),
                         fromMLstring json_path))
  val traces_prefix = String.concat ["traces_", nstr, "_"]
  val test_name_prefix = String.concat ["name_", nstr, "_"]
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
  fun f i [] = ()
    | f i (t::ts) = let
      val istr = Int.toString i
      val padi = StringCvt.padLeft #"0" 2 istr
      val thyname = String.concat["vyperTestDefs", padi]
      val fname = OS.Path.concat("tests", String.concat[thyname, "Script.sml"])
      val jsonp = t
      val contents = String.concat [
        "Theory ", thyname, "[no_sig_docs]\nAncestors jsonToVyper\nLibs vyperTestLib\n",
        "val () = make_definitions_for_file (", istr, ", \"", jsonp, "\");\n"]
      val out = TextIO.openOut(fname)
      val () = TextIO.output(out, contents)
      val () = TextIO.closeOut out
    in f (i+1) ts end
in
  f 0 test_files
end

fun generate_test_scripts () = let
  fun f i [] = ()
    | f i (_::ts) = let
      val istr = Int.toString i
      val padi = StringCvt.padLeft #"0" 2 istr
      val thyname = String.concat["vyperTest", padi]
      val defsname = String.concat["vyperTestDefs", padi]
      val fname = OS.Path.concat("tests", String.concat[thyname, "Script.sml"])
      val contents = String.concat [
        "Theory ", thyname, "[no_sig_docs]\nAncestors ", defsname,
        "\nLibs vyperTestRunnerLib\nval () = List.app ",
        "run_test_on_traces $ all_traces \"", defsname, "\";\n"]
      val out = TextIO.openOut(fname)
      val () = TextIO.output(out, contents)
      val () = TextIO.closeOut out
    in f (i+1) ts end
in
  f 0 test_files
end

end
