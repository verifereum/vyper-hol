Theory vyperTestLibTest
Libs vyperTestLib

fun source code = JSON.OBJECT [("source_code", JSON.STRING code)];

fun expect label expected jsons =
  if unsupported_source_reason_for jsons = expected then ()
  else raise Fail ("source classification: " ^ label);

val _ = expect "calldata len" NONE [source "return len(msg.data)"];
val _ = expect "calldata slice" NONE [source "return slice(msg.data, 0, 4)"];
val _ = expect "calldata raw_call" NONE
  [source "raw_call(target, msg.data, max_outsize=32)"];
val _ = expect "gas retained" (SOME "unsupported source pattern: msg.gas")
  [source "raw_call(target, msg.data, gas=msg.gas)"];
val _ = expect "explicit gas retained" (SOME "unsupported source pattern: gas=")
  [source "raw_call(target, msg.data, gas=1000)"];
val _ = expect "negative missing source" (SOME "missing source_code") [];
val _ = expect "blank source" (SOME "blank source_code") [source " \n"];

val () = load "JsonTraceDecodeFn";

structure TraceDecode = JsonTraceDecodeFn (
  structure B = JsonImportHol
  structure AST = jsonASTLib
  fun translate_annotated_ast jsonast =
    rhs (concl (EVAL (mk_comb (
      prim_mk_const {Thy="jsonToVyper", Name="translate_annotated_ast"},
      jsonast))))
);

(* The portable ABI grammar is a compatibility copy, not a stricter parser.
   Compare terms and acceptance with the pinned implementation. *)
datatype abi_outcome = Parsed of term | Rejected;
fun abi_outcome parse text =
  Parsed (parse text) handle _ => Rejected;
fun check_abi_parity accepted text = let
  val reference = abi_outcome contractABISyntax.parse_abi_type text
  val portable = abi_outcome TraceDecode.parse_abi_type text
  val matches =
    case (reference, portable) of
      (Parsed x, Parsed y) => accepted andalso aconv x y
    | (Rejected, Rejected) => not accepted
    | _ => false
in
  if matches then () else raise Fail ("ABI parser parity: " ^ text)
end;
val () = List.app (check_abi_parity true)
  ["bool", "address", "string", "bytes", "bytes1", "bytes32",
   "uint8", "uint256", "int8", "int256",
   "(uint256,bool)", "(address,(bytes32,string),int128)",
   "uint256[]", "bytes32[2]", "uint8[2][][3]",
   "(uint8,bool)[2][]", "(uint8[],(address,bool)[3])[]",
   (* Preserve inherited numeric-prefix parsing and absent-bound leniency. *)
   "uint7", "uint8suffix", "bytesoops", "uint8[xyz]"];
val () = List.app (check_abi_parity false)
  ["", "uint", "int", "fixed128x18", "tuple", "bool[", "()",
   "(uint8,)", "(uint8,(bool,address)[][2])"];

fun assert_fixture label ok =
  if ok then () else raise Fail ("fixture resolution: " ^ label);
val fixture_metadata = source "return 1";
val fixture_table =
  [("first", fixture_metadata, [1, 2]),
   ("second", source "return 2", [3]),
   ("first", source "return 99", [99])];
val resolved = TraceDecode.resolve_fixtures fixture_table
  ["export/file.json/second", "first", "elsewhere/second"];
val () = assert_fixture "declared order, repeated deps, and lookup precedence"
  (List.map (fn (name, _, _) => name) resolved =
     ["second", "first", "second"] andalso
   List.concat (List.map (fn (_, _, traces) => traces) resolved) = [3, 1, 2, 3]);
val resolved_metadata = List.map (fn (_, json, _) => json) resolved;
val () = expect "source retained from resolved fixtures" NONE resolved_metadata;
val () = expect "blank test still ineligible with fixture source"
  (SOME "blank source_code") (resolved_metadata @ [source " "]);
val () = assert_fixture "empty dependencies"
  (List.null (TraceDecode.resolve_fixtures fixture_table []));
val () = assert_fixture "unresolved dependency retains complete path"
  ((TraceDecode.resolve_fixtures fixture_table
      ["first", "export/file.json/missing"]; false)
   handle Fail message =>
     String.isSubstring "export/file.json/missing" message);

fun balance_trace amount = JSON.OBJECT
  [("trace_type", JSON.STRING "set_balance"),
   ("address", JSON.STRING "0x0000000000000000000000000000000000000001"),
   ("value", JSON.INT (IntInf.fromInt amount))];
fun trace_item kind deps traces = JSON.OBJECT
  [("item_type", JSON.STRING kind),
   ("deps", JSON.ARRAY (List.map JSON.STRING deps)),
   ("traces", JSON.ARRAY (List.map balance_trace traces))];
val exported_cases = JSON.OBJECT
  [("test_b", trace_item "test" ["path/second", "path/first", "path/second"] [4]),
   ("first", trace_item "fixture" ["ignored/already_flattened"] [1, 2]),
   ("test_a", trace_item "test" [] [5]),
   ("second", trace_item "fixture" [] [3])];
val cases = TraceDecode.decode_cases exported_cases;
val () = assert_fixture "test item order"
  (List.map #1 cases = ["test_b", "test_a"]);
fun assert_trace_order ((_, actual), amounts) = let
  val expected =
    #2 (List.hd (TraceDecode.decode_cases
      (JSON.ARRAY (List.map balance_trace amounts))))
in
  assert_fixture "setup precedes test, without recursive expansion"
    (ListPair.allEq (fn (x,y) => aconv x y) (actual, expected))
end;
val () = ListPair.appEq assert_trace_order (cases, [[3, 1, 2, 3, 4], [5]]);
val () = assert_fixture "exported missing fixture is a JSON decode error"
  ((TraceDecode.decode_cases (JSON.OBJECT
      [("missing_dep_test", trace_item "test" ["path/missing"] [])]); false)
   handle JSONDecode.JSONError (Fail _, _) => true
        | _ => false);

(* Chunk partitioning is pure: no JSON decoding, HOL definitions, or generated files. *)
fun check_weighted_chunks (weights, counts) = let
  val total = List.length weights
  val suite_id = "functional_codegen_features_test_example"
  val plan = test_chunks (suite_id, weights)
  fun assert label ok =
    if ok then () else raise Fail
      ("chunk plan " ^ Int.toString total ^ ": " ^ label)
  val () = assert "sizes" (List.map #count plan = counts)
  fun check_layout _ _ [] = ()
    | check_layout part start ((chunk : test_chunk)::rest) = let
        val owned = List.take (List.drop (weights, start), #count chunk)
        val payload = List.foldl op+ 0 owned
        val () = assert "ID" (#id chunk =
          (if part = 0 then suite_id else suite_id ^ "_part" ^ Int.toString part))
        val () = assert "global offset" (#start chunk = start)
        val () = assert "case bound"
          (#count chunk <= 100 andalso
           (#count chunk > 0 orelse total = 0))
        val () = assert "payload bound / oversized singleton"
          (payload <= 262144 orelse #count chunk = 1)
      in check_layout (part + 1) (start + #count chunk) rest end
  val () = check_layout 0 0 plan
  val indices = List.concat (List.map (fn chunk : test_chunk =>
    List.tabulate (#count chunk, fn i => #start chunk + i)) plan)
  val () = assert "coverage/order/no duplicates"
    (indices = List.tabulate (total, fn i => i))
  (* Slice a stand-in for read_test_json's selected list in its existing order.
     Trace/name/result suffixes must use this original suite ID and index. *)
  val selected = List.tabulate (total, fn i =>
    ("test_" ^ Int.toString (total - i), [i, i + 1]))
  val sliced = List.concat (List.map (fn chunk : test_chunk =>
    List.take (List.drop (selected, #start chunk), #count chunk)) plan)
  fun names prefix = List.map (fn i => prefix ^ suite_id ^ "_" ^ Int.toString i)
  val () = assert "selected order" (sliced = selected)
  val () = List.app (fn prefix => assert (prefix ^ "global names")
    (names prefix indices = names prefix (List.tabulate (total, fn i => i))))
    ["traces_", "name_", "result_"]
in () end;

fun check_chunks (total, counts) =
  check_weighted_chunks (List.tabulate (total, fn _ => 0), counts);

val _ = List.app check_chunks
  [(0, [0]), (1, [1]), (99, [99]), (100, [100]), (101, [100, 1]),
   (200, [100, 100]), (201, [100, 100, 1]),
   (739, [100, 100, 100, 100, 100, 100, 100, 39])];

val _ = List.app check_weighted_chunks
  [([131072, 131072, 0], [3]), (* Exactly 262144 is allowed. *)
   ([131072, 131073], [1, 1]), (* One character over the combined budget. *)
   ([262144, 1], [1, 1]),
   ([262145], [1]), (* An oversized final case must never disappear. *)
   ([262145, 0, 262146], [1, 1, 1]), (* Oversized cases are dedicated chunks. *)
   ([0, 262144, 0, 1, 262143, 262145, 0, 262146, 0, 0], [3, 2, 1, 1, 1, 2]),
   (List.tabulate (50, fn _ => 16384), [16, 16, 16, 2]),
   (List.tabulate (101, fn _ => 1), [100, 1])];

val _ = List.app (fn weights =>
  if ((test_chunks ("invalid", weights); false) handle Fail _ => true) then ()
  else raise Fail "negative selected test weight accepted")
  [[~1], [0, ~1, 0], List.tabulate (100, fn _ => 0) @ [~1]];

(* Unowned traces must not populate byteStringCache: those definitions would
   survive slicing and make each chunk reload the entire suite's CV data. *)
val () = holbuild_extra_deps
  ["fixtures/exports/in_static_array/test_in_static_array.json",
   "fixtures/exports/in_static_array/test_in_static_array.json.provenance"];
val fixture = "fixtures/exports/in_static_array/test_in_static_array.json";
fun local_names () =
  List.map (#Name o dest_thy_const) (constants (current_theory ()));
val names_before = local_names ();
val () = make_definitions_for_file_range ("unowned_chunk_probe", fixture, 0, 0);
val added = List.filter
  (fn name => not (List.exists (fn old => old = name) names_before))
  (local_names ());
val () =
  if added = ["json_path_unowned_chunk_probe"] then ()
  else raise Fail "unowned traces created persistent HOL definitions";
val () = make_definitions_for_file_range ("owned_chunk_probe", fixture, 0, 1);
val () =
  if List.exists (fn name => name = "traces_owned_chunk_probe_0")
       (local_names ()) then ()
  else raise Fail "owned trace was not defined";
val () =
  if ((make_definitions_for_file_range ("invalid_range", fixture, 2, 0); false)
      handle Fail _ => true) then ()
  else raise Fail "out-of-bounds test range accepted";
