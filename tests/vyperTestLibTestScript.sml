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
