Theory vyperTestShardLibTest
Libs vyperTestLib

fun assert label ok = if ok then () else raise Fail label;

(* Every selected global index occurs exactly once, including partial tails. *)
val () = List.app (fn total => let
  val parts = test_parts total
  val indices = List.concat (List.map (fn (start, count) =>
    List.tabulate (count, fn i => start + i)) parts)
in
  assert "bounded parts" (List.all (fn (_, n) => n > 0 andalso n <= 64) parts);
  assert "complete disjoint parts" (indices = List.tabulate (total, fn i => i))
end) [0, 1, 63, 64, 65, 128, 129, 739];

fun put path text = let val out = TextIO.openOut path in
  TextIO.output (out, text); TextIO.closeOut out
end;
fun get path = let val input = TextIO.openIn path in
  TextIO.inputAll input before TextIO.closeIn input
end;
fun remove_tree path =
  if OS.FileSys.isDir path then let
    val dir = OS.FileSys.openDir path
    fun loop () = case OS.FileSys.readDir dir of NONE => ()
      | SOME entry => (remove_tree (OS.Path.concat (path, entry)); loop ())
  in loop (); OS.FileSys.closeDir dir; OS.FileSys.rmDir path end
  else OS.FileSys.remove path;

val original_dir = OS.FileSys.getDir ();
val scratch = OS.FileSys.tmpName ();
val () = (OS.FileSys.remove scratch handle OS.SysErr _ => ());
val () = OS.FileSys.mkDir scratch;

fun exercise_generator () = let
  val () = OS.FileSys.chDir scratch
  val () = List.app OS.FileSys.mkDir
    ["generated", "vyper-test-exports", "vyper-test-exports/functional",
     "vyper-test-exports/functional/codegen"]
  val json = "vyper-test-exports/functional/codegen/test_shards.json"
  val id = "functional_codegen_test_shards"
  val defs = "vyperTestDefs_" ^ id
  val tests = "vyperTest_" ^ id
  fun name i = "case_" ^ Int.toString i
  (* Deliberately undecodable traces: generation must never create HOL terms.
     All source eligibility comes from the dependency, as in real exports. *)
  fun item i = String.concat ["\"", name i,
    "\":{\"item_type\":\"test\",\"deps\":[\"fixture\"],",
    "\"traces\":[{\"trace_type\":\"not_decodable\"}]}"]
  val fixture = "\"fixture\":{\"item_type\":\"fixture\",\"traces\":[],\"source_code\":\"pass\"}"
  val excluded = ",\"test_ecrecover_oog_handling\":{\"item_type\":\"test\"}"
  val unsupported = ",\"gas\":{\"item_type\":\"test\",\"deps\":[],\"source_code\":\"msg.gas\"}"
  fun export total = put json (String.concat ["{", fixture, excluded, unsupported,
    if total = 0 then "" else ",",
    String.concatWith "," (List.tabulate (total, item)), "}"])
  fun path thy = "generated/" ^ thy ^ "Script.sml"
  fun exists thy = OS.FileSys.access (path thy, [])
  fun part thy start = thy ^ "_part_" ^ Int.toString start
  fun contains label text fragment = assert label (String.isSubstring fragment text)
  val () = export 179
  val () = assert "fixture selection and reverse export order"
    (selected_test_names_for_file json = List.rev (List.tabulate (179, name)))
  val () = generate_tests ()
  val () = List.app (fn (start, count) => let
    val d = get (path (part defs start))
    val t = get (path (part tests start))
  in
    contains "global suite id, not shard id" d
      ("make_definitions_for_file_part (\"" ^ id ^ "\"");
    contains "global range and stale-selection guard" d (String.concat
      ["{start = ", Int.toString start, ", count = ", Int.toString count, ", total = 179}"]);
    contains "JSON provenance dependency" d ".json.provenance";
    contains "execution imports only its own definitions" t ("Ancestors " ^ part defs start ^ "\n");
    contains "execution count guard" t (" = " ^ Int.toString count ^ " then");
    contains "unchanged runner" t ("run_test_on_traces $ all_traces \"" ^ part defs start ^ "\"");
    contains "definitions aggregate includes each part" (get (path defs)) (part defs start);
    contains "execution aggregate includes each part" (get (path tests)) (part tests start)
  end) [(0, 64), (64, 64), (128, 51)]
  val () = assert "aggregates do not execute or decode"
    (not (String.isSubstring "Libs" (get (path defs))) andalso
     not (String.isSubstring "Libs" (get (path tests))))
  (* Both separate generation entry points must preserve the other half. *)
  val () = generate_defn_scripts ()
  val () = assert "definition generation preserves test shards" (exists (part tests 128))
  val () = generate_test_scripts ()
  val () = assert "test generation preserves definition shards" (exists (part defs 128))
  val () = export 65
  val () = generate_tests ()
  val () = assert "shrinking removes obsolete shards"
    (not (exists (part defs 128)) andalso not (exists (part tests 128)))
  val () = export 64
  val () = generate_tests ()
  val () = assert "threshold keeps original targets" (exists defs andalso exists tests)
  val () = assert "unsharding removes all old shards"
    (List.all (fn n => not (exists (part defs n)) andalso
                       not (exists (part tests n))) [0, 64, 128])
  val () = contains "small suite uses original API" (get (path defs))
    ("make_definitions_for_file (\"" ^ id ^ "\"")
  val () = OS.FileSys.remove json
  val () = generate_tests ()
in
  assert "removed suite cleans up both targets" (not (exists defs) andalso not (exists tests))
end;

val () = ((exercise_generator () before OS.FileSys.chDir original_dir)
  handle e => (OS.FileSys.chDir original_dir; remove_tree scratch; raise e));
val () = remove_tree scratch;
