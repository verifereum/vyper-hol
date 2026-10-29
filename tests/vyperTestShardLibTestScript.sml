Theory vyperTestShardLibTest
Libs vyperTestLib

fun assert label ok = if ok then () else raise Fail label;

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
  fun part thy index = if index = 0 then thy else thy ^ "_part" ^ Int.toString index
  fun contains label text fragment = assert label (String.isSubstring fragment text)
  val () = export 179
  val () = generate_tests ()
  val () = List.app (fn (index, start, count) => let
    val d = get (path (part defs index))
    val t = get (path (part tests index))
  in
    contains "global suite id, not shard id" d
      ("make_definitions_for_file_range (\"" ^ id ^ "\"");
    contains "global range" d (String.concat
      [", ", Int.toString start, ", ", Int.toString count, ");"]);
    contains "JSON provenance dependency" d ".json.provenance";
    contains "execution imports only its own definitions" t ("Ancestors " ^ part defs index ^ "\n");
    contains "complete runner" t ("run_tests_on_traces $ all_traces \"" ^ part defs index ^ "\"")
  end) [(0, 0, 100), (1, 100, 79)]
  (* Both separate generation entry points must preserve the other half. *)
  val () = generate_defn_scripts ()
  val () = assert "definition generation preserves test chunks" (exists (part tests 1))
  val () = generate_test_scripts ()
  val () = assert "test generation preserves definition chunks" (exists (part defs 1))
  val () = export 201
  val () = generate_tests ()
  val () = assert "growing adds complete tail chunk"
    (exists (part defs 2) andalso exists (part tests 2))
  val () = export 101
  val () = generate_tests ()
  val () = assert "shrinking removes obsolete chunks"
    (not (exists (part defs 2)) andalso not (exists (part tests 2)))
  val () = contains "stock chunks refresh their counts"
    (get (path (part defs 1))) ", 100, 1);"
  val () = export 100
  val () = generate_tests ()
  val () = assert "threshold keeps original targets" (exists defs andalso exists tests)
  val () = assert "unsharding removes all old chunks"
    (List.all (fn n => not (exists (part defs n)) andalso
                       not (exists (part tests n))) [1, 2])
  val () = contains "small suite uses original API" (get (path defs))
    ("make_definitions_for_file (\"" ^ id ^ "\"")
  val () = OS.FileSys.remove json
  val () = generate_tests ()
in
  assert "removed suite cleans up both targets" (not (exists defs) andalso not (exists tests))
end;

(* Custom definition scripts carry proof/CV boundaries; generation must not
   discard them, even when invoked only to refresh execution scripts. *)
fun exercise_definition_preservation () = let
  val json = "vyper-test-exports/functional/codegen/test_preservation.json"
  val id = "functional_codegen_test_preservation"
  val defs = "vyperTestDefs_" ^ id
  val tests = "vyperTest_" ^ id
  fun path thy = "generated/" ^ thy ^ "Script.sml"
  fun export total = put json (String.concat ["{",
    String.concatWith "," (List.tabulate (total, fn i => String.concat
      ["\"case_", Int.toString i,
       "\":{\"item_type\":\"test\",\"deps\":[],\"source_code\":\"pass\",",
       "\"traces\":[{\"trace_type\":\"not_decodable\"}]}" ])), "}"])
  val generators = [("combined", generate_tests),
    ("definitions", generate_defn_scripts), ("execution", generate_test_scripts)]
  val boundary = "\n(* Custom JSON/CV proof boundary. *)\nval () = ();\n"
  fun check_preserved label thy custom = List.app (fn (api, generate) => (
    generate ();
    assert (label ^ " via " ^ api) (get (path thy) = custom))) generators
  fun snapshot () = let
    val dir = OS.FileSys.openDir "generated"
    fun loop acc = case OS.FileSys.readDir dir of
        NONE => acc
      | SOME entry => loop ((entry, get ("generated/" ^ entry)) :: acc)
  in loop [] before OS.FileSys.closeDir dir end
  fun check_refused label = let
    val stale = "generated/vyperTestDefs_obsoleteScript.sml"
    val () = put stale "stale target must survive a rejected plan\n"
    val before_files = snapshot ()
    fun check (api, generate) = let
      val failure = (generate (); NONE) handle Fail message => SOME message
    in
      assert (label ^ " reports unsafe custom definitions via " ^ api)
        (failure = SOME "cannot safely update custom Defs script: expected one generated call");
      assert (label ^ " leaves every output untouched via " ^ api)
        (List.length (snapshot ()) = List.length before_files andalso
         List.all (fn (file, text) =>
           OS.FileSys.access ("generated/" ^ file, []) andalso
           get ("generated/" ^ file) = text) before_files)
    end
  in List.app check generators; OS.FileSys.remove stale end
  val () = export 100
  val () = generate_tests ()
  val stock_whole = get (path defs)
  val custom_whole = stock_whole ^ boundary
  val () = put (path defs) custom_whole
  val () = check_preserved "custom whole definitions preserved byte-for-byte"
    defs custom_whole
  val () = put (path tests) "stale execution script\n"
  val () = generate_test_scripts ()
  val () = assert "custom definitions do not prevent execution refresh"
    (get (path defs) = custom_whole andalso
     String.isSubstring ("all_traces \"" ^ defs ^ "\"") (get (path tests)))
  val () = export 101
  val () = generate_tests ()
  val custom_chunk = get (path defs)
  val () = assert "whole-to-chunk retains proof boundary"
    (String.isSuffix boundary custom_chunk andalso
     String.isSubstring "make_definitions_for_file_range" custom_chunk)
  val () = check_preserved "matching custom chunk preserved byte-for-byte"
    defs custom_chunk
  val () = export 179
  val () = check_preserved "custom chunk survives a change in selected total"
    defs custom_chunk
  val tail = defs ^ "_part1"
  val stock_tail = get (path tail)
  val () = put (path tail) (stock_tail ^ boundary)
  val () = export 180
  val () = generate_tests ()
  val () = assert "changed chunk range preserves proof boundary"
    (String.isSuffix boundary (get (path tail)) andalso
     String.isSubstring ", 100, 80);" (get (path tail)))
  val () = export 100
  val before_shrink = snapshot ()
  val () = List.app (fn (api, generate) => let
    val failure = (generate (); NONE) handle Fail message => SOME message
  in
    assert ("obsolete custom chunk is retained via " ^ api)
      (failure = SOME ("obsolete custom test definitions require manual resharding: " ^
        tail ^ "Script.sml"));
    assert ("rejected shrink leaves every output untouched via " ^ api)
      (List.length (snapshot ()) = List.length before_shrink andalso
       List.all (fn (file, text) => get ("generated/" ^ file) = text) before_shrink)
  end) generators
  val () = export 180
  val () = put (path tail) stock_tail
  val () = put (path defs)
    ("Theory " ^ defs ^ "[no_sig_docs]\nAncestors " ^ tail ^ boundary)
  val () = check_refused "custom aggregate cannot silently lose dependencies"
  val () = put (path defs)
    (custom_chunk ^ "val () = make_definitions_for_file (\"extra\", \"extra\");\n")
  val () = check_refused "ambiguous custom calls cannot be overwritten"
  val () = put (path defs) custom_chunk
  val () = export 100
  val () = generate_tests ()
  val () = assert "chunk-to-whole retains proof boundary"
    (get (path defs) = custom_whole)
  val () = put (path defs) stock_whole
in
  OS.FileSys.remove json;
  generate_tests ()
end;

val () = (((exercise_generator (); exercise_definition_preservation ())
    before OS.FileSys.chDir original_dir)
  handle e => (OS.FileSys.chDir original_dir; remove_tree scratch; raise e));
val () = remove_tree scratch;
