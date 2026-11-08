structure vyperTestLib :> vyperTestLib = struct

open HolKernel boolLib bossLib cv_transLib wordsLib intLib
     pairSyntax listSyntax stringSyntax optionSyntax
     intSyntax wordsSyntax fcpSyntax
     vfmTypesSyntax contractABISyntax byteStringCacheLib
     vyperABITheory vyperASTSyntax vyperTestRunnerTheory
     jsonASTLib jsonToVyperTheory
open JSONDecode

(* Translation evaluates constants with EVAL. *)
local open vyperConstEvalLib in end

(* Decode exported traces through the same portable implementation used by the
   standalone entrypoint; only logical AST translation is HOL-specific. *)
structure TraceDecode = JsonTraceDecodeFn (
  structure B = JsonImportHol
  structure AST = jsonASTLib
  fun translate_annotated_ast jsonast =
    rhs (concl (EVAL (mk_comb (
      prim_mk_const {Thy="jsonToVyper", Name="translate_annotated_ast"},
      jsonast))))
)

val unsupported_code = [
]

val unsupported_patterns = unsupported_code @ [
]

fun has_unsupported_patterns src =
  List.exists (fn x => String.isSubstring x src) unsupported_patterns

fun is_blank s =
  List.all Char.isSpace (String.explode s)

val source_codes_json = TraceDecode.source_codes_json

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
  "vyper-test-exports/functional/builtins/codegen/",
  "vyper-test-exports/functional/builtins/folding/"
]

val allowed_test_patterns = [
  "vyper-test-exports/functional/builtins/codegen/test_blobhash.json",
  (* Tuple-return traces exercise literal subscripts of internal/external calls. *)
  "vyper-test-exports/functional/syntax/test_return_tuple.json"
]

(* Path exclusions carry reportable reasons and tracking issues. *)
val excluded_test_file_rules = [
  (* Unbounded (INF-length) types; vyper-hol models only bounded ones, so
     these stay excluded. *)
  ("vyper-test-exports/functional/codegen/features/test_inf_*",
   "unbounded (INF-length) types are not modelled",
   "https://github.com/vyperlang/vyper/pull/5127")
]

val outside_admitted_suites_reason = "outside currently admitted test suites"
val outside_admitted_suites_issue =
  "https://github.com/verifereum/vyper-hol/issues/36"

(* Negative tests assert a compile-time diagnostic, so they record no deployment
   and no call and there is nothing to replay.  Kept in their own bucket rather
   than counted as semantic exclusions: the checks they need are frontend and
   elaboration work, behind the missing formal front end (issues/46) and the
   partial type checker (issues/47). *)
val no_traces_reason = "no exported traces (negative test, frontend diagnostics)"
val no_traces_issue = "https://github.com/verifereum/vyper-hol/issues/46"

(* Individual test names that bypass unsupported pattern checks *)
val allowed_test_names = [
  (* extcall tests - staticcall now enabled globally *)
  "test_external_contract_call_state_change",
  "test_complicated_external_contract_calls"
]

(* Tests excluded by name - require architectural changes *)
val excluded_test_names = [


  (* Tests using shift() builtin which is not yet translated.
     TODO: add shift builtin support *)
  "test_uint256_mulmod_complex",
  "test_shift_builtin_negative_literal*",
  (* Compiles with unbounded (INF-length) types, which are not modelled;
     stays excluded *)
  "test_json_abi_bytes_slice",
  (* Python reads the subscript base before an index call that mutates it;
     the interpreter reads it after. Back with the subscript-overlap port. *)
  "test_array_index_overlap",
  "test_array_index_overlap_extcall",
  "test_array_index_overlap_attribute",
  (* raw_create evaluates value= after the positional args (source order);
     the interpreter evaluates it first. Back with the CREATE semantics
     change. *)
  "test_raw_create_eval_order",
  (* create_from_blueprint must revert on a code_offset that wraps; the
     interpreter doesn't revert. Back with the CREATE semantics change. *)
  "test_create_from_blueprint_bad_code_offset",
  (* Out-of-gas test - we don't model gas *)
  "test_ecrecover_oog_handling"
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

datatype test_file_disposition =
    AdmittedTestFile
  | ExcludedTestFile of string * string (* reason, issue URL *)

fun test_file_disposition path =
  case List.find (fn (pat,_,_) => glob_match pat path)
                 excluded_test_file_rules of
    SOME (_,reason,issue) => ExcludedTestFile (reason,issue)
  | NONE =>
      if List.exists (fn prefix => String.isPrefix prefix path)
           allowed_test_prefixes orelse
         List.exists (fn pat => glob_match pat path) allowed_test_patterns
      then AdmittedTestFile
      else ExcludedTestFile
        (outside_admitted_suites_reason,outside_admitted_suites_issue)

fun is_supported_test_file path =
  case test_file_disposition path of
    AdmittedTestFile => true
  | ExcludedTestFile _ => false

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


(* Keep selection entirely in raw JSON. In particular, a definitions shard must
   not decode (and cache HOL byte/AST definitions for) the other shards. *)
fun collect_fixture ((name, json), acc) =
  if decode (field "item_type" string) json = "fixture"
  then (name, json) :: acc
  else acc

(* Resolve directly listed (already flattened) dependencies and apply the
   original source/name filters without decoding traces. *)
fun select_with_fixtures fixtures
      ((name,json),(selected,failures,name_skips,source_skips,non_tests)) =
  if decode (field "item_type" string) json <> "test"
  then (selected,failures,name_skips,source_skips,non_tests + 1)
  else if List.exists (fn pat => glob_match pat name) excluded_test_names
  then (selected,failures,name::name_skips,source_skips,non_tests)
  else let
    val dep_names = decode (field "deps" (array string)) json
    fun resolve dn =
      case List.find
        (fn (fixture_name, _) => fixture_name = TraceDecode.fixture_name_of_dep dn)
        fixtures of
        NONE => raise Fail ("unresolved fixture dependency: " ^ dn)
      | SOME fixture => fixture
    val resolved = List.map resolve dep_names
    val fixture_jsons = List.map #2 resolved
    val source_reason = unsupported_source_reason_for (fixture_jsons @ [json])
    fun select () =
      ((name, (resolved, json)) :: selected,
       failures,name_skips,source_skips,non_tests)
  in
    if List.exists (equal name) allowed_test_names then select ()
    else case source_reason of
      SOME reason =>
        (selected,failures,name_skips,(name,reason)::source_skips,non_tests)
    | NONE => select ()
  end
  handle JSONError e =>
           (selected,(name,JSONError e)::failures,
            name_skips,source_skips,non_tests)
       | e =>
           (selected,
            (name,JSONError (e,JSON.OBJECT [("source_code",JSON.STRING "")]))
              ::failures,
            name_skips,source_skips,non_tests)

fun select_test_json json_path = let
  val test_jsons = decodeFile rawObject json_path
  val fixtures = List.foldl collect_fixture [] test_jsons
  val (selected,failures,name_skips,source_skips,non_tests) =
    List.foldl (select_with_fixtures fixtures) ([],[],[],[],0) test_jsons
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

fun generated_script_names ids =
  List.map (fn id => String.concat ["vyperTestDefs_", id, "Script.sml"]) ids @
  List.map (fn id => String.concat ["vyperTest_", id, "Script.sml"]) ids

fun is_generated_script name =
  (String.isPrefix "vyperTestDefs_" name orelse
   String.isPrefix "vyperTest_" name) andalso
  String.isSuffix "Script.sml" name

(* Directory basenames must contain both scripts for every planned chunk. *)
fun check_generated_script_inventory ids entries = let
  val expected = Lib.sort lexless (generated_script_names ids)
  val actual = Lib.sort lexless (List.filter is_generated_script entries)
  fun absent xs ys = List.filter (fn x => not (List.exists (equal x) ys)) xs
in
  if expected = actual then ()
  else raise Fail (String.concat [
    "generated script inventory mismatch (regenerate test scripts)",
    "\nmissing: ", String.concatWith ", " (absent expected actual),
    "\nunexpected: ", String.concatWith ", " (absent actual expected)])
end

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
  fun stock_definition entry text =
    case String.fields (fn c => c = #"\n") text of
      [theory, ancestors, libs, deps, call, ""] =>
        theory = "Theory " ^
          String.substring (entry, 0, String.size entry - String.size "Script.sml") ^
          "[no_sig_docs]" andalso
        ancestors = "Ancestors jsonToVyper" andalso libs = "Libs vyperTestLib" andalso
        String.isPrefix "val () = holbuild_extra_deps [" deps andalso
        String.isSuffix "];" deps andalso
        (String.isPrefix "val () = make_definitions_for_file (" call orelse
         String.isPrefix "val () = make_definitions_for_file_range (" call)
    | _ => false
  fun loop d acc =
    case OS.FileSys.readDir d of
      NONE => acc
    | SOME entry =>
        if entry = "." orelse entry = ".." then loop d acc
        else let
          val path = OS.Path.concat(gen_dir, entry)
          val obsolete = is_gen entry andalso not (is_keep entry)
          val () = if obsolete andalso String.isPrefix "vyperTestDefs_" entry
            then let
              val input = TextIO.openIn path
              val text = TextIO.inputAll input before TextIO.closeIn input
            in
              if stock_definition entry text then ()
              else raise Fail ("obsolete custom test definitions require manual resharding: " ^ entry)
            end else ()
        in
          loop d (if obsolete then path :: acc else acc)
        end
  val d = OS.FileSys.openDir gen_dir
  val obsolete = loop d [] handle e => (OS.FileSys.closeDir d; raise e)
  val () = OS.FileSys.closeDir d
in
  List.app OS.FileSys.remove obsolete
end

fun holbuild_extra_deps (_ : string list) = ()
fun holbuild_extra_outputs (_ : string list) = ()

val () = holbuild_extra_deps [
  "../VYPER_PIN", "semantics-profile.json", "semantics-test-constraints.txt",
  "semantics-build-constraints.txt",
  "../tools/vyper_test_exports.py",
  "../tools/vyper_test_export_plugin.py",
  "../.github/actions/setup-vyper-test-exports/action.yml",
  "vyper-regression"
];

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

(* Lightweight inventory for files excluded before executable-test selection. *)
fun read_raw_file_inventory json_path = let
  val items = decodeFile rawObject json_path
  fun count ((_,json),(tests,fixtures,other_items,direct_traces)) =
    let
      val traces = Option.getOpt (raw_array_length_field "traces" json,0)
    in
      case raw_string_field "item_type" json of
        SOME "test" => (tests + 1,fixtures,other_items,
                        direct_traces + traces)
      | SOME "fixture" => (tests,fixtures + 1,other_items,
                           direct_traces + traces)
      | _ => (tests,fixtures,other_items + 1,direct_traces + traces)
    end
  val (tests,fixtures,other_items,direct_traces) =
    List.foldl count (0,0,0,0) items
in
  {items = List.length items,
   tests = tests,
   fixtures = fixtures,
   other_items = other_items,
   direct_traces = direct_traces}
end

fun test_file_suite path =
  case String.fields (fn c => c = #"/" orelse c = #"\\")
         (strip_exports_prefix path) of
    "functional"::"builtins"::third::_ =>
      "functional/builtins/" ^ third
  | "functional"::"codegen"::third::_ =>
      "functional/codegen/" ^ third
  | first::second::_ => first ^ "/" ^ second
  | [first] => first
  | [] => "unknown"

fun read_coverage_json json_path = let
  val items = decodeFile rawObject json_path
  val fixtures = List.mapPartial (fn (name,json) =>
    if raw_string_field "item_type" json = SOME "fixture"
    then SOME (name,json) else NONE) items
  fun deps json = Option.getOpt (raw_string_array_field "deps" json,[])
  fun fixture_for dep =
    List.find
      (fn (name,_) => name = TraceDecode.fixture_name_of_dep dep) fixtures
  fun fixture_trace_count dep =
    case fixture_for dep of
      NONE => 0
    | SOME (_,json) => Option.getOpt (raw_array_length_field "traces" json,0)
  val referenced_fixtures =
    List.concat (List.map (fn (_,json) => deps json) items)
  val unreferenced_traced_fixtures = List.mapPartial (fn (name,json) =>
    if Option.getOpt (raw_array_length_field "traces" json,0) > 0 andalso
       not (List.exists (fn dep => TraceDecode.fixture_name_of_dep dep = name)
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
  val () = emit_named (String.concat [no_traces_reason, "; issue=", no_traces_issue])
               (#no_traces report)
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
  val discovered =
    list_json_files test_exports_root
    |> List.map strip_tests_prefix
    |> Lib.sort lexless
  val admitted_paths = List.filter is_supported_test_file discovered
  val files = List.map (fn path => (json_path_to_id path,path)) admitted_paths
  val reports = List.map (fn (_,path) => (path,read_coverage_json path)) files
  val excluded_files = List.mapPartial (fn path =>
    case test_file_disposition path of
      AdmittedTestFile => NONE
    | ExcludedTestFile (reason,issue) =>
        SOME (path,reason,issue,test_file_suite path,
              read_raw_file_inventory path)) discovered

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
  val excluded_test_items = excluded_name + excluded_pattern + no_traces +
                            missing_source + blank_source

  fun excluded_sum field =
    List.foldl (fn ((_,_,_,_,inventory),n) => field inventory + n)
      0 excluded_files
  val path_excluded_items = excluded_sum #items
  val path_excluded_tests = excluded_sum #tests
  val path_excluded_fixtures = excluded_sum #fixtures
  val path_excluded_other = excluded_sum #other_items
  val path_excluded_traces = excluded_sum #direct_traces

  fun add_exclusion_group
      ((_,reason,issue,suite,inventory),[]) =
        [(reason,issue,suite,1,#items inventory,#tests inventory,
          #fixtures inventory,#other_items inventory,#direct_traces inventory)]
    | add_exclusion_group
      (entry as (_,reason,issue,suite,inventory),
       (group as (reason',issue',suite',files,items,tests,fixtures,
                  other_items,traces))::rest) =
        if reason = reason' andalso issue = issue' andalso suite = suite'
        then (reason',issue',suite',files + 1,items + #items inventory,
              tests + #tests inventory,fixtures + #fixtures inventory,
              other_items + #other_items inventory,
              traces + #direct_traces inventory)::rest
        else group :: add_exclusion_group (entry,rest)
  val exclusion_groups = List.foldl add_exclusion_group [] excluded_files

  val output = TextIO.openOut output_path
  fun emit text = TextIO.output(output,text)
  fun print_excluded_file (path,reason,issue,suite,inventory) =
    emit (String.concat
      ["[vyper-coverage] path_excluded file=", path,
       " suite=", suite,
       " reason=", reason,
       " issue=", issue,
       " items=", Int.toString (#items inventory),
       " tests=", Int.toString (#tests inventory),
       " fixtures=", Int.toString (#fixtures inventory),
       " other_items=", Int.toString (#other_items inventory),
       " direct_traces=", Int.toString (#direct_traces inventory), "\n"])
  fun print_exclusion_group
      (reason,issue,suite,files,items,tests,fixtures,other_items,traces) =
    emit (String.concat
      ["[vyper-coverage] path_exclusion_summary suite=", suite,
       " reason=", reason,
       " issue=", issue,
       " files=", Int.toString files,
       " items=", Int.toString items,
       " tests=", Int.toString tests,
       " fixtures=", Int.toString fixtures,
       " other_items=", Int.toString other_items,
       " direct_traces=", Int.toString traces, "\n"])
  fun write () = let
    val () = emit (String.concat
      ["[vyper-coverage] funnel discovered_files=",
       Int.toString (List.length discovered),
       " admitted_files=", Int.toString (List.length files),
       " path_excluded_files=", Int.toString (List.length excluded_files),
       " discovered_items=", Int.toString (total_items + path_excluded_items),
       " admitted_items=", Int.toString total_items,
       " path_excluded_items=", Int.toString path_excluded_items, "\n"])
    val () = List.app print_excluded_file excluded_files
    val () = List.app print_exclusion_group exclusion_groups
    val () = List.app (fn (json_path,report) =>
      print_raw_coverage output json_path report) reports
  in
    emit (String.concat
      ["[vyper-coverage] summary discovered_files=",
       Int.toString (List.length discovered),
       " admitted_files=", Int.toString (List.length files),
       " path_excluded_files=", Int.toString (List.length excluded_files),
       " discovered_items=", Int.toString (total_items + path_excluded_items),
       " admitted_items=", Int.toString total_items,
       " path_excluded_items=", Int.toString path_excluded_items,
       " path_excluded_tests=", Int.toString path_excluded_tests,
       " path_excluded_fixtures=", Int.toString path_excluded_fixtures,
       " path_excluded_other_items=", Int.toString path_excluded_other,
       " path_excluded_direct_traces=", Int.toString path_excluded_traces,
       " fixtures=", Int.toString fixtures,
       " non_tests=", Int.toString non_tests,
       " selected=", Int.toString selected,
       " direct_traces=", Int.toString direct_traces,
       " expanded_traces=", Int.toString expanded_traces,
       " excluded_test_items=", Int.toString excluded_test_items,
       " excluded_name=", Int.toString excluded_name,
       " excluded_pattern=", Int.toString excluded_pattern,
       " no_exported_traces=", Int.toString no_traces,
       " no_exported_traces_reason=", no_traces_reason,
       " no_exported_traces_issue=", no_traces_issue,
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

fun check_export_provenance json_path = let
  fun find_repo dir =
    if OS.FileSys.access (OS.Path.concat (dir, "VYPER_PIN"), []) andalso
       OS.FileSys.access
         (OS.Path.concat (dir, "tools/vyper_test_exports.py"), []) then dir
    else let val parent = OS.Path.getParent dir in
      if parent = dir then raise Fail "cannot find project root for export validation"
      else find_repo parent
    end
  val repo = find_repo (OS.FileSys.getDir ())
  val script = OS.Path.concat (repo, "tools/vyper_test_exports.py")
  val command = String.concat ["python3 ", Systeml.protect script,
                              " check ", Systeml.protect json_path]
in
  if OS.Process.isSuccess (OS.Process.system command) then ()
  else raise Fail ("invalid export provenance: " ^ json_path)
end

(* Select raw tests and dependencies before decoding any HOL traces. Every
   chunk validates the complete selection, but only decodes its own tests and
   their fixtures; unowned fixtures must not populate byteStringCache. *)
fun read_definition_tests select_tests json_path = let
  val () = check_export_provenance json_path
  val selected = select_test_json json_path
  (* Failures are accumulated in reverse order. Report the original error,
     not a later cascade from a partially constructed decoder constant. *)
  val () = case List.rev (#failures selected) of
      [] => ()
    | (name, err)::_ => raise Fail (String.concat
        ["selection failure in ", json_path, ": ", name, " - ", exnMessage err])
  val tests_json = select_tests (#selected selected)
  val fixture_cache = ref ([] : (string * term list) list)
  fun decode_fixture (name, json) =
    case List.find (fn (n, _) => n = name) (!fixture_cache) of
      SOME (_, traces) => traces
    | NONE => let
        val traces = decode TraceDecode.fixture_decoder json
      in fixture_cache := (name, traces) :: !fixture_cache; traces end
  fun decode_test ((name, (fixtures, json)), (tests, failures)) =
    let
      val (_, traces) = decode TraceDecode.test_with_deps_decoder json
      val fixture_traces = List.concat (List.map decode_fixture fixtures)
    in ((name, fixture_traces @ traces)::tests, failures) end
    handle e => (tests, (name, e)::failures)
  val (reversed_tests, decode_fails) = List.foldl decode_test ([], []) tests_json
  val tests = List.rev reversed_tests
  val () = case List.rev decode_fails of
      [] => ()
    | (name, err)::_ => raise Fail (String.concat
        ["decode failure in ", json_path, ": ", name, " - ", exnMessage err,
         " (", Int.toString (List.length decode_fails), " tests failed to decode)"])
  val () = print_file_coverage json_path
    {selected = tests, failures = decode_fails,
     name_skips = #name_skips selected, source_skips = #source_skips selected,
     total_items = #total_items selected, fixtures = #fixtures selected,
     non_tests = #non_tests selected}
in
  tests
end

fun define_file_tests (id, json_path, start, tests) = let
  val path_vn = String.concat["json_path_", id]
  val path_def = new_definition(path_vn ^ "_def",
                   mk_eq(mk_var(path_vn, string_ty),
                         fromMLstring json_path))
  val traces_prefix = String.concat ["traces_", id, "_"]
  val test_name_prefix = String.concat ["name_", id, "_"]
  fun define_traces i (name, traces) = let
    val trs = mk_list(traces, trace_ty)
    val tn = Int.toString (start + i)
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

fun make_definitions_for_file (id, json_path) =
  define_file_tests
    (id, json_path, 0, read_definition_tests I json_path)

fun make_definitions_for_file_range (id, json_path, start, count) = let
  val total = #selected (read_coverage_json json_path)
  val () =
    if start >= 0 andalso count >= 0 andalso start <= total andalso
       count <= total - start then ()
    else raise Fail ("test range out of bounds in " ^ json_path)
  fun select_tests tests =
    if List.length tests = total
    then List.take (List.drop (tests, start), count)
    else raise Fail ("selected-count mismatch in " ^ json_path)
  val tests = read_definition_tests select_tests json_path
in
  define_file_tests (id, json_path, start, tests)
end

(* Bound saved CV data per theory by both case count and raw binary payload:
   at most 100 cases and 262144 hex characters, except that an oversized case
   gets its own chunk (never dropped). Sibling chunks never import one another.
   Chunk IDs name theories only; constants retain the original suite ID and
   global indices. Keep chunk 0 even for an empty suite, as before. *)
type test_chunk = {id : string, start : int, count : int}

fun test_chunks (id, weights) : test_chunk list = let
  val limit = 262144
  fun chunk part start count =
    {id = if part = 0 then id else id ^ "_part" ^ Int.toString part,
     start = start, count = count}
  fun chunks part start count payload remaining acc =
    case remaining of
      [] => List.rev
        (if count > 0 orelse List.null acc then chunk part start count :: acc
         else acc)
    | weight::rest =>
        if count > 0 andalso
           (count = 100 orelse weight > limit - payload)
        then chunks (part + 1) (start + count) 0 0 remaining
               (chunk part start count :: acc)
        else if weight > limit then
          chunks (part + 1) (start + 1) 0 0 rest
            (chunk part start 1 :: acc)
        else chunks part start (count + 1) (payload + weight) rest acc
in
  if List.exists (fn weight => weight < 0) weights
  then raise Fail "negative selected test weight"
  else chunks 0 0 0 0 weights []
end

(* Count only binary payload strings, including nested call_args.calldata.
   Skip annotated_ast metadata even if it contains payload-like keys; source
   text is not a payload field. No hex decoding or HOL bytecache definitions
   may occur while planning. This does not filter any tests or traces. *)
fun raw_payload_weight (JSON.OBJECT fields) =
      List.foldl (fn ((key,value),total) => total +
        (if key = "annotated_ast" then 0 else
         case value of
           JSON.STRING s =>
             if List.exists (fn field => field = key)
                  ["calldata", "initcode", "runtime_bytecode", "output"]
             then String.size s else 0
         | _ => raw_payload_weight value)) 0 fields
  | raw_payload_weight (JSON.ARRAY values) =
      List.foldl (fn (value,total) => total + raw_payload_weight value) 0 values
  | raw_payload_weight _ = 0

fun read_test_weights json_path = let
  val report = select_test_json json_path
  val selected = #selected report
  val () = case #failures report of
      [] => ()
    | (name,err)::_ => raise Fail (String.concat
        ["raw selection failure in ", json_path, ": ", name, " - ", exnMessage err])
  val () =
    if List.length selected = #selected (read_coverage_json json_path) then ()
    else raise Fail ("selected-count mismatch in " ^ json_path)
in
  List.map (fn (_, (fixtures, json)) =>
    List.foldl (fn ((_,fixture),total) => total + raw_payload_weight fixture)
      (raw_payload_weight json) fixtures) selected
end

fun generated_test_plan () =
  List.concat (List.map (fn (id, path) => let
    val chunks = test_chunks (id, read_test_weights path)
    val chunked = List.length chunks > 1
  in
    List.map (fn chunk => (chunk, id, path, chunked)) chunks
  end) (test_files ()))

fun cleanup_test_plan plan =
  cleanup_generated_scripts
    (List.map (fn (chunk : test_chunk, _, path, _) => (#id chunk, path)) plan)

(* Recompute the expected inventory from raw exports, independently of scripts. *)
fun check_generated_scripts () = let
  val () = check_generate_dirs ()
  val ids = List.map (fn (chunk : test_chunk, _, _, _) => #id chunk)
    (generated_test_plan ())
  val dir = OS.FileSys.openDir generated_dir
  fun entries acc =
    case OS.FileSys.readDir dir of
      NONE => acc
    | SOME entry => entries (entry :: acc)
  val actual = (entries [] before OS.FileSys.closeDir dir)
    handle e => (OS.FileSys.closeDir dir; raise e)
in
  check_generated_script_inventory ids actual
end

(* Replace only the generated call, retaining custom proofs/annotations. A
   nonstandard large-suite wrapper needs manual attention, not deletion. *)
fun rewrite_definition_call call contents = let
  val lines = String.fields (fn c => c = #"\n") contents
  fun is_call line =
    String.isPrefix "val () = make_definitions_for_file (" line orelse
    String.isPrefix "val () = make_definitions_for_file_range (" line
in
  if List.length (List.filter is_call lines) <> 1 then
    raise Fail "cannot safely update custom Defs script: expected one generated call"
  else String.concatWith "\n"
    (List.map (fn line => if is_call line then call else line) lines)
end

fun definition_scripts plan = let
  val gen_dir = generated_dir
in
  List.map (fn (chunk : test_chunk, suite_id, jsonp, chunked) => let
    val id = #id chunk
    val thyname = String.concat["vyperTestDefs_", id]
    val fname = OS.Path.concat(gen_dir, String.concat[thyname, "Script.sml"])
    (* Path is relative to tests/generated/, so prepend ../ to reach tests/vyper-test-exports *)
    val jsonp_from_generated = OS.Path.concat("..", jsonp)
    val call = String.concat
      ["val () = make_definitions_for_file", if chunked then "_range" else "",
       " (\"", suite_id, "\", \"", jsonp_from_generated, "\"",
       if chunked then ", " ^ Int.toString (#start chunk) ^ ", " ^
         Int.toString (#count chunk) else "", ");"]
    val contents = String.concat [
      "Theory ", thyname, "[no_sig_docs]\nAncestors jsonToVyper\nLibs vyperTestLib\n",
      "val () = holbuild_extra_deps [\"", jsonp_from_generated,
      "\", \"", jsonp_from_generated, ".provenance\"];\n", call, "\n"]
    val existing =
      if OS.FileSys.access(fname, []) then let
        val input = TextIO.openIn fname
      in SOME (TextIO.inputAll input before TextIO.closeIn input) end
      else NONE
    val contents = case existing of
        NONE => contents
      | SOME old =>
          if chunked orelse
             String.isSubstring "val () = make_definitions_for_file_range (" old
          then rewrite_definition_call call old
          else old (* Small custom scripts remain byte-for-byte unchanged. *)
  in
    (fname, contents)
  end) plan
end

fun execution_scripts plan = let
  val gen_dir = generated_dir
in
  List.map (fn (chunk : test_chunk, _, _, _) => let
    val id = #id chunk
    val thyname = String.concat["vyperTest_", id]
    val defsname = String.concat["vyperTestDefs_", id]
    val fname = OS.Path.concat(gen_dir, String.concat[thyname, "Script.sml"])
    val contents = String.concat [
      "Theory ", thyname, "[no_sig_docs]\nAncestors ", defsname,
      "\nLibs vyperTestRunnerLib\nval () = ",
      "run_tests_on_traces $ all_traces \"", defsname, "\";\n"]
  in (fname, contents) end) plan
end

fun generation_plan () = let
  val () = check_generate_dirs ()
  val plan = generated_test_plan ()
  (* Validate custom definitions before cleanup or any write, including when
     only execution scripts are requested. A rejected plan leaves all files. *)
  val definitions = definition_scripts plan
  val tests = execution_scripts plan
  val () = cleanup_test_plan plan
in
  {definitions = definitions, tests = tests}
end

fun write_scripts scripts = List.app (fn (path, contents) => let
  val out = TextIO.openOut path
in
  (TextIO.output (out, contents) before TextIO.closeOut out)
  handle e => (TextIO.closeOut out; raise e)
end) scripts

fun generate_defn_scripts () = write_scripts (#definitions (generation_plan ()))
fun generate_test_scripts () = write_scripts (#tests (generation_plan ()))
fun generate_tests () = let
  val plan = generation_plan ()
in
  write_scripts (#definitions plan);
  write_scripts (#tests plan)
end

end
