(*
 * Bytecode parity for programs read at run time as annotated-AST JSON.
 *
 * For each <name>.json (the output of `vyper -f annotated_ast,layout`, as the
 * witness suites store it) this does natively what the witness theories do
 * by EVAL through vyperCheckContractFrontendLib.prepare_check_input and
 * memoryStoreWitnessLib.program: decode the JSON, translate it with the
 * emitted CV translation of translate_annotated_ast, drop empty interface
 * sources, annotate storage slots, and compile the one remaining module with
 * compile_vyper (K SOME) (o1_policy all_capabilities).  The deploy and
 * runtime bytes are compared with <name>.hex.  It does not run check_contract.
 *
 * Usage: bytecode_parity_json.exe DIR [NAME ...]
 * Without names, every <name>.json in DIR with a <name>.hex runs.  Each
 * fixture prints PASS, FAIL (bytes differ, or the compiler failed), or REJECT
 * (the frontend rejected the program, or it has several modules).  Exits
 * non-zero unless every fixture passes.  With NATIVE_PARITY_DUMP=<dir> set, the
 * native bytes of each compiled fixture are written to <dir>/<name>.hex.
 *)
structure compilerNativeJson = struct
  structure AST = JsonASTDecodeFn (JsonImportCV)
  structure P = compilerNativeParity

  exception Reject of string

  (* ---- CV values from the emitted frontend ---- *)
  fun cv_list (RunTestML.Num _) = []
    | cv_list (RunTestML.Pair (x, rest)) = x :: cv_list rest
  fun cv_of_list xs = List.foldr RunTestML.Pair (RunTestML.Num 0) xs
  fun cv_fst (RunTestML.Pair (a, _)) = a
    | cv_fst _ = raise Fail "expected a CV pair"
  fun cv_snd (RunTestML.Pair (_, b)) = b
    | cv_snd _ = raise Fail "expected a CV pair"

  (* The emitted compiler's own copy of the CV datatype. *)
  fun to_compiler (RunTestML.Num n) = compilerNativeML.cv_num n
    | to_compiler (RunTestML.Pair (a, b)) =
        compilerNativeML.cv_pair (to_compiler a) (to_compiler b)

  (* ---- vyperCheckContractFrontendLib.remove_interface_sources ---- *)
  fun import_fields import_tm =
    case JsonImportCV.strip_comb import_tm of
      (_, fields as [_, _, _, _, _]) => fields
    | _ => raise Fail "malformed imported module"
  fun import_path import_tm =
    case List.nth (import_fields import_tm, 1) of
      JsonImportCV.StringValue s => s
    | _ => raise Fail "malformed import path"
  fun remove_repeated_imports imports = let
    fun identity tm = case import_fields tm of
        [src_id, _, resolved, nr_default, body] => [src_id, resolved, nr_default, body]
      | _ => raise Fail "malformed imported module"
    fun keep _ [] = []
      | keep seen (tm :: rest) =
          if List.exists (fn s => identity s = identity tm) seen then keep seen rest
          else tm :: keep (tm :: seen) rest
  in keep [] imports end

  fun normalize_sources sources = let
    fun unique _ [] = []
      | unique seen (source :: rest) = let
          val id = cv_fst source
        in case List.find (fn (sid, _) => sid = id) seen of
             NONE => source :: unique ((id, source) :: seen) rest
           | SOME (_, previous) =>
               if previous = source then unique seen rest
               else raise Reject "conflicting definitions for one source ID"
        end
  in unique [] sources end

  fun remove_interface_sources annotated_ast sources = let
    val _ = normalize_sources sources
    val imports = case JsonImportCV.strip_comb annotated_ast of
        (_, [_, imports]) => remove_repeated_imports (#1 (JsonImportCV.dest_list imports))
      | _ => raise Fail "expected a JAnnotatedAST term"
    val (main, imported) = case sources of
        main :: others => (main, others)
      | [] => raise Fail "translation has no main source"
    fun is_empty source = case cv_snd source of RunTestML.Num _ => true | _ => false
    val kept = List.mapPartial (fn (import_tm, source) =>
        if String.isSuffix ".vyi" (import_path import_tm) andalso is_empty source
        then NONE else SOME source)
      (ListPair.zipEq (imports, imported))
      handle ListPair.UnequalLengths => raise Fail "import/source count mismatch"
  in main :: kept end

  (* The toplevels of the program's one module, as memoryStoreWitnessLib.program. *)
  fun program path = let
    val json = jsonDocumentLib.parse_file path
    val annotated_ast = JSONDecode.decode AST.annotated_ast json
    val layout = JSONDecode.decode AST.storage_layout json
    val translated =
      case RunTestML.translate_annotated_ast (JsonImportCV.encode annotated_ast) of
        RunTestML.Pair (RunTestML.Num 1, result) => result
      | _ => raise Reject "frontend rejected the annotated AST"
    val sources = normalize_sources
      (remove_interface_sources annotated_ast (cv_list (cv_fst translated)))
    val modules = compilerNativeML.annotate_sources_slots
      (to_compiler (JsonImportCV.encode layout)) (to_compiler (cv_of_list sources))
  in case modules of
       [(_, tops)] => tops
     | _ => raise Reject (Int.toString (length modules) ^ " source modules")
  end

  (* With NATIVE_PARITY_DUMP=<dir>, write the native bytes there as <name>.hex. *)
  fun dump name deploy runtime =
    case OS.Process.getEnv "NATIVE_PARITY_DUMP" of
      NONE => ()
    | SOME out => let
        val os = TextIO.openOut (OS.Path.concat (out, name ^ ".hex"))
      in TextIO.output (os, "deploy=" ^ deploy ^ "\nruntime=" ^ runtime ^ "\n");
         TextIO.closeOut os end

  fun run_one dir name = let
    val t0 = Time.now ()
    val outcome =
      (case compilerNativeML.compile (program (OS.Path.concat (dir, name ^ ".json"))) of
         NONE => ("FAIL", "compiler returned NONE")
       | SOME (deploy, runtime) => let
           val (d, r) = P.oracle (OS.Path.concat (dir, name ^ ".hex"))
           val () = dump name (P.hex_bytes deploy) (P.hex_bytes runtime)
         in case P.compare "deploy" d (P.hex_bytes deploy) of
              SOME e => ("FAIL", e)
            | NONE => (case P.compare "runtime" r (P.hex_bytes runtime) of
                         SOME e => ("FAIL", e)
                       | NONE => ("PASS", ""))
         end)
      handle Reject s => ("REJECT", s)
           | compilerNativeRuntime.Stuck s => ("FAIL", "stuck: " ^ s)
           | e => ("FAIL", "exception: " ^ General.exnMessage e)
    val dt = Time.toReal (Time.- (Time.now (), t0))
  in
    print (#1 outcome ^ " " ^ name ^ " " ^ Real.fmt (StringCvt.FIX (SOME 3)) dt ^ "s" ^
           (if #2 outcome = "" then "" else ": " ^ #2 outcome) ^ "\n");
    #1 outcome
  end

  fun fixture_names dir = let
    val d = OS.FileSys.openDir dir
    fun loop acc = case OS.FileSys.readDir d of
        NONE => acc
      | SOME f =>
          loop (if String.isSuffix ".json" f andalso
                   OS.FileSys.access (OS.Path.concat (dir,
                     String.substring (f, 0, size f - 5) ^ ".hex"), [])
                then String.substring (f, 0, size f - 5) :: acc else acc)
    fun insert (x, []) = [x]
      | insert (x, y :: ys) = if x <= y then x :: y :: ys else y :: insert (x, ys)
  in List.foldl insert [] (loop []) before OS.FileSys.closeDir d end

  fun main () = let
    val (dir, names) =
      case CommandLine.arguments () of
        dir :: names => (dir, if null names then fixture_names dir else names)
      | [] => (print "usage: bytecode_parity_json.exe DIR [NAME ...]\n";
               OS.Process.exit OS.Process.failure)
    val () = if null names then
               (print ("no <name>.json/<name>.hex pairs in " ^ dir ^ "\n");
                OS.Process.exit OS.Process.failure)
             else ()
    fun full d = OS.FileSys.fullPath d handle OS.SysErr _ => d
    val () = case OS.Process.getEnv "NATIVE_PARITY_DUMP" of
               SOME out => if full out = full dir then
                 (print "NATIVE_PARITY_DUMP is the fixture directory; the dump would overwrite the oracle\n";
                  OS.Process.exit OS.Process.failure)
                 else ()
             | NONE => ()
    val results = map (run_one dir) names
    fun count tag = length (List.filter (fn t => t = tag) results)
  in
    print (Int.toString (count "PASS") ^ " pass, " ^ Int.toString (count "FAIL") ^
           " fail, " ^ Int.toString (count "REJECT") ^ " rejected, of " ^
           Int.toString (length results) ^ "\n");
    OS.Process.exit (if count "PASS" = length results then OS.Process.success
                     else OS.Process.failure)
  end
end

fun main () = compilerNativeJson.main ()
