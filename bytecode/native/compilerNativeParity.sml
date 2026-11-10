(*
 * Bytecode parity runner for the generated compiler (compilerNativeML).
 * For each fixture it runs compile_vyper natively and compares the deploy
 * and runtime bytes against the pinned Python oracle file (deploy=/runtime=
 * lines, as read by evalCompilerBytecodeLib.read_hex_bytes).
 *
 * Usage: bytecode_parity_native.exe BYTECODE_DIR [PATH ...]
 * A fixture is named by its .hex file's path under BYTECODE_DIR, such as
 * python-o1-no-asm-opt/add_arg.hex or builtin-forms/oracle/ceil_dec.hex.  A
 * PATH selects that fixture, or every fixture under that directory; without
 * one, every fixture runs.  Every .hex file in a directory a selected fixture
 * sits in must have a fixture, except the pending ones below and the oracles
 * listed in ../pending-5127-port.md.  Exits non-zero
 * unless every selected fixture matches.
 *)
structure compilerNativeParity = struct
  open compilerNativeRuntime

  fun read_all path = let
    val ins = TextIO.openIn path
  in TextIO.inputAll ins before TextIO.closeIn ins end

  fun fixture_value entries key =
    case List.find (fn (k, _) => k = key) entries of
      SOME (_, v) => v
    | NONE => raise Fail ("missing " ^ key)

  fun compact_hex s = let
    val s = if String.isPrefix "0x" s orelse String.isPrefix "0X" s
            then String.extract (s, 2, NONE) else s
  in String.map Char.toLower (String.implode (List.filter (not o Char.isSpace)
       (String.explode s))) end

  (* As evalCompilerBytecodeLib.fixture_line: # starts a comment. *)
  fun trim s = Substring.string (Substring.dropl Char.isSpace
    (Substring.dropr Char.isSpace (Substring.full s)))
  fun entry line =
    case trim (hd (String.fields (fn c => c = #"#") line)) of
      "" => NONE
    | line => (case String.fields (fn c => c = #"=") line of
                 [k, v] => SOME (trim k, compact_hex v)
               | _ => raise Fail ("bad bytecode fixture line: " ^ line))

  fun oracle path = let
    val entries = List.mapPartial entry
      (String.tokens (fn c => c = #"\n" orelse c = #"\r") (read_all path))
  in (fixture_value entries "deploy", fixture_value entries "runtime") end

  fun hex_byte (W (_, v)) = let
    val s = IntInf.fmt StringCvt.HEX v
  in String.map Char.toLower (if size s = 1 then "0" ^ s else s) end
  fun hex_bytes bs = String.concat (map hex_byte bs)

  fun first_diff a b = let
    fun go i = if i >= size a orelse i >= size b orelse
                  String.sub (a, i) <> String.sub (b, i) then i else go (i + 1)
  in go 0 div 2 end

  fun compare what expected got =
    if expected = got then NONE
    else SOME (what ^ " differs at byte " ^ Int.toString (first_diff expected got) ^
               " (expected " ^ Int.toString (size expected div 2) ^ " bytes, got " ^
               Int.toString (size got div 2) ^ ")")

  (* Out of parity on purpose; see ../pending-uint2str-buffer.md. *)
  val pending = ["builtin-forms/oracle/uint2str_local.hex"]

  (* Fixtures that must compile but differ from the pinned oracle, so that a
     list entry that starts to match fails and gets removed.
     decoder_divergent: bounded memory decoding checks relative positions and
     head words before forming pointers, which the pinned Python does not (see
     ../pending-bounded-decode-guards.md).
     stale_oracle: the pinned oracle lacks upstream fixes the HOL compiler
     already follows (same file). *)
  val decoder_divergent = [
      "external-calls/oracle/e19_gas_kw.hex",
      "external-calls/oracle/e21_default_ret.hex",
      "external-calls/oracle/e22_static_default.hex",
      "external-calls/oracle/e29_default_ret_skip.hex",
      "external-calls/oracle/e30_default_ret_tuple.hex",
      "external-calls/oracle/e38_default_ret_local_array.hex",
      "external-calls/oracle/e45_default_ret_ifexp.hex",
      "memory-stores/oracle/t04_tuple_assign_extcall.hex"]
  val stale_oracle = [] : string list
  val expected_diff = decoder_divergent @ stale_oracle

  fun hex_files root dir = let
    val d = OS.FileSys.openDir (OS.Path.concat (root, dir))
    fun loop acc = case OS.FileSys.readDir d of
        NONE => acc
      | SOME f => loop (if String.isSuffix ".hex" f
                        then OS.Path.concat (dir, f) :: acc else acc)
  in loop [] before OS.FileSys.closeDir d end

  fun under path name = name = path orelse String.isPrefix (path ^ "/") name

  (* Oracles out of parity until their vyperlang/vyper#5127 port lands, as
     listed in ../pending-5127-port.md: `main/NAME` is the main corpus
     (python-o1-no-asm-opt/NAME.hex), `SUITE/NAME` a feature suite's
     SUITE/oracle/NAME.hex. *)
  fun pending_oracles root = let
    val path = OS.Path.concat (root, "pending-5127-port.md")
    val prefix = "- `"
    fun name line =
      if String.isPrefix prefix line then
        case String.fields (fn c => c = #"/")
               (hd (String.fields (fn c => c = #"`")
                      (String.extract (line, size prefix, NONE)))) of
          ["main", n] => SOME ("python-o1-no-asm-opt/" ^ n ^ ".hex")
        | [suite, n] => SOME (suite ^ "/oracle/" ^ n ^ ".hex")
        | _ => NONE
      else NONE
  in List.mapPartial name (String.tokens (fn c => c = #"\n") (read_all path))
  end handle IO.Io _ => []

  fun run_one dir (name, thunk) = let
    val t0 = Time.now ()
    val outcome =
      (case thunk () of
         NONE => SOME "compiler returned NONE"
       | SOME (deploy, runtime) => let
           val (d, r) = oracle (OS.Path.concat (dir, name))
           val d_diff = compare "deploy" d (hex_bytes deploy)
           val r_diff = compare "runtime" r (hex_bytes runtime)
         in
           if List.exists (fn k => k = name) expected_diff
           then (case (d_diff, r_diff) of
                   (NONE, NONE) => SOME "matches the oracle: remove it from the expected-difference lists"
                 | _ => NONE)
           else (case d_diff of NONE => r_diff | e => e)
         end)
      handle Stuck s => SOME ("stuck: " ^ s)
           | e => SOME ("exception: " ^ General.exnMessage e)
    val dt = Time.toReal (Time.- (Time.now (), t0))
    val tag = case outcome of NONE => "PASS" | SOME _ => "FAIL"
  in
    print (tag ^ " " ^ name ^ " " ^ Real.fmt (StringCvt.FIX (SOME 3)) dt ^ "s" ^
           (case outcome of NONE => "" | SOME e => ": " ^ e) ^ "\n");
    (outcome = NONE, dt)
  end

  fun main () = let
    val (root, paths) =
      case CommandLine.arguments () of
        root :: paths => (root, map (fn p => OS.Path.mkCanonical p) paths)
      | [] => (print "usage: bytecode_parity_native.exe BYTECODE_DIR [PATH ...]\n";
               OS.Process.exit OS.Process.failure)
    (* A pending fixture runs only when its own path is requested. *)
    val pending = pending @ pending_oracles root
    fun is_pending n = List.exists (fn k => k = n) pending
    val selected = List.filter (fn (n, _) =>
                     List.exists (fn p => p = n) paths orelse
                     (not (is_pending n) andalso
                      (null paths orelse List.exists (fn p => under p n) paths)))
                     compilerNativeML.fixtures
    (* A requested path, or an oracle file, with no compiled-in fixture
       would otherwise be skipped without a failure. *)
    val known = map #1 compilerNativeML.fixtures
    val dirs = List.foldr (fn (d, ds) => if List.exists (fn e => e = d) ds then ds
                                         else d :: ds) [] (map (OS.Path.dir o #1) selected)
    val files = List.concat (map (hex_files root) dirs)
    val unmatched =
      List.filter (fn n => not (List.exists (fn k => k = n) (known @ pending))) files @
      List.filter (fn p => not (List.exists (under p) known)) paths
    val () = List.app (fn n => print ("FAIL " ^ n ^ ": no native fixture\n")) unmatched
    val results = map (run_one root) selected
    val passed = length (List.filter #1 results)
    val count = length results + length unmatched
    val total = List.foldl (fn ((_, t), s) => s + t) 0.0 results
  in
    print (Int.toString passed ^ "/" ^ Int.toString count ^
           " fixtures match, " ^ Real.fmt (StringCvt.FIX (SOME 2)) total ^ "s\n");
    OS.Process.exit (if passed = count then OS.Process.success
                     else OS.Process.failure)
  end
end

fun main () = compilerNativeParity.main ()
