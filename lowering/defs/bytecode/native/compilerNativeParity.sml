(*
 * Bytecode parity runner for the generated compiler (compilerNativeML).
 * For each fixture it runs compile_vyper natively and compares the deploy
 * and runtime bytes against the pinned Python oracle file (deploy=/runtime=
 * lines, as read by evalCompilerBytecodeLib.read_hex_bytes).
 *
 * Usage: bytecode_parity_native.exe FIXTURE_DIR [NAME.hex ...]
 * With names, only those fixtures run.  Exits non-zero unless every selected
 * fixture matches.
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

  fun run_one dir (name, thunk) = let
    val t0 = Time.now ()
    val outcome =
      (case thunk () of
         NONE => SOME "compiler returned NONE"
       | SOME (deploy, runtime) => let
           val (d, r) = oracle (OS.Path.concat (dir, name))
         in case compare "deploy" d (hex_bytes deploy) of
              SOME e => SOME e
            | NONE => compare "runtime" r (hex_bytes runtime)
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
    val (dir, only) =
      case CommandLine.arguments () of
        dir :: names => (dir, names)
      | [] => (print "usage: bytecode_parity_native.exe FIXTURE_DIR [NAME.hex ...]\n";
               OS.Process.exit OS.Process.failure)
    val selected = List.filter (fn (n, _) => null only orelse
                     List.exists (fn m => m = n) only) compilerNativeML.fixtures
    val results = map (run_one dir) selected
    val passed = length (List.filter #1 results)
    val total = List.foldl (fn ((_, t), s) => s + t) 0.0 results
  in
    print (Int.toString passed ^ "/" ^ Int.toString (length results) ^
           " fixtures match, " ^ Real.fmt (StringCvt.FIX (SOME 2)) total ^ "s\n");
    OS.Process.exit (if passed = length results then OS.Process.success
                     else OS.Process.failure)
  end
end

fun main () = compilerNativeParity.main ()
