(* JSON-facing adapter. CV trees are exposed only by --dump-input for replay. *)
structure RunTestMain = struct
  open RunTestML
  structure AST = JsonASTDecodeFn (JsonImportCV)
  structure Decode = JsonTraceDecodeFn (
    structure B = JsonImportCV
    structure AST = AST
    fun translate_annotated_ast ast = JsonImportCV.Encoded
      (RunTestML.translate_annotated_ast (JsonImportCV.encode ast))
  )

  fun quote s = let
    fun escape #"\"" = "\\\""
      | escape #"\\" = "\\\\"
      | escape #"\n" = "\\n"
      | escape #"\r" = "\\r"
      | escape #"\t" = "\\t"
      | escape c =
          if Char.ord c < 32 then let
            val hex = Int.fmt StringCvt.HEX (Char.ord c)
          in "\\u00" ^ (if size hex=1 then "0" else "") ^ hex end
          else String.str c
  in "\"" ^ String.translate escape s ^ "\"" end

  fun cv_string cv = let
    fun go (Num n) chars =
          if n=0 then String.implode (List.rev chars)
          else raise Fail "invalid emitted string terminator"
      | go (Pair (Num n,tail)) chars =
          if n >= 0 andalso n <= 255 then go tail (Char.chr (IntInf.toInt n)::chars)
          else raise Fail "invalid emitted character"
      | go _ _ = raise Fail "invalid emitted string"
  in go cv [] end

  fun encoding cv = let
    fun go (Num n) rest = "N " :: IntInf.toString n :: rest
      | go (Pair (a,b)) rest = "P " :: go a (" " :: go b rest)
  in String.concat (go cv []) end

  fun execute dump (name,traces) = let
    val input = JsonImportCV.encode (JsonImportCV.mk_list
      (traces,JsonImportCV.named_type {Thy="vyperTestRunner",Tyop="trace"}))
    val result = run_test input
    val (passed,message) =
      case test_result_summary result of
        Pair (Num flag,text) =>
          if flag=0 orelse flag=1 then (flag=1,cv_string text)
          else raise Fail "invalid emitted result flag"
      | _ => raise Fail "invalid emitted result summary"
    val fields = ["\"name\":" ^ quote name,
      "\"status\":" ^ quote (if passed then "passed" else "failed")] @
      (if passed then [] else ["\"error\":" ^ quote message]) @
      (if dump then ["\"input\":" ^ quote (encoding input),
                     "\"result\":" ^ quote (encoding result)] else [])
    val () = TextIO.output (TextIO.stdOut,"{" ^ String.concatWith "," fields ^ "}\n")
    val () = TextIO.flushOut TextIO.stdOut
  in passed end

  (* JSONParser.parse consumes one value, not the whole document. Inspect its
     remaining stream directly, accepting only JSON whitespace before EOF. *)
  fun require_eof (source : JSONParser.source) =
    case !source of
      NONE => raise Fail "closed JSON source"
    | SOME (stream,line) =>
        (case TextIO.StreamIO.input1 stream of
           NONE => ()
         | SOME (c,rest) =>
             if c = #" " orelse c = #"\t" orelse
                c = #"\r" orelse c = #"\n" then
               (source := SOME (rest,if c = #"\n" then line+1 else line);
                require_eof source)
             else raise Fail "unexpected content after JSON document")

  fun parse_document source = let
    val json = JSONParser.parse source
    val () = require_eof source
  in json end

  fun parse_file file = let
    val source = JSONParser.openFile file
    val json = parse_document source
      handle ex => (JSONParser.close source; raise ex)
    val () = JSONParser.close source
  in json end

  fun main () = let
    val (dump,path) =
      case CommandLine.arguments () of
        ["--dump-input",path] => (true,SOME path)
      | ["--dump-input"] => (true,NONE)
      | [path] => (false,SOME path)
      | [] => (false,NONE)
      | _ => raise Fail "usage: run-test [--dump-input] [case.json]"
    val json = case path of
        SOME file => parse_file file
      | NONE => parse_document (JSONParser.openStream TextIO.stdIn)
    val cases = Decode.decode_cases json
    val () = if null cases then raise Fail "input contains no test cases" else ()
    val passed = List.foldl (fn (item,all) => execute dump item andalso all) true cases
  in if passed then ()
     else OS.Process.exit OS.Process.failure end
end

val () = RunTestMain.main () handle ex =>
  (TextIO.output (TextIO.stdErr, JSONErrors.exnMessage ex ^ "\n");
   OS.Process.exit OS.Process.failure);
