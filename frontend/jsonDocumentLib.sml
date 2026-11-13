(* Parse exactly one JSON document, allowing only JSON whitespace after it. *)
structure jsonDocumentLib = struct

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

  (* The caller owns the source, including stdin-backed sources. *)
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

end
