Theory frontendConstantParity
Ancestors
  jsonToVyper vyperConstEval vyperPinFold
Libs
  jsonASTLib vyperConstEvalLib

(* Opt-in check, outside the default build: every compile-time value the
   frontend computes from source equals the compiler's own folded_value at the
   same node, over every checked-in annotated-AST fixture. The frontend never
   reads folded_value; this compares against it.

   Every folded node is compared, subexpressions included. A node whose
   expression the evaluator leaves alone (a decimal, a list, a runtime value)
   is counted, not compared. Literal nodes are skipped. *)
fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../tests/fixtures", "../bytecode"];

fun json_files dir = let
  val stream = OS.FileSys.openDir dir
  fun loop acc =
    case OS.FileSys.readDir stream of
      NONE => (OS.FileSys.closeDir stream; acc)
    | SOME name => let
        val path = OS.Path.concat (dir, name)
      in
        if OS.FileSys.isDir path then loop (json_files path @ acc)
        else if String.isSuffix ".json" name then loop (path :: acc)
        else loop acc
      end
in loop [] end;

fun field key (JSON.OBJECT fields) =
      Option.map #2 (List.find (fn (k, _) => k = key) fields)
  | field _ _ = NONE;
fun without_folded (JSON.OBJECT fields) =
      JSON.OBJECT (List.filter (fn (k, _) => k <> "folded_value") fields)
  | without_folded v = v;
fun string_field key v =
  case field key v of SOME (JSON.STRING s) => s | _ => "?";

val literal_nodes =
  ["Int", "Decimal", "Hex", "HexBytes", "Str", "Bytes", "NameConstant"];

val evaluate_tm = ``\cx ex. OPTION_BIND (eval_constant (translate_expr cx ex))
                              constant_literal``;
fun computed ctx node =
  rhs (concl (EVAL (list_mk_comb (evaluate_tm, [ctx, node]))));
val pin_evaluate_tm = ``\cx ex.
  case origin_fold_value (translate_expr_with_policy T cx ex) of
    Literal ty l => SOME l
  | _ => NONE``;
fun pin_computed ctx node =
  rhs (concl (EVAL (list_mk_comb (pin_evaluate_tm, [ctx, node]))));
fun folded_literal ctx node = let
  val e = rhs (concl (EVAL ``translate_expr ^ctx ^node``))
  val (head, args) = strip_comb e
in
  if is_const head andalso fst (dest_const head) = "Literal"
  then SOME (optionSyntax.mk_some (List.nth (args, 1)))
  else NONE
end;

val matched = ref 0;
val pin_matched = ref 0;
val pin_mismatches = ref ([] : string list);
val mismatches = ref ([] : string list);
val unevaluated = ref ([] : (string * int) list);
val skipped_files = ref 0;
val undecoded_asts = ref ([] : string list);
fun count_unevaluated kind =
  unevaluated :=
    (case List.find (fn (k, _) => k = kind) (!unevaluated) of
       SOME (_, n) =>
         map (fn (k, m) => if k = kind then (k, m + 1) else (k, m)) (!unevaluated)
     | NONE => (kind, 1) :: !unevaluated);

fun decode decoder v = SOME (JSONDecode.decode decoder v) handle _ => NONE;

fun check_pin_node path ctx source e expected = let
  val got = pin_computed ctx e
  val got =
    if optionSyntax.is_none got then
      case decode jsonASTLib.count_expr source of
        SOME b => pin_computed ctx b
      | NONE => got
    else got
  val src = string_field "src" source
in
  if optionSyntax.is_none got then ()
  else if aconv got expected then pin_matched := !pin_matched + 1
  else pin_mismatches :=
    (path ^ " " ^ src ^ ": origin_fold_value " ^ term_to_string got ^
     ", compiler " ^ term_to_string expected) :: !pin_mismatches
end;

fun check_node path ctx node folded = let
  val kind = string_field "ast_type" node
  val source = without_folded node
in
  (* Decimal.to_dict can retain expression text instead of a numeric value. *)
  if string_field "ast_type" folded = "Decimal" then
    count_unevaluated "Decimal (numeric expectation unavailable)"
  else case (decode jsonASTLib.json_expr source, decode jsonASTLib.json_expr folded) of
    (SOME e, SOME f) =>
      (case folded_literal ctx f of
         NONE => count_unevaluated (kind ^ " (non-scalar fold)")
       | SOME expected => let
           val () = check_pin_node path ctx source e expected
           val got = computed ctx e
           val got =
             if optionSyntax.is_none got then
               case decode jsonASTLib.count_expr source of
                 SOME b => computed ctx b
               | NONE => got
             else got
         in
           if optionSyntax.is_none got then count_unevaluated kind
           else if aconv got expected then matched := !matched + 1
           else let
             val src = string_field "src" node
             val msg = path ^ " " ^ src ^ " " ^ kind ^ ": computed " ^
               term_to_string got ^ ", compiler " ^ term_to_string expected
           in
             mismatches := msg :: !mismatches
           end
         end)
  | _ => count_unevaluated (kind ^ " (undecoded)")
end;

fun walk path ctx v =
  case v of
    JSON.OBJECT fields =>
      (case field "folded_value" v of
         SOME folded =>
           if List.exists (fn k => k = string_field "ast_type" v) literal_nodes
           then () else check_node path ctx v folded
       | NONE => ();
       app (fn (key, child) =>
         if key = "folded_value" then () else walk path ctx child) fields)
  | JSON.ARRAY vs => app (walk path ctx) vs
  | _ => ();

val ctx_ty = fst (dom_rng (type_of ``translate_expr``));
fun module_ctx all_import_maps main_src_id nsid body constants origins = let
  val ctx = rhs (concl (EVAL
    ``expr_with_origins (module_expr_ctx ^all_import_maps ^main_src_id ^nsid ^body [] []
        ^constants) ^origins``))
in Term.inst (match_type (type_of ctx) ctx_ty) ctx end;

(* Annotated ASTs: the file itself, or each one nested under an
   "annotated_ast" key, as in exported deployment traces. Other files use
   that key for metadata, which has no "ast" field. *)
fun nested_asts json =
  case json of
    JSON.OBJECT fields => List.concat (map (fn (key, v) =>
      if key = "annotated_ast" andalso isSome (field "ast" v) then [v]
      else nested_asts v) fields)
  | JSON.ARRAY vs => List.concat (map nested_asts vs)
  | _ => [];

fun annotated_asts json =
  if isSome (field "ast" json) then [json] else nested_asts json;

fun check_ast path json =
  case decode jsonASTLib.annotated_ast json of
    NONE => undecoded_asts := path :: !undecoded_asts
  | SOME ast => let
      val (main, imports) = case strip_comb ast of
          (_, [m, i]) => (m, i) | _ => raise Fail "annotated AST shape"
      val (main_src_id, toplevels) = case strip_comb main of
          (_, [s, _, t]) => (s, t) | _ => raise Fail "module shape"
      val all_import_maps = rhs (concl (EVAL
        ``build_import_maps_from_indexes (build_import_compact_indexes ^imports)``))
      val origins = rhs (concl (EVAL
        ``evaluated_origin_constants
          (LENGTH ^toplevels + SUM (MAP
            (\m. case m of JImportedModule _ _ _ _ body => LENGTH body) ^imports))
          ^all_import_maps ^main_src_id ^toplevels ^imports []``))
      val constants = rhs (concl (EVAL ``scalar_origin_constants ^origins``))
      val imported = map (fn m => case strip_comb m of
          (_, [s, _, _, _, b]) => (intSyntax.int_of_term s, (s, b))
        | _ => raise Fail "import shape") (fst (listSyntax.dest_list imports))
      val () = Option.app (walk path
        (module_ctx all_import_maps main_src_id ``NONE : num option`` toplevels constants origins))
        (field "ast" json)
      fun walk_import v =
        case field "source_id" v of
          SOME (JSON.INT s) =>
            (case List.find (fn (s', _) => s' = Arbint.fromLargeInt s) imported of
               SOME (_, (s_tm, body)) =>
                 walk path (module_ctx all_import_maps main_src_id
                   ``SOME (source_id_to_module_id ^s_tm)`` body constants origins) v
             | NONE => ())
        | _ => ()
    in
      case field "imports" json of
        SOME (JSON.ARRAY vs) => app walk_import vs
      | _ => ()
    end;

fun check_file path = let
  val () = print (path ^ "\n")
  val asts = annotated_asts (JSONDecode.decodeFile JSONDecode.raw path)
in
  if null asts then skipped_files := !skipped_files + 1
  else app (check_ast path) asts
end;

fun verify_mixed_bytes_refusal path = let
  val json = JSONDecode.decodeFile JSONDecode.raw path
  val ast = valOf (field "ast" json)
  val body = case field "body" ast of SOME (JSON.ARRAY xs) => xs
             | _ => raise Fail "mixed bytes module body"
  val func = valOf (List.find (fn x => string_field "name" x = "value") body)
  val ret = case field "body" func of SOME (JSON.ARRAY [x]) => x
            | _ => raise Fail "mixed bytes function body"
  val source = valOf (field "value" ret)
  val () = if string_field "ast_type" source = "Subscript" andalso
              not (isSome (field "folded_value" source)) then ()
           else raise Fail "pin unexpectedly folded mixed bytes selector"
  val node = JSONDecode.decode jsonASTLib.json_expr source
  val raw_ctx = rhs (concl (EVAL ``module_expr_ctx [] (0 : int) NONE [] [] [] []``))
  val ctx = Term.inst (match_type (type_of raw_ctx) ctx_ty) raw_ctx
  val got = pin_computed ctx node
  val () = if optionSyntax.is_none got then ()
           else raise Fail "source-refused mixed bytes selector became literal"
  val len_node = ``JE_Call (JE_Name "len" NONE JMissingSource JT_None)
      [^node] [] (JT_Integer 256 F) JMissingSource``
  val () = if optionSyntax.is_none (pin_computed ctx len_node) then ()
           else raise Fail "outer Len refolded source-refused selector"
in () end;

val () = verify_mixed_bytes_refusal
  "../tests/fixtures/check_contract/constant_mixed_bytes_select.json";

val files = json_files "../tests/fixtures" @ json_files "../bytecode";
val () = app check_file files;

val () = print (String.concat
  ["frontend constant parity: ", Int.toString (length files), " files (",
   Int.toString (!skipped_files), " not annotated ASTs), ",
   Int.toString (!matched), " values match the compiler, ",
   Int.toString (length (!mismatches)), " differ\n"]);
val () = app (fn (k, n) =>
  print ("  not evaluated: " ^ Int.toString n ^ " " ^ k ^ "\n")) (!unevaluated);
val () = app (fn m => print ("  MISMATCH " ^ m ^ "\n")) (rev (!mismatches));
val () = print ("origin_fold_value parity: " ^ Int.toString (!pin_matched) ^
  " values match the compiler, " ^ Int.toString (length (!pin_mismatches)) ^
  " differ\n");
val () = app (fn m => print ("  PIN MISMATCH " ^ m ^ "\n"))
  (rev (!pin_mismatches));
val () = app (fn p => print ("  UNDECODED " ^ p ^ "\n")) (rev (!undecoded_asts));
val () = if null (!undecoded_asts) then ()
  else raise Fail "annotated-AST fixtures no longer decode";
val () = if null (!mismatches) then ()
  else raise Fail "frontend constants differ from the compiler's folded values";
val () = if null (!pin_mismatches) then ()
  else raise Fail "pin_fold_expr differs from the compiler's folded values";
