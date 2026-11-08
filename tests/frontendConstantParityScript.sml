Theory frontendConstantParity
Ancestors
  jsonToVyper vyperConstEval
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
val () = holbuild_extra_deps ["../tests/fixtures", "../lowering/defs/bytecode"];

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
fun folded_literal ctx node = let
  val e = rhs (concl (EVAL ``translate_expr ^ctx ^node``))
  val (head, args) = strip_comb e
in
  if is_const head andalso fst (dest_const head) = "Literal"
  then SOME (optionSyntax.mk_some (List.nth (args, 1)))
  else NONE
end;

(* Nodes where the compiler's unbounded arithmetic and the semantics differ,
   by file, source position and the value the frontend computes. They are
   reported but do not fail the check.
   In constant_shift_overflow, ((1 << 256) >> 255) + 1 is 3 for the compiler
   and 1 under uint256 shifts, and its subexpressions (1 << 256) >> 255 and
   1 << 256 differ likewise; the frontend rejects that contract
   (vyperConstEvalWitnessTheory). *)
val known_differences =
  map (fn (src, got) => ("check_contract/constant_shift_overflow.json", src, got))
    [("42:23:0", "SOME (IntL 1)"), ("43:17:0", "SOME (IntL 0)"),
     ("44:8:0", "SOME (IntL 0)")];
fun known path src got =
  List.exists (fn (file, s, g) =>
    String.isSuffix file path andalso s = src andalso g = term_to_string got)
    known_differences;

val matched = ref 0;
val mismatches = ref ([] : string list);
val known_found = ref ([] : string list);
val unevaluated = ref ([] : (string * int) list);
val skipped_files = ref 0;
val undecoded_asts = ref ([] : string list);
val expected_undecoded_found = ref 0;
(* Annotated ASTs that must not decode: an annotation in the main or an
   imported module does not decode. *)
val expected_undecoded =
  ["check_contract/constant_undecodable_bound.json",
   "check_contract/constant_undecodable_import/main.json"];
fun count_unevaluated kind =
  unevaluated :=
    (case List.find (fn (k, _) => k = kind) (!unevaluated) of
       SOME (_, n) =>
         map (fn (k, m) => if k = kind then (k, m + 1) else (k, m)) (!unevaluated)
     | NONE => (kind, 1) :: !unevaluated);

fun decode decoder v = SOME (JSONDecode.decode decoder v) handle _ => NONE;

fun check_node path ctx node folded = let
  val kind = string_field "ast_type" node
  val source = without_folded node
in
  case (decode jsonASTLib.json_expr source, decode jsonASTLib.json_expr folded) of
    (SOME e, SOME f) =>
      (case folded_literal ctx f of
         NONE => count_unevaluated (kind ^ " (non-scalar fold)")
       | SOME expected => let
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
             if known path src got then known_found := msg :: !known_found
             else mismatches := msg :: !mismatches
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
fun module_ctx all_import_maps main_src_id nsid body constants = let
  val ctx = rhs (concl (EVAL
    ``module_expr_ctx ^all_import_maps ^main_src_id ^nsid ^body [] []
        ^constants``))
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
    NONE =>
      if List.exists (fn f => String.isSuffix f path) expected_undecoded
      then expected_undecoded_found := !expected_undecoded_found + 1
      else undecoded_asts := path :: !undecoded_asts
  | SOME ast => let
      val (main, imports) = case strip_comb ast of
          (_, [m, i]) => (m, i) | _ => raise Fail "annotated AST shape"
      val (main_src_id, toplevels) = case strip_comb main of
          (_, [s, _, t]) => (s, t) | _ => raise Fail "module shape"
      val all_import_maps = rhs (concl (EVAL
        ``build_import_maps_from_indexes (build_import_compact_indexes ^imports)``))
      val constants = rhs (concl (EVAL
        ``annotated_constants ^all_import_maps ^main_src_id ^toplevels
            ^imports``))
      val imported = map (fn m => case strip_comb m of
          (_, [s, _, _, _, b]) => (intSyntax.int_of_term s, (s, b))
        | _ => raise Fail "import shape") (fst (listSyntax.dest_list imports))
      val () = Option.app (walk path
        (module_ctx all_import_maps main_src_id ``NONE : num option`` toplevels constants))
        (field "ast" json)
      fun walk_import v =
        case field "source_id" v of
          SOME (JSON.INT s) =>
            (case List.find (fn (s', _) => s' = Arbint.fromLargeInt s) imported of
               SOME (_, (s_tm, body)) =>
                 walk path (module_ctx all_import_maps main_src_id
                   ``SOME (source_id_to_module_id ^s_tm)`` body constants) v
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

val files = json_files "../tests/fixtures" @ json_files "../lowering/defs/bytecode";
val () = app check_file files;

val () = print (String.concat
  ["frontend constant parity: ", Int.toString (length files), " files (",
   Int.toString (!skipped_files), " not annotated ASTs, ",
   Int.toString (!expected_undecoded_found), " expected not to decode), ",
   Int.toString (!matched), " values match the compiler, ",
   Int.toString (length (!known_found)), " known differences, ",
   Int.toString (length (!mismatches)), " differ\n"]);
val () = app (fn (k, n) =>
  print ("  not evaluated: " ^ Int.toString n ^ " " ^ k ^ "\n")) (!unevaluated);
val () = app (fn m => print ("  known difference " ^ m ^ "\n")) (rev (!known_found));
val () = app (fn m => print ("  MISMATCH " ^ m ^ "\n")) (rev (!mismatches));
val () = app (fn p => print ("  UNDECODED " ^ p ^ "\n")) (rev (!undecoded_asts));
val () = if null (!undecoded_asts) then ()
  else raise Fail "annotated-AST fixtures no longer decode";
val () = if null (!mismatches) then ()
  else raise Fail "frontend constants differ from the compiler's folded values";
