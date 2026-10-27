structure vyperCheckContractFrontendLib :> vyperCheckContractFrontendLib = struct

open HolKernel boolLib
open jsonToVyperTheory
open jsonConstEvalTheory

 type frontend_input =
  {in_deploy : bool,
   address : term,
   annotated_ast : term,
   storage_layout : term}

 type translated_input =
  {in_deploy : bool,
   address : term,
   sources : term,
   import_map : term,
   storage_layout : term}

 type checked_result =
  {input : vyperCheckContractLib.check_input,
   modules : term,
   layouts : term,
   address : term,
   artifact : term,
   theorem : thm}

fun require_closed what tm =
  if null (free_vars tm) then ()
  else raise Fail ("vyperCheckContractFrontendLib: open " ^ what)

fun eval_closed what tm = let
  val () = require_closed what tm
  val thm = bossLib.EVAL tm
  val () = if null (hyp thm) then ()
    else raise Fail ("vyperCheckContractFrontendLib: assumptions evaluating " ^ what)
  val (lhs, result) = dest_eq (concl thm)
  val () = if aconv lhs tm then ()
    else raise Fail ("vyperCheckContractFrontendLib: unexpected theorem for " ^ what)
  val () = require_closed (what ^ " result") result
in result end

fun inst_apply function argument = let
  val (domain_ty, _) = dom_rng (type_of function)
  val instantiated = Term.inst
    (Type.match_type domain_ty (type_of argument)) function
in mk_comb (instantiated, argument) end

fun apply name arguments =
  foldl (fn (argument, function) => inst_apply function argument)
    (prim_mk_const {Thy = "jsonToVyper", Name = name}) arguments

fun annotated_ast_imports annotated_ast =
  case strip_comb annotated_ast of
    (_, [_, imports]) => imports
  | _ => raise Fail
      "vyperCheckContractFrontendLib: expected JAnnotatedAST term"

fun imported_module_fields import_tm =
  case strip_comb import_tm of
    (_, fields as [_, _, _, _, _]) => fields
  | _ => raise Fail
      "vyperCheckContractFrontendLib: malformed imported module"

fun imported_module_path import_tm =
  stringSyntax.fromHOLstring (List.nth (imported_module_fields import_tm, 1))

(* Mirrors jsonToVyper's remove_repeated_imports, so that the remaining
   imports line up with the translated imported sources. *)
fun remove_repeated_imports imports = let
  fun identity import_tm = case imported_module_fields import_tm of
      [src_id, _, resolved_path, nr_default, body] =>
        [src_id, resolved_path, nr_default, body]
    | _ => raise Fail
        "vyperCheckContractFrontendLib: malformed imported module"
  fun same a b = ListPair.allEq (uncurry aconv) (identity a, identity b)
  fun keep seen [] = []
    | keep seen (import_tm::rest) =
        if List.exists (same import_tm) seen then keep seen rest
        else import_tm :: keep (import_tm::seen) rest
in keep [] imports end

(* Multiple import paths can translate to the same module. Preserve the first
   occurrence, but never choose between different definitions of one identity. *)
fun normalize_sources sources = let
  val (entries, source_ty) = listSyntax.dest_list sources
  fun unique seen [] = []
    | unique seen (source::rest) = let
        val (source_id, _) = pairSyntax.dest_pair source
      in
        case List.find (fn (sid, _) => aconv sid source_id) seen of
          NONE => source :: unique ((source_id, source)::seen) rest
        | SOME (_, previous) =>
            if aconv previous source then unique seen rest
            else raise Fail
              ("vyperCheckContractFrontendLib: conflicting definitions for source ID " ^
               term_to_string source_id)
      end
in
  listSyntax.mk_list (unique [] entries, source_ty)
end

(* Interface translation already removes ellipsis-bodied function stubs. Keep
   an interface source when nominal declarations remain, since their source ID
   is part of the nominal type identity needed by check_contract. Drop only
   empty .vyi sources; in particular, builtin interfaces may share source IDs.
   Translation preserves import order. *)
fun remove_interface_sources annotated_ast translated = let
  val (sources, rest) = pairSyntax.dest_pair translated
  (* Detect conflicts even if filtering would discard an empty interface. *)
  val _ = normalize_sources sources
  val (source_entries, source_ty) = listSyntax.dest_list sources
  val (imports, _) = listSyntax.dest_list (annotated_ast_imports annotated_ast)
  val imports = remove_repeated_imports imports
  val (main_source, imported_sources) = case source_entries of
      main::others => (main, others)
    | [] => raise Fail
        "vyperCheckContractFrontendLib: translation has no main source"
  fun source_is_empty source_tm = let
    val (_, toplevels) = pairSyntax.dest_pair source_tm
    val (entries, _) = listSyntax.dest_list toplevels
  in null entries end
  val kept = List.mapPartial
    (fn (import_tm, source_tm) =>
      if String.isSuffix ".vyi" (imported_module_path import_tm) andalso
         source_is_empty source_tm
      then NONE else SOME source_tm)
    (ListPair.zipEq (imports, imported_sources))
    handle ListPair.UnequalLengths => raise Fail
      "vyperCheckContractFrontendLib: import/source count mismatch"
in
  pairSyntax.mk_pair
    (listSyntax.mk_list (main_source::kept, source_ty), rest)
end

fun prepare_translated_input
    {in_deploy, address, sources, import_map, storage_layout} = let
  val () = app (fn (name, tm) => require_closed name tm)
    [("address", address), ("translated sources", sources),
     ("import map", import_map), ("storage layout", storage_layout)]
  val sources = normalize_sources (eval_closed "translated sources" sources)
  val modules = eval_closed "storage-slot annotation"
    (apply "annotate_sources_slots" [storage_layout, sources])
  val layout_pair = eval_closed "storage layout extraction"
    (apply "extract_storage_layout" [import_map, storage_layout])
  val layout_entry = pairSyntax.mk_pair (address, layout_pair)
  val layouts = listSyntax.mk_list ([layout_entry], type_of layout_entry)
in
  {in_deploy = in_deploy, layouts = layouts,
   address = address, modules = modules}
end

fun prepare_check_input
    {in_deploy, address, annotated_ast, storage_layout} = let
  val () = require_closed "annotated AST" annotated_ast
  val translation = eval_closed "annotated AST translation"
    (apply "translate_annotated_ast" [annotated_ast])
  val translated = optionSyntax.dest_some translation
    handle HOL_ERR _ => raise Fail
      "vyperCheckContractFrontendLib: annotated AST translation rejected"
  val translated = remove_interface_sources annotated_ast translated
  val (sources, rest) = pairSyntax.dest_pair translated
  val (_, import_map) = pairSyntax.dest_pair rest
in
  prepare_translated_input
    {in_deploy = in_deploy, address = address, sources = sources,
     import_map = import_map, storage_layout = storage_layout}
end

fun check_contract_result frontend_input = let
  val input = prepare_check_input frontend_input
  val theorem = vyperCheckContractLib.check_contract input
  val (_, result) = dest_eq (concl theorem)
  val artifact = optionSyntax.dest_some result
in
  {input = input, modules = #modules input, layouts = #layouts input,
   address = #address input, artifact = artifact, theorem = theorem}
end

fun check_contract input = #theorem (check_contract_result input)

fun check_contract_file {in_deploy, address, path} =
  check_contract
    {in_deploy = in_deploy,
     address = address,
     annotated_ast = JSONDecode.decodeFile jsonASTLib.annotated_ast path,
     storage_layout = JSONDecode.decodeFile jsonASTLib.storage_layout path}

fun check_constant_contract_file {address, path} = let
  val declarations = JSONDecode.decodeFile jsonConstASTLib.annotated_ast path
  val translation = eval_closed "constant module translation"
    (mk_comb (``translate_constant_module``, declarations))
  val modules = optionSyntax.dest_some translation
    handle HOL_ERR _ => raise Fail
      "vyperCheckContractFrontendLib: constant module translation rejected"
  val layout = ``([] : storage_layout, [] : storage_layout)``
  val entry = pairSyntax.mk_pair (address, layout)
in
  vyperCheckContractLib.check_contract
    {in_deploy = false, address = address, modules = modules,
     layouts = listSyntax.mk_list ([entry], type_of entry)}
end

end
