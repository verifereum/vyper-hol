structure vyperCheckContractFrontendLib :> vyperCheckContractFrontendLib = struct

open HolKernel boolLib
open jsonToVyperTheory
open jsonConstEvalTheory
open sourceModuleDefsTheory

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

fun imported_module_path import_tm =
  case strip_comb import_tm of
    (_, [_, path, _, _, _]) => stringSyntax.fromHOLstring path
  | _ => raise Fail
      "vyperCheckContractFrontendLib: malformed imported module"

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

(* Preserved compatibility evaluator; never called by the source path. *)
fun check_constant_contract_file_legacy {address, path} = let
  val declarations = JSONDecode.decodeFile jsonConstASTLib.annotated_ast path
  val translation = eval_closed "constant module translation"
    (mk_comb (prim_mk_const {Thy="jsonConstEval",Name="translate_constant_module"},
      declarations))
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

(* Raw annotated-only compatibility route. Clean names are rebound below to
   the paired original/claims normalizer; there is no failure retry. *)
val prepare_check_input_legacy = prepare_check_input
val check_contract_result_legacy = check_contract_result
val check_contract_legacy = check_contract
val check_contract_file_legacy = check_contract_file

type source_input =
  {fuel:term, trust:term, keys:term, program:term, layouts:term, address:term}
type source_checked_result = sourceModuleFrontendLib.checked

fun check_source_contract_result
    {fuel, trust, keys, program, layouts, address} : source_checked_result = let
  val () = app (fn (label,tm) => require_closed label tm)
    [("source fuel",fuel),("source trust",trust),("source keys",keys),
     ("original source program",program),("source layouts",layouts),("address",address)]
in
  sourceModuleFrontendLib.check_simple
    {fuel=fuel,trust=trust,keys=keys,program=program}
    {layouts=layouts,address=address}
end

fun check_loaded_source_contract_result {fuel,trust,source,layouts,address} = let
  val () = app (fn (label,tm) => require_closed label tm)
    [("source fuel",fuel),("source trust",trust),("source layouts",layouts),("address",address),
     ("original source program",#program (source:sourceModuleLoaderLib.loaded)),
     ("source keys",#keys source)]
in sourceModuleFrontendLib.check_loaded {fuel=fuel,trust=trust,source=source}
  {layouts=layouts,address=address} end

fun check_source_contract input = #checking (check_source_contract_result input)
fun check_source_contract_file {fuel,trust,keys,layouts,address,path} =
  check_source_contract {fuel=fuel,trust=trust,keys=keys,layouts=layouts,address=address,
    program=JSONDecode.decodeFile sourceSyntaxLib.annotated_ast path}

(* Compatibility adapter for the strict #135 JSON fragment. This constructs
   ORIGINAL syntax only; there is no constant arithmetic/type evaluation here.
   jsonConstASTLib's is_constant/is_public assertions are inherited legacy
   qualifier trust. General source callers must supply pre-erasure syntax. *)
fun source_node thy name args =
  list_mk_comb (prim_mk_const {Thy=thy,Name=name},args)
fun sx name args = source_node "sourceSyntax" name args
fun sca name args = source_node "sourceConstAnnotation" name args
fun source_list name entries = listSyntax.mk_list
  (entries,mk_thy_type {Thy="sourceSyntax",Tyop=name,Args=[]})
fun strict_expression tm =
  case strip_comb tm of
    (ctor,[value,_]) =>
      if same_const ctor (prim_mk_const {Thy="jsonAST",Name="JE_Int"}) then
        sx "SX_Literal" [source_node "sourceConstAST" "SCL_Int" [value]]
      else raise Fail "strict source adapter: unexpected expression"
  | (ctor,[first,second,third,_]) =>
      if same_const ctor (prim_mk_const {Thy="jsonAST",Name="JE_Name"}) then
        sx "SX_Name" [first]
      else if same_const ctor (prim_mk_const {Thy="jsonAST",Name="JE_BinOp"}) then let
        val suffix = String.extract (#Name (dest_thy_const second),5,NONE)
        val source_op = if suffix = "Mult" then "Mul" else suffix
      in sx "SX_Binary"
        [source_node "sourceConstAST" ("SCB_" ^ source_op) [],
         strict_expression first,strict_expression third] end
      else raise Fail "strict source adapter: unexpected expression"
  | _ => raise Fail "strict source adapter: unexpected expression"
fun strict_annotation tm =
  case strip_comb tm of
    (ctor,[first,second]) =>
      if same_const ctor (prim_mk_const {Thy="jsonConstAST",Name="CA_Integer"}) then
        sca "SCA_Name" [listSyntax.mk_list
          ([stringSyntax.fromMLstring
            ((if aconv second boolSyntax.T then "int" else "uint") ^
             Arbnum.toString (numSyntax.dest_numeral first))],stringSyntax.string_ty)]
      else sca "SCA_StaticArray" [strict_annotation first,
        source_node "sourceSyntax" "source_constant_candidate" [strict_expression second]]
  | _ => raise Fail "strict source adapter: unexpected annotation"
fun strict_declaration tm =
  case strip_comb tm of
    (_, [name,ann,value]) => sx "SD_Variable"
      [name,sca "SCA_Qualified"
        [source_node "sourceConstAnnotation" "SCQ_Constant" [],strict_annotation ann],
       optionSyntax.mk_some (strict_expression value)]
  | (_, [name,args,ret,body]) => let
      val (params,_) = listSyntax.dest_list args
      fun argument pair = let val (id,ann) = pairSyntax.dest_pair pair
        in sx "SourceArg" [id,optionSyntax.mk_some (strict_annotation ann)] end
    in sx "SD_Function" [name,
      source_list "source_expr" (List.map (fn s => sx "SX_Name"
        [stringSyntax.fromMLstring s]) ["external","pure"]),
      source_list "source_arg" (List.map argument params),source_list "source_expr" [],
      optionSyntax.mk_some (strict_annotation ret),
      source_list "source_stmt" [sx "SS_Return" [optionSyntax.mk_some (strict_expression body)]]]
    end
  | _ => raise Fail "strict source adapter: unexpected declaration"

fun prepare_constant_source_file {address,path} : source_input = let
  val declarations = JSONDecode.decodeFile jsonConstASTLib.annotated_ast path
  val (decls,_) = listSyntax.dest_list declarations
  val program = sx "SourceProgram"
    [sx "SourceModule" [source_list "source_decl" (List.map strict_declaration decls)],
     source_list "source_module" []]
  val trust = Parse.Term [QUOTE
    "<| smt_ids := [([\"main\"],NONE)]; smt_nominals := []; smt_type_defs := FEMPTY; smt_slots := [] |> : source_module_trust"]
  val layout = ``([] : storage_layout, [] : storage_layout)``
  val entry = pairSyntax.mk_pair (address,layout)
in
  {fuel=``80:num``,trust=trust,keys=``[["main"]]``,program=program,
   layouts=listSyntax.mk_list ([entry],type_of entry),address=address}
end

fun check_constant_source_contract_file input =
  check_source_contract (prepare_constant_source_file input)

(* Extract only kernel consequences of the checked artifact. Compilation is
   an explicit antecedent, not an unchecked promise or a bytecode theorem.
   source_meaning_compile_program retains its independent source-module and
   nominal-environment premises for full interpreter call/load transport. *)
fun source_artifact_semantics (checked:source_checked_result) = let
  val elab = #elaboration checked
  val modules = #modules elab
  val tops = case #1 (listSyntax.dest_list modules) of
      [entry] => let val (owner,tops) = pairSyntax.dest_pair entry in
        if optionSyntax.is_none owner then tops else raise Fail
          "source artifact semantics: expected main module" end
    | _ => raise Fail "source artifact semantics: backend-module-linking"
  val (phase,args) = strip_comb (lhs (concl (#equation elab)))
  val () = if same_const phase ``sourceModuleElaborate$source_module_elaborate_simple`` then ()
    else raise Fail "source artifact semantics: preserved-policy semantic transport"
  val (fuel,trust,keys,program) = case args of
      [fuel,trust,keys,program] => (fuel,trust,keys,program)
    | _ => raise Fail "source artifact semantics: malformed simple phase"
  val {layouts,address,...} = #input checked
  val raw = ``compileVyper$compile_vyper finalizer policy ^tops = SOME bytes``
  val wrapper = ``sourceModuleCompile$source_module_compile ^fuel ^trust ^keys ^program ^layouts ^address
    finalizer policy``
  val compilation = simpLib.SIMP_CONV (bossLib.srw_ss())
    [sourceModuleCompileTheory.source_module_compile_def,
     #composition checked, source_module_bind_def, sourceSyntaxTheory.retained_executable_def,
     ASSUME raw] wrapper
  val meaning = GENL (free_vars raw) (DISCH raw
    (MATCH_MP sourceMeaningCompileTheory.source_meaning_compile_program compilation))
  val (oracles,axioms) = Tag.dest_tag (Thm.tag meaning)
  val () = if null (hyp meaning) andalso null axioms andalso
    List.all (fn tag => tag = "DISK_THM") oracles then ()
    else raise Fail "source artifact semantics: non-kernel certificate"
in meaning end

structure Source = struct
  val check_contract_result = check_source_contract_result
  val check_contract = check_source_contract
  val check_loaded_contract_result = check_loaded_source_contract_result
  fun check_contract_file_result {fuel,trust,layouts,address,path} =
    check_loaded_contract_result
      {fuel=fuel,trust=trust,layouts=layouts,address=address,
       source=sourceModuleLoaderLib.load_file path}
  fun check_contract_file input = #checking (check_contract_file_result input)
  val artifact_semantics = source_artifact_semantics
  val check_constant_contract_file = check_constant_source_contract_file
end

val check_constant_contract_file = check_constant_source_contract_file

(* Ordinary public route: original loader provenance + occurrence claims and
   explicitly inherited runtime type/import/layout contexts. All entry points
   check deployment too, and check precisely the phase's emitted modules. *)
type legacy_frontend_input = frontend_input
type legacy_checked_result = checked_result
type frontend_input = sourceOrdinaryProgramLib.input
type checked_result = sourceOrdinaryProgramLib.checked
val prepare_check_input = sourceOrdinaryProgramLib.prepare_check_input
val check_contract_result = sourceOrdinaryProgramLib.check
val compile_checked = sourceOrdinaryProgramLib.compile
fun check_contract input = #theorem (check_contract_result input)
fun check_contract_file_result {fuel,inherited,address,original_path,annotated_path} = let
  val original = sourceModuleLoaderLib.load_file original_path
  val capture = JSONDecode.decodeFile JSONDecode.raw original_path
  val original_json = JSONDecode.decode (JSONDecode.field "annotated_ast" JSONDecode.raw) capture
  val annotated = JSONDecode.decodeFile JSONDecode.raw annotated_path
  val paired = sourceOrdinaryClaimsLib.pair_program original original_json annotated
in check_contract_result {fuel=fuel,inherited=inherited,address=address,paired=paired} end
fun check_contract_file input = #theorem (check_contract_file_result input)

end
