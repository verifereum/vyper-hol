structure sourceModuleFrontendLib :> sourceModuleFrontendLib = struct
open HolKernel boolLib bossLib
open sourceModuleElaborateTheory sourceModuleDefsTheory sourceSyntaxTheory
open intLib wordsLib

type simple_input = {fuel:term, trust:term, keys:term, program:term}
type input = {fuel:term, trust:term, policies:term, keys:term, program:term}
type elaborated = {retained:term, modules:term, equation:thm, original:thm, linking:thm}
type checked = {elaboration:elaborated, input:vyperCheckContractLib.check_input,
                artifact:term, checking:thm, composition:thm}

fun inst_apply (argument,function) = let
  val (domain,_) = dom_rng (type_of function)
  val instantiated = Term.inst (Type.match_type domain (type_of argument)) function
in mk_comb (instantiated,argument) end
fun application name args = List.foldl inst_apply
  (prim_mk_const {Thy="sourceModuleElaborate",Name=name}) args
fun arguments ({fuel,trust,policies,keys,program}:input) = [fuel,trust,policies,keys,program]
fun simple_arguments ({fuel,trust,keys,program}:simple_input) = [fuel,trust,keys,program]
fun closed tm = if null (free_vars tm) then () else
  raise mk_HOL_ERR "sourceModuleFrontendLib" "closed" "open source input"
fun evaluated tm = let
  val _ = closed tm
  (* Discharge determined typing quantifiers before a residual condition can
     duplicate module continuations. Reuse the checker's kernel conversions;
     no truth value or successful elaboration is asserted by ML. Refresh the
     global base here so client definitions loaded after this library work. *)
  fun checked_conversion term =
    (REWR_CONV sourceExprDefsTheory.source_expr_checked_def THENC
      vyperCheckContractLib.check_contract_conv) term
  val global = computeLib.the_compset ()
  val source_compset = computeLib.copy global
  val source_compset = computeLib.scrub_const source_compset
    ``sourceExprDefs$source_expr_checked``
  val source_compset = computeLib.scrub_const source_compset boolSyntax.existential
    |> computeLib.add_conv
      (``sourceExprDefs$source_expr_checked``,3,checked_conversion)
    |> computeLib.add_conv
      (boolSyntax.existential,1,vyperCheckContractLib.check_contract_conv)
  val source_compset = computeLib.set_skip source_compset boolSyntax.conditional (SOME 1)
  (* Compiled RHSs retain constant-entry references. Recompile the source and
     typing rules against this fresh base, rather than merely replacing a
     dictionary entry that an already compiled caller would never consult. *)
  fun refresh ((_,thy),rules) cs =
    if (String.isPrefix "source" thy andalso
        not (String.isPrefix "sourceMeaning" thy)) orelse thy = "vyperTypeSystem" then
      (* add_thms prepends rules: retain concrete proved specializations ahead
         of general definitions (especially the executable Keccak equations). *)
      List.foldr (fn (clauses.RRules ths,cs) => computeLib.add_thms (rev ths) cs
                  | (_,cs) => cs) cs rules
    else cs
  val source_compset = List.foldl (fn (item,cs) => refresh item cs)
    source_compset (computeLib.listItems global)
  val source_eval = computeLib.CBV_CONV source_compset
  fun reduce 0 tm = REFL tm
    | reduce n tm = let
        val equation = (source_eval THENC simpLib.SIMP_CONV (srw_ss()) [source_module_exists_equal]) tm
        val result = rhs (concl equation)
      in if aconv tm result then equation
         else TRANS equation (reduce (n-1) result) end
in reduce 6 tm end
fun successful equation = let
  val result = rhs (concl equation)
  val (ctor,args) = strip_comb result
in
  if same_const ctor (prim_mk_const {Thy="sourceModuleDefs",Name="SM_Ok"})
     andalso length args = 1 then hd args
  else raise mk_HOL_ERR "sourceModuleFrontendLib" "successful"
    ("source elaboration rejected or incomplete: " ^ term_to_string result)
end
fun elaborate_phase suffix retains args : elaborated = let
  val equation = evaluated (application ("source_module_elaborate" ^ suffix) args)
  val retained = successful equation
  val accessor = ``retained_executable``
  val (domain,_) = dom_rng (type_of accessor)
  val modules = rhs (concl (evaluated (mk_comb
    (Term.inst (Type.match_type domain (type_of retained)) accessor,retained))))
in
  {retained=retained, modules=modules, equation=equation,
   original=MATCH_MP retains equation,
   linking=evaluated (application ("source_module_link_program" ^ suffix) (tl args))}
end
fun elaborate input = elaborate_phase "" source_module_elaborate_retains_source (arguments input)
fun elaborate_simple input = elaborate_phase "_simple" source_module_elaborate_simple_retains_source
  (simple_arguments input)
fun check_phase suffix definition elaboration args {layouts,address} : checked = let
  val input = {in_deploy=true, layouts=layouts, address=address, modules= #modules elaboration}
  val checking = vyperCheckContractLib.check_contract input
  val artifact = optionSyntax.dest_some (rhs (concl checking))
  val composition = simpLib.SIMP_CONV (srw_ss())
    [definition, #equation elaboration, source_module_bind_def,
     retained_executable_def, checking]
    (application ("source_module_check" ^ suffix) (args @ [layouts,address]))
  val _ = successful composition
in
  {elaboration=elaboration, input=input, artifact=artifact,
   checking=checking, composition=composition}
end
fun check source = check_phase "" source_module_check_def (elaborate source) (arguments source)
fun check_simple source = check_phase "_simple" source_module_check_simple_def
  (elaborate_simple source) (simple_arguments source)
fun elaborate_file {fuel,trust,keys,path} = elaborate_simple
  {fuel=fuel,trust=trust,keys=keys,
   program=JSONDecode.decodeFile sourceSyntaxLib.annotated_ast path}
fun loaded_input {fuel,trust,source:sourceModuleLoaderLib.loaded} : input =
  {fuel=fuel,trust=trust,keys= #keys source,program= #program source,
   policies=sourceModuleLoaderLib.policies source}
fun elaborate_loaded source = elaborate (loaded_input source)
fun check_loaded source = check (loaded_input source)
end
