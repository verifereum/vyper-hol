structure sourceTypeFrontendLib :> sourceTypeFrontendLib = struct

open HolKernel boolLib
open sourceTypeDefsTheory sourceTypeResolveTheory sourceTypePropsTheory
open sourceTypeProvenanceTheory
(* Loading these libraries installs proved integer/word computation rules. *)
open intLib wordsLib

type input =
  {type_env : term, names : term, constants : term, annotation : term}

type certificate =
  {resolution : term, equation : thm, well_formed : thm,
   provenance : thm, original_bounds : thm, claim : thm option}

fun application name args =
  list_mk_comb (prim_mk_const {Thy="sourceTypeResolve", Name=name}, args)

fun arguments ({type_env,names,constants,annotation} : input) =
  [type_env,names,constants,annotation]

fun checked_equation tm = let
  val _ = if null (free_vars tm) then () else
    raise mk_HOL_ERR "sourceTypeFrontendLib" "checked_equation" "input is not closed"
  val equation = computeLib.EVAL_CONV tm
  val result = rhs (concl equation)
  val (ctor,args) = strip_comb result
in
  if same_const ctor (prim_mk_const {Thy="sourceTypeDefs", Name="ST_Ok"})
     andalso length args = 1 then (equation,hd args)
  else raise mk_HOL_ERR "sourceTypeFrontendLib" "checked_equation"
    ("source annotation rejected or computation incomplete: " ^ term_to_string result)
end

fun resolve input : certificate = let
  val (equation,resolution) = checked_equation
    (application "source_type_resolve" (arguments input))
  val invariant = MATCH_MP (CONJUNCT1 source_type_resolve_ok) equation
  val facts = REWRITE_RULE [source_type_resolution_ok_def] invariant
in
  {resolution=resolution, equation=equation,
   well_formed=CONJUNCT1 facts, provenance=CONJUNCT2 facts,
   original_bounds=MATCH_MP (CONJUNCT1 source_type_resolve_original_bounds) equation,
   claim=NONE}
end

fun check_claim input claim : certificate = let
  val cert = resolve input
  val (claim_equation,_) = checked_equation
    (application "source_type_check_claim" (arguments input @ [claim]))
in
  {resolution= #resolution cert, equation= #equation cert,
   well_formed= #well_formed cert, provenance= #provenance cert,
   original_bounds= #original_bounds cert, claim=SOME claim_equation}
end

end
