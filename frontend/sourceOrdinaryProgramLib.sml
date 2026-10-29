structure sourceOrdinaryProgramLib :> sourceOrdinaryProgramLib = struct
open HolKernel boolLib bossLib
open sourceOrdinaryProgramTheory sourceModuleDefsTheory sourceSyntaxTheory
open intLib wordsLib

type inherited = {trust:term, contexts:term, layouts:term}
type input = {fuel:term, paired:sourceOrdinaryClaimsLib.paired, inherited:inherited, address:term}
type elaborated = {retained:term, modules:term, equation:thm, original:thm, linking:thm}
type prepared = {paired:sourceOrdinaryClaimsLib.paired, elaboration:elaborated,
  input:vyperCheckContractLib.check_input}
type checked = {paired:sourceOrdinaryClaimsLib.paired, elaboration:elaborated,
  input:vyperCheckContractLib.check_input, modules:term, layouts:term,
  address:term, artifact:term, theorem:thm, composition:thm}
fun application name args = List.foldl (fn (arg,f) => mk_icomb (f,arg))
  (prim_mk_const {Thy="sourceOrdinaryProgram",Name=name}) args
fun closed tm = if null (free_vars tm) then () else raise Fail "ordinary program: open input"
(* Same kernel conversions as the source frontend; no new evaluator or ML
   arithmetic. Refresh source rules against the contract checker's conversions. *)
fun evaluate_uncached tm = let
  val () = closed tm
  fun checked_conversion term =
    (REWR_CONV sourceExprDefsTheory.source_expr_checked_def THENC
      vyperCheckContractLib.check_contract_conv) term
  val global = computeLib.the_compset ()
  val cs = computeLib.copy global
    |> (fn cs => computeLib.scrub_const cs ``sourceExprDefs$source_expr_checked``)
    |> (fn cs => computeLib.scrub_const cs boolSyntax.existential)
    |> computeLib.add_conv (``sourceExprDefs$source_expr_checked``,3,checked_conversion)
    |> computeLib.add_conv (boolSyntax.existential,1,vyperCheckContractLib.check_contract_conv)
  val cs = computeLib.set_skip cs boolSyntax.conditional (SOME 1)
  fun refresh ((_,thy),rules) cs =
    if (String.isPrefix "source" thy andalso not (String.isPrefix "sourceMeaning" thy))
        orelse thy = "vyperTypeSystem" then
      List.foldr (fn (clauses.RRules ths,cs) => computeLib.add_thms (rev ths) cs
        | (_,cs) => cs) cs rules else cs
  val cs = List.foldl (fn (item,cs) => refresh item cs) cs (computeLib.listItems global)
  fun reduce 0 tm = REFL tm
    | reduce n tm = let
      val th = (computeLib.CBV_CONV cs THENC simpLib.SIMP_CONV (srw_ss())
        [sourceModuleDefsTheory.source_module_exists_equal]) tm
      val result = rhs (concl th)
      in if aconv tm result then th else TRANS th (reduce (n-1) result) end
in reduce 6 tm end
(* Cache only closed kernel equations, keyed by the complete HOL input. The
   zipper/metadata validation is always rerun before this library is called. *)
val certificates = ref ([] : thm list)
fun evaluated tm = case List.find (fn th => aconv (lhs (concl th)) tm) (!certificates) of
    SOME th => th
  | NONE => let val th = evaluate_uncached tm
      val () = certificates := th :: List.take (!certificates,Int.min (15,length (!certificates)))
    in th end
fun successful th = let val (c,args) = strip_comb (rhs (concl th)) in
  if same_const c ``SM_Ok`` andalso length args = 1 then hd args
  else raise Fail ("ordinary program rejected: " ^ term_to_string (rhs (concl th))) end
fun arguments ({fuel,paired,inherited,address}:input) = let
  val source = #original paired
in [fuel,#trust inherited,sourceModuleLoaderLib.policies source,#keys source,
    #contexts inherited,#program source,#claims paired] end
fun inherited_contexts (paired:sourceOrdinaryClaimsLib.paired) trust = let
  val ast = JSONDecode.decode jsonASTLib.annotated_ast (#annotated paired)
  val identities = rhs (concl (evaluated ``(^trust).smt_ids``))
  val th = evaluated (application "source_ordinary_legacy_contexts" [identities,ast])
in optionSyntax.dest_some (rhs (concl th)) end
fun elaborate input : elaborated = let
  val args = arguments input
  val equation = evaluated (application "source_ordinary_program" args)
  val retained = successful equation
  val modules = rhs (concl (evaluated (mk_icomb (``retained_executable``,retained))))
  val linking = evaluated (List.foldl (fn (arg,f) => mk_icomb (f,arg))
    ``sourceModuleContext$source_module_link_program``
    [List.nth (args,1),List.nth (args,2),List.nth (args,3),List.nth (args,5)])
in {retained=retained, modules=modules,equation=equation,
    original=MATCH_MP source_ordinary_program_retains_source equation,linking=linking} end
fun check_input ({inherited,address,...}:input) (elab:elaborated) =
  {in_deploy=true,layouts= #layouts inherited,address=address,modules= #modules elab}
fun prepare_check_input (source:input) : prepared = let
  val elab = elaborate source
in {paired= #paired source,elaboration=elab,input=check_input source elab} end
fun check (source:input) : checked = let
  val prepared = prepare_check_input source
  val elab = #elaboration prepared
  val input = #input prepared
  val theorem = vyperCheckContractLib.check_contract input
  val artifact = optionSyntax.dest_some (rhs (concl theorem))
  val composition = simpLib.SIMP_CONV (srw_ss())
    [source_ordinary_check_def,#equation elab,source_module_bind_def,retained_executable_def,theorem]
    (application "source_ordinary_check" (arguments source @ [#layouts input,#address input]))
  val _ = successful composition
in {paired= #paired source,elaboration=elab,input=input,modules= #modules input,
  layouts= #layouts input,address= #address input,artifact=artifact,theorem=theorem,composition=composition} end
fun compile (checked:checked) compiler = let
  val (_,args) = strip_comb (lhs (concl (#composition checked)))
  val backend = evaluated (mk_icomb (compiler,#modules checked))
  val () = if optionSyntax.is_some (rhs (concl backend)) then ()
    else raise Fail "ordinary program backend rejected"
  val th = simpLib.SIMP_CONV (srw_ss())
    [source_ordinary_compile_def,#composition checked,source_module_bind_def,
      retained_executable_def,backend]
    (application "source_ordinary_compile" (compiler::args))
  val _ = successful th
in th end
end
