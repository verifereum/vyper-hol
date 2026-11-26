val target = draftSource <> ""

fun section thy name file =
  {theorem = {Thy = thy, Name = name}, prose = OS.Path.concat (configDir, file)}
val sections =
  if target then
    [section draftTheory "vyper_call_correct_mods" "modules.md"]
  else
    [section "e2eDeployed" "e2e_deploy_correctness_deployed" "deploy.md",
     section "e2eDeployed" "vyper_call_correct_deployed" "single.md",
     section "e2eGasSufficientTop" "e2e_deploy_gas_sufficient" "deploy-gas.md",
     section "e2eDeployed" "vyper_call_gas_sufficient_deployed" "call-gas.md"]

val projectTheories = statementDossierLib.script_theories [projectRoot]
val ancestors = Theory.ancestry "-"
val expandTheories =
  if public then
    case List.filter (fn thy => not (Lib.mem thy ancestors)) publicTheories of
      [] => publicTheories
    | missing => raise Fail ("public-expand.txt names theories the theorems don't depend on: " ^
                             String.concatWith ", " missing)
  else List.filter (fn thy => List.exists (fn a => a = thy) ancestors) projectTheories

val stops = [{Thy = "compileUnit", Name = "compile_vyper_mods"},
             {Thy = "compileVyper", Name = "compile_vyper"},
             {Thy = "vyperTypeContract", Name = "check_contract"},
             {Thy = "vyperInterpreter", Name = "call_external"},
             {Thy = "vyperInterpreter", Name = "call_external_trace"},
             {Thy = "vyperInterpreter", Name = "load_contract"},
             {Thy = "vyperInterpreter", Name = "load_contract_trace"}]

val intro = if target then
  "`vyper_call_correct_mods` is the module-list target. Its proof is open.\n\n" ^ draftSource
  else if public then ""
  else "The deployment theorem shows how the constructor establishes `deployed`, \
       \which combines installed code, source typing, source deployment and \
       \storage validity on the fixed horizon `H`. \
       \The call theorem also needs a well-typed transaction, its fresh EVM \
       \entry frame, the trace bound and `call_within H` for its trace. \
       \`call_premises_deployed` relates the deployed and entry premises \
       \to source typing, call state and initial storage validity."

val exporterInfo = if exporterRevision = "" then
  " The pinned exporter may show a helper's defining equations under the first function \
  \in its mutual-recursion block."
  else " Dossier exporter patch `" ^ exporterRevision ^ "`."

val boundaryStops =
  List.filter (fn {Thy, ...} => List.exists (fn a => a = Thy) ancestors) stops

fun config expand_theories expand_consts stop_consts
  : statementDossierLib.config = {
  title = if target then "Vyper module-list call correctness target" else "Vyper compiler correctness",
  preamble = intro ^ "\n\n[vyper-hol " ^ sourceRevision ^ "]" ^
             "(https://github.com/verifereum/vyper-hol/tree/" ^ sourceRevision ^ ")" ^
             " · HOL `" ^ holRevision ^ "`." ^ exporterInfo,
  theorems = map #theorem sections,
  expand_theories = expand_theories,
  expand_consts = expand_consts,
  stop_theories = [],
  stop_consts = stop_consts,
  equation_lemmas = [],
  source_dirs = [("", projectRoot)],
  outputs = [(statementDossierLib.Html, htmlOutput)],
  snippets = NONE,
  assumptions = sections,
  supporting = []
}

(* The theorems and the definitions of exactly these constants *)
fun statements_expanding consts =
  statementDossierLib.statement_sections (config [] consts boundaryStops)

(* The project constants the sections' statements name *)
fun named_constants (sections : (string * (statementDossierLib.name * Thm.thm) list) list) =
  let
    fun consts th =
      List.concat (map (HolKernel.find_terms Term.is_const) (Thm.concl th :: Thm.hyp th))
    fun project c =
      let val {Thy, Name, ...} = Term.dest_thy_const c in
        if Lib.mem Thy expandTheories then SOME {Thy = Thy, Name = Name} else NONE
      end
  in
    Lib.mk_set (List.mapPartial project
      (List.concat (map (consts o #2) (List.concat (map #2 sections)))))
  end

(* statementDossierLib's anchor of a definition section *)
fun def_anchor ({Thy, Name} : statementDossierLib.name) =
  let
    fun safe ch =
      if Char.isAlphaNum ch orelse ch = #"_" then String.str ch
      else "-" ^ StringCvt.padLeft #"0" 2 (Int.fmt StringCvt.HEX (ord ch))
  in
    "def-" ^ String.translate safe Thy ^ "-" ^ String.translate safe Name
  end

(* The constants with a definition section just below the depth cut, []
   if there are none.  A theorem names the constants at depth 1, their
   definitions name those at depth 2, and so on.  `within` holds the
   project constants within depth k. *)
fun below_cut k within =
  let val next = named_constants (statements_expanding within) in
    if length next = length within then []
    else if k < depth then below_cut (k + 1) next
    else
      let val anchors = map #1 (statements_expanding next) in
        List.filter (fn n => not (Lib.mem n within) andalso
                             Lib.mem (def_anchor n) anchors) next
      end
  end

val cut = if public then [] else below_cut 0 []

val cutAbout = if null cut then "" else
  " This page also stops " ^ Int.toString depth ^ " definition steps below \
  \the theorems: a theorem names the constants at step 1, their definitions \
  \name those at step 2, and so on. The " ^ Int.toString (length cut) ^
  " constants at the next step are listed as not expanded and link to their \
  \sources. Render with a larger `--depth` for the full index."

val publicAbout =
  " This page expands only the definitions in the theories that state the theorems' \
  \hypotheses and result relations, and a few single constants; every other constant \
  \is listed as not expanded and links to its source."

val () = statementDossierLib.run_with_presentation {
  about = "Definitions stop at the compiler, contract checker, source interpreter entry \
          \points, verifereum, and the HOL libraries. The boundary index links to their sources." ^
          (if public then publicAbout else cutAbout),
  omit_types = [],
  reader_view = true,
  theory_sources = theorySources
} (config expandTheories publicConsts (boundaryStops @ cut))
