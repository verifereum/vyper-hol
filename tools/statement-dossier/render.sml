val target = draftSource <> ""

fun section thy name file =
  {theorem = {Thy = thy, Name = name}, prose = OS.Path.concat (configDir, file)}
val sections =
  if target then
    [section draftTheory "vyper_call_correct_mods" "modules.md"]
  else
    [section "e2eDeployCorrectness" "e2e_deploy_correctness" "deploy.md",
     section "e2eCorrectness" "vyper_call_correct" "single.md",
     section "e2eGasSufficientTop" "e2e_deploy_gas_sufficient" "deploy-gas.md",
     section "e2eGasSufficientTop" "vyper_call_gas_sufficient" "call-gas.md"]

val projectTheories = statementDossierLib.script_theories [projectRoot]
val ancestors = Theory.ancestry "-"
val expandTheories = List.filter (fn thy => List.exists (fn a => a = thy) ancestors)
                                projectTheories

val stops = [{Thy = "compileUnit", Name = "compile_vyper_mods"},
             {Thy = "compileVyper", Name = "compile_vyper"},
             {Thy = "vyperTypeContract", Name = "check_contract"},
             {Thy = "vyperInterpreter", Name = "call_external"},
             {Thy = "vyperInterpreter", Name = "call_external_trace"},
             {Thy = "vyperInterpreter", Name = "load_contract"},
             {Thy = "vyperInterpreter", Name = "load_contract_trace"}]

val intro = if target then
  "`vyper_call_correct_mods` is the module-list target. Its proof is open.\n\n" ^ draftSource
  else "Each statement shows any oracle tags, axiom dependencies and kernel assumptions \
       \recorded in the loaded theorem."

val exporterInfo = if exporterRevision = "" then
  " The pinned exporter may show a helper's defining equations under the first function \
  \in its mutual-recursion block."
  else " Dossier exporter patch `" ^ exporterRevision ^ "`."

val config : statementDossierLib.config = {
  title = if target then "Vyper module-list call correctness target" else "Vyper compiler correctness",
  preamble = intro ^ "\n\n[vyper-hol " ^ sourceRevision ^ "]" ^
             "(https://github.com/verifereum/vyper-hol/tree/" ^ sourceRevision ^ ")" ^
             " · HOL `" ^ holRevision ^ "`." ^ exporterInfo,
  theorems = map #theorem sections,
  expand_theories = expandTheories,
  expand_consts = [],
  stop_theories = [],
  stop_consts = List.filter (fn {Thy, ...} => List.exists (fn a => a = Thy) ancestors) stops,
  equation_lemmas = [],
  source_dirs = [("", projectRoot)],
  outputs = [(statementDossierLib.Html, htmlOutput)],
  snippets = NONE,
  assumptions = sections,
  supporting = []
}

val () = statementDossierLib.run_with_presentation {
  about = "Definitions stop at the compiler, contract checker, source interpreter entry \
          \points, verifereum, and the HOL libraries. The boundary index links to their sources.",
  omit_types = [],
  reader_view = true,
  theory_sources = theorySources
} config
