signature sourceOrdinaryProgramLib = sig
  include Abbrev
  (* These claims are inherited, not independently source-inferred runtime
     typing/import/layout facts. No executable bodies are accepted here. *)
  type inherited = {trust:term, contexts:term, layouts:term}
  type input = {fuel:term, paired:sourceOrdinaryClaimsLib.paired,
                inherited:inherited, address:term}
  type elaborated = {retained:term, modules:term, equation:thm, original:thm, linking:thm}
  type prepared = {paired:sourceOrdinaryClaimsLib.paired, elaboration:elaborated,
                   input:vyperCheckContractLib.check_input}
  type checked = {paired:sourceOrdinaryClaimsLib.paired, elaboration:elaborated,
                 input:vyperCheckContractLib.check_input, modules:term, layouts:term,
                 address:term, artifact:term, theorem:thm, composition:thm}
  (* Explicit source_module_trust supplies canonical runtime module IDs;
     imported aliases/duplicates are never aligned by expression syntax. *)
  val inherited_contexts : sourceOrdinaryClaimsLib.paired -> term -> term
  val elaborate : input -> elaborated
  val prepare_check_input : input -> prepared
  val check : input -> checked
  (* Kernel equation for a backend callback on these exact checked modules. *)
  val compile : checked -> term -> thm
end
