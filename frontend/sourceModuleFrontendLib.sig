signature sourceModuleFrontendLib = sig
  include Abbrev
  type simple_input = {fuel:term, trust:term, keys:term, program:term}
  type input = {fuel:term, trust:term, policies:term, keys:term, program:term}
  type elaborated = {retained:term, modules:term, equation:thm, original:thm, linking:thm}
  type checked = {elaboration:elaborated, input:vyperCheckContractLib.check_input,
                  artifact:term, checking:thm, composition:thm}
  val elaborate : input -> elaborated
  val check : input -> {layouts:term, address:term} -> checked
  (* Policy-free equations. A bare program carries no pragmas, so it is
     elaborated as if `#pragma nonreentrancy` were off. Source read from a
     file goes through the loader, which carries the pragma as a policy. *)
  val elaborate_simple : simple_input -> elaborated
  val check_simple : simple_input -> {layouts:term, address:term} -> checked
  val elaborate_loaded : {fuel:term, trust:term, source:sourceModuleLoaderLib.loaded} -> elaborated
  val check_loaded : {fuel:term, trust:term, source:sourceModuleLoaderLib.loaded} ->
    {layouts:term, address:term} -> checked
end
