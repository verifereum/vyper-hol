signature vyperCheckContractFrontendLib = sig

  type frontend_input =
    {in_deploy : bool,
     address : Term.term,
     annotated_ast : Term.term,
     storage_layout : Term.term}

  type translated_input =
    {in_deploy : bool,
     address : Term.term,
     sources : Term.term,
     import_map : Term.term,
     storage_layout : Term.term}

  val prepare_translated_input :
    translated_input -> vyperCheckContractLib.check_input
  val prepare_check_input :
    frontend_input -> vyperCheckContractLib.check_input

  type checked_result =
    {input : vyperCheckContractLib.check_input,
     modules : Term.term,
     layouts : Term.term,
     address : Term.term,
     artifact : Term.term,
     theorem : Thm.thm}

  val check_contract_result : frontend_input -> checked_result
  val check_contract : frontend_input -> Thm.thm

  val check_contract_file :
    {in_deploy : bool, address : Term.term, path : string} -> Thm.thm

  (* Strict first-stage constant frontend; no compiler folding metadata. *)
  val check_constant_contract_file :
    {address : Term.term, path : string} -> Thm.thm

  (* Opt-in source route. It types and evaluates the original pre-erasure
     program itself rather than trusting the compiler's inferred types and
     folded values. Everything above is the default route and is unchanged.
     The source route rejects (as unsupported) some programs the default
     route accepts. *)
  type source_input =
    {fuel : Term.term, trust : Term.term, keys : Term.term,
     program : Term.term, layouts : Term.term, address : Term.term}
  type source_checked_result = sourceModuleFrontendLib.checked

  structure Source : sig
    (* A bare program carries no pragmas: it is checked as if
       `#pragma nonreentrancy` were off, so `reentrant` is rejected. A loader
       capture carries the pragma as a policy. *)
    val check_contract_result : source_input -> source_checked_result
    val check_contract : source_input -> Thm.thm
    (* A pre-erasure capture from tools/source_module_loader.py, not ordinary
       post-erasure annotated JSON. *)
    val check_loaded_contract_result :
      {fuel : Term.term, trust : Term.term, source : sourceModuleLoaderLib.loaded,
       layouts : Term.term, address : Term.term} -> source_checked_result
    val check_contract_file_result :
      {fuel : Term.term, trust : Term.term, layouts : Term.term,
       address : Term.term, path : string} -> source_checked_result
    val check_contract_file :
      {fuel : Term.term, trust : Term.term, layouts : Term.term,
       address : Term.term, path : string} -> Thm.thm
    (* The fragment check_constant_contract_file accepts, rebuilt as source
       syntax and checked by the source route. Its constant and public
       qualifiers are taken from the JSON, as the default route takes them. *)
    val prepare_constant_file :
      {address : Term.term, path : string} -> source_input
    val check_constant_contract_file :
      {address : Term.term, path : string} -> Thm.thm
  end

end
