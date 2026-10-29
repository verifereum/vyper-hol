signature vyperCheckContractFrontendLib = sig

  type legacy_frontend_input =
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
  type legacy_checked_result =
    {input : vyperCheckContractLib.check_input,
     modules : Term.term,
     layouts : Term.term,
     address : Term.term,
     artifact : Term.term,
     theorem : Thm.thm}

  (* Annotated-only route is deliberately explicit and retains old trust. *)
  val prepare_check_input_legacy : legacy_frontend_input -> vyperCheckContractLib.check_input
  val check_contract_result_legacy : legacy_frontend_input -> legacy_checked_result
  val check_contract_legacy : legacy_frontend_input -> Thm.thm
  val check_contract_file_legacy :
    {in_deploy : bool, address : Term.term, path : string} -> Thm.thm
  val check_constant_contract_file_legacy :
    {address : Term.term, path : string} -> Thm.thm

  (* Ordinary #543 route. Original loader provenance is paired with occurrence
     claims. Runtime type/import/layout claims remain explicitly inherited. *)
  type frontend_input = sourceOrdinaryProgramLib.input
  type checked_result = sourceOrdinaryProgramLib.checked
  val prepare_check_input : frontend_input -> sourceOrdinaryProgramLib.prepared
  val check_contract_result : frontend_input -> checked_result
  val check_contract : frontend_input -> Thm.thm
  val compile_checked : checked_result -> Term.term -> Thm.thm
  val check_contract_file_result :
    {fuel:Term.term, inherited:sourceOrdinaryProgramLib.inherited, address:Term.term,
     original_path:string, annotated_path:string} -> checked_result
  val check_contract_file :
    {fuel:Term.term, inherited:sourceOrdinaryProgramLib.inherited, address:Term.term,
     original_path:string, annotated_path:string} -> Thm.thm

end
