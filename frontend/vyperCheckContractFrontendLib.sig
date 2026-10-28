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

  (* Source API: ORIGINAL pre-erasure program, explicit inherited identities,
     nominal environment, slots and layouts. Always checks deployment bodies.
     No legacy translation/retry. This independent full-source API is not the
     ordinary residual bridge; raw compatibility names below remain explicit. *)
  type source_input =
    {fuel : Term.term, trust : Term.term, keys : Term.term,
     program : Term.term, layouts : Term.term, address : Term.term}
  type source_checked_result = sourceModuleFrontendLib.checked
  val check_source_contract_result : source_input -> source_checked_result
  val check_source_contract : source_input -> Thm.thm
  val check_source_contract_file :
    {fuel : Term.term, trust : Term.term, keys : Term.term,
     layouts : Term.term, address : Term.term, path : string} -> Thm.thm

  val check_loaded_source_contract_result :
    {fuel : Term.term, trust : Term.term, source : sourceModuleLoaderLib.loaded,
     layouts : Term.term, address : Term.term} -> source_checked_result

  (* Clean source-facing name without silently changing existing callers. *)
  structure Source : sig
    val check_contract_result : source_input -> source_checked_result
    val check_contract : source_input -> Thm.thm
    (* Trusted pre-erasure capture from tools/source_module_loader.py. These
       entry points validate loader policies; they do NOT accept ordinary
       post-erasure annotated JSON or reconstruct qualifiers from metadata. *)
    val check_loaded_contract_result :
      {fuel : Term.term, trust : Term.term, source : sourceModuleLoaderLib.loaded,
       layouts : Term.term, address : Term.term} -> source_checked_result
    val check_contract_file_result :
      {fuel : Term.term, trust : Term.term, layouts : Term.term,
       address : Term.term, path : string} -> source_checked_result
    val check_contract_file :
      {fuel : Term.term, trust : Term.term, layouts : Term.term,
       address : Term.term, path : string} -> Thm.thm
    (* Kernel extraction for one checked main module. Universally quantified
       finalizer/policy/bytes; raw compile_vyper success remains an antecedent.
       Independent source derivations and nominal-environment agreement remain
       explicit in the call/load conclusion. NOT bytecode correctness or a
       claim that every accepted program has a source semantic derivation. *)
    val artifact_semantics : source_checked_result -> Thm.thm
    (* Strict legacy JSON syntax adapter; same source evaluator, no retry.
       Qualifier flags are trusted compatibility assertions, NOT pre-erasure
       source provenance. *)
    val check_constant_contract_file :
      {address : Term.term, path : string} -> Thm.thm
  end

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
  (* Ordinary #543 route. Runtime type/import/layout claims on residual
     parents are explicitly inherited, not independently source inferred. *)
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

  (* Strict legacy JSON decoder -> ORIGINAL source syntax -> same source
     pipeline. Qualifier flags remain a compatibility trust, not source proof.
     No folded/type metadata or old evaluator retry. *)
  val prepare_constant_source_file :
    {address : Term.term, path : string} -> source_input
  val check_constant_source_contract_file :
    {address : Term.term, path : string} -> Thm.thm
  val check_constant_contract_file_legacy :
    {address : Term.term, path : string} -> Thm.thm
  (* Same strict source route as Source.check_constant_contract_file. The
     explicit _legacy name alone retains the old constant evaluator. *)
  val check_constant_contract_file :
    {address : Term.term, path : string} -> Thm.thm

end
