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

  (* The imports list of a JAnnotatedAST term, and an import's path. *)
  val annotated_ast_imports : Term.term -> Term.term
  val imported_module_path : Term.term -> string

  (* Drops repeated imports, as jsonToVyper's remove_repeated_imports does,
     so the rest line up with the translated imported sources. *)
  val remove_repeated_imports : Term.term list -> Term.term list

  (* Drops empty .vyi sources from a translated (sources, rest) pair, given
     the annotated AST it came from; the returned sources have distinct
     source IDs. Fails on conflicting definitions for one source ID. *)
  val remove_interface_sources : Term.term -> Term.term -> Term.term

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

end
