(* Whitelist removal: the program-level conjuncts of supported_program,
   from the checker.

   supported_declaration_names asks distinct function names (every
   visibility), distinct event names, a fallback without arguments,
   distinct argument names and distinct selectors.  check_contract F gives
   each: self_member_keys_toplevel covers every function name,
   function_header_ok the External __default__, params_ok the arguments.

   supported_function_body's binding conjuncts (arguments distinct, no local
   or loop variable reuses an argument) come from type_stmt's freshness at
   the entry environment: check_contract F for a runtime function,
   check_contract T for any function, the constructor included, as
   supported_program_deploy asks.

   function_header_ok gives the constructor's return type NoneT, which
   supported_function_return admits.

   The FlagDecl, ErrorDecl and InterfaceDecl headers and bodies are T in the
   gate, and its External argument types are unconstrained, so they need no
   lemma here. *)
Theory whitelistCheckerProgram
Ancestors
  list rich_list
  vyperAST vyperTypeContract vyperTypeContractContext
  supportedTypes supportedDecls supportedNames supportedProgram
  supportedStmtTraverse
  whitelistCheckerDecls whitelistCheckerDeploy

Theorem function_names_self_member_sublist[local]:
  !tops.
    sublist (MAP (\n. (NONE, n)) (supported_function_names tops))
            (FLAT (MAP (self_member_keys_toplevel (NONE:num option)) tops))
Proof
  Induct >> simp[supported_function_names_def, sublist_nil] >>
  Cases >>
  simp[supported_function_names_def, self_member_keys_toplevel_def] >>
  simp[GSYM sublist_cons, sublist_cons_include]
QED

Theorem check_contract_function_names_distinct:
  check_contract b layouts addr [(NONE, tops)] = SOME art ==>
  ALL_DISTINCT (supported_function_names tops)
Proof
  strip_tac >> drule check_contract_namespaces_ok >>
  simp[contract_namespaces_ok_def, contract_keys_def] >> strip_tac >>
  irule (INST_TYPE [beta |-> ``:num option # string``] ALL_DISTINCT_MAP) >>
  qexists_tac `\x. (NONE, x)` >>
  irule sublist_ALL_DISTINCT >>
  qexists_tac `FLAT (MAP (self_member_keys_toplevel NONE) tops)` >>
  simp[function_names_self_member_sublist]
QED

Theorem check_contract_supported_declaration_names:
  check_contract F layouts addr [(NONE, tops)] = SOME art ==>
  supported_declaration_names tops
Proof
  strip_tac >>
  simp[supported_declaration_names_def, EVERY_MEM] >>
  rpt conj_tac
  >- metis_tac[check_contract_function_names_distinct]
  >- metis_tac[check_contract_event_names_distinct]
  >- (Cases >> simp[supported_function_header_names_def] >> strip_tac >>
      conj_tac
      >- (strip_tac >> gvs[] >>
          metis_tac[check_contract_fallback_no_arguments]) >>
      drule_all check_contract_function_header_bindings >> simp[])
  >- metis_tac[check_contract_selectors_distinct]
QED

(* The binding conjuncts of supported_function_body for a runtime
   function. *)
Theorem check_contract_function_body_bindings:
  check_contract F layouts addr [(NONE, tops)] = SOME art /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret fbody) tops /\
  vis <> Deploy ==>
  ALL_DISTINCT (MAP FST args) /\
  EVERY (\n. ~MEM n (MAP FST args))
    (MAP FST (supported_stmts_bindings T fbody) ++
     MAP FST (supported_stmts_bindings F fbody))
Proof
  strip_tac >> conj_tac
  >- (drule_all check_contract_function_header_bindings >>
      simp[supported_function_bindings_def]) >>
  drule_all check_contract_body_bindings_not_args >> simp[]
QED

(* The same for any function, the constructor included, from the
   deployment check: the binding conjuncts of supported_program_deploy. *)
Theorem check_contract_deploy_function_body_bindings:
  check_contract T layouts addr [(NONE, tops)] = SOME art /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret fbody) tops ==>
  ALL_DISTINCT (MAP FST args) /\
  EVERY (\n. ~MEM n (MAP FST args))
    (MAP FST (supported_stmts_bindings T fbody) ++
     MAP FST (supported_stmts_bindings F fbody))
Proof
  strip_tac >> conj_tac
  >- (drule_all check_contract_deploy_function_header_bindings >>
      simp[supported_function_bindings_def]) >>
  drule_all check_contract_deploy_body_bindings_not_args >> simp[]
QED

Theorem check_contract_deploy_return:
  check_contract F layouts addr [(NONE, tops)] = SOME art /\
  MEM (FunctionDecl Deploy mut nr rr name args dflts ret fbody) tops ==>
  supported_function_return tops Deploy ret
Proof
  strip_tac >> drule_all check_contract_single_decl >>
  simp[check_toplevel_decl_def, function_header_ok_def,
       supported_function_return_def, supported_return_type_def]
QED
