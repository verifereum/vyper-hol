(* Whitelist removal, constructor gate: the check_contract T twins of the
   runtime checker facts in whitelistCheckerDecls and whitelistScopes.
   check_contract F never checks a Deploy body (check_function_body_in_mode
   F Deploy = F), so the constructor gate takes these from check_contract T,
   which checks every function body of the main module.  Each lemma holds
   for any visibility, the Deploy function included.
   TOP-LEVEL:
     check_contract_deploy_function_header_bindings
     check_contract_deploy_body_bindings_not_args
     check_contract_deploy_arg_not_collect_locals
     check_contract_deploy_function_names_same_vis_distinct
     check_contract_deploy_callable_names_distinct: Internal and Deploy
       functions have distinct names together, as build_func_info and
       build_func_ids (keyed by name over every non-External function)
       need.  check_contract F does not give this: its fn_sigs keys are the
       Internal functions only. *)
Theory whitelistCheckerDeploy
Ancestors
  list rich_list finite_map pred_set option
  vyperAST vyperTypeSystem vyperTypeContract
  vyperTypeContractStaticMaps vyperTypeContractContext
  supportedNames supportedStmtTraverse externalBodyFrame
  whitelistCheckerDecls

Theorem check_contract_deploy_namespaces[local]:
  check_contract T layouts addr [(NONE, tops)] = SOME art ==>
  ALL_DISTINCT (FLAT (MAP (fn_sig_keys_toplevel T (NONE:num option)) tops)) /\
  ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops))
Proof
  strip_tac >> drule check_contract_namespaces_ok >>
  simp[contract_namespaces_ok_def, contract_keys_def]
QED

Theorem check_contract_deploy_decl[local]:
  check_contract T layouts addr [(NONE, tops)] = SOME art /\ MEM tl tops ==>
  check_toplevel_decl [(NONE, tops)] art NONE tl
Proof
  strip_tac >> irule check_contract_toplevel_decl_MEM_checked >> simp[] >>
  metis_tac[]
QED

Theorem check_contract_deploy_body[local]:
  check_contract T layouts addr [(NONE, tops)] = SOME art /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret fbody) tops ==>
  check_function_body layouts addr [(NONE, tops)] art NONE vis mut nr args
    dflts ret fbody
Proof
  strip_tac >> irule check_contract_deploy_function_body_MEM >> simp[] >>
  metis_tac[]
QED

Theorem check_contract_deploy_function_header_bindings:
  check_contract T layouts addr [(NONE, tops)] = SOME art /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret fbody) tops ==>
  supported_function_bindings tops args [] []
Proof
  strip_tac >> drule_all check_contract_deploy_decl >>
  simp[check_toplevel_decl_def, params_ok_def,
       supported_function_bindings_def]
QED

Theorem check_contract_deploy_body_bindings_not_args:
  check_contract T layouts addr [(NONE, tops)] = SOME art /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret fbody) tops ==>
  EVERY (\n. ~MEM n (MAP FST args))
    (MAP FST (supported_stmts_bindings T fbody ++ supported_stmts_bindings F fbody))
Proof
  strip_tac >> drule_all check_contract_deploy_body >>
  simp[check_function_body_def, IS_SOME_EXISTS] >> strip_tac >>
  drule (CONJUNCT2 type_stmt_bindings_fresh) >>
  simp[function_entry_env_var_types_fdom]
QED

Theorem check_contract_deploy_arg_not_collect_locals:
  check_contract T layouts addr [(NONE, tops)] = SOME art /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret fbody) tops /\
  MEM (id,ty) args ==>
  ~MEM id (MAP FST (collect_locals fbody))
Proof
  strip_tac >> drule_all check_contract_deploy_body_bindings_not_args >>
  simp[EVERY_MEM, collect_locals_supported_bindings_mem] >> strip_tac >>
  `MEM id (MAP FST args)` by (simp[MEM_MAP] >> qexists `(id,ty)` >> simp[]) >>
  metis_tac[]
QED

Theorem callable_names_sublist[local]:
  !tops.
    sublist (MAP (\n. (NONE, n))
               (supported_function_names (FILTER (\t. ?vis m nr rr n a d r b.
                  t = FunctionDecl vis m nr rr n a d r b /\ vis <> External) tops)))
            (FLAT (MAP (fn_sig_keys_toplevel T (NONE:num option)) tops))
Proof
  Induct >> simp[supported_function_names_def, sublist_nil] >>
  `!f. include_fn_sig T f <=> f <> External` by
    (Cases >> simp[include_fn_sig_def]) >>
  rpt strip_tac >> Cases_on `h` >>
  simp[supported_function_names_def, fn_sig_keys_toplevel_def] >>
  rw[supported_function_names_def, GSYM sublist_cons]
QED

Theorem check_contract_deploy_callable_names_distinct:
  check_contract T layouts addr [(NONE, tops)] = SOME art ==>
  ALL_DISTINCT (supported_function_names
    (FILTER (\t. ?vis m nr rr n a d r b.
               t = FunctionDecl vis m nr rr n a d r b /\ vis <> External) tops))
Proof
  strip_tac >> drule check_contract_deploy_namespaces >> strip_tac >>
  irule (INST_TYPE [beta |-> ``:num option # string``] ALL_DISTINCT_MAP) >>
  qexists_tac `\x. (NONE, x)` >>
  irule sublist_ALL_DISTINCT >>
  qexists_tac `FLAT (MAP (fn_sig_keys_toplevel T NONE) tops)` >>
  simp[callable_names_sublist]
QED

Theorem supported_function_names_filter_sublist[local]:
  !tops P Q. (!t. P t ==> Q t) ==>
    sublist (supported_function_names (FILTER P tops))
            (supported_function_names (FILTER Q tops))
Proof
  Induct >> simp[supported_function_names_def, sublist_nil] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  rw[supported_function_names_def] >> gvs[] >>
  TRY (Cases_on `h`) >>
  simp[supported_function_names_def, GSYM sublist_cons, sublist_cons_include] >>
  metis_tac[sublist_cons_include, sublist_cons]
QED

Theorem check_contract_deploy_function_names_same_vis_distinct:
  check_contract T layouts addr [(NONE, tops)] = SOME art ==>
  ALL_DISTINCT (supported_function_names
    (FILTER (\t. ?m nr rr n a d r b. t = FunctionDecl vis m nr rr n a d r b) tops))
Proof
  strip_tac >> Cases_on `vis = External`
  >- (gvs[] >> drule check_contract_deploy_namespaces >> strip_tac >>
      irule (INST_TYPE [beta |-> ``:num option # string``] ALL_DISTINCT_MAP) >>
      qexists_tac `\x. (NONE, x)` >>
      irule sublist_ALL_DISTINCT >>
      qexists_tac `FLAT (MAP (external_name_keys_toplevel NONE) tops)` >>
      simp[function_names_external_sublist]) >>
  drule check_contract_deploy_callable_names_distinct >> strip_tac >>
  irule sublist_ALL_DISTINCT >>
  goal_assum (drule_at Any) >>
  irule supported_function_names_filter_sublist >> rw[] >> metis_tac[]
QED
