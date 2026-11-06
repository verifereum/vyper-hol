(* Whitelist removal, rows S25/S26: same-named locals in disjoint scopes.

   supported_function_bindings asks ALL_DISTINCT over a function's
   arguments, locals and loop variables.  The checker gives less: type_stmt
   declares a name only if it is not in scope (id NOTIN FDOM
   env.var_types), and If/For do not thread their arms' environments, so a
   name reused in two if/else arms or two sequential loops is accepted.
   The lowering handles that: declare_local gives each declaration its own
   pointer variable, type and capacity.

   Survey: every theorem outside lowering/supported/ whose proof reads
   supported_function_bindings (directly, through
   supported_function_body_binding_contract or supported_bindings_distinct,
   or through supported_stmts_bindings / collect_locals), and what it takes
   from it:
     externalBodyFrame:101 supported_function_arg_not_collect_locals
       - no argument is a local or loop variable (args vs locals only).
     externalBodyFrame:793 external_entry_target_param_type
       - ALL_DISTINCT (MAP FST args), and no argument is in
         collect_locals fbody, so build_compile_env's
         ALOOKUP (REVERSE (args ++ collect_locals body)) finds the
         argument's type.  Its consumer is external_body_frame, the S1
         entry of an external function.
     whitelistCheckerDecls:252 check_contract_function_header_bindings
       - produces the header clause (arguments only), not a consumer.
   Nothing reads distinctness among the locals themselves.  The rest of
   the S1/S3 body proof takes `?bindings. supported_stmts tops bindings ss`
   (bodyStorageCases supported_callable_body_contract, external_body_frame)
   with the bindings list otherwise free, and the declaration cases work
   from the typing alone:
     bodySimDeclCases declared_name_unbound: type_stmt's freshness and
       ce_locals_declared give FLOOKUP cenv.ce_vars id = NONE at an
       AnnAssign or For;
     bodySimDeclCases declare_local_same_frame, expr_sim_inv_declare_local;
     bodyExprPreFacts ce_locals_declared_declare_local and
       ce_locals_declared_stmt (an If or For leaves cenv and env as they
       were, so an arm's names are unbound again after it);
     body_annassign_case and body_for_case use only these.
   So no lemma needs ALL_DISTINCT of locals.

   Proved here, from the checker's facts instead of supported_function_body:
     check_contract_arg_not_collect_locals: an argument of a runtime
       function is not in collect_locals of its body (type_stmt's
       freshness at the entry environment, through
       check_contract_body_bindings_not_args);
     external_entry_target_param_type_fresh: external_entry_target_param_type
       with its supported_function_body premise replaced by those two
       facts (argument names distinct, as params_ok gives, and the
       argument not a local). *)
Theory whitelistScopes
Ancestors
  list alist compileVyper entryStateRel externalBodyFrame whitelistCheckerDecls

Theorem check_contract_arg_not_collect_locals:
  check_contract F layouts addr [(NONE, tops)] = SOME art /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret fbody) tops /\
  vis <> Deploy /\ MEM (id,ty) args ==>
  ~MEM id (MAP FST (collect_locals fbody))
Proof
  strip_tac >> drule_all check_contract_body_bindings_not_args >>
  simp[EVERY_MEM, collect_locals_supported_bindings_mem] >> strip_tac >>
  `MEM id (MAP FST args)` by (simp[MEM_MAP] >> qexists `(id,ty)` >> simp[]) >>
  metis_tac[]
QED

Theorem external_entry_target_param_type_fresh:
  set_external_package_target target
    (package_external_fn tops use_trans nkey_map
      (mut,nr,rr,fname,fargs,dflts,ret,fbody)) =
    (lbl,cenv0,pos_args,rest) /\
  compile_register_positional_args cenv0 pos_args 4 st = (cenv,st') /\
  ALL_DISTINCT (MAP FST fargs) /\ ~MEM id (MAP FST (collect_locals fbody)) /\
  MEM (id,ty) fargs ==>
  cenv.ce_var_type id = SOME ty
Proof
  strip_tac >>
  `ALOOKUP (REVERSE fargs) id = SOME ty` by
    (irule ALOOKUP_ALL_DISTINCT_MEM >>
     simp[MAP_REVERSE, ALL_DISTINCT_REVERSE]) >>
  drule compile_register_positional_args_cenv >> strip_tac >>
  `cenv.ce_var_type = cenv0.ce_var_type` by
    (qpat_x_assum `cenv = _` SUBST1_TAC >> simp[]) >>
  qpat_x_assum `cenv.ce_var_type = _` (fn th => rewrite_tac[th]) >>
  qpat_x_assum `compile_register_positional_args _ _ _ _ = _` kall_tac >>
  qpat_x_assum `cenv = _` kall_tac >>
  `ALOOKUP (REVERSE (collect_locals fbody)) id = NONE` by
    simp[ALOOKUP_NONE, MAP_REVERSE] >>
  qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
  simp[package_external_fn_def, set_external_package_target_def,
       update_cenv_nonreentrant_def, update_cenv_ret_abi_def] >>
  Cases_on `ret = NoneT` >> simp[] >> strip_tac >>
  gvs[build_compile_env_def] >> rpt (pairarg_tac >> gvs[]) >>
  simp[REVERSE_APPEND, ALOOKUP_APPEND]
QED
