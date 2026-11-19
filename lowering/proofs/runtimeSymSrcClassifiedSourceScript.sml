Theory runtimeSymSrcClassifiedSource
Ancestors
  supportedProgram supportedDecls supportedNameRoot constSubstStmtsPreserve
  supportedExprs constSubst compileVyper list alist

val _ = Parse.hide "body";

Theorem runtime_sym_const_lookup_names:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
  IS_SOME (ALOOKUP (module_consts_env tops []) id) ==>
  ?vis c ty slot.
    supported_variable_decl tops (NONE,id) = SOME (vis,Constant c,ty,slot)
Proof
  strip_tac >> drule distinct_module_consts_env_names_constant >>
  disch_then irule >> spose_not_then assume_tac >> gvs[GSYM ALOOKUP_NONE]
QED

Theorem runtime_sym_supported_function_subst:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
  supported_program tops /\ (vis = Deploy ==> supported_program_deploy tops) /\
  MEM (FunctionDecl vis mut nr rr name args defaults ret body) tops ==>
  subst_consts_fn (module_consts_env tops [])
    (mut,nr,rr,name,args,defaults,ret,body) =
    (mut,nr,rr,name,args,defaults,ret,body)
Proof
  strip_tac >>
  drule_all supported_program_declaration >>
  simp[supported_function_header_contract, supported_declaration_body_def] >>
  strip_tac >>
  irule subst_consts_supported_fn_unchanged >>
  qexistsl_tac [`tops`, `vis`] >>
  Cases_on `vis = Deploy` >> gvs[NULL_EQ, supported_pure_expr_def] >>
  metis_tac[runtime_sym_const_lookup_names, supported_program_deploy_function]
QED
