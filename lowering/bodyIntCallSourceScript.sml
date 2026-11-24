(* Source selection boundaries for the internal-call body simulation. *)
Theory bodyIntCallSource
Ancestors
  bodySim supportedProgram supportedDecls
  vyperTypeContractStaticMaps vyperInterpreter list exprSimHypsDefs
  intCallLookup exprBodyPreProps bodyInvCodeProps bodyCallSupport
  vyperTypeContract supportedExprs

Theorem supported_runtime_callable:
  supported_program tops /\
  lookup_callable_function F name tops = SOME (mut,nr,args,dflts,ret,ss) ==>
  (?rr. MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops) /\
  supported_pure_exprs tops dflts /\
  EVERY (supported_default_expression tops) dflts /\
  supported_function_body tops Internal args ss
Proof
  strip_tac >> drule lookup_callable_function_F_SOME_MEM >> strip_tac >>
  drule_all supported_program_declaration >>
  simp[supported_function_header_contract, supported_declaration_body_def,
       supported_function_return_def, listTheory.NULL_EQ] >>
  strip_tac >> gvs[] >>
  goal_assum (drule_at Any)
QED

Theorem supported_internal_callable:
  supported_program tops /\
  IS_SOME (supported_function_decl tops (NONE,name) Internal) /\
  lookup_callable_function in_deploy name tops =
    SOME (mut,nr,args,dflts,ret,ss) ==>
  (?rr. MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops) /\
  supported_pure_exprs tops dflts /\
  EVERY (supported_default_expression tops) dflts /\
  supported_function_body tops Internal args ss
Proof
  strip_tac >>
  gvs[optionTheory.IS_SOME_EXISTS] >>
  rename1 `supported_function_decl _ _ _ = SOME decl` >>
  PairCases_on `decl` >>
  drule supported_internal_lookup >> strip_tac >>
  gvs[lookup_callable_function_def] >>
  drule_all (REWRITE_RULE [lookup_callable_function_F] supported_runtime_callable) >>
  simp[]
QED

Theorem supported_linked_callable[local]:
  source_body_call_supported cx (src,name) /\
  get_module_code cx src = SOME tops /\
  lookup_callable_function cx.in_deploy name tops =
    SOME (mut,nr,args,dflts,ret,ss) ==>
  ?vis rr. (vis = Internal \/ (cx.in_deploy /\ src <> NONE /\ vis = Deploy)) /\
    MEM (FunctionDecl vis mut nr rr name args dflts ret ss) tops /\
    supported_pure_exprs tops dflts /\
    EVERY (supported_default_expression tops) dflts /\
    supported_function_body tops vis args ss
Proof
  Cases_on `src` >> simp[source_body_call_supported_def] >>
  strip_tac >> gvs[]
  >- (fs[supported_linked_callee_def] >>
      drule_all_then strip_assume_tac supported_internal_callable >>
      qexists_tac `rr` >> simp[]) >>
  rename1 `MEM (FunctionDecl vis mut nr raw name args dflts ret ss) tops` >>
  Cases_on `vis` >>
  gvs[include_fn_sig_def, supported_declaration_body_def,
      supported_deploy_declaration_def]
  >- (qexists_tac `Internal` >> simp[] >> qexists_tac `raw` >> simp[]) >>
  `supported_declaration_header tops
     (FunctionDecl Deploy mut nr raw name args dflts ret ss)` by
    (fs[supported_module_headers_def, EVERY_MEM] >>
     res_tac >> gvs[supported_module_declaration_header_def]) >>
  fs[supported_function_header_contract, listTheory.NULL_EQ] >> gvs[] >>
  qexists_tac `Deploy` >> simp[] >> qexists_tac `raw` >> simp[supported_pure_expr_def]
QED

Theorem expr_body_pre_intcall_main:
  expr_body_pre cenv cx env (Call ty (IntCall (src,name)) es dflt) st ==>
  src = NONE
Proof
  simp[expr_body_pre_split_def,
       vyperTypeCallGraphTheory.int_calls_expr_def] >>
  strip_tac >> gvs[]
QED

Theorem typed_intcall_source_signature:
  well_typed_expr env (Call ty (IntCall (src,name)) es dflt) /\
  fn_sigs_consistent env.fn_sigs cx ==>
  ?ts mut nr args dflts ret ss.
    get_module_code cx src = SOME ts /\
    lookup_callable_function cx.in_deploy name ts =
      SOME (mut,nr,args,dflts,ret,ss) /\
    LENGTH es <= LENGTH args /\
    LENGTH args - LENGTH dflts <= LENGTH es /\
    LIST_REL (type_widens_to env.type_defs) (MAP expr_type es)
      (TAKE (LENGTH es) (MAP SND args)) /\
    type_widens_to env.type_defs ret ty
Proof
  simp[vyperTypeSystemTheory.well_typed_expr_def] >> strip_tac >>
  gvs[vyperTypeInvariantsTheory.fn_sigs_consistent_def] >>
  first_x_assum drule >> strip_tac >>
  goal_assum (drule_at Any) >> gvs[]
QED

Theorem expr_body_pre_intcall_signature_mods:
  expr_body_pre_mods mods cenv cx env (Call ty (IntCall (src,name)) es dflt) st ==>
  ?ts mut nr args dflts ret ss.
    get_module_code cx src = SOME ts /\
    lookup_callable_function cx.in_deploy name ts =
      SOME (mut,nr,args,dflts,ret,ss) /\
    LENGTH es <= LENGTH args /\
    LENGTH args - LENGTH dflts <= LENGTH es /\
    LIST_REL (type_widens_to env.type_defs) (MAP expr_type es)
      (TAKE (LENGTH es) (MAP SND args)) /\
    type_widens_to env.type_defs ret ty
Proof
  strip_tac >> drule expr_body_pre_mods_inv >> strip_tac >>
  drule expr_sim_inv_mods_env >> strip_tac >>
  drule expr_body_pre_mods_well_typed >> strip_tac >>
  `well_typed_expr env (Call ty (IntCall (src,name)) es dflt) /\
   fn_sigs_consistent env.fn_sigs cx` by
    fs[vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >>
  drule_all typed_intcall_source_signature >> simp[]
QED

Theorem expr_body_pre_intcall_signature:
  expr_body_pre cenv cx env (Call ty (IntCall (src,name)) es dflt) st ==>
  ?ts mut nr args dflts ret ss.
    get_module_code cx src = SOME ts /\
    lookup_callable_function cx.in_deploy name ts =
      SOME (mut,nr,args,dflts,ret,ss) /\
    LENGTH es <= LENGTH args /\
    LENGTH args - LENGTH dflts <= LENGTH es /\
    LIST_REL (type_widens_to env.type_defs) (MAP expr_type es)
      (TAKE (LENGTH es) (MAP SND args)) /\
    type_widens_to env.type_defs ret ty
Proof
  metis_tac[expr_body_pre_split_def, expr_body_pre_intcall_signature_mods]
QED

Theorem body_intcall_source_selection_mods:
  contract_inv mods exps ctx cenv cx /\
  expr_body_pre_mods mods cenv cx env (Call ty (IntCall (src,name)) es dflt) st ==>
  ?callee_tops vis mut nr args dflts ret ss.
    ALOOKUP mods src = SOME callee_tops /\
    get_module_code cx src = SOME callee_tops /\
    lookup_callable_function cx.in_deploy name callee_tops =
      SOME (mut,nr,args,dflts,ret,ss) /\
    LENGTH es <= LENGTH args /\
    LENGTH args - LENGTH dflts <= LENGTH es /\
    LIST_REL (type_widens_to env.type_defs) (MAP expr_type es)
      (TAKE (LENGTH es) (MAP SND args)) /\
    type_widens_to env.type_defs ret ty /\
    (vis = Internal \/ (cx.in_deploy /\ src <> NONE /\ vis = Deploy)) /\
    (?rr. MEM (FunctionDecl vis mut nr rr name args dflts ret ss) callee_tops) /\
    supported_pure_exprs callee_tops dflts /\
    EVERY (supported_default_expression callee_tops) dflts /\
    supported_function_body callee_tops vis args ss
Proof
  strip_tac >>
  `source_body_call_supported cx (src,name)` by
    (drule expr_body_pre_mods_int_calls >>
     simp[vyperTypeCallGraphTheory.int_calls_expr_def]) >>
  drule expr_body_pre_intcall_signature_mods >> strip_tac >>
  drule contract_inv_module_codes >> strip_tac >>
  drule_all supported_linked_callable >> strip_tac >>
  goal_assum (drule_at Any) >> gvs[] >> metis_tac[]
QED

Theorem body_intcall_source_selection:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Call ty (IntCall (src,name)) es dflt) st ==>
  ?mut nr args dflts ret ss.
    src = NONE /\
    get_module_code cx src = SOME tops /\
    lookup_callable_function cx.in_deploy name tops =
      SOME (mut,nr,args,dflts,ret,ss) /\
    LENGTH es <= LENGTH args /\
    LENGTH args - LENGTH dflts <= LENGTH es /\
    LIST_REL (type_widens_to env.type_defs) (MAP expr_type es)
      (TAKE (LENGTH es) (MAP SND args)) /\
    type_widens_to env.type_defs ret ty /\
    (?rr. MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops) /\
    supported_pure_exprs tops dflts /\
    EVERY (supported_default_expression tops) dflts /\
    supported_function_body tops Internal args ss
Proof
  strip_tac >> drule expr_body_pre_intcall_main >> strip_tac >> gvs[] >>
  drule_all body_inv_expr_body_pre_mods >> strip_tac >>
  drule body_inv_contract >> strip_tac >>
  drule_all body_intcall_source_selection_mods >>
  simp[alistTheory.ALOOKUP_def] >> metis_tac[]
QED

Theorem typed_internal_call_occurrences:
  (!env e ann src name args dflt.
    well_typed_expr env e /\
    supported_expr_exists
      (\child. child = Call ann (IntCall (src,name)) args dflt) e ==>
    well_typed_expr env (Call ann (IntCall (src,name)) args dflt)) /\
  (!env e vt ann src name args dflt.
    type_place_expr env e = SOME vt /\
    supported_expr_exists
      (\child. child = Call ann (IntCall (src,name)) args dflt) e ==>
    well_typed_expr env (Call ann (IntCall (src,name)) args dflt)) /\
  (!env target vt ann src name args dflt.
    type_place_target env target = SOME vt /\
    supported_target_exists
      (\child. child = Call ann (IntCall (src,name)) args dflt) target ==>
    well_typed_expr env (Call ann (IntCall (src,name)) args dflt)) /\
  (!env es ann src name args dflt.
    well_typed_exprs env es /\
    supported_exprs_exists
      (\child. child = Call ann (IntCall (src,name)) args dflt) es ==>
    well_typed_expr env (Call ann (IntCall (src,name)) args dflt)) /\
  (!env opt ann src name args dflt.
    well_typed_opt env opt /\
    supported_opt_exists
      (\child. child = Call ann (IntCall (src,name)) args dflt) opt ==>
    well_typed_expr env (Call ann (IntCall (src,name)) args dflt)) /\
  (!env fields ann src name args dflt.
    well_typed_named_exprs env fields /\
    supported_fields_exists
      (\child. child = Call ann (IntCall (src,name)) args dflt) fields ==>
    well_typed_expr env (Call ann (IntCall (src,name)) args dflt))
Proof
  ho_match_mp_tac vyperTypeSystemTheory.well_typed_expr_ind >>
  rpt conj_tac >> rpt strip_tac >>
  gvs[supportedExprTraverseTheory.supported_expr_exists_def] >>
  FIRST (map (fn pat => qpat_x_assum pat
    (strip_assume_tac o PURE_ONCE_REWRITE_RULE
      [vyperTypeSystemTheory.well_typed_expr_def]))
    [`well_typed_expr _ _`, `type_place_expr _ _ = SOME _`,
     `type_place_target _ _ = SOME _`, `well_typed_exprs _ _`,
     `well_typed_opt _ _`, `well_typed_named_exprs _ _`]) >>
  gvs[AllCaseEqs(), supportedExprTraverseTheory.supported_expr_exists_def] >>
  metis_tac[]
QED
