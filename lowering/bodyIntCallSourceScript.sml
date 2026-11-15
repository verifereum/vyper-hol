(* Source selection boundaries for the internal-call body simulation. *)
Theory bodyIntCallSource
Ancestors
  bodySim supportedProgram supportedDecls bodyIntCallReturn
  vyperTypeContractStaticMaps vyperInterpreter list exprSimHypsDefs
  intCallLookup

Theorem supported_runtime_callable:
  supported_program tops /\
  lookup_callable_function F name tops = SOME (mut,nr,args,dflts,ret,ss) ==>
  (?rr. MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops) /\
  supported_pure_exprs tops dflts /\
  EVERY (supported_default_expression tops) dflts /\
  EVERY (supported_value_type tops o SND) args /\
  supported_return_type tops ret /\
  supported_function_body tops Internal args ss /\
  supported_return_layouts ret ss
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
  EVERY (supported_value_type tops o SND) args /\
  supported_return_type tops ret /\
  supported_function_body tops Internal args ss /\
  supported_return_layouts ret ss
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

Theorem expr_body_pre_intcall_main:
  expr_body_pre cenv cx env (Call ty (IntCall (src,name)) es dflt) st ==>
  src = NONE
Proof
  simp[expr_body_pre_def,
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
  strip_tac >>
  `well_typed_expr env (Call ty (IntCall (src,name)) es dflt) /\
   fn_sigs_consistent env.fn_sigs cx` by
    gvs[expr_body_pre_def,
        expr_sim_inv_def,
        vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >>
  drule_all typed_intcall_source_signature >> simp[]
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
    EVERY (supported_value_type tops o SND) args /\
    supported_return_type tops ret /\
    supported_function_body tops Internal args ss /\
    supported_return_layouts ret ss
Proof
  strip_tac >>
  drule expr_body_pre_intcall_main >> strip_tac >> gvs[] >>
  drule expr_body_pre_intcall_signature >> strip_tac >>
  `get_module_code cx NONE = SOME tops` by gvs[body_inv_def] >>
  `IS_SOME (supported_function_decl tops (NONE,name) Internal)` by
    gvs[expr_body_pre_def, vyperTypeCallGraphTheory.int_calls_expr_def] >>
  gvs[] >>
  `supported_program tops` by gvs[body_inv_def] >>
  drule_all supported_internal_callable >> strip_tac >> gvs[] >>
  goal_assum (drule_at Any) >> simp[]
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

Theorem deploy_lookup_param_types[local]:
  !tops name mut nr params dflts ret body.
    lookup_function NONE name Internal tops = NONE /\
    lookup_function NONE name Deploy tops = SOME (mut,nr,params,dflts,ret,body) ==>
    build_func_param_types tops name = MAP SND params
Proof
  Induct >> simp[lookup_function_def, compileVyperTheory.build_func_param_types_def] >>
  Cases >> simp[lookup_function_def, compileVyperTheory.build_func_param_types_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
  >~ [`(if vis = External then _ else _) name = _`]
  >- (Cases_on `vis` >> gvs[]) >>
  Cases_on `v` >> gvs[lookup_function_def]
QED

Theorem supported_callable_param_defaults:
  supported_program tops /\
  lookup_callable_function in_deploy name tops =
    SOME (mut,nr,params,dflts,ret,ss) ==>
  dflts = [] /\ build_func_param_types tops name = MAP SND params
Proof
  strip_tac >>
  `dflts = []` by
    (reverse (Cases_on `in_deploy`)
     >- (drule_all supported_runtime_callable >> simp[]) >>
     drule lookup_callable_function_T_SOME_cases >> strip_tac >> gvs[] >>
     drule_all supported_program_declaration >>
     simp[supported_function_header_contract, listTheory.NULL_EQ]) >>
  simp[] >>
  Cases_on `lookup_function NONE name Internal tops`
  >- (gvs[lookup_callable_function_def] >>
      metis_tac[deploy_lookup_param_types]) >>
  gvs[lookup_callable_function_def] >>
  drule lookup_function_Internal_SOME_MEM >> strip_tac >>
  `ALL_DISTINCT (supported_function_names tops)` by
    gvs[supported_program_def,
        supportedNamesTheory.supported_declaration_names_def] >>
  drule build_func_param_types_distinct >>
  disch_then (qspec_then `Internal` mp_tac) >> simp[] >>
  disch_then drule >> simp[]
QED

Theorem body_fn_sig_defaults_params:
  body_inv tops ctx cenv cx /\ fn_sigs_consistent env.fn_sigs cx /\
  FLOOKUP env.fn_sigs (src,name) = SOME sig ==>
  src = NONE /\ sig.num_defaults = 0 /\
  cenv.ce_func_param_types name = sig.param_types
Proof
  strip_tac >>
  gvs[vyperTypeInvariantsTheory.fn_sigs_consistent_def] >>
  first_x_assum drule >> strip_tac >>
  `src = NONE` by gvs[body_inv_def] >>
  `get_module_code cx NONE = SOME tops /\ supported_program tops /\
   cenv.ce_func_param_types = build_func_param_types tops` by
    gvs[body_inv_def] >>
  gvs[] >> drule_all supported_callable_param_defaults >> gvs[]
QED

(* Supported source signatures have no defaults. Their complete supplied arity
   makes the compiler's omitted suffix empty, independently of its default table. *)
Theorem body_expr_intcall_defaults_empty:
  body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e st ==>
  !ann src name args dflt.
    supported_expr_exists
      (\child. child = Call ann (IntCall (src,name)) args dflt) e ==>
    src = NONE /\
    ?sig. FLOOKUP env.fn_sigs (src,name) = SOME sig /\
      sig.num_defaults = 0 /\
      LENGTH args = LENGTH sig.param_types /\
      LENGTH args = LENGTH (cenv.ce_func_param_types name) /\
      omitted_defaults cenv name (LENGTH args) = []
Proof
  rpt strip_tac >>
  `well_typed_expr env e /\ fn_sigs_consistent env.fn_sigs cx` by
    gvs[expr_body_pre_def, expr_sim_inv_def,
        vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >>
  drule_all (CONJUNCT1 typed_internal_call_occurrences) >>
  simp[vyperTypeSystemTheory.well_typed_expr_def] >> strip_tac >>
  drule_all body_fn_sig_defaults_params >> strip_tac >>
  `LENGTH args = LENGTH sig.param_types` by decide_tac >>
  gvs[] >> simp[exprLoweringTheory.omitted_defaults_def]
QED
