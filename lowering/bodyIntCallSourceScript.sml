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
