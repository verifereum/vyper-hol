(* Source selection boundaries for the internal-call body simulation. *)
Theory bodyIntCallSource
Ancestors
  bodySim supportedProgram supportedDecls bodyIntCallReturn
  vyperTypeContractStaticMaps vyperInterpreter list exprSimHypsDefs

Theorem supported_runtime_callable:
  supported_program tops /\
  lookup_callable_function F name tops = SOME (mut,nr,args,dflts,ret,ss) ==>
  nr = F /\ dflts = [] /\
  (?rr. MEM (FunctionDecl Internal mut F rr name args [] ret ss) tops) /\
  EVERY (supported_value_type tops o SND) args /\
  supported_return_type tops ret /\
  supported_function_body tops Internal args ss /\
  supported_return_layouts ret ss
Proof
  strip_tac >> drule lookup_callable_function_F_SOME_MEM >> strip_tac >>
  drule_all supported_program_declaration >>
  simp[supported_function_header_contract, supported_declaration_body_def,
       supported_function_argument_def, supported_function_return_def,
       listTheory.NULL_EQ] >>
  strip_tac >> gvs[] >>
  gvs[EVERY_MEM, supported_function_argument_def] >>
  goal_assum (drule_at Any)
QED

(* The supported declaration rules out the synthetic deployment fallback. *)
Theorem supported_internal_lookup:
  !tops name mut nr rr args dflts ret ss.
    supported_function_decl tops (NONE,name) Internal =
      SOME (mut,nr,rr,args,dflts,ret,ss) ==>
    lookup_function NONE name Internal tops =
      SOME (mut,nr,args,dflts,ret,ss)
Proof
  Induct_on `tops` >- simp[supported_function_decl_def] >>
  Cases_on `h` >>
  simp[supported_function_decl_def, lookup_function_def] >>
  rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()]
  >~ [`lookup_function _ _ _ (VariableDecl _ _ _ _ _ :: _)`]
    >- (rename1 `VariableDecl vis _ _ _ _` >> Cases_on `vis` >>
        simp[lookup_function_def] >> metis_tac[])
  >~ [`lookup_function _ _ _ (HashMapDecl _ _ _ _ _ _ :: _)`]
    >- (rename1 `HashMapDecl vis _ _ _ _ _` >> Cases_on `vis` >>
        simp[lookup_function_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem supported_internal_callable:
  supported_program tops /\
  IS_SOME (supported_function_decl tops (NONE,name) Internal) /\
  lookup_callable_function in_deploy name tops =
    SOME (mut,nr,args,dflts,ret,ss) ==>
  nr = F /\ dflts = [] /\
  (?rr. MEM (FunctionDecl Internal mut F rr name args [] ret ss) tops) /\
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
    MAP expr_type es = TAKE (LENGTH es) (MAP SND args) /\
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
    MAP expr_type es = TAKE (LENGTH es) (MAP SND args) /\
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
  ?mut args ret ss.
    src = NONE /\
    get_module_code cx src = SOME tops /\
    lookup_callable_function cx.in_deploy name tops =
      SOME (mut,F,args,[],ret,ss) /\
    LENGTH es = LENGTH args /\
    MAP expr_type es = MAP SND args /\
    type_widens_to env.type_defs ret ty /\
    (?rr. MEM (FunctionDecl Internal mut F rr name args [] ret ss) tops) /\
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
  `LENGTH es = LENGTH args` by decide_tac >>
  gvs[] >> goal_assum (drule_at Any) >> simp[]
QED
