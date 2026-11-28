Theory scratchIntCallDefaultSetupPremises
Ancestors
  bodyFullPreds bodyInvSplit bodyIntCallDefaultSliceConstRootsMods
  constSubstMods exprLowering exprSimHypsDefs finite_map list vyperInterpreter

(* The source premises of the defaults-stage setup imply all the premises
   of the restated defaults-source setup. *)
Theorem defaults_source_setup_premises:
  (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\
  body_const_cells_agree mods cx tenv es0 /\
  expr_body_pre_mods mods cenv cx tenv (Call ann (IntCall (NONE,name)) es dflt) es0 /\
  EVERY (\e. expr_body_pre_mods mods cenv cx tenv e es0) es /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  expr_sim_inv_mods mods cenv cx tenv ee /\
  eval_exprs cx es (es0 with gas_obs := obs) = (INL xs,ee with gas_obs := []) /\
  length_skip = LENGTH dflts - (LENGTH args - LENGTH es) /\
  cxd = cx with stk updated_by CONS (NONE,name) /\
  ds = DROP length_skip (subst_consts_exprs_mods (consts_env_mods mods) dflts) ==>
  (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\
  body_const_cells_agree mods cx tenv es0 /\
  expr_body_pre_mods mods cenv cx tenv (Call ann (IntCall (NONE,name)) es dflt) es0 /\
  EVERY (\e. expr_body_pre_mods mods cenv cx tenv e es0) es /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  expr_sim_inv_mods mods cenv cx tenv ee /\
  eval_exprs cx es (es0 with gas_obs := obs) = (INL xs,ee with gas_obs := []) /\
  length_skip = LENGTH dflts - (LENGTH args - LENGTH es) /\
  cxd = cx with stk updated_by CONS (NONE,name) /\
  ds = DROP length_skip (subst_consts_exprs_mods (consts_env_mods mods) dflts) /\
  ~supported_exprs_exists (const_name_root_mods mods) ds
Proof
  strip_tac >>
  `~supported_exprs_exists (const_name_root_mods mods) ds` by
    (qpat_assum `body_const_cells_agree mods cx tenv es0`
       (strip_assume_tac o PURE_REWRITE_RULE [body_const_cells_agree_def]) >>
     drule_all_then ACCEPT_TAC intcall_default_slice_no_const_roots_mods) >>
  asm_rewrite_tac[]
QED

Theorem defaults_source_result_requires_main_pin:
  expr_sim_inv_mods mods (cenv_without_defaults cenv name)
    cxd (tenv with current_src := NONE) ee /\
  FLOOKUP tenv.bare_globals (NONE,id) = SOME ty /\
  ~cx_const_name_mods mods (NONE,id) ==>
  cenv.ce_module = NONE
Proof
  simp[expr_sim_inv_mods_def, cenv_without_defaults_def] >>
  strip_tac >>
  qpat_assum `!src id ty. FLOOKUP tenv.bare_globals (src,id) = SOME ty /\ _ ==> _`
    (qspecl_then [`NONE`, `id`, `ty`] mp_tac) >>
  impl_tac
  >- (conj_tac >- first_assum ACCEPT_TAC >>
      disj1_tac >> first_assum ACCEPT_TAC) >>
  disch_then (ACCEPT_TAC o REWRITE_RULE [] o CONJUNCT1)
QED
