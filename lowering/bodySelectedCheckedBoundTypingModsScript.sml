(* Use the checker artifact of the actual qualified caller to type the
   selected declaration with the parameters of its already-bound scope. *)
Theory bodySelectedCheckedBoundTypingMods
Ancestors
  bodyFullPredsMods constSubstCorrect constSubstMods vyperTypeContract
  vyperTypeContractContext vyperTypeContractStaticMaps vyperTypeBindArguments
  vyperTypeConstantFold vyperTypeEvalProofs vyperTypeInvariants
  vyperTypeSystem vyperContext vyperState finite_map
  intCallCallee moduleLowering compileUnit compileVyper
  gasShadowStmtEnv stmtsEnvRetTy externalCallSelected option

Theorem checked_formals[local]:
  ALL_DISTINCT (MAP FST args) ==>
  let env = function_entry_env art mods src vis args in
    (!id ty. MEM (id,ty) args ==>
      FLOOKUP env.var_types id = SOME ty /\
      FLOOKUP env.var_assignable id = SOME (vis = Internal)) /\
    (!id ty. FLOOKUP env.var_types id = SOME ty ==> MEM (id,ty) args) /\
    (!id b. FLOOKUP env.var_assignable id = SOME b ==> ?ty. MEM (id,ty) args)
Proof
  strip_tac >> simp[function_entry_env_def, artifact_env_def] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_all FOLDL_extend_local_args_formal_lookup >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_all FOLDL_extend_local_args_var_types_range >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  drule_all FOLDL_extend_local_args_var_assignable_range >> simp[] >>
  metis_tac[]
QED

Theorem selected_checked_bound_body_typing_mods:
  body_const_cells_agree_mods mods cx tenv es1 /\
  well_typed_expr tenv (Call ann (IntCall (src,name)) es dflt) /\
  ALOOKUP mods src = SOME tops /\
  MEM (FunctionDecl vis mut nr raw name args dflts ret ss) tops /\
  (vis = Deploy ==> cx.in_deploy) /\
  bind_arguments (get_tenv cx) args vs = SOME penv /\
  es1.scopes = [penv] /\ locked.scopes = es1.scopes ==>
  ?art env env' env_raw.
    check_contract cx.in_deploy cx.layouts cx.txn.target mods = SOME art /\
    check_function_body cx.layouts cx.txn.target mods art src vis mut nr
      args dflts ret ss /\
    env = function_entry_env art mods src vis args /\
    env.current_src = current_module (cx with stk updated_by CONS (src,name)) /\
    env.type_defs = get_tenv (cx with stk updated_by CONS (src,name)) /\
    env_scopes_consistent env (cx with stk updated_by CONS (src,name)) locked /\
    type_stmts env ret ss = SOME env_raw /\
    type_stmts env ret (subst_consts_stmts_mods (consts_env_mods mods) ss) = SOME env' /\
    stmts_no_control_escape ss /\ (ret = NoneT \/ stmts_no_fallthrough ss) /\
    (!id ty. MEM (id,ty) args ==> FLOOKUP env.var_types id = SOME ty /\
      FLOOKUP env.var_assignable id = SOME (vis = Internal)) /\
    (!id ty. FLOOKUP env.var_types id = SOME ty ==> MEM (id,ty) args) /\
    (!id b. FLOOKUP env.var_assignable id = SOME b ==> ?ty. MEM (id,ty) args)
Proof
  strip_tac >>
  qpat_x_assum `body_const_cells_agree_mods _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [body_const_cells_agree_mods_def]) >>
  `check_function_body cx.layouts cx.txn.target mods art src vis mut nr
     args dflts ret ss` by
    (irule check_contract_function_body_MEM >> conj_tac
     >- (qexists_tac `cx.in_deploy` >> simp[check_function_body_in_mode_def]) >>
     qexistsl_tac [`name`, `raw`, `tops`] >> simp[] >>
     qpat_x_assum `well_typed_expr _ _`
       (strip_assume_tac o PURE_ONCE_REWRITE_RULE [well_typed_expr_def]) >>
     drule check_contract_artifact_fields >> strip_tac >>
     gvs[frame_maps_def, FLOOKUP_DRESTRICT_SOME]) >>
  qabbrev_tac `env = function_entry_env art mods src vis args` >>
  qpat_assum `Abbrev (env = _)` (fn def =>
    qpat_assum `check_function_body _ _ _ _ _ _ _ _ _ _ _ _`
      (strip_assume_tac o SIMP_RULE pure_ss
        [check_function_body_def, LET_THM, IS_SOME_EXISTS,
         GSYM (REWRITE_RULE [markerTheory.Abbrev_def] def)])) >>
  `ALL_DISTINCT (MAP FST args)` by fs[params_ok_def] >>
  drule checked_formals >>
  qpat_assum `Abbrev (env = _)` (fn def => disch_then
    (qspecl_then [`vis`, `src`, `mods`, `art`] (strip_assume_tac o
      SIMP_RULE pure_ss [LET_THM, GSYM (REWRITE_RULE [markerTheory.Abbrev_def] def)]))) >>
  `env_scopes_consistent env (cx with stk updated_by CONS (src,name)) locked` by
    (simp[env_scopes_consistent_stk_irrelevant] >>
     `locked = locked with scopes := [penv]` by simp[evaluation_state_component_equality] >>
     pop_assum (fn th => CONV_TAC (RAND_CONV (REWR_CONV th))) >>
     irule bind_arguments_env_scopes_consistent >>
     qexistsl_tac [`args`, `get_tenv cx`, `vs`] >> asm_rewrite_tac[] >>
     conj_tac >- simp[] >> conj_tac >- simp[] >>
     rpt gen_tac >> disch_tac >>
     qpat_assum `!id ty. MEM (id,ty) args ==> _` drule >> simp[]) >>
  rename1 `type_stmts env ret ss = SOME raw_env` >>
  rename1 `type_stmts env ret (subst_consts_stmts_mods _ _) = SOME sub_env` >>
  qexistsl_tac [`art`, `env`, `sub_env`, `raw_env`] >> asm_rewrite_tac[] >>
  drule get_tenv_sources >> strip_tac >>
  simp[Abbr `env`, function_entry_env_def, artifact_env_def, current_module_def,
       FOLDL_extend_local_args_static, get_tenv_stk_irrelevant]
QED

(* Only the compiler uses the void tag.  The typing above is at NoneT,
   whose absence of valued returns makes that tag immaterial to compilation. *)
Theorem selected_checked_body_interval_types_mods:
  set_internal_package_target target
    (package_internal_fn_unit mods T (K global_nonreentrant_slot) deploy ilen
      (src,subst_consts_fn_mods (consts_env_mods mods)
        (mut,nr,raw,name,args,dflts,ret,ss))) =
    (label,ce,params,has_rb,nr',key,trans,view,ctor,ilen',b,rt) /\
  type_stmts env ret (subst_consts_stmts_mods (consts_env_mods mods) ss) = SOME env' /\
  supported_stmts tops bindings b ==>
  b = subst_consts_stmts_mods (consts_env_mods mods) ss /\
  rt = (if ret = NoneT then NONE else SOME ret) /\
  stmts_env body_ce NoLoop ret b =
    stmts_env body_ce NoLoop (case rt of SOME t => t | NONE => BaseT BoolT) b /\
  stmts_env (gas_shadow_env T body_ce) NoLoop ret (MAP gas_shadow_stmt b) =
    stmts_env (gas_shadow_env T body_ce) NoLoop
      (case rt of SOME t => t | NONE => BaseT BoolT) (MAP gas_shadow_stmt b)
Proof
  simp[subst_consts_fn_mods_def, package_internal_fn_unit_def,
       set_internal_package_target_def] >>
  strip_tac >> Cases_on `ret = NoneT` >> gvs[] >>
  drule_then assume_tac type_stmts_none_valued_return >>
  conj_tac
  >- (irule stmts_env_ret_ty_no_valued_return >> simp[] >>
      qexistsl_tac [`bindings`,`tops`] >> simp[]) >>
  irule stmts_env_ret_ty_no_valued_return >> simp[gas_shadow_valued_return] >>
  qexistsl_tac [`bindings`,`tops`] >> simp[gas_shadow_supported_stmts]
QED
