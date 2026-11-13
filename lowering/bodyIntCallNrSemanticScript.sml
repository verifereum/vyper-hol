(* Source typing and admissibility at an internal call's guarded entry. *)
Theory bodyIntCallNrSemantic
Ancestors
  bodyIntCallSeamDefs bodyIntCallBodyTyping bodyIntCallProducerSemantic
  bodySim vyperState vyperInterpreter gasContext exprSimDefs stmtSimDefs
Libs
  monadsyntax

Theorem intcall_entry_body_typing_nr:
  body_inv tops ctx cenv cx /\ cenv_module_pins tops cenv /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
  intcall_entry tops ctx func cenv cx tenv name es sa sb vv s0 es0
    (mut,nr,args,ret,ss,rr) prev penv rtv es1 t ==>
  ?env_body env_after.
    env_body.current_src = NONE /\ env_body.type_defs = get_tenv cx /\
    env_body.fn_sigs = tenv.fn_sigs /\
    env_body.bare_globals = tenv.bare_globals /\
    env_body.bare_global_assignable = tenv.bare_global_assignable /\
    env_body.toplevel_vtypes = tenv.toplevel_vtypes /\
    env_body.flag_members = tenv.flag_members /\
    type_stmts env_body ret ss = SOME env_after /\
    IS_SOME (type_stmts (env_body with bare_global_assignable := FEMPTY) ret ss) /\
    (ret = NoneT \/ stmts_no_fallthrough ss) /\ stmts_no_control_escape ss /\
    (!id ty. MEM (id,ty) args ==>
      FLOOKUP env_body.var_types id = SOME ty /\
      IS_SOME (FLOOKUP env_body.var_assignable id)) /\
    (!n ty. FLOOKUP env_body.var_types n = SOME ty ==> MEM (n,ty) args) /\
    (!n b. FLOOKUP env_body.var_assignable n = SOME b ==> ?ty. MEM (n,ty) args) /\
    env_consistent env_body (cx with stk updated_by CONS (NONE,name)) es1
Proof
  strip_tac >>
  `es1.scopes = [penv] /\
   stmt_state_rel ctx func cenv cx (es1 with scopes := prev) t /\
   expr_sim_inv cenv cx tenv (es1 with scopes := prev)` by
    (qpat_x_assum `intcall_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       mp_tac >> simp[intcall_entry_def] >> rpt strip_tac >> simp[]) >>
  drule intcall_entry_source >> strip_tac >>
  drule internal_decl_lookup_not_none >> strip_tac >>
  gvs[cenv_module_pins_def] >>
  drule_all pinned_internal_bound_body_typing >> strip_tac >>
  qexistsl [`env_body`, `env_after`] >> simp[] >>
  `es1 with scopes := [penv] = es1` by simp[evaluation_state_component_equality] >>
  fs[] >> metis_tac[]
QED

Theorem intcall_rest_stmts_admissible_locked:
  gas_admissible (intcall_rest cx name mut nr ss prev rtv) expr_vv_res_ok es /\
  lock_if_nr cx nr (is_view_mut mut) es = (INL (),locked) ==>
  gas_admissible (eval_stmts (cx with stk updated_by CONS (NONE,name)) ss)
    (stmt_res_ok NoLoop) locked
Proof
  strip_tac >>
  `!gs. lock_if_nr cx nr (is_view_mut mut) (es with gas_obs := gs) =
    (INL (),locked with gas_obs := gs)` by
    (Cases_on `nr` >> gvs[lock_if_nr_def, return_def] >>
     Cases_on `cx.nonreentrant_slot` >> gvs[raise_def] >>
     gvs[acquire_nonreentrant_lock_def, ignore_bind_def, bind_def,
         get_transient_storage_def, update_transient_def, return_def,
         raise_def, check_not_static_def, check_def, assert_def,
         AllCaseEqs(), COND_RATOR] >>
     rpt IF_CASES_TAC >>
     gvs[bind_def, return_def, raise_def, update_transient_def, assert_def,
         evaluation_state_component_equality]) >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >>
  rewrite_tac[gas_admissible_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!gs res ee. _` (qspec_then `gs` mp_tac) >>
  asm_simp_tac std_ss [intcall_rest_def, ignore_bind_def, bind_def] >>
  Cases_on `res`
  >- (rename1 `INL u` >> Cases_on `u` >> simp[stmtSimDefsTheory.stmt_res_ok_def]) >>
  rename1 `INR exc` >> Cases_on `exc` >>
  simp[stmtSimDefsTheory.stmt_res_ok_def, try_def, finally_def,
       finally_unless_halt_def, bind_def, ignore_bind_def,
       handle_function_def, pop_function_def, set_scopes_def,
       return_def, raise_def, expr_vv_res_ok_def] >>
  Cases_on `nr /\ mut <> View /\ mut <> Pure` >> simp[] >>
  Cases_on `cx.nonreentrant_slot` >>
  simp[release_nonreentrant_lock_def, update_transient_def,
       get_transient_storage_def, return_def, bind_def, expr_vv_res_ok_def] >>
  rename1 `INR (Error err)` >> Cases_on `err` >> simp[]
QED
