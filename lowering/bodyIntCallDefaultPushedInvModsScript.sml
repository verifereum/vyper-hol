Theory bodyIntCallDefaultPushedInvMods
Ancestors
  bodyFullPreds bodyFullPredsMods bodyInvSplit bodyCallSupport exprSimHypsDefs placeTypingProps
  constSubstCorrect constSubstStmts vyperTypeContract
  vyperTypeInvariants vyperTypeEvalProofs vyperLookupStorage vyperContext compileEnv
  alist list

Theorem default_retained_contract[local]:
  contract_inv mods exps ctx ce cx ==>
  contract_inv mods exps ctx (ce with ce_module := src)
    (cx with stk updated_by CONS (src,name))
Proof
  pure_rewrite_tac [contract_inv_def, cenv_module_pins_mods_def,
    immutable_section_layout_mods_def, linked_body_calls_resolved_def,
    context_function_live_def, get_tenv_stk_irrelevant,
    compile_env_accfupds, evaluation_context_accfupds, combinTheory.K_THM,
    listTheory.MEM, combinTheory.C_THM] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!s nm. IS_SOME (ALOOKUP mods s) /\ _ ==> _` irule >>
  qpat_x_assum `~(_ \/ _)` mp_tac >> simp[]
QED

Theorem default_pushed_env[local]:
  env_consistent env cx z ==>
  env_consistent (env with current_src := src) (cx with stk updated_by CONS (src,name)) z
Proof
  simp[env_consistent_def, env_context_consistent_def, env_scopes_consistent_def,
       env_immutables_consistent_def, current_module_def, get_tenv_stk_irrelevant,
       get_module_code_stk_irrelevant, fn_sigs_consistent_def,
       fn_sigs_declared_complete_def, toplevel_vtypes_complete_def, bare_globals_complete_def,
       bare_global_assignable_complete_def, flag_members_complete_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  gvs[] >> rpt (first_assum ACCEPT_TAC ORELSE conj_tac)
QED

Theorem default_pushed_expr_inv[local]:
  expr_sim_inv_mods mods ce cx env z ==>
  expr_sim_inv_mods mods (ce with ce_module := src) (cx with stk updated_by CONS (src,name))
    (env with current_src := src) z
Proof
  `place_map_tables_agree_on_defined (ce with ce_module := src) (env with current_src := src) =
   place_map_tables_agree_on_defined ce env` by
    (irule place_map_tables_agree_on_defined_cong >> simp[]) >>
  simp[expr_sim_inv_mods_def, get_module_code_stk_irrelevant, get_tenv_stk_irrelevant,
       functions_well_typed_stk_irrelevant, context_well_typed_stk_irrelevant,
       bare_globals_layout_def] >>
  strip_tac >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (irule default_pushed_env >> simp[]) >>
  rpt strip_tac >> rename1 `FLOOKUP env.bare_globals (owner,id) = SOME ty` >>
  qpat_assum `!s id t. FLOOKUP env.bare_globals (s,id) = SOME t /\ _ ==> _`
    (qspecl_then [`owner`, `id`, `ty`] mp_tac) >> simp[]
QED

Theorem default_pushed_cells[local]:
  body_const_cells_agree mods cx env z ==>
  body_const_cells_agree mods (cx with stk updated_by CONS (src,name))
    (env with current_src := src) z
Proof
  rewrite_tac[body_const_cells_agree_def] >> strip_tac >>
  `cx with stk updated_by CONS (src,name) = cx with stk := (src,name)::cx.stk` by
    simp[evaluation_context_component_equality] >>
  `!a. frame_maps (env with current_src := src) a = frame_maps env a` by
    simp[frame_maps_def] >>
  qexistsl_tac [`roots`, `art`, `imms`] >>
  simp[get_tenv_stk] >> rpt (first_assum ACCEPT_TAC ORELSE conj_tac)
  >- (rpt strip_tac >>
      qpat_assum `!addr src id tv root. MEM _ roots ==> _` drule >>
      simp[checked_frame_context_def]) >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!s id r. ALOOKUP (consts_env_mods _) _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  simp[] >> qexistsl_tac [`pv`, `v`] >>
  `!ty a b. const_result_at roots (cx with stk := (src,name)::cx.stk) ty a b =
             const_result_at roots cx ty a b` by simp[const_result_at_def, get_tenv_stk] >>
  drule constant_expr_eval_stk >> strip_tac >>
  simp[lookup_global_stk] >>
  first_assum ACCEPT_TAC
QED

(* The logical view repins only the module. The actual erased compiler cut
   and the caller's physical frame are not changed by this theorem. *)
Theorem intcall_default_pushed_inv_retained_mods:
  contract_inv mods exps ctx ce cx /\
  expr_sim_inv_mods mods ce cx env z /\
  body_const_cells_agree mods cx env z /\
  ALOOKUP mods src = SOME tops ==>
  let p = cx with stk updated_by CONS (src,name) in
  let ed = env with current_src := src in
  let cd = ce with ce_module := src in
  contract_inv mods exps ctx cd p /\
  module_body_inv mods src tops cd p /\
  expr_sim_inv_mods mods cd p ed z /\
  body_const_cells_agree mods p ed z
Proof
  simp[LET_THM, module_body_inv_def] >> strip_tac >>
  conj_tac >- (irule default_retained_contract >> simp[]) >>
  conj_tac >- (irule default_pushed_expr_inv >> simp[]) >>
  irule default_pushed_cells >> simp[]
QED
