(*
 * A pop's target: target_pre, which target_case needs, from the pop's
 * expr_body_pre.
 *
 * TOP-LEVEL:
 *   target_pre_of_pop       — target_pre from a pop's expr_body_pre
 *   pop_immutable_root_rejected — no pop of a target rooted at an
 *                             immutable meets expr_body_pre: allocLimits'
 *                             target_in_immutables rejects it
 *)

Theory popTargetPre
Ancestors
  targetPlaceSim targetPlaceSimCasesBase exprSimHypsDefs
  vyperAST vyperTypeSystem vyperTypeEnv vyperTypeCallGraph
  vyperTypeCallStackSoundness vyperTypeInvariants vyperTypeAssignContext
  supportedExprTraverse supportedProgram allocLimits list

(* Every index of a typed target meets expr_body_pre wherever expr_sim_inv
   holds, from the target's part of an expression's expr_body_pre. *)
Theorem target_indices_pre_of_body:
  !bt vt cenv cx env.
    type_place_target env bt = SOME vt /\ byte_widths_target bt /\
    alloc_limits_target cenv bt /\
    call_evaluation_safe cx (int_calls_target bt) /\
    ~supported_target_exists expr_evm_run_root bt /\
    ~supported_target_exists call_operands_effect_root bt /\
    ~supported_target_exists (const_name_root cx) bt /\
    EVERY (\c. FST c = NONE /\
               ?tops. supported_program tops /\
                      get_module_code cx NONE = SOME tops /\
                      IS_SOME (supported_function_decl tops c Internal))
          (int_calls_target bt) /\
    (!target. supported_target_exists (expr_abi_decode_target_root target) bt ==>
              occurs_abi_decode_target target (cx_tops cx)) /\
    (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
              is_dynamic (vyper_to_abi_type (type_env (cx_tops cx)) target)) ==>
    target_indices_pre cenv cx env bt
Proof
  recInduct base_assignment_target_induct >> rw[target_indices_pre_def] >>
  gvs[type_place_target_AttributeTarget, type_place_target_SubscriptTarget,
      byte_widths_expr_def, alloc_limits_expr_def, int_calls_expr_def,
      supported_expr_exists_def] >>
  imp_res_tac call_evaluation_safe_append_left >>
  imp_res_tac call_evaluation_safe_append_right
  >~ [`expr_body_pre _ _ _ e _`]
  >- rw[expr_body_pre_def, expr_has_evm_run_def] >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

(* A pop's target meets target_pre where the pop meets expr_body_pre and
   its root is not an immutable. *)
Theorem target_pre_of_pop:
  !cenv cx env ann bt es.
    expr_body_pre cenv cx env (Pop ann bt) es /\ ~immutable_root cx bt ==>
    target_pre cenv cx env bt es
Proof
  rw[expr_body_pre_def, target_pre_def] >>
  gvs[Once well_typed_expr_def, byte_widths_expr_def, alloc_limits_expr_def,
      int_calls_expr_def, expr_has_evm_run_def, supported_expr_exists_def,
      expr_abi_decode_target_root_def, expr_evm_run_root_def,
      call_operands_effect_root_def,
        exprSimHypsDefsTheory.const_name_root_def] >>
  irule target_indices_pre_of_body >> simp[] >> metis_tac[]
QED

(* A target is in an immutable exactly when its root is a module variable
   at an ImmutableLoc. *)
Theorem target_in_immutables_root:
  !bt mvars.
    target_in_immutables mvars bt <=>
    ?nsid off. target_root bt = TopLevelNameTarget nsid /\
               FLOOKUP mvars nsid = SOME (ImmutableLoc off)
Proof
  `(!e:expr. T) /\
   !bt mvars.
     target_in_immutables mvars bt <=>
     ?nsid off. target_root bt = TopLevelNameTarget nsid /\
                FLOOKUP mvars nsid = SOME (ImmutableLoc off)`
    suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
  rw[target_root_def, target_in_immutables_def] >>
  BasicProvers.every_case_tac >> simp[]
QED

Theorem target_root_untyped:
  !env bt. type_place_target env (target_root bt) = NONE ==>
    type_place_target env bt = NONE
Proof
  gen_tac >> measureInduct_on `base_assignment_target_size bt` >>
  Cases_on `bt` >> simp[target_root_def] >> rpt strip_tac >>
  first_x_assum (drule_at Any) >> simp[] >> strip_tac >>
  qmatch_goalsub_abbrev_tac `type_place_target env tgt` >>
  Cases_on `type_place_target env tgt` >> simp[] >>
  gvs[Abbr `tgt`, type_place_target_AttributeTarget,
      type_place_target_SubscriptTarget]
QED

(* A pop whose target is rooted at a module name with no storage declaration
   (an immutable or a constant) never meets expr_body_pre: the target types
   only through an assignable immutable, which expr_sim_inv places at an
   ImmutableLoc, and alloc_limits_expr rejects a pop of a target in an
   immutable (target_in_immutables, Venom's "Cannot load from location:
   immutables"). *)
Theorem pop_immutable_root_rejected:
  !cenv cx env es ann bt src id.
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = TopLevelNameTarget (src,id) /\
    (!ts. get_module_code cx src = SOME ts ==>
          find_var_decl_by_name id ts = NONE) ==>
    F
Proof
  rpt gen_tac >> strip_tac >>
  `expr_sim_inv cenv cx env es /\ well_typed_expr env (Pop ann bt) /\
   alloc_limits_expr cenv (Pop ann bt)` by fs[expr_body_pre_def] >>
  `env_context_consistent env cx` by
    fs[expr_sim_inv_def, env_consistent_def] >>
  `?ty. FLOOKUP env.bare_global_assignable (src,id) = SOME ty` by
    (drule well_typed_expr_Pop_dynamic_target >> strip_tac >>
     Cases_on `type_place_target env (TopLevelNameTarget (src,id))`
     >- (qspecl_then [`env`, `bt`] mp_tac target_root_untyped >> simp[]) >>
     gvs[type_place_target_TopLevelNameTarget] >>
     rename1 `FLOOKUP env.toplevel_vtypes _ = SOME vt` >> Cases_on `vt` >>
     fs[env_context_consistent_def] >> res_tac >> gvs[]) >>
  `FLOOKUP env.bare_globals (src,id) = SOME ty` by
    (fs[env_context_consistent_def] >> metis_tac[]) >>
  `?off. FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off)` by
    (`IS_SOME (FLOOKUP env.bare_global_assignable (src,id))` by fs[] >>
     fs[expr_sim_inv_def] >> metis_tac[]) >>
  `target_in_immutables cenv.ce_module_vars bt` by
    (simp[target_in_immutables_root] >> metis_tac[]) >>
  fs[alloc_limits_expr_def]
QED
