(* The constant-cell certificate is independent of local bindings and locks. *)
Theory bodySelectedLockedCellsMods
Ancestors
  bodyFullPredsMods constSubstCorrect constSubstStmts constSubstMods
  vyperTypeContract vyperTypeContractContext vyperTypeContractStaticMaps
  vyperTypeConstantFold vyperTypeEvalProofs vyperLookupStorage
  vyperContext vyperInterpreter vyperState finite_map

Theorem const_result_at_stk[local]:
  const_result_at roots (cx with stk := stack) ty pv v =
  const_result_at roots cx ty pv v
Proof
  simp[const_result_at_def, get_tenv_stk]
QED

Theorem selected_locked_const_cells_mods:
  body_const_cells_agree_mods mods cx tenv es1 /\
  check_contract cx.in_deploy cx.layouts cx.txn.target mods = SOME art /\
  lock_if_nr cx nr (is_view_mut mut) es1 = (INL (),locked) ==>
  body_const_cells_agree_mods mods (cx with stk updated_by CONS (src,name))
    (function_entry_env art mods src vis args) locked
Proof
  strip_tac >>
  `locked.immutables = es1.immutables` by
    (qpat_assum `lock_if_nr _ _ _ _ = _` (assume_tac o REWRITE_RULE[lock_if_nr_def]) >>
     drule intcall_lock_state_preserves_frame >> simp[]) >>
  qpat_x_assum `body_const_cells_agree_mods _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[body_const_cells_agree_mods_def]) >>
  gvs[] >>
  `!key ty. FLOOKUP art.cta_bare_globals key = SOME ty ==>
            FLOOKUP art.cta_toplevel_vtypes key = SOME (Type ty)` by
    (PairCases >> rpt gen_tac >> strip_tac >>
     drule_all check_contract_bare_globals_consistent_checked >>
     disch_then (qspec_then `cx.layouts` strip_assume_tac) >>
     first_assum ACCEPT_TAC) >>
  `cx with stk updated_by CONS (src,name) = cx with stk := (src,name)::cx.stk` by
    simp[evaluation_context_component_equality] >>
  pure_rewrite_tac[body_const_cells_agree_mods_def] >>
  qexistsl_tac [`roots`, `art`,
    `case ALOOKUP es1.immutables cx.txn.target of
       NONE => empty_immutables | SOME cells => cells`] >>
  simp[get_tenv_stk] >>
  conj_tac
  >- (simp[function_entry_env_def, artifact_env_def, FOLDL_extend_local_args_static] >>
      drule get_tenv_sources >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!addr src id tv root. MEM _ roots ==> _` drule >>
      simp[checked_frame_context_def]) >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >>
      qpat_assum `!s id r. ALOOKUP (consts_env_mods _) _ = _ ==> _`
        (drule_then strip_assume_tac) >>
      gvs[frame_maps_def] >>
      simp[function_entry_env_def, artifact_env_def, FOLDL_extend_local_args_static] >>
      qexistsl_tac [`pv`, `v`] >>
      simp[const_result_at_stk, lookup_global_stk] >>
      drule constant_expr_eval_stk >> simp[] >> metis_tac[]) >>
  fs[const_cells_agree_def]
QED
