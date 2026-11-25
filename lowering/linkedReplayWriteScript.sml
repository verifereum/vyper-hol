Theory linkedReplayWrite
Ancestors
  constSubstStmts constSubstCorrect constSubstMods vyperTypeSystem
  vyperInterpreter vyperState vyperAST list

Theorem linked_replay_write_cases:
  const_subst_context roots cx env [] mods art /\
  (!bt. IS_SOME (type_place_target env bt) ==>
    !s. const_cells_agree roots s ==>
      eval_base_place cx bt s = eval_base_place cx (subst_consts_btarget_mods E bt) s /\
      eval_target_place cx bt s = eval_target_place cx (subst_consts_btarget_mods E bt) s) /\
  ((well_typed_expr env e \/ IS_SOME (type_place_expr env e)) ==>
    !s. const_cells_agree roots s ==>
      const_computations_related (const_results_related roots cx (expr_type e))
        (eval_expr cx e) (eval_expr cx (subst_consts_expr_mods E e)) s /\
      (!kt vt. type_place_expr env e = SOME (HashMapT kt vt) ==>
        eval_expr cx e s = eval_expr cx (subst_consts_expr_mods E e) s)) ==>
  (IS_SOME (type_stmt env ret (Assign tgt e)) ==>
    !s. const_cells_agree roots s ==>
      eval_stmt cx (subst_consts_stmt_mods E (Assign tgt e)) s =
      eval_stmt cx (Assign tgt e) s) /\
  (IS_SOME (type_stmt env ret (AugAssign ty bt bop e)) ==>
    !s. const_cells_agree roots s ==>
      eval_stmt cx (subst_consts_stmt_mods E (AugAssign ty bt bop e)) s =
      eval_stmt cx (AugAssign ty bt bop e) s) /\
  (IS_SOME (type_stmt env ret (Append bt e)) ==>
    !s. const_cells_agree roots s ==>
      eval_stmt cx (subst_consts_stmt_mods E (Append bt e)) s =
      eval_stmt cx (Append bt e) s)
Proof
  strip_tac >>
  `!t v s. writable_atarget env t /\ const_cells_agree roots s ==>
      assign_tuple_targets cx (subst_consts_target_mods E t) v s =
      assign_tuple_targets cx t v s` by
    (`(!E' t. E' = E ==> !v s.
        writable_atarget env t /\ const_cells_agree roots s ==>
        assign_tuple_targets cx (subst_consts_target_mods E' t) v s =
        assign_tuple_targets cx t v s) /\
      (!E' ts. E' = E ==> !vs s.
        EVERY (writable_atarget env) ts /\ const_cells_agree roots s ==>
        assign_tuple_target_list cx (subst_consts_targets_mods E' ts) vs s =
        assign_tuple_target_list cx ts vs s)` by
       (ho_match_mp_tac subst_consts_target_mods_ind >>
        rpt conj_tac >> rpt gen_tac >> rpt strip_tac >> gvs[]
        >- (simp[subst_consts_target_mods_def, evaluate_def, bind_def] >>
            drule writable_atarget_base >> strip_tac >>
            qpat_assum `!bt. IS_SOME _ ==> _` drule >>
            simp[evaluate_def, bind_def])
        >- (simp[subst_consts_target_mods_def, evaluate_def] >>
            CASE_TAC >> simp[] >> CASE_TAC >> simp[] >>
            first_x_assum irule >> simp[writable_atarget_tuple])
        >- (Cases_on `vs` >> simp[subst_consts_target_mods_def, evaluate_def]) >>
        Cases_on `vs` >> simp[subst_consts_target_mods_def, evaluate_def] >>
        gvs[ignore_bind_def, bind_def] >>
        `assign_tuple_targets cx (subst_consts_target_mods E t) h s =
         assign_tuple_targets cx t h s` by
          (qpat_assum `!v s. _ ==> assign_tuple_targets _ _ _ _ = _`
             irule >> simp[]) >>
        simp[] >> Cases_on `assign_tuple_targets cx t h s` >> Cases_on `q` >> simp[] >>
        first_x_assum irule >> simp[] >>
        drule_all const_subst_context_tuple_frame >> simp[]) >>
     metis_tac[]) >>
  `!s k l. well_typed_expr env e /\ const_cells_agree roots s /\
      (!v t. const_cells_agree roots t ==> k v t = (l v t : unit evaluation_result)) ==>
      bind (eval_expr cx e) (\p. bind (read_result cx p) k) s =
      bind (eval_expr cx (subst_consts_expr_mods E e))
        (\q. bind (read_result cx q) l) s` by
    (rpt gen_tac >> strip_tac >> rewrite_tac[GSYM const_computations_related_eq] >>
     irule const_computations_related_bind >>
     qexists `const_results_related roots cx (expr_type e)` >>
     reverse conj_tac >- metis_tac[] >>
     rpt strip_tac >> BETA_TAC >>
     rename1 `eval_expr cx e s = (INL x,t)` >>
     `const_cells_agree roots t` by
       (fs[const_subst_context_def] >>
        drule_all checked_eval_expr_const_cells_agree >> simp[]) >>
     match_mp_tac const_computations_related_prefix >> conj_tac
     >- (irule const_computations_related_read >> metis_tac[]) >>
     rpt strip_tac >> drule read_result_state >> strip_tac >>
     gvs[const_computations_related_eq]) >>
  `!b s k l. IS_SOME (type_place_target env b) /\ const_cells_agree roots s /\
      (!p t. const_cells_agree roots t ==> k p t = (l p t : unit evaluation_result)) ==>
      bind (eval_target_place cx b) k s =
      bind (eval_target_place cx (subst_consts_btarget_mods E b)) l s` by
    (rpt gen_tac >> strip_tac >> rewrite_tac[GSYM const_computations_related_eq] >>
     match_mp_tac const_computations_related_prefix >> conj_tac
     >- (simp[const_computations_related_eq] >> metis_tac[]) >>
     rpt strip_tac >> simp[const_computations_related_eq] >>
     first_x_assum irule >>
     irule protected_cell_frame_cells_agree >> qexists `s` >> simp[] >>
     rpt strip_tac >>
     `checked_frame_context cx mods art src id env` by
       (fs[const_subst_context_def] >>
        qpat_assum `!a sr i tv r. MEM _ _ ==> checked_frame_context _ _ _ _ _ _`
          (drule_then ACCEPT_TAC)) >>
     drule_all checked_eval_target_place_protected_cell_frame >>
     rewrite_tac[vyperCallOutcomeFrameTheory.state_rel_frame_result] >>
     simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `writable_atarget env tgt` by
        (drule typed_assign_target >> simp[writable_atarget_def] >> metis_tac[]) >>
      `well_typed_expr env e` by fs[type_stmt_def, AllCaseEqs()] >>
      `!g rhs. eval_stmt cx (Assign g rhs) =
          bind (eval_expr cx rhs) (\p. bind (read_result cx p) (\v. assign_tuple_targets cx g v))` by
        (Cases >> simp[evaluate_def]) >>
      simp[subst_consts_stmt_mods_def] >> sym_tac >>
      qpat_assum `!s k l. _ ==> bind (eval_expr _ _) _ _ = _` ho_match_mp_tac >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      drule typed_augassign_target >> strip_tac >>
      `well_typed_expr env e` by fs[type_stmt_def, AllCaseEqs()] >>
      simp[subst_consts_stmt_mods_def] >> pure_once_rewrite_tac[evaluate_def] >> sym_tac >>
      qpat_assum `!b s k l. _ ==> bind (eval_target_place _ _) _ _ = _` irule >>
      simp[] >> rpt strip_tac >>
      rewrite_tac[GSYM const_computations_related_eq] >>
      match_mp_tac const_computations_related_prefix >>
      simp[const_computations_related_refl] >> rpt strip_tac >>
      drule read_place_state >> strip_tac >> gvs[] >>
      match_mp_tac const_computations_related_prefix >>
      simp[const_computations_related_refl] >> rpt strip_tac >>
      drule place_type_value_state >> strip_tac >> gvs[const_computations_related_eq] >>
      qpat_assum `!s k l. _ ==> bind (eval_expr _ _) _ _ = _` ho_match_mp_tac >> simp[]) >>
  rpt strip_tac >>
  drule typed_append_target >> strip_tac >>
  `well_typed_expr env e` by
    (qpat_x_assum `IS_SOME (type_stmt _ _ (Append _ _))` mp_tac >>
     simp[type_stmt_def] >>
     namedCases_on `type_place_target env bt` ["", "vt"] >> simp[] >>
     Cases_on `vt` >> simp[] >>
     rename1 `Type tyv` >> Cases_on `tyv` >> simp[] >>
     rename1 `ArrayT elem sz` >> Cases_on `sz` >> simp[]) >>
  simp[subst_consts_stmt_mods_def] >> pure_once_rewrite_tac[evaluate_def] >> sym_tac >>
  qpat_assum `!b s k l. _ ==> bind (eval_target_place _ _) _ _ = _` irule >>
  simp[] >> rpt strip_tac >>
  qpat_assum `!s k l. _ ==> bind (eval_expr _ _) _ _ = _` ho_match_mp_tac >> simp[]
QED
