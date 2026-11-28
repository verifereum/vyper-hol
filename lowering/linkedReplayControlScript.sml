Theory linkedReplayControl
Ancestors
  constSubstStmts constSubstCorrect constSubstMods vyperInterpreter vyperState
  vyperTypeSystem vyperTypeEnvExtension vyperTypeContract vyperAST
  vyperCallOutcomeFrame

Theorem linked_replay_if_case:
  const_subst_context roots cx env [] mods art /\
  ((well_typed_expr env e \/ IS_SOME (type_place_expr env e)) ==>
   !s. const_cells_agree roots s ==>
     const_computations_related (const_results_related roots cx (expr_type e))
       (eval_expr cx e) (eval_expr cx (subst_consts_expr_mods E e)) s /\
     (!kt vt. type_place_expr env e = SOME (HashMapT kt vt) ==>
       eval_expr cx e s = eval_expr cx (subst_consts_expr_mods E e) s)) /\
  (!s. const_cells_agree roots s ==>
       eval_stmts cx (subst_consts_stmts_mods E yes) s = eval_stmts cx yes s) /\
  (!s. const_cells_agree roots s ==>
       eval_stmts cx (subst_consts_stmts_mods E no) s = eval_stmts cx no s) ==>
  IS_SOME (type_stmt env ret (If e yes no)) ==>
  !s. const_cells_agree roots s ==>
    eval_stmt cx (subst_consts_stmt_mods E (If e yes no)) s =
    eval_stmt cx (If e yes no) s
Proof
  rpt strip_tac >>
  `well_typed_expr env e` by gvs[type_stmt_def] >>
  `!addr src id tv root. MEM (addr,src,id,tv,root) roots ==>
     checked_frame_context cx mods art src id env` by
    fs[const_subst_context_def] >>
  once_rewrite_tac[EQ_SYM_EQ] >>
  rewrite_tac[GSYM const_computations_related_eq] >>
  simp[subst_consts_stmt_mods_def, evaluate_def] >>
  irule const_computations_related_bind >>
  qexists `const_results_related roots cx (expr_type e)` >>
  reverse conj_tac >- (qpat_assum `_ ==> !s. _` mp_tac >> simp[]) >>
  rpt strip_tac >>
  qmatch_asmsub_rename_tac `eval_expr cx e s = (INL x,s1)` >>
  `const_cells_agree roots s1` by
    (drule_all checked_eval_expr_const_cells_agree >> simp[]) >>
  simp[const_computations_related_eq, bind_def, ignore_bind_def,
       push_scope_def, return_def, finally_def] >>
  AP_THM_TAC >> AP_TERM_TAC >>
  qmatch_goalsub_abbrev_tac `switch_BoolV cx x _ _ s2` >>
  `const_cells_agree roots s2` by gvs[Abbr `s2`, const_cells_agree_def] >>
  rewrite_tac[GSYM const_computations_related_eq] >>
  irule const_computations_related_switch >>
  simp[const_computations_related_eq] >>
  qexistsl [`expr_type e`, `roots`] >> simp[]
QED

Theorem linked_replay_for_case:
  const_subst_context roots cx env [] mods art /\
  (!e. (well_typed_expr env e \/ IS_SOME (type_place_expr env e)) ==>
       expr_type (subst_consts_expr_mods E e) = expr_type e) /\
  (!e. (well_typed_expr env e \/ IS_SOME (type_place_expr env e)) ==>
   !s. const_cells_agree roots s ==>
     const_computations_related (const_results_related roots cx (expr_type e))
       (eval_expr cx e) (eval_expr cx (subst_consts_expr_mods E e)) s /\
     (!kt vt. type_place_expr env e = SOME (HashMapT kt vt) ==>
       eval_expr cx e s = eval_expr cx (subst_consts_expr_mods E e) s)) /\
  (!s. const_cells_agree roots s ==>
       eval_stmts cx (subst_consts_stmts_mods E lbody) s = eval_stmts cx lbody s) ==>
  IS_SOME (type_stmt env ret (For nm ty it n lbody)) ==>
  !s. const_cells_agree roots s ==>
    eval_stmt cx (subst_consts_stmt_mods E (For nm ty it n lbody)) s =
    eval_stmt cx (For nm ty it n lbody) s
Proof
  rpt strip_tac >>
  `well_typed_iterator env ty it /\
   IS_SOME (type_stmts (extend_local env nm ty F) ret lbody)` by
    gvs[type_stmt_def, AllCaseEqs()] >>
  `!addr src id tv root. MEM (addr,src,id,tv,root) roots ==>
     checked_frame_context cx mods art src id env` by
    fs[const_subst_context_def] >>
  `!e s. well_typed_expr env e /\ const_cells_agree roots s ==>
     const_computations_related (const_results_related roots cx (expr_type e))
       (eval_expr cx e) (eval_expr cx (subst_consts_expr_mods E e)) s` by
    (qpat_assum `!e. _ ==> !s. _` mp_tac >> simp[]) >>
  `!e s (k:eval_result -> evaluation_state -> eval_result list evaluation_result) l.
     well_typed_expr env e /\ const_cells_agree roots s /\
     (!p q s'. const_results_related roots cx (expr_type e) p q /\
       const_cells_agree roots s' ==> const_computations_related $= (k p) (l q) s') ==>
     const_computations_related $= (bind (eval_expr cx e) k)
       (bind (eval_expr cx (subst_consts_expr_mods E e)) l) s` by
    (rpt strip_tac >> irule const_computations_related_bind >>
     qexists `const_results_related roots cx (expr_type e)` >>
     reverse conj_tac >- simp[] >>
     rpt strip_tac >> drule_all checked_eval_expr_const_cells_agree >>
     simp[]) >>
  `!p q et s (k:value -> evaluation_state -> eval_result list evaluation_result) l.
     const_results_related roots cx et p q /\ const_cells_agree roots s /\
     (!v. const_computations_related $= (k v) (l v) s) ==>
     const_computations_related $= (bind (read_result cx p) k)
       (bind (read_result cx q) l) s` by
    (rpt strip_tac >> match_mp_tac const_computations_related_prefix >>
     conj_tac >- (irule const_computations_related_read >> qexistsl [`roots`, `et`] >> simp[]) >>
     rpt strip_tac >> drule read_result_state >> simp[]) >>
  `eval_iterator cx it s = eval_iterator cx (subst_consts_iter_mods E it) s` by
    (rewrite_tac[GSYM const_computations_related_eq] >>
     Cases_on `it` >> fs[well_typed_iterator_def] >>
     simp[subst_consts_iter_mods_def, evaluate_def]
     >- (`expr_type (subst_consts_expr_mods E e) = expr_type e` by simp[] >>
         simp[] >> qpat_assum `!e s k l. _` irule >> simp[] >>
         rpt strip_tac >> simp[const_computations_related_eq] >>
         `read_result cx p s' = read_result cx q s'` by
           (drule_all const_results_related_read >> simp[]) >>
         qpat_x_assum `const_results_related _ _ _ _ _` mp_tac >>
         simp[const_results_related_def] >> rpt strip_tac >> gvs[const_result_at_def] >>
         fs[array_iterator_results_def, bind_def]) >>
     qpat_assum `!e s k l. _` irule >> simp[] >>
     rpt strip_tac >> qpat_assum `!p q et s k l. _` irule >>
     goal_assum (drule_at Any) >> simp[] >>
     reverse conj_tac >- (qexists `ty` >> simp[]) >>
     gen_tac >> qpat_assum `!e s k l. _` irule >> simp[] >>
     rpt strip_tac >> qpat_assum `!p q et s k l. _` irule >>
     goal_assum (drule_at Any) >> simp[const_computations_related_refl] >>
     qexists `ty` >> simp[]) >>
  `!s0 res s1. const_cells_agree roots s0 /\ eval_stmts cx lbody s0 = (res,s1) ==>
     const_cells_agree roots s1` by
    (rpt strip_tac >>
     `const_subst_context roots cx (extend_local env nm ty F) [] mods art` by
       (irule const_subst_context_extend_local >> goal_assum (drule_at Any)) >>
     `!addr src id tv root. MEM (addr,src,id,tv,root) roots ==>
        checked_frame_context cx mods art src id (extend_local env nm ty F)` by
       (qpat_assum `const_subst_context _ _ (extend_local _ _ _ _) _ _ _` mp_tac >>
        pure_rewrite_tac[const_subst_context_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
     drule_all checked_eval_stmts_const_cells_agree >> simp[]) >>
  (* Induct over the evaluated iterator results, not the body syntax. *)
  `!vs ss tyv. const_cells_agree roots ss ==>
     eval_for cx tyv nm (subst_consts_stmts_mods E lbody) vs ss =
     eval_for cx tyv nm lbody vs ss` by
    (Induct >- simp[evaluate_def] >>
     rpt strip_tac >> simp[evaluate_def, bind_def] >>
     Cases_on `read_result cx h ss` >> drule read_result_state >> strip_tac >>
     gvs[] >> Cases_on `q` >> simp[] >>
     simp[ignore_bind_def, bind_def, push_scope_with_var_def, return_def,
          finally_def, try_def] >>
     qmatch_goalsub_abbrev_tac `eval_stmts cx lbody s2` >>
     `const_cells_agree roots s2` by gvs[Abbr `s2`, const_cells_agree_def] >>
     simp[] >> Cases_on `eval_stmts cx lbody s2` >>
     rename1 `eval_stmts cx lbody s2 = (res2,s3)` >>
     `const_cells_agree roots s3` by
       (qpat_assum `!s0 res s1. _` drule_all >> simp[]) >>
     Cases_on `res2` >> simp[return_def]
     >- (simp[pop_scope_def] >> CASE_TAC >> simp[return_def, raise_def] >>
         qpat_assum `!ss tyv. _ ==> eval_for _ _ _ _ _ _ = _` irule >>
         simp[const_cells_agree_scopes]) >>
     simp[handle_loop_exception_def] >>
     rw[return_def, raise_def, pop_scope_def] >>
     CASE_TAC >> simp[return_def, raise_def] >>
     qpat_assum `!ss tyv. _ ==> eval_for _ _ _ _ _ _ = _` irule >>
     simp[const_cells_agree_scopes]) >>
  simp[subst_consts_stmt_mods_def, evaluate_def] >>
  Cases_on `evaluate_type (get_tenv cx) ty` >>
  simp[lift_option_type_def, return_def, raise_def, bind_def, ignore_bind_def] >>
  qpat_x_assum `eval_iterator cx it s = _` (fn th => pure_once_rewrite_tac[GSYM th]) >>
  Cases_on `eval_iterator cx it s` >>
  rename1 `eval_iterator cx it s = (res,s1)` >>
  Cases_on `res` >> simp[] >>
  `const_cells_agree roots s1` by
    (irule protected_cell_frame_cells_agree >> qexists `s` >> simp[] >>
     rpt strip_tac >>
     qpat_assum `!addr src id tv root. _ ==> checked_frame_context _ _ _ _ _ _` drule >>
     strip_tac >> drule_all checked_eval_iterator_protected_cell_frame >>
     rewrite_tac[state_rel_frame_result] >> strip_tac >> first_x_assum drule >> simp[]) >>
  simp[check_def, assert_def, return_def, raise_def, bind_def]
QED
