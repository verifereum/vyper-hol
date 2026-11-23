Theory linkedReplayReason
Ancestors
  linkedConstAnnotations constSubstCorrect constSubstMods vyperTypeSystem vyperInterpreter vyperAST
  vyperState list option pair

Theorem linked_replay_reason_cases:
  const_subst_context roots cx env [] mods art /\
  (!e. (well_typed_expr env e \/ IS_SOME (type_place_expr env e)) ==>
    !s. const_cells_agree roots s ==>
      const_computations_related (const_results_related roots cx (expr_type e))
        (eval_expr cx e) (eval_expr cx (subst_consts_expr_mods E e)) s /\
      (!kt vt. type_place_expr env e = SOME (HashMapT kt vt) ==>
        eval_expr cx e s = eval_expr cx (subst_consts_expr_mods E e) s)) /\
  (!xs. well_typed_exprs env xs ==> !s. const_cells_agree roots s ==>
    eval_exprs cx xs s = eval_exprs cx (subst_consts_exprs_mods E xs) s) ==>
  (IS_SOME (type_stmt env ret (Raise rr)) ==> !s. const_cells_agree roots s ==>
    eval_stmt cx (subst_consts_stmt_mods E (Raise rr)) s = eval_stmt cx (Raise rr) s) /\
  (IS_SOME (type_stmt env ret (Assert e ar)) ==> !s. const_cells_agree roots s ==>
    eval_stmt cx (subst_consts_stmt_mods E (Assert e ar)) s = eval_stmt cx (Assert e ar) s)
Proof
  strip_tac >>
  `!xs. MAP (subst_consts_expr_mods E) xs = subst_consts_exprs_mods E xs` by
    (Induct >> simp[subst_consts_expr_mods_def]) >>
  `!exp k l s. well_typed_expr env exp /\ const_cells_agree roots s /\
    (!p q u. const_results_related roots cx (expr_type exp) p q /\
      const_cells_agree roots u ==> const_computations_related $= (k p) (l q) u) ==>
    const_computations_related (($=) : unit -> unit -> bool) (bind (eval_expr cx exp) k)
      (bind (eval_expr cx (subst_consts_expr_mods E exp)) l) s` by
    (rpt strip_tac >> irule const_computations_related_bind >>
     qexists `const_results_related roots cx (expr_type exp)` >>
     reverse conj_tac >- metis_tac[] >>
     rpt strip_tac >> rename1 `eval_expr cx exp s = (INL p,snext)` >>
     `const_cells_agree roots snext` by
       (fs[const_subst_context_def] >> drule_all checked_eval_expr_const_cells_agree >> simp[]) >>
     metis_tac[]) >>
  `!r. IS_SOME (type_stmt env ret (Raise r)) ==> !s. const_cells_agree roots s ==>
    const_computations_related $= (eval_stmt cx (Raise r))
      (eval_stmt cx (Raise (subst_consts_rreason_mods E r))) s` by
    (Cases >> simp[subst_consts_rreason_mods_def, const_computations_related_refl] >>
     rpt strip_tac
     >~ [`RaiseReason msg`] >-
       (simp[evaluate_def] >> first_x_assum ho_match_mp_tac >>
        gvs[type_stmt_def, AllCaseEqs()] >> rpt strip_tac >>
        irule const_computations_related_prefix >>
        simp[const_computations_related_refl] >>
        irule const_computations_related_read >> metis_tac[]) >>
     rename1 `RaiseCustomError err` >> Cases_on `err` >>
     rename1 `CustomError id pos kw` >>
     simp[evaluate_def, ordered_error_args_subst] >>
     simp[subst_consts_error_mods_def] >>
     Cases_on `get_module_code cx (FST id)` >> simp[const_computations_related_refl] >>
     rename1 `get_module_code _ _ = SOME tops` >>
     Cases_on `lookup_custom_error_args_in (SND id) tops` >>
     simp[const_computations_related_refl] >>
     rename1 `lookup_custom_error_args_in _ _ = SOME params` >>
     Cases_on `order_custom_error_args params (CustomError id pos kw)` >>
     simp[const_computations_related_refl] >>
     irule const_computations_related_prefix >>
     simp[const_computations_related_eq, const_computations_related_refl] >>
     gvs[type_stmt_def, AllCaseEqs()] >>
     drule_all frame_ordered_custom_error_typing >> simp[]) >>
  conj_tac
  >- (simp[subst_consts_stmt_mods_def] >>
      metis_tac[const_computations_related_eq]) >>
  rpt strip_tac >>
  `well_typed_expr env e` by (Cases_on `ar` >> gvs[type_stmt_def, AllCaseEqs()]) >>
  `?r. IS_SOME (type_stmt env ret (Raise r)) /\
    eval_stmt cx (Assert e ar) =
      bind (eval_expr cx e) (\p. switch_BoolV cx p (return ()) (eval_stmt cx (Raise r))) /\
    eval_stmt cx (subst_consts_stmt_mods E (Assert e ar)) =
      bind (eval_expr cx (subst_consts_expr_mods E e))
        (\q. switch_BoolV cx q (return ())
          (eval_stmt cx (Raise (subst_consts_rreason_mods E r))))` by
    (Cases_on `ar` >>
     gvs[type_stmt_def, AllCaseEqs(), subst_consts_stmt_mods_def, subst_consts_areason_mods_def]
     >- (qexists `RaiseBare` >> simp[type_stmt_def, subst_consts_rreason_mods_def, evaluate_def])
     >- (qexists `RaiseUnreachable` >> simp[type_stmt_def, subst_consts_rreason_mods_def, evaluate_def])
     >- (rename1 `AssertReason msg` >> qexists `RaiseReason msg` >>
         simp[type_stmt_def, subst_consts_rreason_mods_def, evaluate_def]) >>
     rename1 `AssertCustomError err` >> qexists `RaiseCustomError err` >>
     simp[type_stmt_def, subst_consts_rreason_mods_def, evaluate_def]) >>
  asm_rewrite_tac[] >> sym_tac >>
  rewrite_tac[GSYM const_computations_related_eq] >>
  first_x_assum ho_match_mp_tac >> simp[] >> rpt strip_tac >>
  irule const_computations_related_switch >>
  simp[const_computations_related_refl] >> metis_tac[]
QED
