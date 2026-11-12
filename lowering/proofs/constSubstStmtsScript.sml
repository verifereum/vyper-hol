(* Statement-level constant inlining: a body and its subst_consts_stmts image
   evaluate identically from every state that agrees on the constant cells.
   The source semantics never runs substituted code (internal calls look up
   the raw callee), so both sides run in the same context. *)
Theory constSubstStmts
Ancestors
  constSubstCorrect constSubst vyperAST vyperState vyperContext
  vyperInterpreter vyperTypeSystem vyperTypeEnvExtension
  vyperTypeContract vyperCallOutcomeFrame vyperLookupStorage
  vyperTypeContractStaticMaps vyperTypeConstantFold vyperTypeContractContext
  finite_map alist list

(* ===== Typing environments ===== *)

Theorem const_subst_context_static:
  const_subst_context roots cx env E mods art /\
  env'.type_defs = env.type_defs /\ env'.bare_globals = env.bare_globals /\
  env'.bare_global_assignable = env.bare_global_assignable /\
  env'.toplevel_vtypes = env.toplevel_vtypes /\ env'.fn_sigs = env.fn_sigs ==>
  const_subst_context roots cx env' E mods art
Proof
  simp[const_subst_context_def, checked_frame_context_def, frame_maps_def] >>
  metis_tac[]
QED

Theorem const_subst_context_type_stmt:
  const_subst_context roots cx env E mods art /\
  type_stmt env ret s = SOME env' ==>
  const_subst_context roots cx env' E mods art
Proof
  strip_tac >> drule type_stmt_env_preserved_static >> strip_tac >>
  irule const_subst_context_static >> simp[] >> metis_tac[]
QED

Theorem const_subst_context_extend_local:
  const_subst_context roots cx env E mods art ==>
  const_subst_context roots cx (extend_local env nm ty b) E mods art
Proof
  strip_tac >> irule const_subst_context_static >>
  simp[extend_local_def] >> metis_tac[]
QED

(* ===== Constant cells across state steps ===== *)

Theorem const_cells_agree_scopes[local]:
  const_cells_agree roots (st with scopes := sc) = const_cells_agree roots st
Proof
  simp[const_cells_agree_def]
QED

Theorem const_subst_context_frames[local]:
  const_subst_context roots cx env E mods art ==>
  !addr src id tv root. MEM (addr,src,id,tv,root) roots ==>
    checked_frame_context cx mods art src id env
Proof
  rw[const_subst_context_def]
QED

Theorem const_subst_context_target_frame[local]:
  const_subst_context roots cx env E mods art /\
  IS_SOME (type_place_target env bt) /\ const_cells_agree roots st /\
  eval_target_place cx bt st = (res,st') ==>
  const_cells_agree roots st'
Proof
  strip_tac >> irule protected_cell_frame_cells_agree >>
  qexists `st` >> simp[] >> rpt strip_tac >>
  drule_all const_subst_context_frames >> strip_tac >>
  drule_all checked_eval_target_place_protected_cell_frame >>
  simp[state_rel_frame_result] >> metis_tac[]
QED

Theorem const_subst_context_iterator_frame[local]:
  const_subst_context roots cx env E mods art /\
  well_typed_iterator env ty it /\ const_cells_agree roots st /\
  eval_iterator cx it st = (res,st') ==>
  const_cells_agree roots st'
Proof
  strip_tac >> irule protected_cell_frame_cells_agree >>
  qexists `st` >> simp[] >> rpt strip_tac >>
  drule_all const_subst_context_frames >> strip_tac >>
  drule_all checked_eval_iterator_protected_cell_frame >>
  simp[state_rel_frame_result] >> metis_tac[]
QED

Theorem const_subst_context_stmt_frame[local]:
  const_subst_context roots cx env E mods art /\
  IS_SOME (type_stmt env ret s) /\ const_cells_agree roots st /\
  eval_stmt cx s st = (res,st') ==>
  const_cells_agree roots st'
Proof
  strip_tac >> irule protected_cell_frame_cells_agree >>
  qexists `st` >> simp[] >> rpt strip_tac >>
  drule_all const_subst_context_frames >> strip_tac >>
  drule_all checked_eval_stmt_protected_cell_frame >>
  simp[state_rel_frame_result] >> metis_tac[]
QED

Theorem const_subst_context_stmts_frame[local]:
  const_subst_context roots cx env E mods art /\
  IS_SOME (type_stmts env ret ss) /\ const_cells_agree roots st /\
  eval_stmts cx ss st = (res,st') ==>
  const_cells_agree roots st'
Proof
  strip_tac >> irule checked_eval_stmts_const_cells_agree >>
  metis_tac[const_subst_context_frames]
QED

Theorem const_subst_context_tuple_frame[local]:
  const_subst_context roots cx env E mods art /\
  writable_atarget env g /\ const_cells_agree roots st /\
  assign_tuple_targets cx g v st = (res,st') ==>
  const_cells_agree roots st'
Proof
  strip_tac >> irule protected_cell_frame_cells_agree >>
  qexists `st` >> simp[] >> rpt strip_tac >>
  drule_all const_subst_context_frames >> strip_tac >>
  drule_all checked_assign_tuple_targets_protected_cell_frame >>
  simp[state_rel_frame_result] >> metis_tac[]
QED

(* ===== Composition helpers ===== *)

Theorem const_subst_expr_or_place_then[local]:
  const_subst_context roots cx env E mods art /\
  (well_typed_expr env e \/ IS_SOME (type_place_expr env e)) /\
  const_cells_agree roots st /\
  (!p q s. const_results_related roots cx (expr_type e) p q /\
     const_cells_agree roots s ==>
     const_computations_related Rel (k p) (l q) s) ==>
  const_computations_related Rel (bind (eval_expr cx e) k)
    (bind (eval_expr cx (subst_consts_expr E e)) l) st
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  irule const_computations_related_bind >>
  qexists `const_results_related roots cx (expr_type e)` >>
  `const_subst_expr_ok roots cx env E e` by
    metis_tac[cj 1 const_subst_structural] >>
  reverse conj_tac >- gvs[const_subst_expr_ok_def] >>
  rpt strip_tac >> drule_all const_subst_context_expr_frame >> strip_tac >>
  qpat_x_assum `!p q s. _` (qspecl_then [`x`,`y`,`s`] mp_tac) >> simp[]
QED

(* irule cannot use the disjunctive premise above *)
Theorem const_subst_expr_then[local]:
  const_subst_context roots cx env E mods art /\ well_typed_expr env e /\
  const_cells_agree roots st /\
  (!p q s. const_results_related roots cx (expr_type e) p q /\
     const_cells_agree roots s ==>
     const_computations_related Rel (k p) (l q) s) ==>
  const_computations_related Rel (bind (eval_expr cx e) k)
    (bind (eval_expr cx (subst_consts_expr E e)) l) st
Proof
  strip_tac >> drule const_subst_expr_or_place_then >>
  disch_then (qspecl_then [`st`,`l`,`k`,`e`,`Rel`] mp_tac) >>
  impl_tac >- gvs[] >> simp[]
QED

Theorem const_subst_read_then[local]:
  const_results_related roots cx ty p q /\ const_cells_agree roots s /\
  (!v. const_computations_related Rel (k v) (l v) s) ==>
  const_computations_related Rel (bind (read_result cx p) k)
    (bind (read_result cx q) l) s
Proof
  strip_tac >> match_mp_tac const_computations_related_prefix >>
  conj_tac >- (irule const_computations_related_read >> metis_tac[]) >>
  rpt strip_tac >> drule read_result_state >> strip_tac >> gvs[]
QED

Theorem const_subst_exprs_eq[local]:
  const_subst_context roots cx env E mods art /\ well_typed_exprs env es /\
  const_cells_agree roots st ==>
  eval_exprs cx es st = eval_exprs cx (subst_consts_exprs E es) st
Proof
  strip_tac >>
  `const_subst_exprs_ok roots cx env E es` by
    (irule const_subst_exprs_from_elements >>
     metis_tac[cj 3 const_subst_structural]) >>
  gvs[const_subst_exprs_ok_def]
QED

Theorem const_subst_target_place_eq[local]:
  const_subst_context roots cx env E mods art /\
  IS_SOME (type_place_target env bt) /\ const_cells_agree roots st ==>
  eval_target_place cx bt st =
  eval_target_place cx (subst_consts_btarget E bt) st
Proof
  strip_tac >>
  `const_subst_btarget_ok roots cx env E bt` by
    metis_tac[cj 2 const_subst_structural] >>
  gvs[const_subst_btarget_ok_def]
QED

Theorem const_results_related_hashmap_ref[local]:
  const_results_related roots cx ty p q ==>
  is_HashMapRef p = is_HashMapRef q
Proof
  rw[const_results_related_def, const_result_at_def] >> gvs[]
QED

Theorem const_results_related_array_iterator[local]:
  const_results_related roots cx ty p q /\ const_cells_agree roots s ==>
  array_iterator_results cx t p s = array_iterator_results cx t q s
Proof
  `!r. (?v. r = Value v) \/ (?src id path. r = PlaceR (ImmutablePlace src id path)) ==>
     array_iterator_results cx t r =
     bind (read_result cx r) (\v. do
       arr_tv <- lift_option_type (evaluate_type (get_tenv cx) t) "For array type";
       vs <- lift_option_type (extract_elements arr_tv v) "For not ArrayV";
       return (MAP Value vs) od)` by
    (rw[] >> simp[array_iterator_results_def]) >>
  rw[const_results_related_def] >> simp[] >>
  `read_result cx p s = read_result cx q s` by
    (irule const_results_related_read >> simp[const_results_related_def] >>
     metis_tac[]) >>
  gvs[const_result_at_def] >> simp[bind_def]
QED

Theorem const_subst_finally_eq[local]:
  m s = m' s ==> finally m g s = finally m' g s
Proof
  simp[finally_def]
QED

(* ===== Custom errors and assertion reasons ===== *)

Theorem order_custom_error_kwargs_subst[local]:
  !params kw.
    order_custom_error_kwargs params (subst_consts_fields E kw) =
    OPTION_MAP (subst_consts_exprs E) (order_custom_error_kwargs params kw)
Proof
  Induct_on `kw`
  >- (Cases >> simp[order_custom_error_kwargs_def, subst_consts_expr_def]) >>
  rpt gen_tac >> PairCases_on `h` >>
  Cases_on `params` >- simp[order_custom_error_kwargs_def, subst_consts_expr_def] >>
  rename1 `order_custom_error_kwargs (p::ps)` >> PairCases_on `p` >>
  rw[order_custom_error_kwargs_def, subst_consts_expr_def] >>
  gvs[optionTheory.OPTION_MAP_COMPOSE, combinTheory.o_DEF, subst_consts_expr_def]
QED

Theorem order_custom_error_args_subst[local]:
  order_custom_error_args params
    (CustomError id (subst_consts_exprs E pos) (subst_consts_fields E kw)) =
  OPTION_MAP (subst_consts_exprs E)
    (order_custom_error_args params (CustomError id pos kw))
Proof
  `NULL (subst_consts_fields E kw) = NULL kw` by
    (Cases_on `kw` >> TRY (PairCases_on `h`) >> simp[subst_consts_expr_def]) >>
  simp[order_custom_error_args_def, order_custom_error_kwargs_subst,
       subst_consts_exprs_map] >>
  rw[subst_consts_exprs_map]
QED

Theorem const_subst_raise[local]:
  const_subst_context roots cx env E mods art /\
  IS_SOME (type_stmt env ret (Raise r)) /\ const_cells_agree roots st ==>
  const_computations_related $= (eval_stmt cx (Raise r))
    (eval_stmt cx (Raise (subst_consts_rreason E r))) st
Proof
  strip_tac >> Cases_on `r` >>
  simp[subst_consts_rreason_def]
  >~ [`RaiseReason e`]
  >- (simp[evaluate_def] >> drule_then irule const_subst_expr_then >>
      gvs[type_stmt_def, AllCaseEqs()] >>
      rpt strip_tac >> drule_then (drule_then irule) const_subst_read_then >>
      simp[const_computations_related_eq])
  >~ [`RaiseCustomError err`]
  >- (Cases_on `err` >> rename1 `CustomError ns pos kw` >>
      simp[subst_consts_error_def, evaluate_def, order_custom_error_args_subst] >>
      rpt (CASE_TAC >> simp[const_computations_related_refl]) >>
      match_mp_tac const_computations_related_prefix >> conj_tac
      >- (simp[const_computations_related_eq] >>
          irule const_subst_exprs_eq >> simp[] >>
          qexistsl [`art`,`env`,`mods`,`roots`] >> asm_rewrite_tac[] >>
          gvs[type_stmt_def, AllCaseEqs()] >>
          drule_all frame_ordered_custom_error_typing >> simp[]) >>
      rpt strip_tac >> simp[const_computations_related_refl]) >>
  simp[const_computations_related_refl]
QED

Theorem eval_stmt_assert_raise[local]:
  eval_stmt cx (Assert e AssertBare) =
    bind (eval_expr cx e) (\tv. switch_BoolV cx tv (return ())
      (eval_stmt cx (Raise RaiseBare))) /\
  eval_stmt cx (Assert e AssertUnreachable) =
    bind (eval_expr cx e) (\tv. switch_BoolV cx tv (return ())
      (eval_stmt cx (Raise RaiseUnreachable))) /\
  eval_stmt cx (Assert e (AssertReason se)) =
    bind (eval_expr cx e) (\tv. switch_BoolV cx tv (return ())
      (eval_stmt cx (Raise (RaiseReason se)))) /\
  eval_stmt cx (Assert e (AssertCustomError err)) =
    bind (eval_expr cx e) (\tv. switch_BoolV cx tv (return ())
      (eval_stmt cx (Raise (RaiseCustomError err))))
Proof
  simp[evaluate_def]
QED

Theorem const_subst_assert[local]:
  const_subst_context roots cx env E mods art /\
  IS_SOME (type_stmt env ret (Assert e r)) /\ const_cells_agree roots st ==>
  const_computations_related $= (eval_stmt cx (Assert e r))
    (eval_stmt cx (subst_consts_stmt E (Assert e r))) st
Proof
  strip_tac >>
  `well_typed_expr env e` by (Cases_on `r` >> gvs[type_stmt_def, AllCaseEqs()]) >>
  `?r'. IS_SOME (type_stmt env ret (Raise r')) /\
     subst_consts_rreason E r' = (case subst_consts_areason E r of
       AssertBare => RaiseBare | AssertUnreachable => RaiseUnreachable
     | AssertReason x => RaiseReason x | AssertCustomError x => RaiseCustomError x) /\
     !cx. eval_stmt cx (Assert e r) =
       bind (eval_expr cx e) (\tv. switch_BoolV cx tv (return ())
         (eval_stmt cx (Raise r')))` by
    (Cases_on `r` >> gvs[type_stmt_def, AllCaseEqs(), eval_stmt_assert_raise,
       subst_consts_areason_def, subst_consts_rreason_def]
     >- (qexists `RaiseBare` >> simp[type_stmt_def, subst_consts_rreason_def])
     >- (qexists `RaiseUnreachable` >> simp[type_stmt_def, subst_consts_rreason_def])
     >- (qexists `RaiseReason e'` >> simp[type_stmt_def, subst_consts_rreason_def])
     >> qexists `RaiseCustomError c` >> simp[type_stmt_def, subst_consts_rreason_def]) >>
  `?r''. subst_consts_rreason E r' = r'' /\
     eval_stmt cx (subst_consts_stmt E (Assert e r)) =
       bind (eval_expr cx (subst_consts_expr E e)) (\tv. switch_BoolV cx tv
         (return ()) (eval_stmt cx (Raise r'')))` by
    (Cases_on `r` >> gvs[subst_consts_stmt_def, subst_consts_areason_def,
       eval_stmt_assert_raise]) >>
  gvs[] >> drule_then irule const_subst_expr_then >>
  gvs[type_stmt_def, AllCaseEqs()] >> rpt strip_tac >>
  `const_computations_related $= (eval_stmt cx (Raise r'))
     (eval_stmt cx (Raise (subst_consts_rreason E r'))) s` by
    (irule const_subst_raise >> metis_tac[]) >>
  gvs[] >> irule const_computations_related_switch >>
  simp[const_computations_related_refl] >> metis_tac[]
QED

(* ===== Tuple assignment ===== *)

Theorem const_subst_assign_tuple:
  (!E g roots cx env mods art v st.
     const_subst_context roots cx env E mods art /\ writable_atarget env g /\
     const_cells_agree roots st ==>
     assign_tuple_targets cx (subst_consts_target E g) v st =
     assign_tuple_targets cx g v st) /\
  (!E gs roots cx env mods art vs st.
     const_subst_context roots cx env E mods art /\
     EVERY (writable_atarget env) gs /\ const_cells_agree roots st ==>
     assign_tuple_target_list cx (subst_consts_targets E gs) vs st =
     assign_tuple_target_list cx gs vs st)
Proof
  ho_match_mp_tac subst_consts_target_ind >>
  rpt conj_tac >> rpt gen_tac >> rpt strip_tac
  >- (simp[subst_consts_target_def, evaluate_def, bind_def] >>
      drule_all writable_atarget_base >> strip_tac >>
      drule_all const_subst_target_place_eq >> simp[evaluate_def, bind_def])
  >- (simp[subst_consts_target_def, evaluate_def] >>
      CASE_TAC >> simp[] >> CASE_TAC >> simp[] >>
      first_x_assum irule >> metis_tac[writable_atarget_tuple])
  >- (Cases_on `vs` >> simp[subst_consts_target_def, evaluate_def])
  >> Cases_on `vs` >> simp[subst_consts_target_def, evaluate_def] >>
  gvs[] >> simp[ignore_bind_def, bind_def] >>
  first_x_assum drule_all >> disch_then (qspecl_then [`h`,`st`] assume_tac) >>
  gvs[] >> Cases_on `assign_tuple_targets cx g h st` >> Cases_on `q` >> simp[] >>
  first_x_assum irule >> simp[] >> goal_assum (drule_at Any) >>
  metis_tac[const_subst_context_tuple_frame]
QED

(* ===== Iterators and loops ===== *)

Theorem const_subst_eval_iterator:
  const_subst_context roots cx env E mods art /\
  well_typed_iterator env ty it /\ const_cells_agree roots st ==>
  eval_iterator cx (subst_consts_iter E it) st = eval_iterator cx it st
Proof
  strip_tac >> once_rewrite_tac[EQ_SYM_EQ] >>
  rewrite_tac[GSYM const_computations_related_eq] >>
  Cases_on `it` >> gvs[subst_consts_iter_def, well_typed_iterator_def] >>
  simp[evaluate_def]
  >- (`expr_type (subst_consts_expr E e) = expr_type e` by
        metis_tac[const_subst_typed_annotation] >>
      simp[] >> drule_then irule const_subst_expr_then >> simp[] >>
      rpt strip_tac >> simp[const_computations_related_eq] >>
      metis_tac[const_results_related_array_iterator]) >>
  drule_then irule const_subst_expr_then >> simp[] >>
  rpt strip_tac >> drule_then (drule_then irule) const_subst_read_then >>
  simp[] >> gen_tac >> drule_then irule const_subst_expr_then >>
  simp[] >> rpt strip_tac >>
  drule_then (drule_then irule) const_subst_read_then >>
  simp[const_computations_related_refl]
QED

Theorem const_subst_eval_for[local]:
  !vs s.
    (!s. const_cells_agree roots s ==>
       eval_stmts cx body' s = eval_stmts cx body s) /\
    (!s res s'. const_cells_agree roots s /\ eval_stmts cx body s = (res,s') ==>
       const_cells_agree roots s') /\
    const_cells_agree roots s ==>
    eval_for cx tyv nm body' vs s = eval_for cx tyv nm body vs s
Proof
  Induct >- simp[evaluate_def] >>
  rpt strip_tac >>
  simp[evaluate_def, bind_def] >>
  Cases_on `read_result cx h s` >> drule read_result_state >> strip_tac >>
  gvs[] >> Cases_on `q` >> simp[] >>
  simp[push_scope_with_var_def, return_def] >>
  qmatch_goalsub_abbrev_tac `eval_stmts cx body' s2` >>
  `const_cells_agree roots s2` by gvs[Abbr `s2`, const_cells_agree_def] >>
  `eval_stmts cx body' s2 = eval_stmts cx body s2` by metis_tac[] >>
  simp[finally_def, try_def, ignore_bind_def, bind_def] >>
  Cases_on `eval_stmts cx body s2` >>
  `const_cells_agree roots r` by metis_tac[] >>
  Cases_on `q` >> simp[return_def]
  >- (simp[pop_scope_def] >> CASE_TAC >> simp[return_def, raise_def] >>
      first_x_assum irule >> simp[const_cells_agree_def] >>
      gvs[const_cells_agree_def]) >>
  simp[handle_loop_exception_def] >>
  rw[return_def, raise_def, pop_scope_def] >>
  CASE_TAC >> simp[return_def, raise_def] >>
  first_x_assum irule >> gvs[const_cells_agree_def]
QED

(* ===== Statements ===== *)

Theorem const_subst_stmt_related[local]:
  (!E s roots cx env mods art ret st.
     const_subst_context roots cx env E mods art /\
     IS_SOME (type_stmt env ret s) /\ const_cells_agree roots st ==>
     const_computations_related $= (eval_stmt cx s)
       (eval_stmt cx (subst_consts_stmt E s)) st) /\
  (!E ss roots cx env mods art ret st.
     const_subst_context roots cx env E mods art /\
     IS_SOME (type_stmts env ret ss) /\ const_cells_agree roots st ==>
     const_computations_related $= (eval_stmts cx ss)
       (eval_stmts cx (subst_consts_stmts E ss)) st)
Proof
  ho_match_mp_tac subst_consts_stmt_ind >>
  rpt conj_tac >> rpt gen_tac >> rpt strip_tac
  >~ [`Assert e r`] >- metis_tac[const_subst_assert]
  >~ [`Raise r`] >- (simp[subst_consts_stmt_def] >> metis_tac[const_subst_raise])
  >~ [`Expr e`]
  >- (simp[subst_consts_stmt_def, evaluate_def] >>
      drule_then irule const_subst_expr_then >>
      gvs[type_stmt_def, AllCaseEqs()] >> rpt strip_tac >>
      drule const_results_related_hashmap_ref >>
      simp[const_computations_related_refl])
  >~ [`Return opt`]
  >- (Cases_on `opt` >>
      simp[subst_consts_stmt_def, subst_consts_expr_def, evaluate_def,
           const_computations_related_refl] >>
      drule_then irule const_subst_expr_then >>
      gvs[type_stmt_def, AllCaseEqs()] >> rpt strip_tac >>
      drule_then (drule_then irule) const_subst_read_then >>
      simp[const_computations_related_refl])
  >~ [`Log ns es`]
  >- (simp[subst_consts_stmt_def, evaluate_def] >>
      match_mp_tac const_computations_related_prefix >>
      simp[const_computations_related_refl, const_computations_related_eq] >>
      drule_then irule const_subst_exprs_eq >>
      gvs[type_stmt_def, AllCaseEqs()])
  >~ [`AnnAssign nm ty e`]
  >- (simp[subst_consts_stmt_def, evaluate_def] >>
      match_mp_tac const_computations_related_prefix >>
      simp[const_computations_related_refl] >> rpt strip_tac >>
      `s = st` by gvs[lift_option_type_def, AllCaseEqs(), return_def] >>
      gvs[] >> drule_then irule const_subst_expr_then >>
      gvs[type_stmt_def, AllCaseEqs()] >> rpt strip_tac >>
      drule_then (drule_then irule) const_subst_read_then >>
      simp[const_computations_related_refl])
  >~ [`Append bt e`]
  >- (simp[subst_consts_stmt_def, evaluate_def] >>
      drule_all typed_append_target >> strip_tac >>
      match_mp_tac const_computations_related_prefix >> conj_tac
      >- (simp[const_computations_related_eq] >>
          metis_tac[const_subst_target_place_eq]) >>
      rpt strip_tac >>
      `const_cells_agree roots s` by
        metis_tac[const_subst_context_target_frame] >>
      drule_then irule const_subst_expr_then >>
      gvs[type_stmt_def, AllCaseEqs()] >> rpt strip_tac >>
      drule_then (drule_then irule) const_subst_read_then >>
      simp[const_computations_related_refl])
  >~ [`AugAssign ty bt bop e`]
  >- (simp[subst_consts_stmt_def, evaluate_def] >>
      drule_all typed_augassign_target >> strip_tac >>
      match_mp_tac const_computations_related_prefix >> conj_tac
      >- (simp[const_computations_related_eq] >>
          metis_tac[const_subst_target_place_eq]) >>
      rpt strip_tac >>
      `const_cells_agree roots s` by
        metis_tac[const_subst_context_target_frame] >>
      match_mp_tac const_computations_related_prefix >>
      simp[const_computations_related_refl] >> rpt strip_tac >>
      drule read_place_state >> strip_tac >> gvs[] >>
      match_mp_tac const_computations_related_prefix >>
      simp[const_computations_related_refl] >> rpt strip_tac >>
      drule place_type_value_state >> strip_tac >> gvs[] >>
      drule_then irule const_subst_expr_then >>
      gvs[type_stmt_def, AllCaseEqs()] >> rpt strip_tac >>
      drule_then (drule_then irule) const_subst_read_then >>
      simp[const_computations_related_refl])
  >~ [`Assign tgt e`]
  >- (drule_all typed_assign_target >> strip_tac >>
      `well_typed_expr env e` by gvs[type_stmt_def, AllCaseEqs()] >>
      Cases_on `tgt` >>
      simp[subst_consts_stmt_def, subst_consts_target_def, evaluate_def] >>
      drule_then irule const_subst_expr_then >> simp[] >>
      rpt strip_tac >>
      drule_then (drule_then irule) const_subst_read_then >> simp[] >> gen_tac
      >- (match_mp_tac const_computations_related_prefix >>
          simp[const_computations_related_refl, const_computations_related_eq] >>
          drule typed_base_atarget >> strip_tac >>
          metis_tac[const_subst_target_place_eq]) >>
      simp[const_computations_related_eq] >>
      `writable_atarget env (TupleTarget l)` by
        metis_tac[writable_atarget_def] >>
      `assign_tuple_targets cx (subst_consts_target E (TupleTarget l)) v s =
       assign_tuple_targets cx (TupleTarget l) v s` by
        metis_tac[cj 1 const_subst_assign_tuple] >>
      gvs[subst_consts_target_def])
  >~ [`If e ss1 ss2`]
  >- (simp[subst_consts_stmt_def, evaluate_def] >>
      drule_then irule const_subst_expr_then >>
      gvs[type_stmt_def, AllCaseEqs()] >> rpt strip_tac >>
      simp[const_computations_related_eq, bind_def, ignore_bind_def,
           push_scope_def, return_def] >>
      irule const_subst_finally_eq >>
      qmatch_goalsub_abbrev_tac `switch_BoolV cx p _ _ s2` >>
      `const_cells_agree roots s2` by gvs[Abbr `s2`, const_cells_agree_def] >>
      rewrite_tac[GSYM const_computations_related_eq] >>
      irule const_computations_related_switch >> simp[] >> metis_tac[])
  >~ [`For nm ty it n body`]
  >- (simp[subst_consts_stmt_def, evaluate_def] >>
      `well_typed_iterator env ty it /\
       IS_SOME (type_stmts (extend_local env nm ty F) ret body)` by
        gvs[type_stmt_def, AllCaseEqs()] >>
      match_mp_tac const_computations_related_prefix >>
      simp[const_computations_related_refl] >> rpt strip_tac >>
      `s = st` by gvs[lift_option_type_def, AllCaseEqs(), return_def] >>
      gvs[] >>
      match_mp_tac const_computations_related_prefix >> conj_tac
      >- (simp[const_computations_related_eq] >>
          metis_tac[const_subst_eval_iterator]) >>
      rpt strip_tac >>
      `const_cells_agree roots s` by
        metis_tac[const_subst_context_iterator_frame] >>
      simp[const_computations_related_eq, ignore_bind_def, bind_def,
           check_def, assert_def] >>
      rw[return_def, raise_def] >>
      `const_subst_context roots cx (extend_local env nm ty F) E mods art` by
        metis_tac[const_subst_context_extend_local] >>
      CONV_TAC SYM_CONV >> irule const_subst_eval_for >> simp[] >>
      conj_tac >- metis_tac[const_subst_context_stmts_frame] >>
      rpt strip_tac >> first_x_assum drule_all >>
      simp[const_computations_related_eq])
  >~ [`eval_stmts cx []`]
  >- simp[subst_consts_stmt_def, const_computations_related_refl]
  >~ [`eval_stmts cx (s::ss)`]
  >- (simp[subst_consts_stmt_def, evaluate_def] >>
      gvs[type_stmt_def, AllCaseEqs()] >> simp[ignore_bind_def] >>
      match_mp_tac const_computations_related_prefix >> conj_tac
      >- (first_x_assum irule >> simp[] >> metis_tac[]) >>
      rpt strip_tac >> first_x_assum irule >> simp[] >>
      qexistsl [`art`,`env'`,`mods`,`ret`] >>
      metis_tac[const_subst_context_type_stmt, const_subst_context_stmt_frame,
                optionTheory.IS_SOME_DEF]) >>
  simp[subst_consts_stmt_def, const_computations_related_refl]
QED

Theorem const_subst_eval_stmt:
  const_subst_context roots cx env E mods art /\
  IS_SOME (type_stmt env ret s) /\ const_cells_agree roots st ==>
  eval_stmt cx (subst_consts_stmt E s) st = eval_stmt cx s st
Proof
  strip_tac >> drule_all (cj 1 const_subst_stmt_related) >>
  simp[const_computations_related_eq]
QED

Theorem const_subst_eval_stmts:
  const_subst_context roots cx env E mods art /\
  IS_SOME (type_stmts env ret ss) /\ const_cells_agree roots st ==>
  eval_stmts cx (subst_consts_stmts E ss) st = eval_stmts cx ss st
Proof
  strip_tac >> drule_all (cj 2 const_subst_stmt_related) >>
  simp[const_computations_related_eq]
QED

Theorem const_subst_eval_exprs:
  const_subst_context roots cx env E mods art /\ well_typed_exprs env es /\
  const_cells_agree roots st ==>
  eval_exprs cx (subst_consts_exprs E es) st = eval_exprs cx es st
Proof
  metis_tac[const_subst_exprs_eq]
QED

Theorem const_subst_external_defaults:
  const_subst_context roots cx env E mods art /\ well_typed_exprs env es /\
  const_cells_agree roots st ==>
  eval_external_defaults cx (subst_consts_exprs E es) st =
  eval_external_defaults cx es st
Proof
  strip_tac >> simp[eval_external_defaults_run] >>
  `const_cells_agree roots (st with scopes := [FEMPTY])` by
    simp[const_cells_agree_scopes] >>
  drule_all const_subst_eval_exprs >> simp[]
QED

(* ===== Internal calls: the callee frame ===== *)

Theorem stk_state_funs[local]:
  get_storage_backend (cx with stk := s) = get_storage_backend cx /\
  get_immutables (cx with stk := s) = get_immutables cx /\
  read_storage_slot (cx with stk := s) = read_storage_slot cx
Proof
  simp[FUN_EQ_THM, get_storage_backend_stk, get_immutables_stk,
       read_storage_slot_stk]
QED

Theorem resolve_array_element_stk[local]:
  !cx tr slot tv subs.
    resolve_array_element (cx with stk := s) tr slot tv subs =
    resolve_array_element cx tr slot tv subs
Proof
  ho_match_mp_tac resolve_array_element_ind >>
  rw[resolve_array_element_def, stk_state_funs]
QED

Theorem resolve_array_element_stk_fun[local]:
  resolve_array_element (cx with stk := s) = resolve_array_element cx
Proof
  simp[FUN_EQ_THM, resolve_array_element_stk]
QED

Theorem read_result_stk[local]:
  read_result (cx with stk := s) = read_result cx
Proof
  simp[FUN_EQ_THM, oneline read_result_def, oneline read_place_def,
       stk_state_funs]
QED

Theorem select_result_stk[local]:
  select_result (cx with stk := s) = select_result cx
Proof
  simp[FUN_EQ_THM, oneline select_result_def, oneline extend_place_def,
       oneline extend_storage_place_def, oneline place_type_value_def,
       oneline read_place_def, get_tenv_stk, stk_state_funs,
       resolve_array_element_stk_fun]
QED

Theorem result_array_length_stk[local]:
  result_array_length (cx with stk := s) = result_array_length cx
Proof
  simp[FUN_EQ_THM, oneline result_array_length_def, stk_state_funs,
       read_result_stk]
QED

Theorem evaluate_builtin_stk[local]:
  evaluate_builtin (cx with stk := s) = evaluate_builtin cx
Proof
  simp[FUN_EQ_THM, evaluate_builtin_def, get_tenv_stk]
QED

Theorem evaluate_type_builtin_stk[local]:
  evaluate_type_builtin (cx with stk := s) = evaluate_type_builtin cx
Proof
  simp[FUN_EQ_THM, oneline evaluate_type_builtin_def, get_tenv_stk]
QED

Theorem eval_exprs_stk_from_elements[local]:
  !es. (!e. MEM e es ==> !st. eval_expr (cx with stk := s) e st = eval_expr cx e st) ==>
  !st. eval_exprs (cx with stk := s) es st = eval_exprs cx es st
Proof
  Induct >> simp[evaluate_def] >> rpt strip_tac >>
  simp[bind_def, read_result_stk] >>
  Cases_on `eval_expr cx h st` >> Cases_on `q` >> simp[] >>
  Cases_on `read_result cx x r` >> Cases_on `q` >> simp[]
QED

Theorem constant_expr_eval_stk:
  !mods e. constant_expr mods e ==>
    !st. eval_expr (cx with stk := s) e st = eval_expr cx e st
Proof
  ho_match_mp_tac constant_expr_ind >>
  rw[constant_expr_def] >> simp[evaluate_def]
  >~ [`TopLevelName`] >- (PairCases_on `v1` >> simp[evaluate_def, lookup_global_stk])
  >~ [`StructLit`]
  >- (PairCases_on `v4` >> simp[evaluate_def, bind_def] >>
      `!st. eval_exprs (cx with stk := s) (MAP SND kes) st =
            eval_exprs cx (MAP SND kes) st` by
        (irule eval_exprs_stk_from_elements >> gvs[EVERY_MEM]) >>
      simp[])
  >~ [`Subscript`]
  >- (simp[bind_def, read_result_stk, select_result_stk])
  >~ [`Attribute`]
  >- (simp[bind_def, select_result_stk])
  >~ [`Builtin`]
  >- (`!st. eval_exprs (cx with stk := s) es st = eval_exprs cx es st` by
        (irule eval_exprs_stk_from_elements >> gvs[EVERY_MEM]) >>
      simp[bind_def, ignore_bind_def, get_tenv_stk, evaluate_builtin_stk,
           result_array_length_stk] >>
      rw[] >> gvs[constant_builtin_def])
  >~ [`TypeBuiltin`]
  >- (`!st. eval_exprs (cx with stk := s) es st = eval_exprs cx es st` by
        (irule eval_exprs_stk_from_elements >> gvs[EVERY_MEM]) >>
      simp[bind_def, ignore_bind_def, evaluate_type_builtin_stk])
QED

Theorem const_results_related_stk[local]:
  const_results_related roots (cx with stk := s) = const_results_related roots cx
Proof
  simp[FUN_EQ_THM, const_results_related_def, const_result_at_def, get_tenv_stk]
QED

Theorem const_subst_context_stk:
  const_subst_context roots cx env E mods art /\
  (!id r. ALOOKUP E id = SOME r ==> constant_expr mods r) ==>
  const_subst_context roots (cx with stk := s) env E mods art
Proof
  simp[const_subst_context_def, get_tenv_stk, const_results_related_stk,
       lookup_global_stk] >>
  rpt strip_tac >> res_tac >> simp[] >>
  qexists `pv` >> simp[] >> rpt strip_tac >>
  drule constant_expr_eval_stk >> simp[]
QED

Theorem const_subst_context_function_entry:
  const_subst_context roots cx env E mods art /\
  check_contract F cx.layouts cx.txn.target mods = SOME art /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\ frame_maps env art ==>
  const_subst_context roots cx (function_entry_env art mods src Internal args)
    E mods art
Proof
  strip_tac >> gvs[const_subst_context_def, frame_maps_def] >>
  `(function_entry_env art mods src Internal args).toplevel_vtypes =
     art.cta_toplevel_vtypes /\
   (function_entry_env art mods src Internal args).type_defs =
     type_env_all_modules mods` by
    simp[function_entry_env_def, artifact_env_def,
         vyperTypeContractContextTheory.FOLDL_extend_local_args_static] >>
  simp[function_entry_constant_maps] >> rpt conj_tac
  >- (drule get_tenv_sources >> simp[])
  >- (rpt strip_tac >> irule checked_frame_context_transport >>
      simp[frame_maps_def, function_entry_constant_maps] >> metis_tac[])
  >> rpt strip_tac >> res_tac >> gvs[] >>
  drule check_contract_bare_globals_consistent_checked >>
  disch_then (qspec_then `cx.sources` mp_tac) >>
  disch_then (qspec_then `cx.txn` mp_tac) >> simp[] >>
  disch_then drule >> strip_tac >> simp[]
QED

Theorem const_subst_intcall_body:
  const_subst_context roots cx env E mods art /\
  (!id r. ALOOKUP E id = SOME r ==> constant_expr mods r) /\
  check_contract F cx.layouts cx.txn.target mods = SOME art /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\ frame_maps env art /\
  well_typed_expr env (Call ty (IntCall (NONE,fn)) es drv) /\
  get_module_code cx NONE = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,ss) /\
  const_cells_agree roots st ==>
  eval_stmts (cx with stk updated_by CONS (NONE,fn)) (subst_consts_stmts E ss) st =
  eval_stmts (cx with stk updated_by CONS (NONE,fn)) ss st
Proof
  strip_tac >>
  `IS_SOME (type_stmts (function_entry_env art mods NONE Internal args) ret ss)` by
    (drule_then irule (cj 1 checked_typed_intcall_body) >>
     gvs[frame_maps_def] >> metis_tac[]) >>
  `cx with stk updated_by CONS (NONE,fn) = cx with stk := (NONE,fn)::cx.stk` by
    simp[theorem "evaluation_context_component_equality"] >>
  pop_assum SUBST1_TAC >>
  irule const_subst_eval_stmts >> goal_assum (drule_at Any) >>
  simp[] >> irule const_subst_context_stk >> simp[] >>
  irule const_subst_context_function_entry >> metis_tac[]
QED

Theorem module_consts_env_constant_expr:
  check_contract mode layouts addr mods = SOME art /\
  ALOOKUP mods NONE = SOME tops /\
  constants_fold_module mods imms NONE tops FEMPTY = SOME A /\
  ALOOKUP (module_consts_env tops []) id = SOME r ==>
  constant_expr mods r
Proof
  strip_tac >> drule_all checked_module_consts_env_agrees >>
  simp[const_acc_agrees_def] >> metis_tac[]
QED

Theorem module_consts_intcall_body:
  const_subst_context roots cx env (module_consts_env tops []) mods art /\
  check_contract F cx.layouts cx.txn.target mods = SOME art /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  ALOOKUP mods NONE = SOME tops /\
  constants_fold_module mods imms NONE tops FEMPTY = SOME A /\
  frame_maps env art /\
  well_typed_expr env (Call ty (IntCall (NONE,fn)) es drv) /\
  get_module_code cx NONE = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,ss) /\
  const_cells_agree roots st ==>
  eval_stmts (cx with stk updated_by CONS (NONE,fn))
    (subst_consts_stmts (module_consts_env tops []) ss) st =
  eval_stmts (cx with stk updated_by CONS (NONE,fn)) ss st
Proof
  strip_tac >> irule const_subst_intcall_body >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[module_consts_env_constant_expr]
QED
