Theory linkedReplayElements
Ancestors
  constSubstCorrect constSubstMods vyperTypeSystem vyperInterpreter
  vyperState vyperAST alist finite_map list pair

Theorem linked_replay_typed_annotation:
  (!src id r. ALOOKUP E (src,id) = SOME r ==>
    FLOOKUP env.bare_globals (src,id) = SOME (expr_type r) /\
    FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type (expr_type r))) ==>
  !e. well_typed_expr env e \/ IS_SOME (type_place_expr env e) ==>
    expr_type (subst_consts_expr_mods E e) = expr_type e
Proof
  strip_tac >> gen_tac >> Cases_on `e` >>
  simp[subst_consts_expr_mods_def, expr_type_def] >>
  rename1 `TopLevelName ty ns` >> Cases_on `ns` >>
  rename1 `TopLevelName ty (src,id)` >>
  simp[subst_consts_expr_mods_def, expr_type_def] >>
  Cases_on `ALOOKUP E (src,id)` >- simp[expr_type_def] >>
  simp[] >>
  first_x_assum drule >> strip_tac >>
  simp[well_typed_expr_def, vtype_annotation_ok_def] >>
  rpt strip_tac >> simp[]
QED

Theorem linked_replay_list_from_elements:
  const_subst_context roots cx env [] mods art ==>
  !xs. EVERY (\e. well_typed_expr env e \/ IS_SOME (type_place_expr env e) ==>
    !s. const_cells_agree roots s ==>
      const_computations_related (const_results_related roots cx (expr_type e))
        (eval_expr cx e) (eval_expr cx (subst_consts_expr_mods E e)) s /\
      (!kt vt. type_place_expr env e = SOME (HashMapT kt vt) ==>
        eval_expr cx e s = eval_expr cx (subst_consts_expr_mods E e) s)) xs ==>
    well_typed_exprs env xs ==>
    !s. const_cells_agree roots s ==>
      eval_exprs cx xs s = eval_exprs cx (subst_consts_exprs_mods E xs) s
Proof
  strip_tac >> Induct
  >- simp[subst_consts_expr_mods_def, evaluate_def] >>
  simp[well_typed_expr_def, EVERY_DEF] >>
  rpt strip_tac >>
  simp_tac bool_ss [subst_consts_expr_mods_def, Ntimes evaluate_def 2] >>
  rewrite_tac[GSYM const_computations_related_eq] >>
  irule const_computations_related_bind >>
  qexists `const_results_related roots cx (expr_type h)` >>
  reverse conj_tac >- gvs[] >>
  rpt strip_tac >>
  rename1 `eval_expr cx h st = (INL p,mid)` >>
  `const_cells_agree roots mid` by metis_tac[const_subst_context_expr_frame] >>
  BETA_TAC >> irule const_computations_related_prefix >>
  reverse conj_tac >- (irule const_computations_related_read >> metis_tac[]) >>
  rpt strip_tac >> drule read_result_state >> strip_tac >> gvs[] >>
  irule const_computations_related_prefix >>
  reverse conj_tac >- gvs[const_computations_related_eq] >>
  rpt strip_tac >> irule const_computations_related_refl >> simp[]
QED
