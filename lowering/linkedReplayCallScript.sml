Theory linkedReplayCall
Ancestors
  constSubstCorrect constSubstMods vyperTypeEvalProofs vyperInterpreter
  vyperTypeSystem vyperState vyperAST vyperCreate rich_list list pair

Theorem linked_replay_call_case:
  const_subst_context roots cx env [] mods art /\
  (!e. (well_typed_expr env e \/ IS_SOME (type_place_expr env e)) ==>
       expr_type (subst_consts_expr_mods E e) = expr_type e) /\
  (!xs. EVERY (\e. (well_typed_expr env e \/ IS_SOME (type_place_expr env e)) ==>
                    !s. const_cells_agree roots s ==>
                      const_computations_related (const_results_related roots cx (expr_type e))
                        (eval_expr cx e) (eval_expr cx (subst_consts_expr_mods E e)) s /\
                      (!kt vt. type_place_expr env e = SOME (HashMapT kt vt) ==>
                         eval_expr cx e s = eval_expr cx (subst_consts_expr_mods E e) s)) xs ==>
         well_typed_exprs env xs ==> !s. const_cells_agree roots s ==>
           eval_exprs cx xs s = eval_exprs cx (subst_consts_exprs_mods E xs) s) /\
  (!salt xs. blueprint_literal_offset cx salt (subst_consts_exprs_mods E xs) =
             blueprint_literal_offset cx salt xs) /\
  EVERY (\e. (well_typed_expr env e \/ IS_SOME (type_place_expr env e)) ==>
             !s. const_cells_agree roots s ==>
               const_computations_related (const_results_related roots cx (expr_type e))
                 (eval_expr cx e) (eval_expr cx (subst_consts_expr_mods E e)) s /\
               (!kt vt. type_place_expr env e = SOME (HashMapT kt vt) ==>
                  eval_expr cx e s = eval_expr cx (subst_consts_expr_mods E e) s)) es /\
  (case d of NONE => T | SOME e =>
     (well_typed_expr env e \/ IS_SOME (type_place_expr env e)) ==>
     !s. const_cells_agree roots s ==>
       const_computations_related (const_results_related roots cx (expr_type e))
         (eval_expr cx e) (eval_expr cx (subst_consts_expr_mods E e)) s /\
       (!kt vt. type_place_expr env e = SOME (HashMapT kt vt) ==>
          eval_expr cx e s = eval_expr cx (subst_consts_expr_mods E e) s)) ==>
  (well_typed_expr env (Call ty ct es d) \/ IS_SOME (type_place_expr env (Call ty ct es d))) ==>
  !s. const_cells_agree roots s ==>
    const_computations_related (const_results_related roots cx (expr_type (Call ty ct es d)))
      (eval_expr cx (Call ty ct es d))
      (eval_expr cx (subst_consts_expr_mods E (Call ty ct es d))) s /\
    (!kt vt. type_place_expr env (Call ty ct es d) = SOME (HashMapT kt vt) ==>
       eval_expr cx (Call ty ct es d) s = eval_expr cx (subst_consts_expr_mods E (Call ty ct es d)) s)
Proof
  strip_tac >> simp[frame_place_expr_other, expr_type_def] >> strip_tac >>
  `well_typed_exprs env es` by
    (Cases_on `ct` >> gvs[well_typed_expr_def] >~ [`IntCall p`] >-
       (PairCases_on `p` >> gvs[well_typed_expr_def]) >>
     rename1 `ExtCall _ _ sig _` >> PairCases_on `sig` >> gvs[well_typed_expr_def]) >>
  `!xs. subst_consts_exprs_mods E xs = MAP (subst_consts_expr_mods E) xs` by
    (Induct >> simp[subst_consts_expr_mods_def]) >>
  `!s. const_cells_agree roots s ==>
     eval_exprs cx es s = eval_exprs cx (subst_consts_exprs_mods E es) s` by
    (qpat_assum `!xs. EVERY _ xs ==> _` (qspec_then `es` mp_tac) >> simp[]) >>
  `!xs. LENGTH (subst_consts_exprs_mods E xs) = LENGTH xs` by simp[] >>
  qx_gen_tac `st` >> strip_tac >>
  (* The evaluator ignores the separate optional operand. For external calls,
     the default return value is evaluated in the keyword operand slice. *)
  Cases_on `ct`
  >~ [`IntCall p`] >- suspend "internal"
  >~ [`ExtCall _ _ _ _`] >- suspend "external"
  >~ [`CreateTarget _ _ _ _`] >- suspend "creation"
  >~ [`Send _`] >- suspend "send"
  >> simp_tac bool_ss [subst_consts_expr_mods_def, Ntimes evaluate_def 2]
  >> irule const_computations_related_prefix
  >> simp[const_computations_related_eq, const_results_related_def,
          const_computations_related_refl]
QED

Resume linked_replay_call_case[internal]:
  PairCases_on `p` >>
  simp_tac bool_ss [subst_consts_expr_mods_def, Ntimes evaluate_def 2] >>
  asm_rewrite_tac[ignore_bind_def] >>
  irule const_computations_related_prefix >> reverse conj_tac
  >- simp[const_computations_related_eq] >>
  rpt strip_tac >> BETA_TAC >>
  `s = st` by gvs[type_check_def, assert_def, return_def, raise_def, AllCaseEqs()] >>
  gvs[] >>
  irule const_computations_related_prefix >> reverse conj_tac
  >- simp[const_computations_related_eq] >>
  rpt strip_tac >> BETA_TAC >>
  Cases_on `get_module_code cx p0` >>
  gvs[lift_option_type_def, lift_option_def, return_def, raise_def] >>
  irule const_computations_related_prefix >> reverse conj_tac
  >- simp[const_computations_related_eq] >>
  rpt strip_tac >> BETA_TAC >>
  rename1 `lookup_callable_function cx.in_deploy p1 ts` >>
  Cases_on `lookup_callable_function cx.in_deploy p1 ts` >>
  gvs[lift_option_type_def, lift_option_def, return_def, raise_def] >>
  PairCases_on `x` >> simp[] >>
  irule const_computations_related_prefix >> reverse conj_tac
  >- simp[const_computations_related_eq] >>
  rpt strip_tac >> BETA_TAC >>
  qpat_x_assum `type_check _ "IntCall args length" _ = _` mp_tac >>
  simp[type_check_def, assert_def, return_def, raise_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  irule const_computations_related_prefix >>
  simp[const_computations_related_eq, const_results_related_def,
       const_computations_related_refl]
QED

Resume linked_replay_call_case[external]:
  rename1 `ExtCall _ _ sig _` >> PairCases_on `sig` >>
  `!xs s res t. well_typed_exprs env xs /\ const_cells_agree roots s /\
      eval_exprs cx xs s = (res,t) ==> const_cells_agree roots t` by
    (rpt strip_tac >> drule_all const_subst_context_exprs_frame >> simp[]) >>
  `well_typed_exprs env (TAKE 1 es) /\
   well_typed_exprs env (TAKE (LENGTH sig1) (DROP 1 es)) /\
   well_typed_exprs env (DROP (1 + LENGTH sig1) es)` by
    simp[frame_well_typed_exprs_slices] >>
  `!s. const_cells_agree roots s ==>
     eval_exprs cx (TAKE 1 es) s = eval_exprs cx (subst_consts_exprs_mods E (TAKE 1 es)) s` by
    (qpat_assum `!xs. EVERY _ xs ==> _` (qspec_then `TAKE 1 es` mp_tac) >> simp[EVERY_TAKE]) >>
  `!s. const_cells_agree roots s ==>
     eval_exprs cx (TAKE (LENGTH sig1) (DROP 1 es)) s =
     eval_exprs cx (subst_consts_exprs_mods E (TAKE (LENGTH sig1) (DROP 1 es))) s` by
    (qpat_assum `!xs. EVERY _ xs ==> _`
       (qspec_then `TAKE (LENGTH sig1) (DROP 1 es)` mp_tac) >> simp[EVERY_TAKE, EVERY_DROP]) >>
  `!s. const_cells_agree roots s ==>
     eval_exprs cx (DROP (1 + LENGTH sig1) es) s =
     eval_exprs cx (subst_consts_exprs_mods E (DROP (1 + LENGTH sig1) es)) s` by
    (qpat_assum `!xs. EVERY _ xs ==> _`
       (qspec_then `DROP (1 + LENGTH sig1) es` mp_tac) >> simp[EVERY_DROP]) >>
  simp_tac bool_ss [subst_consts_expr_mods_def, Ntimes evaluate_def 2,
                    LET_THM, FST, SND] >>
  asm_rewrite_tac[GSYM MAP_TAKE, GSYM MAP_DROP] >>
  irule const_computations_related_prefix >> reverse conj_tac
  >- simp[const_computations_related_eq] >>
  rpt strip_tac >> BETA_TAC >>
  `const_cells_agree roots s` by metis_tac[] >>
  irule const_computations_related_prefix >> reverse conj_tac
  >- simp[const_computations_related_eq] >>
  rpt strip_tac >> BETA_TAC >>
  qmatch_asmsub_rename_tac
    `eval_exprs cx (TAKE (LENGTH sig1) (DROP 1 es)) s = (INL vs,mid)` >>
  `const_cells_agree roots mid` by metis_tac[] >>
  irule const_computations_related_prefix >>
  simp[const_computations_related_eq, const_results_related_def,
       const_computations_related_refl]
QED

Resume linked_replay_call_case[creation]:
  qmatch_goalsub_rename_tac `CreateTarget kind salt rof ks` >>
  `well_typed_exprs env (create_operand_order kind salt es)` by
    simp[well_typed_exprs_create_operand_order] >>
  `!P. EVERY P es ==> EVERY P (create_operand_order kind salt es)` by
    (Cases_on `kind` >> Cases_on `es` >>
     simp[create_operand_order_def, EVERY_TAKE, EVERY_DROP] >>
     rename1 `create_operand_order RawCreate _ (operand :: rest)` >>
     Cases_on `rest` >> simp[create_operand_order_def, EVERY_TAKE, EVERY_DROP]) >>
  `!s. const_cells_agree roots s ==>
     eval_exprs cx (create_operand_order kind salt es) s =
     eval_exprs cx (subst_consts_exprs_mods E (create_operand_order kind salt es)) s` by
    (qpat_assum `!xs. EVERY _ xs ==> _`
       (qspec_then `create_operand_order kind salt es` mp_tac) >> simp[]) >>
  `create_operand_order kind salt (MAP (subst_consts_expr_mods E) es) =
   MAP (subst_consts_expr_mods E) (create_operand_order kind salt es)` by
    (Cases_on `kind` >> Cases_on `es` >> simp[create_operand_order_def, MAP_TAKE, MAP_DROP] >>
     rename1 `MAP _ (create_operand_order RawCreate _ (operand :: rest))` >>
     Cases_on `rest` >> simp[create_operand_order_def, MAP_TAKE, MAP_DROP]) >>
  `MAP expr_type (subst_consts_exprs_mods E es) = MAP expr_type es` by
    (qpat_x_assum `well_typed_exprs env es` mp_tac >>
     simp[frame_well_typed_exprs_every, EVERY_MEM, MAP_MAP_o] >> strip_tac >>
     irule MAP_CONG >> simp[]) >>
  simp_tac bool_ss [subst_consts_expr_mods_def, Ntimes evaluate_def 2] >>
  asm_rewrite_tac[] >>
  irule const_computations_related_prefix >>
  simp[const_computations_related_eq, const_results_related_def,
       const_computations_related_refl]
QED

Resume linked_replay_call_case[send]:
  simp_tac bool_ss [subst_consts_expr_mods_def, Ntimes evaluate_def 2] >>
  asm_rewrite_tac[ignore_bind_def] >>
  irule const_computations_related_prefix >> reverse conj_tac
  >- simp[const_computations_related_eq] >>
  rpt strip_tac >> BETA_TAC >>
  `s = st` by gvs[type_check_def, assert_def, return_def, raise_def, AllCaseEqs()] >>
  gvs[] >> irule const_computations_related_prefix >>
  simp[const_computations_related_eq, const_results_related_def,
       const_computations_related_refl]
QED

Finalise linked_replay_call_case
