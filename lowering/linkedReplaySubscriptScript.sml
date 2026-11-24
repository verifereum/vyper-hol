Theory linkedReplaySubscript
Ancestors
  constSubstCorrect constSubstMods vyperTypeEvalCaseProofs option
  vyperTypeSystem vyperTypeExprResult vyperInterpreter vyperState vyperAST

Theorem linked_replay_subscript_case:
  const_subst_context roots cx env [] mods art /\
  (!e. well_typed_expr env e \/ IS_SOME (type_place_expr env e) ==>
       expr_type (subst_consts_expr_mods E e) = expr_type e) /\
  ((well_typed_expr env a \/ IS_SOME (type_place_expr env a)) ==>
   !s. const_cells_agree roots s ==>
       const_computations_related (const_results_related roots cx (expr_type a))
         (eval_expr cx a) (eval_expr cx (subst_consts_expr_mods E a)) s /\
       (!kt vt. type_place_expr env a = SOME (HashMapT kt vt) ==>
                eval_expr cx a s = eval_expr cx (subst_consts_expr_mods E a) s)) /\
  ((well_typed_expr env b \/ IS_SOME (type_place_expr env b)) ==>
   !s. const_cells_agree roots s ==>
       const_computations_related (const_results_related roots cx (expr_type b))
         (eval_expr cx b) (eval_expr cx (subst_consts_expr_mods E b)) s /\
       (!kt vt. type_place_expr env b = SOME (HashMapT kt vt) ==>
                eval_expr cx b s = eval_expr cx (subst_consts_expr_mods E b) s)) /\
  (!s p t. (well_typed_expr env a \/ IS_SOME (type_place_expr env a)) /\
           const_cells_agree roots s /\
           subscript_reads_base cx a b <>
             subscript_reads_base cx (subst_consts_expr_mods E a)
                                     (subst_consts_expr_mods E b) /\
           eval_expr cx a s = (INL p,t) ==>
           (?v. p = Value v) \/ (?v. const_result_at roots cx (expr_type a) p v)) ==>
  (well_typed_expr env (Subscript ty a b) \/
   IS_SOME (type_place_expr env (Subscript ty a b))) ==>
  !s. const_cells_agree roots s ==>
      const_computations_related (const_results_related roots cx (expr_type (Subscript ty a b)))
        (eval_expr cx (Subscript ty a b))
        (eval_expr cx (subst_consts_expr_mods E (Subscript ty a b))) s /\
      (!kt vt. type_place_expr env (Subscript ty a b) = SOME (HashMapT kt vt) ==>
               eval_expr cx (Subscript ty a b) s =
                 eval_expr cx (subst_consts_expr_mods E (Subscript ty a b)) s)
Proof
  disch_then strip_assume_tac >> disch_tac >> qx_gen_tac `st` >> disch_tac >>
  drule (SRULE [GSYM IS_SOME_EXISTS] frame_subscript_typing) >>
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  `expr_type (subst_consts_expr_mods E a) = expr_type a` by metis_tac[] >>
  `!s p t. const_cells_agree roots s /\ eval_expr cx b s = (INL p,t) ==>
           const_cells_agree roots t` by
    (rpt strip_tac >> metis_tac[const_subst_context_expr_frame]) >>
  `!s. const_cells_agree roots s ==>
       const_computations_related (const_results_related roots cx (expr_type b))
         (eval_expr cx b) (eval_expr cx (subst_consts_expr_mods E b)) s` by
    metis_tac[] >>
  Cases_on `?kt vt. type_place_expr env a = SOME (HashMapT kt vt)`
  >- suspend "hashmap" >>
  conj_tac
  >- suspend "ordinary" >>
  rpt gen_tac >> disch_tac >> drule const_subscript_hashmap_base >> simp[]
QED

Resume linked_replay_subscript_case[hashmap]:
  pop_assum strip_assume_tac >>
  `~is_ArrayT (expr_type a)` by
    (drule type_place_expr_vtype_annotation >> simp[vtype_annotation_ok_def]) >>
  `~subscript_reads_base cx a b /\
   ~subscript_reads_base cx (subst_consts_expr_mods E a)
                          (subst_consts_expr_mods E b)` by
    metis_tac[subscript_reads_base_through_dynarray] >>
  `eval_expr cx a st = eval_expr cx (subst_consts_expr_mods E a) st` by
    metis_tac[] >>
  `eval_expr cx (Subscript ty a b) st =
   eval_expr cx (Subscript ty (subst_consts_expr_mods E a)
                             (subst_consts_expr_mods E b)) st` by
    (rewrite_tac[GSYM const_computations_related_eq] >>
     simp_tac bool_ss [Ntimes evaluate_def 2] >>
     simp[vyperStateTheory.bind_return] >>
     irule const_computations_related_subscript_exact_base >>
     reverse conj_tac >- simp[] >>
     qexistsl [`expr_type b`, `roots`] >> simp[] >>
     rpt strip_tac >> metis_tac[const_subst_context_expr_frame]) >>
  simp[subst_consts_expr_mods_def] >>
  irule const_computations_related_equal >> simp[const_results_related_def]
QED

Resume linked_replay_subscript_case[ordinary]:
  `subscript_type_ok (expr_type a) b ty` by
    metis_tac[const_subscript_domain_type_ok] >>
  `!p s. eval_expr cx a st = (INL p,s) ==> const_cells_agree roots s` by
    (rpt strip_tac >> metis_tac[const_subst_context_expr_frame]) >>
  simp_tac bool_ss [subst_consts_expr_mods_def, Ntimes evaluate_def 2, expr_type_def] >>
  simp[] >>
  CONV_TAC (ONCE_DEPTH_CONV (HO_REWR_CONV (GSYM vyperStateTheory.bind_assoc))) >>
  irule const_computations_related_subscript >>
  rpt conj_tac
  >- (rpt strip_tac >>
      gvs[bind_def, AllCaseEqs()] >>
      Cases_on `subscript_reads_base cx a b` >>
      gvs[bind_def, return_def, AllCaseEqs()] >>
      metis_tac[read_result_state])
  >- (rpt strip_tac >>
      qpat_assum `!s p t. _ /\ eval_expr cx b s = (INL p,t) ==> _`
        (drule_at Any) >> simp[])
  >- (qexists `expr_type b` >> simp[])
  >- (qexists `b` >> simp[] >> rpt strip_tac >>
      metis_tac[eval_expr_subscript_index_matches_stmt]) >>
  irule const_computations_related_bind >>
  qexists `const_results_related roots cx (expr_type a)` >>
  reverse conj_tac >- metis_tac[] >>
  rpt strip_tac >> BETA_TAC >>
  `const_cells_agree roots s` by metis_tac[] >>
  qabbrev_tac `capture = subscript_reads_base cx a b` >>
  qabbrev_tac `capture' = subscript_reads_base cx (subst_consts_expr_mods E a)
                                                 (subst_consts_expr_mods E b)` >>
  Cases_on `x = y /\ capture = capture'`
  >- (gvs[] >> irule const_computations_related_refl >> simp[const_results_related_def]) >>
  `(?v. x = Value v /\ y = Value v) \/
   (?v. const_result_at roots cx (expr_type a) x v /\
        const_result_at roots cx (expr_type a) y v)` by
    (Cases_on `x = y`
     >- (qpat_assum `!s p t. _ /\ _ /\ _ /\ eval_expr cx a s = (INL p,t) ==> _`
           (qspecl_then [`st`, `x`, `s`] mp_tac) >>
         unabbrev_all_tac >> gvs[]) >>
     disj2_tac >>
     qpat_x_assum `const_results_related roots cx (expr_type a) x y` mp_tac >>
     simp[const_results_related_def]) >>
  pop_assum strip_assume_tac
  >- (gvs[] >> Cases_on `capture` >> Cases_on `capture'` >>
      simp[read_result_def, vyperStateTheory.bind_return] >>
      irule const_computations_related_refl >> simp[const_results_related_def]) >>
  `read_result cx x s = (INL v,s) /\ read_result cx y s = (INL v,s)` by
    metis_tac[const_result_at_observe] >>
  `const_result_at roots cx (expr_type a) (Value v) v` by
    (qpat_assum `const_result_at roots cx _ x v`
       (mp_tac o REWRITE_RULE [const_result_at_def]) >>
     simp[const_result_at_def]) >>
  Cases_on `capture` >> Cases_on `capture'` >>
  simp[bind_def, return_def, const_computations_related_def, const_results_related_def] >>
  metis_tac[]
QED

Finalise linked_replay_subscript_case
