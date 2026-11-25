(* Dynamic-array spines whose syntax changes under qualified inlining. *)
Theory linkedReplaySpine
Ancestors
  constSubstCorrect constSubstMods vyperTypeExprResult vyperTypeConstantFold
  vyperPlaceResultTyping vyperValueOperation vyperState vyperInterpreter
  vyperAST vyperContext vyperTypeSystem vyperValue alist pair

Theorem hashmap_spine_mods[local]:
  (!src id r. ALOOKUP E (src,id) = SOME r ==>
    FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type (expr_type r))) /\
  (!e. well_typed_expr env e \/ IS_SOME (type_place_expr env e) ==>
    expr_type (subst_consts_expr_mods E e) = expr_type e) ==>
  !a kt vt. type_place_expr env a = SOME (HashMapT kt vt) ==>
    base_through_dynarray a = base_through_dynarray (subst_consts_expr_mods E a)
Proof
  strip_tac >> measureInduct_on `expr_size a` >> Cases_on `a` >>
  simp[subst_consts_expr_mods_def, base_through_dynarray_def] >> rpt strip_tac
  >>~ [`type_place_expr env (TopLevelName ty ns) = _`] >-
    (PairCases_on `ns` >>
     gvs[subst_consts_expr_mods_def, base_through_dynarray_def] >>
     Cases_on `ALOOKUP E (ns0,ns1)` >> gvs[base_through_dynarray_def] >>
     drule type_place_expr_global_lookup >> strip_tac >>
     qpat_assum `!src id r. ALOOKUP E (src,id) = SOME r ==> _`
       (drule_then assume_tac) >>
     gvs[])
  >>~ [`type_place_expr env (Subscript ty a b) = _`] >-
    (drule const_subscript_hashmap_base >> strip_tac >>
     `expr_type (subst_consts_expr_mods E a) = expr_type a` by
       metis_tac[optionTheory.IS_SOME_EXISTS] >>
     `base_through_dynarray a = base_through_dynarray (subst_consts_expr_mods E a)` by
       (qpat_x_assum `!y. expr_size y < _ ==> _` (qspec_then `a` mp_tac) >>
        simp[expr_size_def] >> metis_tac[]) >>
     simp[]) >>
  gvs[frame_place_expr_other]
QED

Theorem linked_replay_changed_spine:
  const_subst_context roots cx env [] mods art /\
  (!src id r. ALOOKUP E (src,id) = SOME r ==>
    declared_constant mods src id /\ constant_expr mods r /\
    vyperSubscriptOverlap$accesses_expr r = [] /\
    FLOOKUP env.bare_globals (src,id) = SOME (expr_type r) /\
    FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type (expr_type r)) /\
    (?pv v. const_result_at roots cx (expr_type r)
              (PlaceR (ImmutablePlace src id [])) v /\
            const_result_at roots cx (expr_type r) pv v /\
            !s. const_cells_agree roots s ==>
              lookup_global cx src id s =
                (INL (PlaceR (ImmutablePlace src id [])),s) /\
              eval_expr cx r s = (INL pv,s))) /\
  (!e. well_typed_expr env e \/ IS_SOME (type_place_expr env e) ==>
    expr_type (subst_consts_expr_mods E e) = expr_type e) /\
  (well_typed_expr env a \/ IS_SOME (type_place_expr env a)) /\
  const_cells_agree roots st /\
  base_through_dynarray a <> base_through_dynarray (subst_consts_expr_mods E a) /\
  eval_expr cx a st = (INL p,s) ==>
  (?v. p = Value v) \/ (?v. const_result_at roots cx (expr_type a) p v)
Proof
  `!c cx p st q s.
       (if c then bind (read_result cx p) (\v. return (Value v))
        else return p) st = (INL q,s) ==> s = st` by
    (Cases >> simp[bind_def, return_def, AllCaseEqs()] >>
     rpt strip_tac >> drule read_result_state >> simp[]) >>
  ntac 3 (pure_once_rewrite_tac[GSYM AND_IMP_INTRO] >> disch_tac) >>
  map_every qid_spec_tac [`p`,`s`,`st`,`a`] >>
  measureInduct_on `expr_size a` >> Cases_on `a` >>
  simp[subst_consts_expr_mods_def, base_through_dynarray_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS)
  >>~ [`eval_expr cx (TopLevelName ty ns) st = _`] >-
    (PairCases_on `ns` >> gvs[subst_consts_expr_mods_def] >>
     Cases_on `ALOOKUP E (ns0,ns1)` >> gvs[base_through_dynarray_def] >>
     qpat_x_assum `!e. _ ==> expr_type (subst_consts_expr_mods E e) = _`
       (qspec_then `TopLevelName ty (ns0,ns1)` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     gvs[subst_consts_expr_mods_def, expr_type_def] >>
     qpat_assum `!src id r. ALOOKUP E (src,id) = SOME r ==> _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!t. const_cells_agree roots t ==> lookup_global _ _ _ _ = _ /\ _`
       (drule_then strip_assume_tac) >>
     gvs[Once evaluate_def, expr_type_def] >> metis_tac[])
  >>~ [`eval_expr cx (Subscript ty a b) st = _`] >-
    (drule_then (CONJUNCTS_THEN2 assume_tac assume_tac)
       (REWRITE_RULE [GSYM optionTheory.IS_SOME_EXISTS] frame_subscript_typing) >>
     `expr_type (subst_consts_expr_mods E a) = expr_type a` by
       (qpat_assum `!e. _ ==> expr_type (subst_consts_expr_mods E e) = _`
          (qspec_then `a` irule) >> first_assum ACCEPT_TAC) >>
     `base_through_dynarray a <> base_through_dynarray (subst_consts_expr_mods E a)` by
       (qpat_x_assum `~(_ = _)` mp_tac >> simp[] >> metis_tac[]) >>
     qpat_x_assum `eval_expr cx (Subscript ty a b) st = _` mp_tac >>
     simp[Once evaluate_def, bind_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[] >>
     rename1 `select_result cx (expr_type a) capres (ValueSubscript iv) readst = (INL p,s)` >>
     rename1 `read_result cx idx idxst = (INL iv,readst)` >>
     rename1 `eval_expr cx b cap = (INL idx,idxst)` >>
     rename1 `eval_expr cx a st = (INL res,mid)` >>
     (Q.SUBGOAL_THEN
        `(?v. res = Value v) \/ (?v. const_result_at roots cx (expr_type a) res v)`
        assume_tac >-
      (qpat_x_assum `!y. expr_size y < _ ==> _` (qspec_then `a` mp_tac) >>
       simp[expr_size_def] >>
       disch_then (qspecl_then [`st`,`mid`,`res`] mp_tac) >> simp[])) >>
     qpat_x_assum `!y. expr_size y < _ ==> _` kall_tac >>
     (Q.SUBGOAL_THEN
        `cap = mid /\ ((?v. capres = Value v) \/
         (?v. const_result_at roots cx (expr_type a) capres v))`
        (CONJUNCTS_THEN2 assume_tac assume_tac) >-
      (conj_tac
       >- (qpat_assum `!c cx p st q s. _ ==> s = st`
             (qspecl_then [`subscript_reads_base cx a b`,`cx`,`res`,`mid`,
                          `capres`,`cap`] mp_tac) >> simp[]) >>
       mp_tac (Q.INST [`p` |-> `res`, `q` |-> `capres`,
         `ty` |-> `expr_type a`, `st` |-> `mid`, `s` |-> `cap`,
         `c` |-> `subscript_reads_base cx a b`] value_or_const_capture_success) >>
       simp[])) >>
     `const_cells_agree roots mid` by
       metis_tac[const_subst_context_expr_frame] >>
     `const_cells_agree roots readst` by
       (drule read_result_state >> strip_tac >>
        metis_tac[const_subst_context_expr_frame]) >>
     `~?kt vt. type_place_expr env a = SOME (HashMapT kt vt)` by
       (strip_tac >> mp_tac hashmap_spine_mods >>
        (impl_tac >- (conj_tac >- (rpt strip_tac >>
           qpat_assum `!src id r. ALOOKUP E (src,id) = SOME r ==> _`
             (drule_then strip_assume_tac) >> simp[]) >>
         first_assum ACCEPT_TAC)) >>
        disch_then drule >> metis_tac[]) >>
     `subscript_type_ok (expr_type a) b ty` by
       (irule const_subscript_domain_type_ok >> qexists `env` >>
        fs[NOT_EXISTS_THM]) >>
     `vyperTypeExprResult$subscript_index_matches (expr_type a) b iv` by
       (Cases_on `expr_type a` >>
        gvs[vyperTypeExprResultTheory.subscript_index_matches_def,
            vyperTypeExprResultTheory.subscript_type_ok_tuple] >>
        gvs[Once evaluate_def, evaluate_literal_def, return_def, read_result_def]) >>
     simp[expr_type_def] >> irule value_or_const_select_success >>
     goal_assum (drule_at (Pos last)) >>
     goal_assum (drule_at (Pos (el 2))) >>
     (reverse conj_tac >- metis_tac[]) >>
     rpt strip_tac >>
     `env.type_defs = get_tenv cx` by fs[const_subst_context_def] >>
     `evaluate_type env.type_defs (expr_type a) = SOME tv` by simp[] >>
     drule_all constant_subscript_selected_typed >> simp[] >> metis_tac[]) >>
  gvs[frame_place_expr_other] >>
  rename1 `eval_expr cx (Attribute ty a fld) st = _` >>
  `well_typed_expr env a /\ attribute_type (get_tenv cx) (expr_type a) fld = SOME ty` by
    gvs[Once well_typed_expr_def, const_subst_context_def, attribute_type_ok_def] >>
  qpat_x_assum `eval_expr cx (Attribute ty a fld) st = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  rename1 `select_result cx (expr_type a) res (AttrSubscript fld) mid = (INL p,s)` >>
  `(?v. res = Value v) \/ (?v. const_result_at roots cx (expr_type a) res v)` by
    (qpat_x_assum `!y. expr_size y < _ ==> _` (qspec_then `a` mp_tac) >>
     simp[expr_size_def] >>
     disch_then (qspecl_then [`st`,`mid`,`res`] mp_tac) >> simp[]) >>
  qpat_x_assum `!y. expr_size y < _ ==> _` kall_tac >>
  `const_cells_agree roots mid` by metis_tac[const_subst_context_expr_frame] >>
  simp[expr_type_def] >> irule value_or_const_select_success >>
  goal_assum (drule_at (Pos last)) >>
  goal_assum (drule_at (Pos (el 2))) >>
  (reverse conj_tac >- metis_tac[]) >>
  rpt strip_tac >>
  `env.type_defs = get_tenv cx` by fs[const_subst_context_def] >>
  `attribute_type env.type_defs (expr_type a) fld = SOME ty` by simp[] >>
  `evaluate_type env.type_defs (expr_type a) = SOME tv` by simp[] >>
  drule_all constant_attribute_selected_typed >> simp[] >> metis_tac[]
QED
