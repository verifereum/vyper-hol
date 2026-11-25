Theory linkedConstReplay
Ancestors
  constSubstStmts constSubstCorrect constSubstMods constSubst vyperTypeContract
  vyperTypeSystem vyperInterpreter vyperState vyperAST vyperSubscriptOverlap
  vyperTypeCallGraph vyperTypeExprResult vyperContext vyperCreate
  linkedReplayElements linkedReplayOverlap linkedReplaySpine linkedReplaySubscript
  linkedReplayBuiltin linkedReplayCall linkedReplayWrite linkedReplayControl
  linkedReplayReason vyperTypeEvalCaseProofs vyperTypeEnvExtension
  vyperCallOutcomeFrame vyperTypeContractStaticMaps list finite_map alist pair

Theorem const_subst_eval_stmts_mods:
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  ALL_DISTINCT (MAP FST mods) /\ env.type_defs = get_tenv cx /\
  (!addr src id tv root. MEM (addr,src,id,tv,root) roots ==>
    checked_frame_context cx mods art src id env) /\
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
  (!salt es. blueprint_literal_offset cx salt (subst_consts_exprs_mods E es) =
             blueprint_literal_offset cx salt es) /\
  IS_SOME (type_stmts env ret ss) /\ const_cells_agree roots st ==>
  eval_stmts cx (subst_consts_stmts_mods E ss) st = eval_stmts cx ss st
Proof
  strip_tac >>
  qabbrev_tac `ok = \shadow.
    const_subst_context roots cx shadow [] mods art /\
    shadow.bare_globals = env.bare_globals /\
    shadow.toplevel_vtypes = env.toplevel_vtypes` >>
  `ok env` by (simp[Abbr `ok`, const_subst_context_def, ALOOKUP_def] >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `X = \shadow e.
    (well_typed_expr shadow e \/ IS_SOME (type_place_expr shadow e)) ==>
    !s. const_cells_agree roots s ==>
      const_computations_related (const_results_related roots cx (expr_type e))
        (eval_expr cx e) (eval_expr cx (subst_consts_expr_mods E e)) s /\
      (!kt vt. type_place_expr shadow e = SOME (HashMapT kt vt) ==>
        eval_expr cx e s = eval_expr cx (subst_consts_expr_mods E e) s)` >>
  qabbrev_tac `B = \shadow t.
    IS_SOME (type_place_target shadow t) ==>
    !s. const_cells_agree roots s ==>
      eval_base_place cx t s = eval_base_place cx (subst_consts_btarget_mods E t) s /\
      eval_target_place cx t s = eval_target_place cx (subst_consts_btarget_mods E t) s` >>
  `!fs. MAP FST (subst_consts_fields_mods E fs) = MAP FST fs /\
        MAP SND (subst_consts_fields_mods E fs) = subst_consts_exprs_mods E (MAP SND fs)` by
    (Induct >> simp[subst_consts_expr_mods_def] >>
     Cases_on `h` >> simp[subst_consts_expr_mods_def]) >>
  `!src id r. ALOOKUP E (src,id) = SOME r ==>
     declared_constant mods src id /\ constant_expr mods r /\
     vyperSubscriptOverlap$accesses_expr r = []` by metis_tac[] >>
  `!shadow. ok shadow ==>
    !src id r. ALOOKUP E (src,id) = SOME r ==>
       declared_constant mods src id /\ constant_expr mods r /\
       vyperSubscriptOverlap$accesses_expr r = [] /\
       FLOOKUP shadow.bare_globals (src,id) = SOME (expr_type r) /\
       FLOOKUP shadow.toplevel_vtypes (src,id) = SOME (Type (expr_type r)) /\
       (?pv v. const_result_at roots cx (expr_type r)
          (PlaceR (ImmutablePlace src id [])) v /\
        const_result_at roots cx (expr_type r) pv v /\
        !s. const_cells_agree roots s ==>
          lookup_global cx src id s = (INL (PlaceR (ImmutablePlace src id [])),s) /\
          eval_expr cx r s = (INL pv,s))` by
    (gen_tac >> simp[Abbr `ok`] >> strip_tac >> metis_tac[]) >>
  `!shadow. ok shadow ==> !e. well_typed_expr shadow e \/ IS_SOME (type_place_expr shadow e) ==>
    expr_type (subst_consts_expr_mods E e) = expr_type e` by
    (gen_tac >> strip_tac >> match_mp_tac linked_replay_typed_annotation >>
     metis_tac[]) >>
  `!shadow. ok shadow ==> (!e. X shadow e) /\ (!t. B shadow t)` by
    (gen_tac >> strip_tac >>
     `const_subst_context roots cx shadow [] mods art` by fs[Abbr `ok`] >>
     qpat_assum `!shadow. ok shadow ==> !src id r. _` (drule_then (mk_asm "entries")) >>
     qpat_assum `!shadow. ok shadow ==> !e. _` (drule_then assume_tac) >>
     qabbrev_tac `x = X shadow` >> qabbrev_tac `b = B shadow` >>
     `!es. EVERY x es ==> well_typed_exprs shadow es ==>
       !s. const_cells_agree roots s ==> eval_exprs cx es s =
         eval_exprs cx (subst_consts_exprs_mods E es) s` by
       (simp[Abbr `x`, Abbr `X`] >>
        match_mp_tac linked_replay_list_from_elements >> first_assum ACCEPT_TAC) >>
     `(!al e. al = E ==> x e) /\ (!al t. al = E ==> b t) /\
      (!al es. al = E ==> EVERY x es) /\
      (!al d. al = E ==> (case d of NONE => T | SOME e => x e)) /\
      (!al (fs : (identifier # expr) list). al = E ==> EVERY x (MAP SND fs))` by
       (ho_match_mp_tac subst_consts_expr_mods_ind >> simp[EVERY_DEF] >>
        rpt conj_tac >> rpt gen_tac >> rpt strip_tac
        >~ [`x (TopLevelName ty (ns,id))`]
        >- (Cases_on `ALOOKUP E (ns,id)`
            >- simp[Abbr `x`, Abbr `X`, subst_consts_expr_mods_def,
                 const_computations_related_refl, const_results_related_def] >>
            rename1 `ALOOKUP E (ns,id) = SOME rhs` >>
            asm "entries" (drule_then strip_assume_tac) >>
            simp[Abbr `x`, Abbr `X`, subst_consts_expr_mods_def, expr_type_def,
                 well_typed_expr_def, vtype_annotation_ok_def] >>
            rpt strip_tac >> gvs[] >>
            simp[Once evaluate_def, const_computations_related_def, const_results_related_def] >>
            disj2_tac >> qexists `v` >> simp[])
        >~ [`x (IfExp ty a d c)`]
        >- (gvs[Abbr `x`, Abbr `X`] >>
            simp[frame_place_expr_other, Once well_typed_expr_def] >>
            rpt strip_tac >>
            simp_tac bool_ss [subst_consts_expr_mods_def, Ntimes evaluate_def 2, SF ETA_ss, expr_type_def] >>
            `!e u p v. well_typed_expr shadow e /\ const_cells_agree roots u /\
               eval_expr cx e u = (p,v) ==> const_cells_agree roots v` by
              (rpt gen_tac >> strip_tac >>
               irule const_subst_context_expr_frame >>
               qpat_assum `eval_expr cx e u = (p,v)` (irule_at Any) >>
               qpat_assum `const_subst_context roots cx shadow [] mods art` (irule_at Any) >>
               simp[]) >>
            irule const_computations_related_ifexp_eval >> rpt conj_tac
            >- (rpt strip_tac >> first_x_assum drule_all >> simp[])
            >- (rpt strip_tac >>
                gvs[bind_def, switch_BoolV_def, AllCaseEqs()] >>
                drule read_result_state >> strip_tac >> gvs[] >>
                rename1 `eval_expr cx a s = (INL v0,mid)` >>
                `const_cells_agree roots mid` by
                  (qpat_assum `!e u p v. well_typed_expr shadow e /\ _ ==> _` drule_all >> simp[]) >>
                qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
                IF_CASES_TAC >- (simp[] >> strip_tac >> qpat_assum `!e u p v. well_typed_expr shadow e /\ _ ==> _` drule_all >> simp[]) >>
                IF_CASES_TAC >> simp[raise_def] >> strip_tac >>
                qpat_assum `!e u p v. well_typed_expr shadow e /\ _ ==> _` drule_all >> simp[])
            >- metis_tac[] >>
            qexists `expr_type a` >> metis_tac[])
        >~ [`x (StructLit ty ns fs)`]
        >- (PairCases_on `ns` >> simp[Abbr `x`, Abbr `X`, frame_place_expr_other, Once well_typed_expr_def] >>
            rpt strip_tac >>
            simp_tac bool_ss [subst_consts_expr_mods_def, Ntimes evaluate_def 2, expr_type_def] >>
            drule_then strip_assume_tac well_typed_named_exprs_MAP_SND_stmt >>
            `eval_exprs cx (MAP SND fs) s = eval_exprs cx (subst_consts_exprs_mods E (MAP SND fs)) s` by metis_tac[] >>
            simp[LET_THM] >>
            irule const_computations_related_prefix >>
            simp[const_computations_related_eq, const_computations_related_refl, const_results_related_def])
        >~ [`x (Subscript ty a d)`]
        >- (gvs[Abbr `x`, Abbr `X`] >>
            `!s p t. (well_typed_expr shadow a \/ IS_SOME (type_place_expr shadow a)) /\
               const_cells_agree roots s /\
               subscript_reads_base cx a d <>
                 subscript_reads_base cx (subst_consts_expr_mods E a) (subst_consts_expr_mods E d) /\
               eval_expr cx a s = (INL p,t) ==>
               (?v. p = Value v) \/ (?v. const_result_at roots cx (expr_type a) p v)` by
              (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
               `expr_type (subst_consts_expr_mods E a) = expr_type a` by
                 (qpat_assum `!e. _ ==> expr_type _ = _` (qspec_then `a` irule) >>
                  first_assum ACCEPT_TAC) >>
               `base_through_dynarray a <> base_through_dynarray (subst_consts_expr_mods E a)` by
                 (irule linked_replay_guard_spine >> reverse conj_tac >- first_assum ACCEPT_TAC >>
                  qexistsl [`d`,`cx`,`mods`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
               irule linked_replay_changed_spine >> conj_tac
               >- (qpat_assum `eval_expr cx a s = _` (irule_at Any) >> first_assum ACCEPT_TAC) >>
               qexistsl [`E`,`art`,`shadow`,`mods`] >> rpt conj_tac >>
               (first_assum ACCEPT_TAC ORELSE asm "entries" ACCEPT_TAC)) >>
            match_mp_tac linked_replay_subscript_case >>
            qpat_assum `const_subst_context roots cx shadow [] mods art` (irule_at Any) >>
            rpt conj_tac >> first_assum ACCEPT_TAC)
        >~ [`x (Attribute ty a id)`]
        >- (gvs[Abbr `x`, Abbr `X`] >> simp[frame_place_expr_other, Once well_typed_expr_def] >>
            rpt strip_tac >>
            simp_tac bool_ss [subst_consts_expr_mods_def, Ntimes evaluate_def 2, expr_type_def] >>
            `expr_type (subst_consts_expr_mods E a) = expr_type a` by metis_tac[] >> simp[] >>
            irule const_computations_related_attribute >> rpt conj_tac
            >- metis_tac[const_subst_context_expr_frame]
            >- gvs[const_subst_context_def, attribute_type_ok_def] >>
            metis_tac[])
        >~ [`x (Builtin ty bi es)`]
        >- (gvs[Abbr `x`, Abbr `X`] >> match_mp_tac linked_replay_builtin_case >>
            qpat_assum `const_subst_context roots cx shadow [] mods art` (irule_at Any) >>
            rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE metis_tac[]))
        >~ [`x (TypeBuiltin ty bi t es)`]
        >- (simp[Abbr `x`, Abbr `X`, frame_place_expr_other, Once well_typed_expr_def] >>
            rpt strip_tac >>
            simp_tac bool_ss [subst_consts_expr_mods_def, Ntimes evaluate_def 2, expr_type_def] >>
            `!xs. subst_consts_exprs_mods E xs = MAP (subst_consts_expr_mods E) xs` by
              (Induct >> simp[subst_consts_expr_mods_def]) >>
            `MAP expr_type (subst_consts_exprs_mods E es) = MAP expr_type es` by
              (simp[MAP_MAP_o, MAP_EQ_f, combinTheory.o_DEF] >>
               rpt strip_tac >> qpat_assum `!e. _ ==> expr_type _ = _` irule >>
               disj1_tac >> irule frame_well_typed_exprs_member >> metis_tac[]) >>
            `!s. const_cells_agree roots s ==> eval_exprs cx es s = eval_exprs cx (subst_consts_exprs_mods E es) s` by metis_tac[] >>
            irule const_computations_related_equal >>
            simp[const_results_related_def, type_check_def, assert_def, ignore_bind_def, bind_def,
                 return_def, raise_def])
        >~ [`x (Pop ty tgt)`]
        >- (gvs[Abbr `x`, Abbr `X`, Abbr `b`, Abbr `B`] >>
            simp[frame_place_expr_other, Once well_typed_expr_def] >> rpt strip_tac >>
            simp_tac bool_ss [subst_consts_expr_mods_def, Ntimes evaluate_def 2, expr_type_def] >>
            simp_tac bool_ss [Ntimes evaluate_def 3] >>
            irule const_computations_related_prefix >> reverse conj_tac
            >- (gvs[const_computations_related_eq] >> simp[bind_def]) >>
            rpt strip_tac >> irule const_computations_related_refl >> simp[const_results_related_def])
        >~ [`x (Call ty ct es d)`]
        >- (gvs[Abbr `x`, Abbr `X`] >> match_mp_tac linked_replay_call_case >>
            qpat_assum `const_subst_context roots cx shadow [] mods art` (irule_at Any) >>
            rpt conj_tac >> first_assum ACCEPT_TAC)
        >~ [`b (SubscriptTarget tgt e)`]
        >- (gvs[Abbr `x`, Abbr `X`, Abbr `b`, Abbr `B`] >>
            simp[Once well_typed_expr_def] >> disch_tac >> gen_tac >> strip_tac >>
            `well_typed_expr shadow e /\ IS_SOME (type_place_target shadow tgt)` by
              (Cases_on `well_typed_expr shadow e` >> Cases_on `type_place_target shadow tgt` >> gvs[]) >>
            rename1 `const_cells_agree roots st0` >>
            `eval_base_place cx (SubscriptTarget tgt e) st0 =
             eval_base_place cx (subst_consts_btarget_mods E (SubscriptTarget tgt e)) st0` by
              (simp_tac bool_ss [subst_consts_expr_mods_def, Ntimes evaluate_def 2] >>
               rewrite_tac[GSYM const_computations_related_eq] >>
               irule const_computations_related_prefix >> reverse conj_tac
               >- gvs[const_computations_related_eq] >>
               rpt strip_tac >> BETA_TAC >>
               `const_cells_agree roots s` by metis_tac[const_subst_context_base_frame] >>
               simp_tac bool_ss [GSYM vyperStateTheory.bind_assoc] >>
               irule const_computations_related_prefix >> reverse conj_tac
               >- (irule const_computations_related_bind >>
                   qexists `const_results_related roots cx (expr_type e)` >>
                   reverse conj_tac >- metis_tac[] >>
                   rpt strip_tac >> BETA_TAC >> irule const_computations_related_read >>
                   rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE metis_tac[const_subst_context_expr_frame])) >>
               rpt strip_tac >> irule const_computations_related_refl >> simp[]) >>
            simp[] >>
            qpat_x_assum `eval_base_place cx (SubscriptTarget tgt e) st0 = _` mp_tac >>
            simp_tac bool_ss [evaluate_def, subst_consts_expr_mods_def, bind_def] >> metis_tac[])
        >~ [`b (AttributeTarget tgt id)`]
        >- (gvs[Abbr `b`, Abbr `B`] >> simp[Once well_typed_expr_def, AllCaseEqs()] >>
            rpt strip_tac >>
            simp_tac bool_ss [subst_consts_expr_mods_def, Ntimes evaluate_def 4] >>
            `IS_SOME (type_place_target shadow tgt)` by (Cases_on `type_place_target shadow tgt` >> gvs[]) >>
            gvs[] >> simp[bind_def]) >>
        simp[Abbr `x`, Abbr `X`, Abbr `b`, Abbr `B`, subst_consts_expr_mods_def,
             const_computations_related_refl, const_results_related_def]) >>
     gvs[] >> metis_tac[]) >>
  (* For statements the environment changes, but the global typing maps
     and the checked frame do not. *)
  `!shadow u next. ok shadow /\ type_stmt shadow ret u = SOME next ==> ok next` by
    (simp[Abbr `ok`] >> rpt strip_tac >>
     drule_then strip_assume_tac type_stmt_env_preserved_static >> simp[] >>
     metis_tac[const_subst_context_type_stmt]) >>
  `!shadow id ty. ok shadow ==> ok (extend_local shadow id ty F)` by
    (simp[Abbr `ok`] >> rpt strip_tac >>
     drule const_subst_context_extend_local >> simp[extend_local_def]) >>
  `!shadow u s ures t. ok shadow /\ IS_SOME (type_stmt shadow ret u) /\
      const_cells_agree roots s /\ eval_stmt cx u s = (ures,t) ==>
      const_cells_agree roots t` by
    (simp[Abbr `ok`] >> rpt strip_tac >>
     irule protected_cell_frame_cells_agree >> qexists `s` >> simp[] >>
     rpt strip_tac >>
     `checked_frame_context cx mods art src id shadow` by
       (qpat_assum `const_subst_context roots cx shadow [] mods art` mp_tac >>
        simp_tac bool_ss [const_subst_context_def] >> strip_tac >>
        qpat_assum `!addr src id tv root. MEM _ roots ==> checked_frame_context cx mods art src id shadow`
          (drule_then ACCEPT_TAC)) >>
     drule_all checked_eval_stmt_protected_cell_frame >>
     simp[state_rel_frame_result] >> metis_tac[]) >>
  `!shadow es. ok shadow /\ well_typed_exprs shadow es ==>
      !s. const_cells_agree roots s ==>
      eval_exprs cx es s = eval_exprs cx (subst_consts_exprs_mods E es) s` by
    (rpt gen_tac >> strip_tac >>
     `const_subst_context roots cx shadow [] mods art` by fs[Abbr `ok`] >>
     qpat_assum `!shadow. ok shadow ==> (!e. X shadow e) /\ _` (drule_then strip_assume_tac) >>
     rpt strip_tac >> irule linked_replay_list_from_elements >>
     qpat_assum `const_subst_context roots cx shadow [] mods art` (irule_at Any) >>
     gvs[Abbr `X`, EVERY_MEM] >> gen_tac >> strip_tac >>
     qpat_assum `!e. _ ==> !s. _` (qspec_then `e` mp_tac) >> metis_tac[]) >>
  `!shadow exp k l s. ok shadow /\ well_typed_expr shadow exp /\ const_cells_agree roots s /\
    (!p q u. const_results_related roots cx (expr_type exp) p q /\
      const_cells_agree roots u ==> const_computations_related $= (k p) (l q) u) ==>
    const_computations_related (($=) : unit -> unit -> bool) (bind (eval_expr cx exp) k)
      (bind (eval_expr cx (subst_consts_expr_mods E exp)) l) s` by
    (rpt strip_tac >>
     `const_subst_context roots cx shadow [] mods art` by fs[Abbr `ok`] >>
     qpat_assum `!shadow. ok shadow ==> (!e. X shadow e) /\ _` (drule_then strip_assume_tac) >>
     irule const_computations_related_bind >>
     qexists `const_results_related roots cx (expr_type exp)` >>
     reverse conj_tac >- gvs[Abbr `X`] >>
     rpt strip_tac >> rename1 `eval_expr cx exp s = (INL p,snext)` >>
     `const_cells_agree roots snext` by
       (fs[const_subst_context_def] >> drule_all checked_eval_expr_const_cells_agree >> simp[]) >>
     first_x_assum irule >> simp[]) >>
  `!ty p q s (k:value -> evaluation_state -> unit evaluation_result).
      const_results_related roots cx ty p q /\ const_cells_agree roots s ==>
      bind (read_result cx p) k s = bind (read_result cx q) k s` by
    (rpt strip_tac >> drule_all const_results_related_read >> simp[bind_def]) >>
  `(!al u. al = E ==> !shadow. ok shadow /\ IS_SOME (type_stmt shadow ret u) ==>
      !s. const_cells_agree roots s ==>
      eval_stmt cx (subst_consts_stmt_mods al u) s = eval_stmt cx u s) /\
   (!al us. al = E ==> !shadow. ok shadow /\ IS_SOME (type_stmts shadow ret us) ==>
      !s. const_cells_agree roots s ==>
      eval_stmts cx (subst_consts_stmts_mods al us) s = eval_stmts cx us s)` by
    (ho_match_mp_tac subst_consts_stmt_mods_ind >>
     rpt conj_tac >> rpt gen_tac >> rpt strip_tac >> gvs[] >>
     TRY (simp[subst_consts_stmt_mods_def] >> NO_TAC) >>
     `const_subst_context roots cx shadow [] mods art` by fs[Abbr `ok`] >>
     qpat_assum `!shadow. ok shadow ==> (!e. X shadow e) /\ _` (drule_then strip_assume_tac) >>
     gvs[Abbr `X`, Abbr `B`]
     >~ [`eval_stmt _ _ _ = eval_stmt _ (Assign _ _) _`]
     >- (irule (cj 1 linked_replay_write_cases) >>
         qpat_assum `const_subst_context roots cx shadow [] mods art` (irule_at Any) >>
         qpat_assum `IS_SOME (type_stmt shadow ret _)` (irule_at Any) >>
         rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE first_assum (qspec_then `e` ACCEPT_TAC)))
     >~ [`eval_stmt _ _ _ = eval_stmt _ (AugAssign _ _ _ _) _`]
     >- (irule (cj 2 linked_replay_write_cases) >>
         qpat_assum `const_subst_context roots cx shadow [] mods art` (irule_at Any) >>
         qpat_assum `IS_SOME (type_stmt shadow ret _)` (irule_at Any) >>
         rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE first_assum (qspec_then `e` ACCEPT_TAC)))
     >~ [`eval_stmt _ _ _ = eval_stmt _ (Append _ _) _`]
     >- (irule (cj 3 linked_replay_write_cases) >>
         qpat_assum `const_subst_context roots cx shadow [] mods art` (irule_at Any) >>
         qpat_assum `IS_SOME (type_stmt shadow ret _)` (irule_at Any) >>
         rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE first_assum (qspec_then `e` ACCEPT_TAC)))
     >~ [`eval_stmt _ _ _ = eval_stmt _ (Raise _) _`]
     >- (irule (cj 1 linked_replay_reason_cases) >>
         qpat_assum `const_subst_context roots cx shadow [] mods art` (irule_at Any) >>
         qpat_assum `IS_SOME (type_stmt shadow ret _)` (irule_at Any) >>
         rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE (gen_tac >> strip_tac >> metis_tac[])))
     >~ [`eval_stmt _ _ _ = eval_stmt _ (Assert _ _) _`]
     >- (irule (cj 2 linked_replay_reason_cases) >>
         qpat_assum `const_subst_context roots cx shadow [] mods art` (irule_at Any) >>
         qpat_assum `IS_SOME (type_stmt shadow ret _)` (irule_at Any) >>
         rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE (gen_tac >> strip_tac >> metis_tac[])))
     >~ [`eval_stmt _ _ _ = eval_stmt _ (If e yes no) _`]
     >- (`IS_SOME (type_stmts shadow ret yes) /\ IS_SOME (type_stmts shadow ret no)` by
           gvs[type_stmt_def, AllCaseEqs()] >>
         irule linked_replay_if_case >>
         qpat_assum `const_subst_context roots cx shadow [] mods art` (irule_at Any) >>
         qpat_assum `IS_SOME (type_stmt shadow ret _)` (irule_at Any) >>
         rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE first_assum (qspec_then `e` ACCEPT_TAC) ORELSE metis_tac[]))
     >~ [`eval_stmt _ _ _ = eval_stmt _ (For nm ty it n lbody) _`]
     >- (`IS_SOME (type_stmts (extend_local shadow nm ty F) ret lbody)` by
           gvs[type_stmt_def, AllCaseEqs()] >>
         `ok (extend_local shadow nm ty F)` by simp[] >>
         irule linked_replay_for_case >>
         qpat_assum `const_subst_context roots cx shadow [] mods art` (irule_at Any) >>
         qpat_assum `IS_SOME (type_stmt shadow ret _)` (irule_at Any) >>
         rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE metis_tac[]))
     >~ [`eval_stmt _ _ _ = eval_stmt _ (Expr e) _`]
     >- (once_rewrite_tac[EQ_SYM_EQ] >> rewrite_tac[GSYM const_computations_related_eq] >>
         simp[subst_consts_stmt_mods_def, evaluate_def] >>
         qpat_assum `!shadow exp k l s. _` ho_match_mp_tac >>
         qexists `shadow` >> gvs[type_stmt_def, AllCaseEqs()] >>
         rpt strip_tac >>
         gvs[const_computations_related_refl, const_results_related_def, const_result_at_def])
     >~ [`eval_stmt _ _ _ = eval_stmt _ (Return opt) _`]
     >- (Cases_on `opt` >> simp[subst_consts_stmt_mods_def, subst_consts_expr_mods_def]
         >> once_rewrite_tac[EQ_SYM_EQ] >> rewrite_tac[GSYM const_computations_related_eq] >>
         simp[evaluate_def] >>
         qpat_assum `!shadow exp k l s. _` ho_match_mp_tac >>
         qexists `shadow` >> gvs[type_stmt_def, AllCaseEqs()] >>
         rpt strip_tac >> simp[const_computations_related_eq] >> metis_tac[])
     >~ [`eval_stmt _ _ _ = eval_stmt _ (Log ns es) _`]
     >- (`well_typed_exprs shadow es` by
           (qpat_x_assum `IS_SOME (type_stmt shadow ret (Log ns es))` mp_tac >>
            simp[type_stmt_def] >> Cases_on `FLOOKUP shadow.event_fields ns` >> simp[]) >>
         `eval_exprs cx es s = eval_exprs cx (subst_consts_exprs_mods E es) s` by
           (qpat_assum `!shadow es. ok shadow /\ well_typed_exprs shadow es ==> _`
             (qspecl_then [`shadow`,`es`] mp_tac) >> simp[]) >>
         simp[subst_consts_stmt_mods_def, evaluate_def, bind_def])
     >~ [`eval_stmt _ _ _ = eval_stmt _ (AnnAssign nm ty e) _`]
     >- (Cases_on `evaluate_type (get_tenv cx) ty`
         >- simp[subst_consts_stmt_mods_def, evaluate_def, lift_option_type_def, bind_def, raise_def] >>
         simp[subst_consts_stmt_mods_def, evaluate_def, lift_option_type_def, vyperStateTheory.bind_return] >>
         once_rewrite_tac[EQ_SYM_EQ] >> rewrite_tac[GSYM const_computations_related_eq] >>
         qpat_assum `!shadow exp k l s. _` ho_match_mp_tac >>
         qexists `shadow` >> gvs[type_stmt_def, AllCaseEqs()] >>
         rpt strip_tac >> simp[const_computations_related_eq] >> metis_tac[])
     >~ [`eval_stmts _ _ _ = eval_stmts _ (u::us) _`]
     >- (Cases_on `type_stmt shadow ret u` >> fs[type_stmt_def] >>
         rename1 `type_stmt shadow ret u = SOME next` >>
         `IS_SOME (type_stmt shadow ret u)` by simp[] >>
         `ok next` by
           (qpat_assum `!shadow u next. ok shadow /\ type_stmt shadow ret u = SOME next ==> ok next`
              (drule_all_then ACCEPT_TAC)) >>
         `eval_stmt cx (subst_consts_stmt_mods E u) s = eval_stmt cx u s` by
           (qpat_assum `!shadow. ok shadow /\ IS_SOME (type_stmt shadow ret u) ==> _`
              (qspec_then `shadow` mp_tac) >> simp[]) >>
         simp[subst_consts_stmt_mods_def, evaluate_def, ignore_bind_def, bind_def] >>
         Cases_on `eval_stmt cx u s` >> rename1 `eval_stmt cx u s = (outcome,mid)` >>
         Cases_on `outcome` >> simp[] >>
         `const_cells_agree roots mid` by
           (qpat_assum `!shadow u s ures t. ok shadow /\ IS_SOME (type_stmt shadow ret u) /\ _ ==> const_cells_agree roots t`
              (drule_all_then ACCEPT_TAC)) >>
         qpat_assum `!shadow. ok shadow /\ IS_SOME (type_stmts shadow ret us) ==> _`
           (qspec_then `next` mp_tac) >> simp[])) >>
  qpat_assum `!al us. al = E ==> !shadow. ok shadow /\ IS_SOME (type_stmts shadow ret us) ==> _`
    (qspecl_then [`E`,`ss`] mp_tac) >> simp[] >>
  disch_then (qspec_then `env` mp_tac) >> simp[]
QED
