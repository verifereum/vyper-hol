Theory linkedRuntimeDefaultReplay
Ancestors
  constSubstStmts constSubstCorrect constSubstMods constSubst vyperTypeContract
  vyperTypeSystem vyperInterpreter vyperState vyperAST vyperSubscriptOverlap
  vyperTypeCallGraph vyperTypeExprResult vyperPlaceResultTyping vyperContext vyperCreate
  linkedReplayElements linkedReplayOverlap linkedReplaySpine linkedReplaySubscript
  linkedReplayBuiltin linkedReplayCall linkedReplayWrite linkedReplayControl
  linkedReplayReason whitelistCheckerConsts vyperTypeEvalCaseProofs vyperTypeEnvExtension
  vyperCallOutcomeFrame vyperTypeContractStaticMaps list finite_map alist pair

Theorem const_subst_runtime_default_exprs_mods:
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
  EVERY (runtime_constant_expr mods) es /\
  well_typed_exprs env es /\ const_cells_agree roots st ==>
  eval_exprs cx (subst_consts_exprs_mods E es) st = eval_exprs cx es st /\
  eval_external_defaults cx (subst_consts_exprs_mods E es) st =
    eval_external_defaults cx es st
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `const_subst_context roots cx env [] mods art` by
    (simp[const_subst_context_def, ALOOKUP_def] >> first_assum ACCEPT_TAC) >>
  `!src id r. ALOOKUP E (src,id) = SOME r ==>
    declared_constant mods src id /\ constant_expr mods r /\
    vyperSubscriptOverlap$accesses_expr r = []` by metis_tac[] >>
  `!e. well_typed_expr env e \/ IS_SOME (type_place_expr env e) ==>
    expr_type (subst_consts_expr_mods E e) = expr_type e` by
    (match_mp_tac linked_replay_typed_annotation >>
     rpt strip_tac >> qpat_assum `!src id r. ALOOKUP E (src,id) = SOME r ==> _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `!xs st. EVERY (\e. (well_typed_expr env e \/ IS_SOME (type_place_expr env e)) ==>
      !s. const_cells_agree roots s ==>
       const_computations_related (const_results_related roots cx (expr_type e))
         (eval_expr cx e) (eval_expr cx (subst_consts_expr_mods E e)) s /\
       (!kt vt. type_place_expr env e = SOME (HashMapT kt vt) ==>
          eval_expr cx e s = eval_expr cx (subst_consts_expr_mods E e) s)) xs /\
    well_typed_exprs env xs /\ const_cells_agree roots st ==>
    eval_exprs cx (subst_consts_exprs_mods E xs) st = eval_exprs cx xs st` by
    (rpt gen_tac >> strip_tac >> sym_tac >>
     qpat_assum `const_subst_context _ _ _ _ _ _`
       (mp_tac o MATCH_MP linked_replay_list_from_elements) >>
     disch_then (qspec_then `xs` mp_tac) >> simp[]) >>
  `(!replacements e. replacements = E /\ runtime_constant_expr mods e /\
       (well_typed_expr env e \/ IS_SOME (type_place_expr env e)) ==>
       !s. const_cells_agree roots s ==>
         const_computations_related (const_results_related roots cx (expr_type e))
           (eval_expr cx e) (eval_expr cx (subst_consts_expr_mods replacements e)) s /\
         (!kt vt. type_place_expr env e = SOME (HashMapT kt vt) ==>
           eval_expr cx e s = eval_expr cx (subst_consts_expr_mods replacements e) s)) /\
   (!replacements:((num option # identifier) # expr) list.
      !bt:base_assignment_target. T) /\
   (!replacements args. replacements = E ==>
     EVERY (\e. runtime_constant_expr mods e /\
       (well_typed_expr env e \/ IS_SOME (type_place_expr env e)) ==>
       !s. const_cells_agree roots s ==>
         const_computations_related (const_results_related roots cx (expr_type e))
           (eval_expr cx e) (eval_expr cx (subst_consts_expr_mods replacements e)) s /\
         (!kt vt. type_place_expr env e = SOME (HashMapT kt vt) ==>
           eval_expr cx e s = eval_expr cx (subst_consts_expr_mods replacements e) s)) args) /\
   (!replacements:((num option # identifier) # expr) list. !opt:expr option. T) /\
   (!replacements (fields:(identifier # expr) list). replacements = E ==>
     EVERY (\e. runtime_constant_expr mods e /\
       (well_typed_expr env e \/ IS_SOME (type_place_expr env e)) ==>
       !s. const_cells_agree roots s ==>
         const_computations_related (const_results_related roots cx (expr_type e))
           (eval_expr cx e) (eval_expr cx (subst_consts_expr_mods replacements e)) s /\
         (!kt vt. type_place_expr env e = SOME (HashMapT kt vt) ==>
           eval_expr cx e s = eval_expr cx (subst_consts_expr_mods replacements e) s))
        (MAP SND fields))` suffices_by
    (strip_tac >>
     `!s. const_cells_agree roots s ==>
        eval_exprs cx (subst_consts_exprs_mods E es) s = eval_exprs cx es s` by
       (gen_tac >> strip_tac >>
        qpat_assum `!xs st. EVERY _ xs /\ _ ==> _`
          (qspecl_then [`es`,`s`] mp_tac) >> simp[EVERY_MEM] >>
        impl_tac >-
          (rpt strip_tac >>
           qpat_assum `!replacements e. replacements = E /\ runtime_constant_expr mods e /\ _ ==> _`
             (qspecl_then [`E`,`e`] mp_tac) >> fs[EVERY_MEM]) >>
        simp[]) >>
     simp[eval_external_defaults_run, const_cells_agree_scopes]) >>
  `!args. LENGTH (subst_consts_exprs_mods E args) = LENGTH args` by
    (Induct >> simp[subst_consts_expr_mods_def]) >>
  `!args. well_typed_exprs env args ==>
           MAP expr_type (subst_consts_exprs_mods E args) = MAP expr_type args` by
    (Induct >> simp[subst_consts_expr_mods_def, well_typed_expr_def] >>
     rpt strip_tac >>
     qpat_assum `!e. _ ==> expr_type (subst_consts_expr_mods E e) = _`
       (qspec_then `h` mp_tac) >> simp[]) >>
  `!e. constant_expr mods e ==> ~is_self_addr e` by
    (Cases >> simp[constant_expr_def, is_self_addr_def] >>
     rename1 `constant_builtin bt` >> Cases_on `bt` >>
     simp[constant_builtin_def] >> rename1 `Env field` >>
     Cases_on `field` >> simp[constant_builtin_def, is_self_addr_def]) >>
  `!e. runtime_constant_expr mods e ==>
       ~is_self_addr e /\ ~is_self_addr (subst_consts_expr_mods E e)` by
    (Cases >> simp[subst_consts_expr_mods_def, runtime_constant_expr_def,
                  is_self_addr_def]
     >- (rename1 `TopLevelName _ key` >> PairCases_on `key` >>
         Cases_on `ALOOKUP E (key0,key1)` >>
         simp[subst_consts_expr_mods_def, runtime_constant_expr_def, is_self_addr_def] >>
         rpt strip_tac >>
         qpat_assum `!src id r. ALOOKUP E (src,id) = SOME r ==> _`
           (drule_then strip_assume_tac) >>
         qpat_assum `!a. constant_expr mods a ==> ~is_self_addr a`
           (qspec_then `x` mp_tac) >> simp[]) >>
     rename1 `runtime_constant_builtin bt` >> Cases_on `bt` >>
     simp[runtime_constant_builtin_def, constant_builtin_def] >>
     Cases_on `e` >> Cases_on `l` >>
     simp[runtime_constant_builtin_def, is_self_addr_def,
          subst_consts_expr_mods_def]) >>
  ho_match_mp_tac subst_consts_expr_mods_ind >>
  simp[runtime_constant_expr_def, frame_place_expr_other] >>
  rpt conj_tac >> rpt gen_tac >> rpt strip_tac >> gvs[EVERY_DEF]
  >>~- ([`eval_expr cx (TopLevelName ty (src,id))`],
      Cases_on `ALOOKUP E (src,id)` >>
      simp[subst_consts_expr_mods_def, const_computations_related_refl,
           const_results_related_def] >>
      rename1 `ALOOKUP E (src,id) = SOME r` >>
      qpat_assum `!src id r. ALOOKUP E (src,id) = SOME r ==>
        constant_expr mods r /\ accesses_expr r = [] /\
        FLOOKUP env.bare_globals (src,id) = SOME (expr_type r) /\ _`
          (drule_then strip_assume_tac) >>
      imp_res_tac type_place_expr_global_lookup >> fs[] >>
      `expr_type r = ty` by
        fs[well_typed_expr_def, vtype_annotation_ok_def, expr_type_def] >>
      qpat_assum `!s. const_cells_agree roots s ==> _`
        (qspec_then `s` (drule_then strip_assume_tac)) >>
      fs[Once evaluate_def, expr_type_def, const_computations_related_def,
         const_results_related_def] >>
      disj2_tac >> qexists_tac `v` >> simp[])
  >>~- ([`eval_expr cx (Subscript _ _ _)`],
      qmatch_goalsub_rename_tac `eval_expr cx (Subscript ty a b)` >>
      `!u p v. (well_typed_expr env a \/ IS_SOME (type_place_expr env a)) /\
        const_cells_agree roots u /\
        subscript_reads_base cx a b <>
          subscript_reads_base cx (subst_consts_expr_mods E a) (subst_consts_expr_mods E b) /\
        eval_expr cx a u = (INL p,v) ==>
        (?w. p = Value w) \/ (?w. const_result_at roots cx (expr_type a) p w)` by
        (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
         `expr_type (subst_consts_expr_mods E a) = expr_type a` by
           (qpat_assum `!e. _ ==> expr_type _ = _` (qspec_then `a` irule) >>
            first_assum ACCEPT_TAC) >>
         `base_through_dynarray a <> base_through_dynarray (subst_consts_expr_mods E a)` by
           (irule linked_replay_guard_spine >> reverse conj_tac >- first_assum ACCEPT_TAC >>
            qexistsl [`b`,`cx`,`mods`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
         irule linked_replay_changed_spine >> conj_tac
         >- (qpat_assum `eval_expr cx a u = _` (irule_at Any) >> first_assum ACCEPT_TAC) >>
         qexistsl [`E`,`art`,`env`,`mods`] >>
         rpt conj_tac >>
         (first_assum ACCEPT_TAC ORELSE
          (rpt gen_tac >> strip_tac >>
           qpat_assum `!src id r. ALOOKUP E (src,id) = SOME r ==> declared_constant _ _ _ /\ _`
             (drule_then strip_assume_tac) >>
           qpat_assum `!src id r. ALOOKUP E (src,id) = SOME r ==>
             constant_expr mods r /\ accesses_expr r = [] /\
             FLOOKUP env.bare_globals (src,id) = SOME (expr_type r) /\ _`
               (drule_then strip_assume_tac) >>
           simp[] >> qexistsl_tac [`pv`,`v'`] >> simp[]))) >>
      mp_tac (Q.INST [`a` |-> `a`,`b` |-> `b`,`ty` |-> `ty`,
        `env` |-> `env`,`E` |-> `E`,`mods` |-> `mods`,`art` |-> `art`]
        linked_replay_subscript_case) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      impl_tac >- simp[] >>
      disch_then (qspec_then `s` mp_tac) >> simp[])
  >>~- ([`eval_expr cx (Literal _ _)`],
      simp[subst_consts_expr_mods_def, Ntimes evaluate_def 2] >>
      irule const_computations_related_refl >>
      simp[const_results_related_def])
  >>~- ([`eval_expr cx (IfExp _ _ _ _)`],
      qmatch_goalsub_rename_tac `eval_expr cx (IfExp ty guard yes no)` >>
      fs[well_typed_expr_def] >>
      simp_tac bool_ss [subst_consts_expr_mods_def, Ntimes evaluate_def 2,
        expr_type_def, SF ETA_ss] >>
      `!e a r b. eval_expr cx e a = (r,b) /\
          const_cells_agree roots a /\ well_typed_expr env e ==>
          const_cells_agree roots b` by
        (qpat_assum `!addr src id tv root. _` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >>
         metis_tac[checked_eval_expr_const_cells_agree]) >>
      irule const_computations_related_ifexp_eval >>
      rpt conj_tac
      >- (rpt strip_tac >>
          qpat_assum `!e a r b. _` (drule_then irule) >> simp[])
      >- (rpt strip_tac >>
          gvs[bind_def, switch_BoolV_def, AllCaseEqs()] >>
          drule read_result_state >> strip_tac >> gvs[] >>
          qmatch_asmsub_rename_tac `read_result cx guard_place mid = (INL bv,mid)` >>
          `const_cells_agree roots mid` by
            (qpat_assum `!e a r b. _` (qspec_then `guard` mp_tac) >>
             simp[] >> strip_tac >>
             qpat_assum `eval_expr cx guard _ = _`
               (fn run => first_assum (mp_tac o (fn th => MATCH_MP
                 (REWRITE_RULE [GSYM AND_IMP_INTRO] th) run))) >> simp[]) >>
          qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
          IF_CASES_TAC
          >- (simp[] >> strip_tac >>
              qpat_assum `!e a r b. _` (drule_then irule) >> simp[]) >>
          IF_CASES_TAC >> simp[raise_def] >> strip_tac >>
          qpat_assum `!e a r b. _` (drule_then irule) >> simp[])
      >- fs[]
      >- (qexists_tac `expr_type guard` >> fs[]))
  >>~- ([`eval_expr cx (Attribute ty e fld)`],
      fs[well_typed_expr_def] >>
      `expr_type (subst_consts_expr_mods E e) = expr_type e` by
        (qpat_assum `!e. _ ==> expr_type (subst_consts_expr_mods E e) = _`
           (qspec_then `e` mp_tac) >> simp[]) >>
      simp_tac bool_ss [subst_consts_expr_mods_def, Ntimes evaluate_def 2,
        expr_type_def] >>
      asm_rewrite_tac[] >>
      irule const_computations_related_attribute >>
      rpt conj_tac
      >- metis_tac[checked_eval_expr_const_cells_agree]
      >- (qpat_assum `env.type_defs = get_tenv cx`
            (PURE_REWRITE_TAC o single o GSYM) >>
          fs[attribute_type_ok_def])
      >- fs[])
  >>~- ([`eval_expr cx (StructLit ty ns fields)`],
      PairCases_on `ns` >>
      fs[well_typed_expr_def] >>
      `!fs. MAP FST (subst_consts_fields_mods E fs) = MAP FST fs /\
            MAP SND (subst_consts_fields_mods E fs) =
              subst_consts_exprs_mods E (MAP SND fs)` by
        (Induct >> simp[subst_consts_expr_mods_def] >>
         Cases >> simp[subst_consts_expr_mods_def]) >>
      simp_tac bool_ss [subst_consts_expr_mods_def, Ntimes evaluate_def 2,
        expr_type_def, LET_THM] >>
      asm_rewrite_tac[] >>
      irule const_computations_related_prefix >> reverse conj_tac
      >- (simp[const_computations_related_eq] >>
          ONCE_REWRITE_TAC[EQ_SYM_EQ] >>
          qpat_assum `!xs st. EVERY _ xs /\ _ ==> _`
            (qspecl_then [`MAP SND fields`,`s`] mp_tac) >>
          impl_tac >-
            (conj_tac
             >- (gvs[EVERY_MEM] >> rpt strip_tac >> res_tac) >>
             simp[] >> irule vyperTypeEvalCaseProofsTheory.well_typed_named_exprs_MAP_SND_stmt >>
             first_assum ACCEPT_TAC) >>
          simp[]) >>
      rpt strip_tac >> irule const_computations_related_refl >>
      simp[const_results_related_def])
  >>~- ([`eval_expr cx (TypeBuiltin _ _ _ _)`],
      qmatch_goalsub_rename_tac `eval_expr cx (TypeBuiltin ty bt target args)` >>
      fs[well_typed_expr_def] >>
      `eval_exprs cx (subst_consts_exprs_mods E args) s = eval_exprs cx args s` by
        (qpat_assum `!xs st. EVERY _ xs /\ _ ==> _` (qspecl_then [`args`,`s`] mp_tac) >>
         simp[] >> gvs[EVERY_MEM] >> rpt strip_tac >> res_tac) >>
      simp_tac bool_ss [subst_consts_expr_mods_def, Ntimes evaluate_def 2,
        expr_type_def] >>
      `MAP expr_type (subst_consts_exprs_mods E args) = MAP expr_type args` by fs[] >>
      asm_rewrite_tac[] >>
      irule const_computations_related_equal >>
      Cases_on `type_builtin_args_length_ok bt (LENGTH args)` >>
      fs[ignore_bind_def, type_check_def, assert_def, bind_def, raise_def,
         return_def, const_results_related_def])
  >>~- ([`eval_expr cx (Builtin _ _ _)`],
      qmatch_goalsub_rename_tac `eval_expr cx (Builtin ty bt args)` >>
      fs[well_typed_expr_def] >>
      `EVERY (runtime_constant_expr mods) args` by
        fs[EVERY_MEM, constant_expr_runtime_constant] >>
      `MAP expr_type (subst_consts_exprs_mods E args) = MAP expr_type args` by fs[] >>
      simp_tac bool_ss [subst_consts_expr_mods_def] >>
      PURE_ONCE_REWRITE_TAC [evaluate_def] >>
      asm_rewrite_tac[] >>
      Cases_on `builtin_args_length_ok bt (LENGTH args)` >> asm_rewrite_tac[]
      >- (`!e. assert T e = return ()` by simp[FUN_EQ_THM, assert_def, return_def] >>
          simp_tac bool_ss [ignore_bind_def, type_check_def, bind_return] >>
          asm_rewrite_tac[bind_return] >>
          Cases_on `bt = Len` >> asm_rewrite_tac[]
          >- (qpat_x_assum `bt = Len` SUBST_ALL_TAC >>
              `?arg. args = [arg]` by
                (Cases_on `args` >> fs[builtin_args_length_ok_def] >>
                 Cases_on `t` >> gvs[]) >>
              pop_assum SUBST_ALL_TAC >>
              fs[subst_consts_expr_mods_def, well_typed_expr_def, EVERY_DEF] >>
              simp_tac bool_ss [HD, GSYM vyperStateTheory.bind_assoc] >>
              irule const_computations_related_prefix >> reverse conj_tac
              >- (irule const_computations_related_prefix >> reverse conj_tac
                  >- (simp_tac bool_ss [SF ETA_ss] >>
                      irule const_computations_related_length >>
                      qexistsl [`expr_type arg`,`roots`] >> fs[] >>
                      rpt strip_tac >>
                      drule_all checked_eval_expr_const_cells_agree >> simp[]) >>
                  rpt strip_tac >> irule const_computations_related_refl >> simp[]) >>
              rpt strip_tac >> irule const_computations_related_refl >>
              simp[const_results_related_def]) >>
          Cases_on `bt = Env MsgGas` >> asm_rewrite_tac[]
          >- (irule const_computations_related_refl >> simp[const_results_related_def]) >>
          `!es. code_slice_source bt es = NONE` by
            (qx_gen_tac `argv` >> Cases_on `code_slice_source bt argv` >> simp[] >>
             rename1 `code_slice_source bt argv = SOME found` >>
             PairCases_on `found` >> fs[code_slice_source_SOME] >>
             gvs[runtime_constant_builtin_def, constant_builtin_def]) >>
          simp_tac bool_ss [] >>
          `!es. EVERY (runtime_constant_expr mods) es ==>
             ~is_self_codesize bt es /\
             ~is_self_codesize bt (subst_consts_exprs_mods E es)` by
            (qx_gen_tac `argv` >> Cases_on `bt` >> simp[is_self_codesize_def] >>
             Cases_on `a` >> simp[] >>
             Cases_on `argv` >> simp[subst_consts_expr_mods_def] >>
             Cases_on `t` >> simp[subst_consts_expr_mods_def] >>
             strip_tac >> res_tac >> simp[]) >>
          `~is_self_codesize bt args /\
             ~is_self_codesize bt (subst_consts_exprs_mods E args)` by
            (qpat_assum `!es. EVERY (runtime_constant_expr mods) es ==> _`
               (drule_then ACCEPT_TAC)) >>
          `eval_exprs cx (subst_consts_exprs_mods E args) s = eval_exprs cx args s` by
            (qpat_assum `!xs st. EVERY _ xs /\ _ ==> _` (qspecl_then [`args`,`s`] mp_tac) >>
             simp[] >> gvs[EVERY_MEM] >> rpt strip_tac >> res_tac) >>
          irule const_computations_related_equal >>
          simp[bind_def, const_results_related_def]) >>
      irule const_computations_related_equal >>
      simp[ignore_bind_def, type_check_def, assert_def, bind_def,
           const_results_related_def])
QED
