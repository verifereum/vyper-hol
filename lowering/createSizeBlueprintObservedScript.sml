Theory createSizeBlueprintObserved
Ancestors
  fragExec relation list words pair arithmetic vfmConstants compileEnv createSizeItinerary
  exprLoweringProps rich_list integer_word createCtorSegmentArrival createExprSizeExitDefs
  createSizeCopyReplay createSizeObservedPrefix

Theorem blueprint_preparation_coordinates[local]:
  create_blueprint_args_itinerary ce raw later ctors ca prep data len b /\
  cuts = ca :: (prep ++ [c;d;e;f] ++ app) /\
  j = SUC (LENGTH prep) ==>
  EL j (sa::cuts) = b /\ EL (SUC j) (sa::cuts) = c /\
  EL (j+2) (sa::cuts) = d /\ EL (j+3) (sa::cuts) = e /\
  EL (j+4) (sa::cuts) = f /\ DROP (j+4) cuts = app
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `LAST (ca::prep) = b` by
    (qpat_assum `create_blueprint_args_itinerary _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [create_blueprint_args_itinerary_def]) >>
     fs[LAST_CONS_cond]) >>
  `sa::cuts = ([sa;ca] ++ prep) ++ ([c;d;e;f] ++ app)` by simp[APPEND_ASSOC] >>
  `SUC j = LENGTH ([sa;ca] ++ prep)` by simp[] >>
  `j+4 = LENGTH (ca::(prep ++ [c;d;e;f]))` by simp[] >>
  conj_tac
  >- (`EL (LENGTH prep) (ca::prep) = b` by
        (qspec_then `ca::prep` mp_tac LAST_EL >> simp[]) >>
      `cuts = (ca::prep) ++ ([c;d;e;f] ++ app)` by simp[] >>
      qpat_assum `j = SUC _` (pure_rewrite_tac o single) >>
      rewrite_tac[EL,TL] >> pop_assum (pure_once_rewrite_tac o single) >>
      simp[EL_APPEND1]) >>
  conj_tac
  >- (qpat_assum `sa::cuts = _` (pure_rewrite_tac o single) >>
      qpat_assum `SUC j = LENGTH _` (pure_once_rewrite_tac o single) >>
      pure_once_rewrite_tac[EL_APPEND_EQN] >> simp[]) >>
  `j+2 = LENGTH ([sa;ca] ++ prep)+1 /\ j+3 = LENGTH ([sa;ca] ++ prep)+2 /\
   j+4 = LENGTH ([sa;ca] ++ prep)+3` by decide_tac >>
  map_every (fn q => conj_tac >-
    (qpat_assum `sa::cuts = _` (pure_rewrite_tac o single) >>
     qpat_assum q (pure_once_rewrite_tac o single) >>
     pure_once_rewrite_tac[EL_APPEND_EQN] >> simp[EL]))
    [`j+2 = LENGTH _ + 1`,`j+3 = LENGTH _ + 2`,`j+4 = LENGTH _ + 3`] >>
  qpat_assum `j+4 = LENGTH _` (pure_rewrite_tac o single) >>
  `cuts = (ca::(prep ++ [c;d;e;f])) ++ app` by simp[APPEND_ASSOC] >>
  pop_assum (pure_once_rewrite_tac o single) >> pure_rewrite_tac[DROP_LENGTH_APPEND] >> REFL_TAC
QED

Theorem blueprint_ctor_observed_coordinates[local]:
  create_itinerary_ctor_rows ce ctors vals ca k cs mid vv /\
  prep = create_itinerary_ctor_cuts cs mid (LENGTH ctors) ++ [a;b] /\
  code = sa::ca::(prep ++ suffix) /\ p = 1+2*LENGTH ctors ==>
  LENGTH prep = 2*LENGTH ctors+2 /\
  EL p code = k /\ EL (SUC p) code = a /\ EL (p+2) code = b /\
  (!i. i <= LENGTH ctors ==> EL (1+2*i) code = EL i cs) /\
  (!i. i < LENGTH ctors ==> EL (SUC (1+2*i)) code = EL i mid)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `n = LENGTH ctors` >>
  qabbrev_tac `rows = create_itinerary_ctor_cuts cs mid n` >>
  qspecl_then [`n`,`\i. EL i mid`,`\i. EL (SUC i) cs`] (strip_assume_tac o BETA_RULE) raw_observed_pairs >>
  `LENGTH rows = 2*n /\ (!i. i < n ==> EL (2*i) rows = EL i mid /\ EL (SUC (2*i)) rows = EL (SUC i) cs)` by
    simp[Abbr `rows`,create_itinerary_ctor_cuts_def] >>
  qpat_x_assum `create_itinerary_ctor_rows _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [create_itinerary_ctor_rows_def]) >>
  `EL 0 cs = ca /\ EL n cs = k` by (Cases_on `cs` >> gvs[EL,LAST_EL]) >>
  `code = [sa;ca] ++ rows ++ [a;b] ++ suffix` by fs[APPEND_ASSOC] >>
  `!i. i < 2*n ==> EL (SUC (SUC i)) code = EL i rows` by
    (rpt strip_tac >> pop_assum mp_tac >> simp[EL,EL_APPEND_EQN]) >>
  `!i. i < n ==> EL (SUC (1+2*i)) code = EL i mid /\ EL (1+2*SUC i) code = EL (SUC i) cs` by
    (rpt strip_tac >>
     `1+2*SUC i = SUC (SUC (SUC (2*i)))` by (simp[MULT_CLAUSES] >> decide_tac) >>
     `SUC (1+2*i) = SUC (SUC (2*i)) /\ 2*i < 2*n /\ SUC (2*i) < 2*n` by decide_tac >>
     metis_tac[]) >>
  `!i. i <= n ==> EL (1+2*i) code = EL i cs` by
    (Cases >- simp[EL] >> strip_tac >> `n' < n` by decide_tac >> metis_tac[]) >>
  `SUC p = LENGTH ([sa;ca] ++ rows) /\ p+2 = LENGTH ([sa;ca] ++ rows)+1` by
    (simp[] >> decide_tac) >>
  `code = ([sa;ca] ++ rows) ++ a::b::suffix` by simp[APPEND_ASSOC] >>
  conj_tac >- simp[] >>
  conj_tac >- metis_tac[LESS_EQ_REFL] >>
  conj_tac
  >- (pop_assum (pure_rewrite_tac o single) >>
      qpat_assum `SUC p = LENGTH _` (pure_once_rewrite_tac o single) >>
      pure_rewrite_tac[EL_LENGTH_APPEND_0] >> REFL_TAC) >>
  conj_tac
  >- (pop_assum (pure_rewrite_tac o single) >>
      qpat_assum `p+2 = LENGTH _ + 1` (pure_once_rewrite_tac o single) >>
      pure_rewrite_tac[EL_LENGTH_APPEND_1] >> REFL_TAC) >>
  metis_tac[]
QED

(* The case-specific coordinates are projections of one observed traversal.
   In particular, M is indexed by edges, while C and Obs index vertices. *)
Theorem create_blueprint_observed_bands:
  cuts = ca :: (prep ++ [c;d;e;f] ++ app) /\
  create_blueprint_args_itinerary ce raw later ctors ca prep data len b /\
  create_itinerary_code sa cuts sc /\ cs_extends sc sb /\ fn_has_code sa sb fn /\
  C = (\i. EL i (sa::cuts)) /\ Obs = (\i. EL i states) /\ M = (\i. EL i chunks0) /\
  R = (\i. FLAT (DROP i chunks0)) /\ n = LENGTH cuts /\ j = SUC (LENGTH prep) /\
  HD states = s0 /\ LAST states = s /\ ~s0.vs_halted /\
  LENGTH chunks0 = n /\ marks = FLAT chunks0 /\
  LIST_REL (\c u. u.vs_current_bb = c.cs_current_bb /\
                  u.vs_inst_idx = LENGTH c.cs_current_insts) (sa::cuts) states /\
  (!i. i < n ==> create_expr_prefix (C i) (C (SUC i)) explicit ctx fn
                   (Obs i) (M i) (Obs (SUC i))) /\
  ctor_segment_fetch fn s = SOME dispatch /\ dispatch.inst_opcode <> PHI /\
  dispatch.inst_id = sc.cs_next_id ==>
  C 0 = sa /\ C 1 = ca /\ C j = b /\ C (SUC j) = c /\ C (j+2) = d /\
  C (j+3) = e /\ C (j+4) = f /\ C n = sc /\ j+4 <= n /\ DROP (j+4) cuts = app /\
  Obs 0 = s0 /\ Obs n = s /\ R n = [] /\ marks = M 0 ++ R 1 /\
  create_expr_prefix sa ca explicit ctx fn s0 (M 0) (Obs 1) /\
  (!i. i <= n ==> ~(Obs i).vs_halted /\
    (Obs i).vs_current_bb = (C i).cs_current_bb /\
    (Obs i).vs_inst_idx = LENGTH (C i).cs_current_insts /\
    ?x. ctor_segment_fetch fn (Obs i) = SOME x /\ x.inst_opcode <> PHI /\
        (C i).cs_next_id <= x.inst_id) /\
  (!i k. i <= k /\ k <= n ==> ci_mono (C i) (C k) /\ fn_has_code (C i) (C k) fn) /\
  (!i. i < n ==> (C i).cs_next_id <= (C (SUC i)).cs_next_id /\
    create_expr_prefix (C i) (C (SUC i)) explicit ctx fn (Obs i) (M i) (Obs (SUC i)) /\
    R i = M i ++ R (SUC i) /\
    (C i = C (SUC i) ==> Obs (SUC i) = Obs i /\ M i = [])) /\
  (!i. SUC i < n ==> create_expr_prefix (C i) (C (SUC (SUC i))) explicit ctx fn
    (Obs i) (M i ++ M (SUC i)) (Obs (SUC (SUC i)))) /\
  (!cm cs cu cl. prep = [cm;cs;cu;cl;b] ==>
    j = 6 /\ C 2 = cm /\ C 3 = cs /\ C 4 = cu /\ C 5 = cl /\
    R 1 = M 1 ++ (M 2 ++ (M 3 ++ (M 4 ++ M 5 ++ R j)))) /\
  (~raw /\ ctors = [] ==> prep = [] /\ j = 1 /\ b = ca) /\
  (!vals k cs mid vv a p.
    create_itinerary_ctor_rows ce ctors vals ca k cs mid vv /\
    prep = create_itinerary_ctor_cuts cs mid (LENGTH ctors) ++ [a;b] /\
    p = 1+2*LENGTH ctors ==>
    j = p+2 /\ C p = k /\ C (SUC p) = a /\ R p = M p ++ M (SUC p) ++ R j /\
    (!i. i <= LENGTH ctors ==> C (1+2*i) = EL i cs) /\
    (!i. i < LENGTH ctors ==> C (SUC (1+2*i)) = EL i mid /\
      R (1+2*i) = (M (1+2*i) ++ M (SUC (1+2*i))) ++ R (1+2*SUC i) /\
      create_expr_prefix (EL i cs) (EL (SUC i) cs) explicit ctx fn
        (Obs (1+2*i)) (M (1+2*i) ++ M (SUC (1+2*i))) (Obs (1+2*SUC i))))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `LENGTH states = SUC n /\ LENGTH (sa::cuts) = SUC n` by fs[LIST_REL_EL_EQN] >>
  `Obs 0 = s0 /\ Obs n = s` by (Cases_on `states` >> gvs[EL,LAST_EL]) >>
  `C 0 = sa /\ C 1 = ca` by fs[EL] >>
  `C n = sc` by
    (drule create_itinerary_code_relations >> strip_tac >>
     qpat_assum `C = _` (pure_rewrite_tac o single) >>
     qspec_then `sa::cuts` mp_tac LAST_EL >> simp[]) >>
  `j+4 <= n /\ 0 < n` by
    (`n = LENGTH prep + LENGTH app + 5` by (simp[] >> decide_tac) >> decide_tac) >>
  `C j = b /\ C (SUC j) = c /\ C (j+2) = d /\ C (j+3) = e /\
   C (j+4) = f /\ DROP (j+4) cuts = app` by
    (qpat_assum `C = _` (pure_rewrite_tac o single) >> BETA_TAC >>
     drule_all blueprint_preparation_coordinates >> disch_then (qspec_then `sa` ACCEPT_TAC)) >>
  pop_assum strip_assume_tac >>
  `!i k. i <= k /\ k <= n ==> ci_mono (C i) (C k)` by
    (drule create_itinerary_index_mono >> fs[]) >>
  `!i k. i <= k /\ k <= n ==> fn_has_code (C i) (C k) fn` by
    (rpt gen_tac >> strip_tac >>
     `ci_mono (C 0) (C i) /\ ci_mono (C i) (C k) /\ ci_mono (C k) (C n)` by
       (rpt conj_tac >> first_assum irule >> decide_tac) >>
     map_every (fn q => qpat_x_assum q (strip_assume_tac o REWRITE_RULE [ci_mono_def]))
       [`ci_mono (C 0) (C i)`,`ci_mono (C i) (C k)`,`ci_mono (C k) (C n)`] >>
     `cs_extends (C k) sb` by metis_tac[cs_extends_trans] >>
     irule fn_has_code_mid >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`sb`,`sa`] >> metis_tac[]) >>
  `!i. i < n ==> (C i).cs_next_id <= (C (SUC i)).cs_next_id /\
      create_expr_prefix (C i) (C (SUC i)) explicit ctx fn (Obs i) (M i) (Obs (SUC i))` by
    (rpt gen_tac >> disch_tac >> conj_tac
     >- (`ci_mono (C i) (C (SUC i))` by (first_assum irule >> decide_tac) >>
         qpat_assum `ci_mono (C i) (C (SUC i))` (ACCEPT_TAC o cj 3 o REWRITE_RULE[ci_mono_def])) >>
     first_assum irule >> first_assum ACCEPT_TAC) >>
  `~(Obs 0).vs_halted /\ ctor_segment_fetch fn (Obs n) = SOME dispatch /\
     (C n).cs_next_id <= dispatch.inst_id` by simp[] >>
  drule_all raw_observed_spine >> strip_tac >>
  suspend "project"
QED

Resume create_blueprint_observed_bands[project]:
  `!i. i < n ==> R i = M i ++ R (SUC i)` by simp[] >>
  `!i. i <= n ==> ~(Obs i).vs_halted /\
    (Obs i).vs_current_bb = (C i).cs_current_bb /\
    (Obs i).vs_inst_idx = LENGTH (C i).cs_current_insts /\
    ?x. ctor_segment_fetch fn (Obs i) = SOME x /\ x.inst_opcode <> PHI /\
        (C i).cs_next_id <= x.inst_id` by fs[PAIR_EQ] >>
  `R 0 = marks` by
    (qpat_assum `R = _` (pure_rewrite_tac o single) >> BETA_TAC >>
     pure_rewrite_tac[DROP_0] >> qpat_assum `marks = FLAT _` (ACCEPT_TAC o SYM)) >>
  `marks = M 0 ++ R 1` by
    (qpat_assum `!i. i < n ==> R i = _` (qspec_then `0` (drule_then mp_tac)) >>
     pure_rewrite_tac[arithmeticTheory.ONE] >>
     qpat_assum `R 0 = marks` (pure_rewrite_tac o single) >> simp_tac bool_ss []) >>
  `create_expr_prefix sa ca explicit ctx fn s0 (M 0) (Obs 1)` by
    (qpat_assum `!i. i < n ==> create_expr_prefix _ _ _ _ _ _ _ _`
       (qspec_then `0` (drule_then mp_tac)) >>
     pure_rewrite_tac [GSYM arithmeticTheory.ONE] >>
     map_every (fn q => qpat_assum q (pure_rewrite_tac o single))
       [`C 0 = sa`,`C 1 = ca`,`Obs 0 = s0`] >> simp_tac bool_ss []) >>
  `!i. i < n /\ C i = C (SUC i) ==> Obs (SUC i) = Obs i /\ M i = []` by
    (rpt gen_tac >> strip_tac >> `i <= n` by decide_tac >>
     qpat_assum `!i. i <= n ==> _ /\ _` (drule_then strip_assume_tac) >>
     qpat_assum `!i. i < n ==> create_expr_prefix _ _ _ _ _ _ _ _`
       (drule_then assume_tac) >> metis_tac[create_copy_empty_cut]) >>
  `R n = []` by
    (qpat_assum `R = _` (pure_rewrite_tac o single) >> BETA_TAC >>
     qpat_assum `LENGTH chunks0 = n` (pure_rewrite_tac o single o SYM) >> simp[]) >>
  ntac 19 (conj_tac >-
    (TRY (first_assum ACCEPT_TAC) >>
     rpt gen_tac >> disch_tac >> rpt conj_tac >> metis_tac[])) >>
  suspend "modes"
QED

Resume create_blueprint_observed_bands[modes]:
  conj_tac
  >- (rpt gen_tac >> disch_tac >>
      `j = 6 /\ C 2 = cm /\ C 3 = cs /\ C 4 = cu /\ C 5 = cl` by simp[EL] >>
      `1<n /\ 2<n /\ 3<n /\ 4<n /\ 5<n` by decide_tac >>
      qpat_assum `!i. i < n ==> R i = _`
        (fn th => map_every (fn q => qspec_then q
          (drule_then (assume_tac o SIMP_RULE (srw_ss()) [])) th) [`1`,`2`,`3`,`4`,`5`]) >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
      qpat_assum `j = 6` (pure_rewrite_tac o single) >>
      map_every (fn q => qpat_assum q (pure_rewrite_tac o single))
        [`R 1 = _`,`R 2 = _`,`R 3 = _`,`R 4 = _`,`R 5 = _`] >> simp_tac bool_ss [APPEND_ASSOC]) >>
  conj_tac
  >- (disch_tac >>
      qpat_assum `create_blueprint_args_itinerary _ _ _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [create_blueprint_args_itinerary_def]) >> simp[]) >>
  suspend "ctor"
QED

Resume create_blueprint_observed_bands[ctor]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `LENGTH prep = 2*LENGTH ctors+2 /\ C p = k /\ C (SUC p) = a /\
   (!i. i <= LENGTH ctors ==> C (1+2*i) = EL i cs) /\
   (!i. i < LENGTH ctors ==> C (SUC (1+2*i)) = EL i mid)` by
    (qpat_assum `C = _` (pure_rewrite_tac o single) >> BETA_TAC >>
     `sa::cuts = sa::ca::(prep ++ ([c;d;e;f] ++ app))` by simp[APPEND_ASSOC] >>
     drule_all blueprint_ctor_observed_coordinates >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  `j = p+2 /\ p < n /\ SUC p < n /\ j = SUC (SUC p)` by decide_tac >>
  `R p = M p ++ M (SUC p) ++ R j` by
    (qpat_assum `!i. i < n ==> R i = _`
       (fn th => map_every (fn q => qspec_then q (drule_then assume_tac) th) [`p`,`SUC p`]) >>
     metis_tac[APPEND_ASSOC]) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  gen_tac >> disch_tac >>
  `1+2*SUC i = SUC (SUC (1+2*i))` by (simp[MULT_CLAUSES] >> decide_tac) >>
  `i <= LENGTH ctors /\ SUC i <= LENGTH ctors /\ 1+2*i < n /\ SUC (1+2*i) < n` by decide_tac >>
  qpat_assum `!i. i <= LENGTH ctors ==> C _ = _`
    (fn th => map_every (fn q => qspec_then q (drule_then assume_tac) th) [`i`,`SUC i`]) >>
  qpat_assum `!i. i < LENGTH ctors ==> C _ = _` (drule_then assume_tac) >>
  qpat_assum `!i. i < n ==> R i = _`
    (fn th => map_every (fn q => qspec_then q (drule_then assume_tac) th)
      [`1+2*i`,`SUC (1+2*i)`]) >>
  qpat_assum `!i. SUC i < n ==> create_expr_prefix _ _ _ _ _ _ _ _`
    (qspec_then `1+2*i` (drule_then assume_tac)) >>
  rpt conj_tac >> metis_tac[APPEND_ASSOC]
QED

Finalise create_blueprint_observed_bands
