Theory createSizeRawObserved
Ancestors
  fragExec fragGasOrigin venomInst relation list words createMarkedPath pair arithmetic
  exprLowering vfmConstants createSizeItinerary rich_list context fragGasPath integer_word
  createCtorSegmentArrival createExprSizeExitDefs createSizePrefixReplay
  createSizeBlueprintRawScalars createSizeCtorValueRow createSizeObservedPrefix

Theorem raw_observed_ctor_coordinates[local]:
  n = LENGTH xs /\ create_itinerary_ctor_rows ce xs vals d k cs mid vv /\
  code = [sa;a;b;c;d] ++ create_itinerary_ctor_cuts cs mid n ++ suffix ==>
  LENGTH (create_itinerary_ctor_cuts cs mid n) = 2*n /\
  EL (4+2*n) code = k /\
  (!i. i <= n ==> EL (4+2*i) code = EL i cs) /\
  (!i. i < n ==> EL (SUC (4+2*i)) code = EL i mid)
Proof
  strip_tac >> qpat_x_assum `n = LENGTH xs` (assume_tac o SYM) >>
  qspecl_then [`n`,`\i. EL i mid`,`\i. EL (SUC i) cs`] (strip_assume_tac o BETA_RULE) raw_observed_pairs >>
  qpat_x_assum `create_itinerary_ctor_rows _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [createSizeItineraryTheory.create_itinerary_ctor_rows_def]) >>
  `EL 0 cs = d /\ EL n cs = k` by (Cases_on `cs` >> gvs[EL,LAST_EL]) >>
  qabbrev_tac `rows = create_itinerary_ctor_cuts cs mid n` >>
  `LENGTH rows = 2*n /\ (!i. i < n ==> EL (2*i) rows = EL i mid /\ EL (SUC (2*i)) rows = EL (SUC i) cs)` by
    simp[Abbr `rows`,createSizeItineraryTheory.create_itinerary_ctor_cuts_def] >>
  `!j. j < 2*n ==> EL (5+j) code = EL j rows` by
    (rpt strip_tac >> qpat_assum `code = _` (pure_rewrite_tac o single) >>
     pure_rewrite_tac [EL_APPEND_EQN] >> simp[]) >>
  `!i. i < n ==> EL (SUC (4+2*i)) code = EL i mid /\ EL (4+2*SUC i) code = EL (SUC i) cs` by
    (rpt strip_tac >>
     `SUC (4+2*i) = 5+2*i /\ 4+2*SUC i = 5+SUC (2*i)` by (simp[MULT_CLAUSES] >> decide_tac) >>
     `2*i < 2*n /\ SUC (2*i) < 2*n` by decide_tac >> metis_tac[]) >>
  `!i. i <= n ==> EL (4+2*i) code = EL i cs` by
    (Cases >- (qpat_assum `code = _` (pure_rewrite_tac o single) >> simp[]) >>
     strip_tac >> `n' < n` by decide_tac >> metis_tac[]) >>
  simp[] >>
  metis_tac[LESS_EQ_REFL]
QED

Theorem raw_observed_suffix_coordinates[local]:
  prep = rows ++ [ca;cb;cc;ce;cv] /\ LENGTH rows = 2*n /\
  code = [sa;a;b;c;d] ++ prep ++ [cq;sc] /\ p = 4+2*n ==>
  EL (p+1) code = ca /\ EL (p+2) code = cb /\ EL (p+3) code = cc /\
  EL (p+4) code = ce /\ EL (p+5) code = cv /\ EL (p+6) code = cq /\
  EL (p+7) code = sc
Proof
  strip_tac >> pure_asm_rewrite_tac [EL_APPEND_EQN,LENGTH_APPEND,LENGTH] >>
  rpt conj_tac >> simp[] >>
  rpt (IF_CASES_TAC >> fs[]) >> decide_tac
QED

Theorem create_raw_observed_bands:
  cuts = [a;b;c;d] ++ prep ++ [cq;sc] /\
  C = (\i. EL i (sa::cuts)) /\ Obs = (\i. EL i states) /\ M = (\i. EL i chunks0) /\
  n = LENGTH cuts /\ vpos = 4 + LENGTH prep /\
  HD states = s0 /\ LAST states = bad /\ ~s0.vs_halted /\
  LENGTH chunks0 = n /\ marks = FLAT chunks0 /\
  LIST_REL (\c s. s.vs_current_bb = c.cs_current_bb /\
                  s.vs_inst_idx = LENGTH c.cs_current_insts) (sa::cuts) states /\
  (!i. i < n ==> (C i).cs_next_id <= (C (SUC i)).cs_next_id /\ fn_has_code (C i) (C (SUC i)) fn /\
      create_expr_prefix (C i) (C (SUC i)) explicit ctx fn (Obs i) (M i) (Obs (SUC i))) /\
  ctor_segment_fetch fn bad = SOME dispatch /\ dispatch.inst_opcode <> PHI /\
  dispatch.inst_id = sc.cs_next_id /\
  emit_op ADD [snap;Lit 32w] c = (data,d) /\
  create_raw_prep_itinerary cenv xs cap data len d prep bufop size_op cv ==>
  Obs 0 = s0 /\ Obs n = bad /\
  (!i. i <= n ==> ~ (Obs i).vs_halted /\
    ((Obs i).vs_current_bb,(Obs i).vs_inst_idx) =
      ((C i).cs_current_bb,LENGTH (C i).cs_current_insts) /\
    ?j. ctor_segment_fetch fn (Obs i) = SOME j /\ j.inst_opcode <> PHI /\
       (C i).cs_next_id <= j.inst_id) /\
  (!i. i < n ==> FLAT (DROP i chunks0) = M i ++ FLAT (DROP (SUC i) chunks0)) /\
  marks = M 0 ++ M 1 ++ M 2 ++ M 3 ++ FLAT (DROP 4 chunks0) /\
  C 0 = sa /\ C 1 = a /\ C 2 = b /\ C 3 = c /\ C 4 = d /\
  C vpos = cv /\ C (SUC vpos) = cq /\ C n = sc /\
  create_expr_prefix sa a explicit ctx fn s0 (M 0) (Obs 1) /\
  create_expr_prefix a b explicit ctx fn (Obs 1) (M 1) (Obs 2) /\
  create_expr_prefix b c explicit ctx fn (Obs 2) (M 2) (Obs 3) /\
  create_expr_prefix c d explicit ctx fn (Obs 3) (M 3) (Obs 4) /\
  gas_origin_edge F explicit ctx fn (Obs 3) (M 3) (OK (Obs 4)) /\
  create_expr_prefix cv cq explicit ctx fn (Obs vpos) (M vpos) (Obs (SUC vpos)) /\
  create_expr_prefix cq sc explicit ctx fn (Obs (SUC vpos)) (M (SUC vpos)) bad /\
  FLAT (DROP vpos chunks0) = M vpos ++ M (SUC vpos) /\
  (cq = sc ==> Obs (SUC vpos) = bad /\ M (SUC vpos) = []) /\
  (if xs = [] then prep = [] /\ cv = d /\ size_op = len /\ bufop = data /\ Obs vpos = Obs 4
   else
   ?vals k cs mid vs buf ca cb dst cc alen ce p.
     compile_create_ctor_args compile_expr cenv xs d = (vals,k) /\
     create_itinerary_ctor_rows cenv xs vals d k cs mid vs /\
     compile_alloc_buffer cap k = (buf,ca) /\
     compile_copy_memory_dynamic buf.buf_operand data len ca = ((),cb) /\
     emit_op ADD [buf.buf_operand;len] cb = (dst,cc) /\
     compile_abi_encode_values_to_buf cenv dst (ZIP (vals,MAP (lowered_value_type cenv) xs)) cc = (alen,ce) /\
     emit_op ADD [len;alen] ce = (size_op,cv) /\ bufop = buf.buf_operand /\
     prep = create_itinerary_ctor_cuts cs mid (LENGTH xs) ++ [ca;cb;cc;ce;cv] /\
     p = 4+2*LENGTH xs /\ vpos = p+5 /\
     C p = k /\ C (p+1) = ca /\ C (p+2) = cb /\ C (p+3) = cc /\ C (p+4) = ce /\
     (!i. i <= LENGTH xs ==> C (4+2*i) = EL i cs) /\
     (!i. i < LENGTH xs ==>
       C (SUC (4+2*i)) = EL i mid /\
       create_expr_prefix (EL i cs) (EL i mid) explicit ctx fn
         (Obs (4+2*i)) (M (4+2*i)) (Obs (SUC (4+2*i))) /\
       create_expr_prefix (EL i mid) (EL (SUC i) cs) explicit ctx fn
         (Obs (SUC (4+2*i))) (M (SUC (4+2*i))) (Obs (4+2*SUC i)) /\
       create_expr_prefix (EL i cs) (EL (SUC i) cs) explicit ctx fn
         (Obs (4+2*i)) (M (4+2*i) ++ M (SUC (4+2*i))) (Obs (4+2*SUC i)) /\
       (Obs (4+2*SUC i)).vs_labels = (Obs (4+2*i)).vs_labels /\
       (EL i mid = EL (SUC i) cs ==>
        Obs (SUC (4+2*i)) = Obs (4+2*SUC i) /\ M (SUC (4+2*i)) = []) /\
       RTC (\u v. (u.vs_current_bb,u.vs_inst_idx) <>
               ((EL (SUC i) cs).cs_current_bb,LENGTH (EL (SUC i) cs).cs_current_insts) /\
         ?j ms. ctor_segment_fetch fn u = SOME j /\ (EL i mid).cs_next_id <= j.inst_id /\
           j.inst_id < (EL (SUC i) cs).cs_next_id /\ gas_origin_edge F explicit ctx fn u ms (OK v))
         (Obs (SUC (4+2*i))) (Obs (4+2*SUC i))) /\
     gas_origin_edge F explicit ctx fn (Obs p) (M p) (OK (Obs (p+1))) /\
     gas_origin_edge F explicit ctx fn (Obs (p+1)) (M (p+1)) (OK (Obs (p+2))) /\
     gas_origin_edge F explicit ctx fn (Obs (p+2)) (M (p+2)) (OK (Obs (p+3))) /\
     create_expr_prefix cc ce explicit ctx fn (Obs (p+3)) (M (p+3)) (Obs (p+4)) /\
     gas_origin_edge F explicit ctx fn (Obs (p+4)) (M (p+4)) (OK (Obs vpos)) /\
     (!j. j < 3 ==>
       (C (p+4+j)).cs_next_id <= (C (p+4+SUC j)).cs_next_id /\
       create_expr_prefix (C (p+4+j)) (C (p+4+SUC j)) explicit ctx fn
         (Obs (p+4+j)) (M (p+4+j)) (Obs (p+4+SUC j))))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `LENGTH states = SUC n /\ LENGTH (sa::cuts) = SUC n` by fs[LIST_REL_EL_EQN] >>
  `Obs 0 = s0 /\ Obs n = bad` by
    (Cases_on `states` >> gvs[EL,LAST_EL]) >>
  `n = LENGTH prep + 6` by
    (qpat_assum `n = LENGTH cuts` (pure_rewrite_tac o single) >> simp[] >> decide_tac) >>
  `n = SUC (SUC vpos)` by (fs[] >> decide_tac) >>
  `C 0 = sa /\ C 1 = a /\ C 2 = b /\ C 3 = c /\ C 4 = d` by fs[EL] >>
  `C (SUC vpos) = cq /\ C n = sc` by
    (qpat_assum `C = _` (pure_rewrite_tac o single) >> BETA_TAC >>
     `sa::cuts = ([sa;a;b;c;d] ++ prep) ++ [cq;sc]` by fs[] >>
     pop_assum (pure_rewrite_tac o single) >>
     `SUC vpos = LENGTH ([sa;a;b;c;d] ++ prep) /\
      n = SUC (LENGTH ([sa;a;b;c;d] ++ prep))` by (fs[] >> decide_tac) >>
     qpat_assum `SUC vpos = LENGTH _` (once_rewrite_tac o single) >>
     qpat_assum `n = SUC (LENGTH _)` (once_rewrite_tac o single) >>
     pure_rewrite_tac[EL_APPEND_EQN] >> simp[]) >>
  `ctor_segment_fetch fn (Obs n) = SOME dispatch /\ (C n).cs_next_id <= dispatch.inst_id` by metis_tac[LESS_EQ_REFL] >>
  `!i. i < n ==> (C i).cs_next_id <= (C (SUC i)).cs_next_id /\
      create_expr_prefix (C i) (C (SUC i)) explicit ctx fn (Obs i) (M i) (Obs (SUC i))` by metis_tac[] >>
  `~(Obs 0).vs_halted` by metis_tac[] >>
  drule_all raw_observed_spine >> strip_tac >>
  suspend "header"
QED

Resume create_raw_observed_bands[header]:
  `C vpos = cv` by
    (qpat_assum `create_raw_prep_itinerary _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [createSizeItineraryTheory.create_raw_prep_itinerary_def])
     >- (`vpos = 4` by fs[] >> metis_tac[]) >>
     qpat_assum `C = _` (pure_rewrite_tac o single) >> BETA_TAC >>
     qpat_assum `prep = _ ++ [_;_;_;_;_]` (fn th =>
       `sa::cuts = (([sa;a;b;c;d] ++ FRONT prep) ++ [cv;cq;sc])` by
        (simp[th,rich_listTheory.FRONT_APPEND_NOT_NIL,APPEND_ASSOC] >> fs[APPEND_ASSOC])) >>
     `vpos = LENGTH ([sa;a;b;c;d] ++ FRONT prep)` by
       (qpat_assum `prep = _ ++ [_;_;_;_;_]` (pure_rewrite_tac o single) >>
        fs[rich_listTheory.FRONT_APPEND_NOT_NIL] >> decide_tac) >>
     qpat_assum `sa::cuts = _` (pure_rewrite_tac o single) >>
     qpat_assum `vpos = LENGTH _` (once_rewrite_tac o single) >>
     pure_rewrite_tac[EL_APPEND_EQN] >> simp[]) >>
  `0<n /\ 1<n /\ 2<n /\ 3<n /\ vpos<n /\ SUC vpos<n /\ 3<=n /\ 4<=n` by decide_tac >>
  qpat_assum `!i. i < n ==> _ /\ fn_has_code _ _ _ /\ _`
    (fn th => map_every (fn q => qspec_then q
       (strip_assume_tac o SIMP_RULE arith_ss [] o UNDISCH) th)
       [`0`,`1`,`2`,`3`,`vpos`,`SUC vpos`]) >>
  `!i. i <= n ==> ((Obs i).vs_current_bb,(Obs i).vs_inst_idx) =
      ((C i).cs_current_bb,LENGTH (C i).cs_current_insts)` by metis_tac[] >>
  `gas_origin_edge F explicit ctx fn (Obs 3) (M 3) (OK (Obs 4))` by
    (irule raw_observed_prefix_emit >> qexistsl_tac [`c`,`d`,`ADD`,`[snap;Lit 32w]`,`data`] >>
     simp_tac (srw_ss()) [is_terminator_def] >>
     qpat_assum `!i. i <= n ==> _ = _` (fn th => map_every (fn q => qspec_then q
       (drule_then (strip_assume_tac o REWRITE_RULE [PAIR_EQ])) th) [`3`,`4`]) >>
     rpt conj_tac >> metis_tac[]) >>
  `marks = M 0 ++ M 1 ++ M 2 ++ M 3 ++ FLAT (DROP 4 chunks0) /\
   FLAT (DROP vpos chunks0) = M vpos ++ M (SUC vpos)` by
    (qpat_assum `!i. i < n ==> FLAT _ = _`
      (fn th => map_every (fn q => qspec_then q
         (assume_tac o SIMP_RULE arith_ss [] o UNDISCH) th) [`0`,`1`,`2`,`3`,`vpos`,`SUC vpos`]) >>
     `FLAT (DROP (SUC (SUC vpos)) chunks0) = []` by metis_tac[DROP_LENGTH_NIL,FLAT] >>
     conj_tac
     >- (qpat_assum `FLAT (DROP 0 chunks0) = _` (mp_tac o REWRITE_RULE [DROP_0]) >>
         pure_asm_rewrite_tac [APPEND_ASSOC] >> simp[]) >>
     pure_asm_rewrite_tac [APPEND_NIL] >> simp[]) >>
  `(cq = sc ==> Obs (SUC vpos) = bad /\ M (SUC vpos) = [])` by
    metis_tac[create_prefix_empty] >>
  (rpt conj_tac >>> SPLIT_LT ~1 (ALLGOALS (metis_tac[]), ALL_LT)) >>
  suspend "prep"
QED

Resume create_raw_observed_bands[prep]:
  qpat_x_assum `create_raw_prep_itinerary _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [createSizeItineraryTheory.create_raw_prep_itinerary_def])
  >- (`vpos = 4` by fs[] >> simp[]) >>
  qpat_assum `xs <> []` (fn th => simp_tac bool_ss [th]) >>
  rename1 `compile_create_ctor_args compile_expr cenv xs d = (vals,k)` >>
  rename1 `create_itinerary_ctor_rows cenv xs vals d k cs mid vs` >>
  rename1 `compile_alloc_buffer cap k = (buf,ca)` >>
  rename1 `compile_copy_memory_dynamic buf.buf_operand data len ca = ((),cb)` >>
  rename1 `emit_op ADD [buf.buf_operand;len] cb = (dst,cc)` >>
  rename1 `emit_op ADD [len;alen] ce = (size_op,cv)` >>
  qabbrev_tac `rows = create_itinerary_ctor_cuts cs mid (LENGTH xs)` >>
  `sa::cuts = [sa;a;b;c;d] ++ rows ++ ([ca;cb;cc;ce;cv] ++ [cq;sc])` by fs[APPEND_ASSOC] >>
  `LENGTH rows = 2*LENGTH xs /\ C (4+2*LENGTH xs) = k /\
   (!i. i <= LENGTH xs ==> C (4+2*i) = EL i cs) /\
   (!i. i < LENGTH xs ==> C (SUC (4+2*i)) = EL i mid)` by
    (qpat_assum `C = _` (pure_rewrite_tac o single) >> BETA_TAC >>
     UNABBREV_ALL_TAC >>
     `LENGTH xs = LENGTH xs` by simp[] >>
     drule_all raw_observed_ctor_coordinates >> simp[]) >>
  `LENGTH prep = 2*LENGTH xs+5` by
    (qpat_assum `prep = rows ++ _` (pure_rewrite_tac o single) >> simp[]) >>
  qabbrev_tac `p = 4+2*LENGTH xs` >>
  `vpos = p+5 /\ n = p+7` by (simp[Abbr `p`] >> decide_tac) >>
  `C (p+1) = ca /\ C (p+2) = cb /\ C (p+3) = cc /\ C (p+4) = ce` by
    (qpat_assum `C = _` (pure_rewrite_tac o single) >> BETA_TAC >>
     `sa::cuts = [sa;a;b;c;d] ++ prep ++ [cq;sc]` by fs[] >>
     `p = 4+2*LENGTH xs` by simp[Abbr `p`] >>
     drule_all raw_observed_suffix_coordinates >>
     disch_then (map_every assume_tac o CONJUNCTS) >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`vals`,`cs`,`mid`,`vs`,`buf`,`dst`,`alen`] >>
  map_every (fn q => qpat_assum q (pure_rewrite_tac o single))
    [`C p = k`,`C (p+1) = ca`,`C (p+2) = cb`,`C (p+3) = cc`,`C (p+4) = ce`] >>
  rpt (conj_tac >- (first_assum ACCEPT_TAC ORELSE
       (rename1 `prep = _ ++ _` >> simp[Abbr `rows`]))) >>
  conj_tac
  >- (suspend "rows") >>
  suspend "fixed"
QED

Resume create_raw_observed_bands[rows]:
  gen_tac >> disch_tac >>
  `4+2*SUC i = SUC (SUC (4+2*i))` by (simp[MULT_CLAUSES] >> decide_tac) >>
  `4+2*i < n /\ SUC (4+2*i) < n /\ i <= LENGTH xs /\ SUC i <= LENGTH xs` by
    (simp[Abbr `p`] >> decide_tac) >>
  qpat_assum `!i. i <= LENGTH xs ==> C _ = _`
    (fn th => map_every (fn q => qspec_then q (drule_then assume_tac) th) [`i`,`SUC i`]) >>
  qpat_assum `!i. i < LENGTH xs ==> C _ = _` (drule_then assume_tac) >>
  qpat_assum `!i. i < n ==> _ /\ fn_has_code _ _ _ /\ _`
    (fn th => map_every (fn q => qspec_then q (drule_then strip_assume_tac) th)
      [`4+2*i`,`SUC (4+2*i)`]) >>
  qpat_assum `!i. SUC i < n ==> _` (qspec_then `4+2*i` (drule_then assume_tac)) >>
  metis_tac[create_prefix_labels,create_prefix_empty,blueprint_ctor_segment_rtc]
QED

Resume create_raw_observed_bands[fixed]:
  `!j. j < 5 ==> fn_has_code (C (p+j)) (C (p+j+1)) fn /\
    ((Obs (p+j)).vs_current_bb,(Obs (p+j)).vs_inst_idx) =
      ((C (p+j)).cs_current_bb,LENGTH (C (p+j)).cs_current_insts) /\
    ((Obs (p+j+1)).vs_current_bb,(Obs (p+j+1)).vs_inst_idx) =
      ((C (p+j+1)).cs_current_bb,LENGTH (C (p+j+1)).cs_current_insts) /\
    create_expr_prefix (C (p+j)) (C (p+j+1)) explicit ctx fn
      (Obs (p+j)) (M (p+j)) (Obs (p+j+1))` by
    (gen_tac >> disch_tac >>
     `p+j < n /\ p+j <= n /\ p+j+1 <= n /\ SUC (p+j) = p+j+1` by decide_tac >>
     qpat_assum `!i. i <= n ==> _ = _` (fn th => map_every (fn q => qspec_then q
       (drule_then assume_tac) th) [`p+j`,`p+j+1`]) >>
     qpat_assum `!i. i < n ==> _ /\ fn_has_code _ _ _ /\ _`
       (qspec_then `p+j` (drule_then strip_assume_tac)) >>
     rpt conj_tac >> metis_tac[]) >>
  `0<5 /\ 1<5 /\ 2<5 /\ 3<5 /\ 4<5` by decide_tac >>
  qpat_assum `!j. j < 5 ==> _` (fn th => map_every (fn q => qspec_then q
    (strip_assume_tac o SIMP_RULE arith_ss [] o UNDISCH) th) [`0`,`1`,`2`,`3`,`4`]) >>
  `C (p+5) = cv` by metis_tac[] >>
  rpt conj_tac
  >- (irule raw_observed_prefix_alloc >> qexistsl_tac [`k`,`ca`] >>
      goal_assum (drule_at Any) >> simp_tac bool_ss [PAIR_EQ] >> rpt conj_tac >> metis_tac[])
  >- (irule raw_observed_prefix_copy >> qexistsl_tac [`ca`,`cb`] >>
      goal_assum (drule_at Any) >> simp_tac bool_ss [PAIR_EQ] >> rpt conj_tac >> metis_tac[])
  >- (irule raw_observed_prefix_emit >> qexistsl_tac [`cb`,`cc`,`ADD`,`[buf.buf_operand;len]`,`dst`] >>
      simp_tac (srw_ss()) [is_terminator_def] >> rpt conj_tac >> metis_tac[PAIR_EQ])
  >- metis_tac[]
  >- (irule raw_observed_prefix_emit >> qexistsl_tac [`ce`,`cv`,`ADD`,`[len;alen]`,`size_op`] >>
      simp_tac (srw_ss()) [is_terminator_def] >> rpt conj_tac >> metis_tac[PAIR_EQ]) >>
  gen_tac >> disch_tac >>
  `p+4+j < n /\ p+4+SUC j = SUC (p+4+j)` by decide_tac >>
  qpat_assum `!i. i < n ==> _ /\ create_expr_prefix _ _ _ _ _ _ _ _`
    (qspec_then `p+4+j` (drule_then strip_assume_tac)) >>
  metis_tac[]
QED

Finalise create_raw_observed_bands
