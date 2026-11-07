Theory bodyPtrPopLiveStep
Ancestors bodyPtrPopLiveSupport bodyPtrPopPathStep pred_set list arithmetic
  vyperValueOperation loweringPosts valueEncodingProofs vyperTyping vyperState

Theorem pop_indexed_support_extract:
  j < n /\
  (!i. i < n ==> supp i SUBSET {x | off i <= x /\ x < off i + sz i}) /\
  (!i. i < n /\ i <> j ==>
     off i + sz i <= off j \/ off j + sz j <= off i) ==>
  supp j SUBSET BIGUNION {supp i | i < n} /\
  DISJOINT ((BIGUNION {supp i | i < n}) DIFF supp j)
    {x | off j <= x /\ x < off j + sz j}
Proof
  strip_tac >> conj_tac
  >- (simp[SUBSET_DEF, IN_BIGUNION] >> metis_tac[]) >>
  simp[DISJOINT_DEF, EXTENSION, IN_BIGUNION] >> rpt strip_tac >>
  spose_not_then strip_assume_tac >> gvs[] >>
  rename1 `x IN supp i` >>
  `i <> j` by metis_tac[] >>
  `off i <= x /\ x < off i + sz i` by
    (qpat_x_assum `!i. i < n ==> _` drule >> simp[SUBSET_DEF]) >>
  first_x_assum drule_all >> decide_tac
QED

Theorem pop_prefix_window_before:
  !xs i j f. j < LENGTH xs /\ i < j ==>
    SUM (MAP f (TAKE i xs)) + f (EL i xs) <= SUM (MAP f (TAKE j xs))
Proof
  Induct_on `xs` >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `j` >> gvs[] >> Cases_on `i` >> simp[] >>
  first_x_assum irule >> simp[]
QED

Theorem pop_prefix_windows_apart:
  i < LENGTH xs /\ j < LENGTH xs /\ i <> j ==>
  SUM (MAP f (TAKE i xs)) + f (EL i xs) <= SUM (MAP f (TAKE j xs)) \/
  SUM (MAP f (TAKE j xs)) + f (EL j xs) <= SUM (MAP f (TAKE i xs))
Proof
  strip_tac >> Cases_on `i < j` >>
  metis_tac[pop_prefix_window_before, arithmeticTheory.NOT_LESS,
    arithmeticTheory.LESS_OR_EQ]
QED

Theorem pop_stride_support_extract:
  j < n /\
  (!i. i < n ==> pop_live_support tv (v i)
    (addr+i*type_memory_size tv) (supp i)) ==>
  supp j SUBSET BIGUNION {supp i | i < n} /\
  DISJOINT ((BIGUNION {supp i | i < n}) DIFF supp j)
    {x | addr+j*type_memory_size tv <= x /\
         x < addr+j*type_memory_size tv+type_memory_size tv}
Proof
  strip_tac >> irule (BETA_RULE $ Q.INST [`off` |-> `\i. addr+i*type_memory_size tv`,
    `sz` |-> `\i. type_memory_size tv`] (SPEC_ALL pop_indexed_support_extract)) >>
  simp[] >> reverse conj_tac
  >- (rpt strip_tac >> first_x_assum drule >>
      disch_then (mp_tac o MATCH_MP pop_live_support_bounds) >>
      simp[AC ADD_ASSOC ADD_COMM]) >>
  rpt strip_tac >> drule pop_stride_intervals_apart >>
  disch_then (qspec_then `type_memory_size tv` mp_tac) >> decide_tac
QED

Theorem pop_prefix_support_extract:
  j < LENGTH tvs /\
  (!i. i < LENGTH tvs ==> pop_live_support (EL i tvs) (v i)
    (addr+SUM (MAP type_memory_size (TAKE i tvs))) (supp i)) ==>
  supp j SUBSET BIGUNION {supp i | i < LENGTH tvs} /\
  DISJOINT ((BIGUNION {supp i | i < LENGTH tvs}) DIFF supp j)
    {x | addr+SUM (MAP type_memory_size (TAKE j tvs)) <= x /\
         x < addr+SUM (MAP type_memory_size (TAKE j tvs))+type_memory_size (EL j tvs)}
Proof
  strip_tac >> irule (BETA_RULE $ Q.INST
    [`off` |-> `\i. addr+SUM (MAP type_memory_size (TAKE i tvs))`,
     `sz` |-> `\i. type_memory_size (EL i tvs)`] (SPEC_ALL pop_indexed_support_extract)) >>
  simp[] >> reverse conj_tac
  >- (rpt strip_tac >> first_x_assum drule >>
      disch_then (mp_tac o MATCH_MP pop_live_support_bounds) >> simp[]) >>
  rpt strip_tac >> drule_all pop_prefix_windows_apart >>
  disch_then (qspec_then `type_memory_size` mp_tac) >> decide_tac
QED

Theorem pop_fields_selected_index:
  !fts fields fld child k ct.
  struct_has_type fts fields /\ ALOOKUP fields fld = SOME child /\
  mem_field_offset fts fld = SOME (k,ct) ==>
  ?j. j < LENGTH fts /\ ct = SND (EL j fts) /\ child = SND (EL j fields) /\
      k = SUM (MAP (type_memory_size o SND) (TAKE j fts))
Proof
  Induct_on `fts` >> simp[mem_field_offset_def] >>
  PairCases >> Cases_on `fields` >> simp[value_has_type_def] >>
  PairCases_on `h` >>
  simp[value_has_type_def, mem_field_offset_def] >> rpt strip_tac >>
  Cases_on `h0 = fld` >> gvs[AllCaseEqs()]
  >- (qexists_tac `0` >> simp[]) >>
  PairCases_on `z` >> gvs[] >> first_x_assum drule_all >>
  strip_tac >> qexists_tac `SUC j` >> simp[]
QED

Theorem pop_fields_support_extract:
  j < LENGTH fts /\
  (!i. i < LENGTH fts ==> pop_live_support (SND (EL i fts)) (SND (EL i fields))
    (addr+SUM (MAP (type_memory_size o SND) (TAKE i fts))) (supp i)) ==>
  supp j SUBSET BIGUNION {supp i | i < LENGTH fts} /\
  DISJOINT ((BIGUNION {supp i | i < LENGTH fts}) DIFF supp j)
    {x | addr+SUM (MAP (type_memory_size o SND) (TAKE j fts)) <= x /\
         x < addr+SUM (MAP (type_memory_size o SND) (TAKE j fts))+type_memory_size (SND (EL j fts))}
Proof
  strip_tac >> irule (BETA_RULE $ Q.INST
    [`off` |-> `\i. addr+SUM (MAP (type_memory_size o SND) (TAKE i fts))`,
     `sz` |-> `\i. type_memory_size (SND (EL i fts))`] (SPEC_ALL pop_indexed_support_extract)) >>
  simp[] >> reverse conj_tac
  >- (rpt strip_tac >> first_x_assum drule >>
      disch_then (mp_tac o MATCH_MP pop_live_support_bounds) >> simp[]) >>
  rpt strip_tac >> drule_all pop_prefix_windows_apart >>
  disch_then (qspec_then `type_memory_size o SND` mp_tac) >> simp[] >> decide_tac
QED

Theorem pop_header_stride_support_extract:
  j < n /\
  (!i. i < n ==> pop_live_support tv (v i)
    (addr+32+i*type_memory_size tv) (supp i)) ==>
  supp j SUBSET ({x | addr <= x /\ x < addr+32} UNION BIGUNION {supp i | i < n}) /\
  DISJOINT (({x | addr <= x /\ x < addr+32} UNION BIGUNION {supp i | i < n}) DIFF supp j)
    {x | addr+32+j*type_memory_size tv <= x /\
         x < addr+32+j*type_memory_size tv+type_memory_size tv}
Proof
  strip_tac >>
  `supp j SUBSET BIGUNION {supp i | i < n} /\
   DISJOINT ((BIGUNION {supp i | i < n}) DIFF supp j)
     {x | addr+32+j*type_memory_size tv <= x /\
          x < addr+32+j*type_memory_size tv+type_memory_size tv}` by
    (irule pop_stride_support_extract >> simp[] >> qexists_tac `v` >> gvs[AC ADD_ASSOC ADD_COMM]) >>
  conj_tac >- metis_tac[SUBSET_UNION, SUBSET_TRANS] >>
  `DISJOINT {x | addr <= x /\ x < addr+32}
    {x | addr+32+j*type_memory_size tv <= x /\
         x < addr+32+j*type_memory_size tv+type_memory_size tv}` by
    (simp[DISJOINT_DEF, EXTENSION] >> rpt strip_tac >> decide_tac) >>
  ASM_SET_TAC []
QED

