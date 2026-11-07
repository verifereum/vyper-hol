Theory bodyPtrPopLiveStep
Ancestors bodyPtrPopLiveSupport bodyPtrPopPathStep pred_set list arithmetic
  vyperValueOperation loweringPosts valueEncodingProofs vyperTyping vyperState
  vyperAssignPreservesType exprSimProps

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
      fld = FST (EL j fields) /\
      k = SUM (MAP (type_memory_size o SND) (TAKE j fts)) /\
      (!new. AFUPDKEY fld (K new) fields = LUPDATE (fld,new) j fields)
Proof
  Induct_on `fts` >> simp[mem_field_offset_def] >>
  PairCases >> Cases_on `fields` >> simp[value_has_type_def] >>
  PairCases_on `h` >>
  simp[value_has_type_def, mem_field_offset_def] >> rpt strip_tac >>
  Cases_on `h0 = fld` >> gvs[AllCaseEqs()]
  >- (qexists_tac `0` >> simp[alistTheory.AFUPDKEY_def, LUPDATE_def]) >>
  PairCases_on `z` >> gvs[] >> first_x_assum drule_all >>
  strip_tac >> qexists_tac `SUC j` >> simp[alistTheory.AFUPDKEY_def, LUPDATE_def]
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

Theorem pop_sparse_support_at:
  j < n /\
  (!i. i < n ==> pop_live_support tv
    (case ALOOKUP kvs i of NONE => default_value tv | SOME v => v)
    (addr+i*type_memory_size tv) (supp i)) ==>
  pop_live_support tv
    (case ALOOKUP kvs j of NONE => default_value tv | SOME v => v)
    (addr+j*type_memory_size tv) (supp j) /\
  supp j SUBSET BIGUNION {supp i | i < n} /\
  DISJOINT ((BIGUNION {supp i | i < n}) DIFF supp j)
    {x | addr+j*type_memory_size tv <= x /\
         x < addr+j*type_memory_size tv+type_memory_size tv}
Proof
  strip_tac >> conj_tac >- metis_tac[] >>
  irule pop_stride_support_extract >> simp[] >>
  qexists_tac `\i. case ALOOKUP kvs i of NONE => default_value tv | SOME w => w` >> simp[]
QED

Theorem pop_tuple_support_at:
  j < LENGTH tvs /\
  (!i. i < LENGTH tvs ==> pop_live_support (EL i tvs) (EL i vs)
    (addr+SUM (MAP type_memory_size (TAKE i tvs))) (supp i)) ==>
  pop_live_support (EL j tvs) (EL j vs)
    (addr+SUM (MAP type_memory_size (TAKE j tvs))) (supp j) /\
  supp j SUBSET BIGUNION {supp i | i < LENGTH tvs} /\
  DISJOINT ((BIGUNION {supp i | i < LENGTH tvs}) DIFF supp j)
    {x | addr+SUM (MAP type_memory_size (TAKE j tvs)) <= x /\
         x < addr+SUM (MAP type_memory_size (TAKE j tvs))+type_memory_size (EL j tvs)}
Proof
  strip_tac >> conj_tac >- metis_tac[] >>
  irule pop_prefix_support_extract >> simp[] >>
  qexists_tac `\i. EL i vs` >> simp[]
QED

Theorem pop_dynamic_support_at:
  j < LENGTH vs /\
  (!i. i < LENGTH vs ==> pop_live_support tv (EL i vs)
    (addr+(i*type_memory_size tv+32)) (supp i)) ==>
  pop_live_support tv (EL j vs) (addr+32+j*type_memory_size tv) (supp j) /\
  supp j SUBSET ({x | addr <= x /\ x < addr+32} UNION BIGUNION {supp i | i < LENGTH vs}) /\
  DISJOINT (({x | addr <= x /\ x < addr+32} UNION BIGUNION {supp i | i < LENGTH vs}) DIFF supp j)
    {x | addr+32+j*type_memory_size tv <= x /\
         x < addr+32+j*type_memory_size tv+type_memory_size tv}
Proof
  strip_tac >> conj_tac
  >- (first_x_assum (qspec_then `j` mp_tac) >> simp[AC ADD_ASSOC ADD_COMM]) >>
  irule pop_header_stride_support_extract >> simp[] >>
  qexists_tac `\i. EL i vs` >> gvs[AC ADD_ASSOC ADD_COMM]
QED

Theorem pop_value_step_support_extract:
  !rt root key child k ct addr supp.
  pop_live_support rt root addr supp /\
  evaluate_subscripts rt root [ValueSubscript key] = INL child /\
  mem_step_offset rt (ValueSubscript key) = SOME (k,ct) ==>
  ?cs. pop_live_support ct child (addr+k) cs /\ cs SUBSET supp /\
    DISJOINT (supp DIFF cs) {x | addr+k <= x /\ x < addr+k+type_memory_size ct}
Proof
  Cases_on `key` >> Cases_on `rt` >> simp[mem_step_offset_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  qpat_x_assum `pop_live_support _ _ _ _` mp_tac >>
  simp[Once pop_live_support_cases] >> strip_tac >> gvs[] >>
  gvs[evaluate_subscripts_def, array_index_def, AllCaseEqs(), listTheory.oEL_THM]
  >- (drule_all pop_tuple_support_at >> strip_tac >>
      qexists_tac `supp' (Num i)` >> FULL_SIMP_TAC bool_ss [type_memory_size_list_sum, AC ADD_ASSOC ADD_COMM])
  >- (gvs[mem_step_offset_def] >>
      qpat_x_assum `!j. _ ==> pop_live_support _ _ _ _` mp_tac >>
      pure_rewrite_tac[GSYM ADD_ASSOC] >> strip_tac >>
      drule_all pop_dynamic_support_at >> strip_tac >>
      qexists_tac `supp' (Num i)` >>
      FULL_SIMP_TAC bool_ss [optionTheory.option_case_def, AC ADD_ASSOC ADD_COMM] >> metis_tac[]) >>
  gvs[mem_step_offset_def] >>
  drule_all pop_sparse_support_at >> strip_tac >>
  qpat_assum `ALOOKUP _ _ = _` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th, optionTheory.option_case_def])) >>
  qexists_tac `supp' (Num i)` >>
      FULL_SIMP_TAC bool_ss [optionTheory.option_case_def, AC ADD_ASSOC ADD_COMM] >> metis_tac[]
QED

Theorem pop_attr_step_support_extract:
  !rt root fld child k ct addr supp.
  pop_live_support rt root addr supp /\
  evaluate_subscripts rt root [AttrSubscript fld] = INL child /\
  mem_step_offset rt (AttrSubscript fld) = SOME (k,ct) ==>
  ?cs. pop_live_support ct child (addr+k) cs /\ cs SUBSET supp /\
    DISJOINT (supp DIFF cs) {x | addr+k <= x /\ x < addr+k+type_memory_size ct}
Proof
  Cases_on `rt` >> simp[mem_step_offset_def] >> rpt strip_tac >>
  qpat_x_assum `pop_live_support _ _ _ _` mp_tac >>
  simp[Once pop_live_support_cases] >> strip_tac >> gvs[] >>
  gvs[evaluate_subscripts_def, AllCaseEqs(), value_has_type_def] >>
  drule_all pop_fields_selected_index >> strip_tac >> gvs[] >>
  drule_all pop_fields_support_extract >> strip_tac >>
  qexists_tac `supp' j` >>
  FULL_SIMP_TAC bool_ss [AC ADD_ASSOC ADD_COMM] >> metis_tac[]
QED

Theorem pop_step_support_extract:
  !rt root addr supp sb child k ct.
  pop_live_support rt root addr supp /\
  evaluate_subscripts rt root [sb] = INL child /\
  mem_step_offset rt sb = SOME (k,ct) ==>
  ?cs. pop_live_support ct child (addr+k) cs /\ cs SUBSET supp /\
    DISJOINT (supp DIFF cs) {x | addr+k <= x /\ x < addr+k+type_memory_size ct}
Proof
  rpt gen_tac >> Cases_on `sb` >>
  metis_tac[pop_value_step_support_extract, pop_attr_step_support_extract]
QED

Theorem pop_live_support_unique:
  !tv v addr supp. pop_live_support tv v addr supp ==>
  !other. pop_live_support tv v addr other ==> supp = other
Proof
  ho_match_mp_tac pop_live_support_ind >>
  rpt strip_tac >>
  qpat_x_assum `pop_live_support _ _ _ _` mp_tac >>
  simp[Once pop_live_support_cases] >> rpt strip_tac >> gvs[] >>
  simp[EXTENSION, IN_BIGUNION] >> metis_tac[]
QED

Theorem pop_indexed_support_update:
  j < n /\ DISJOINT head (supp j) /\
  (!i. i < n /\ i <> j ==> DISJOINT (supp i) (supp j)) ==>
  ((head UNION BIGUNION {supp i | i < n}) DIFF supp j) UNION ns =
  head UNION BIGUNION {(if i = j then ns else supp i) | i < n}
Proof
  simp[DISJOINT_DEF, EXTENSION, IN_BIGUNION] >> metis_tac[]
QED

Theorem pop_stride_support_siblings:
  j < n /\
  (!i. i < n ==> pop_live_support tv (v i)
    (addr+i*type_memory_size tv) (supp i)) ==>
  !i. i < n /\ i <> j ==> DISJOINT (supp i) (supp j)
Proof
  rpt strip_tac >>
  `supp i SUBSET {x | addr+i*type_memory_size tv <= x /\
    x < addr+i*type_memory_size tv+type_memory_size tv}` by
    metis_tac[pop_live_support_bounds] >>
  `supp j SUBSET {x | addr+j*type_memory_size tv <= x /\
    x < addr+j*type_memory_size tv+type_memory_size tv}` by
    metis_tac[pop_live_support_bounds] >>
  drule pop_stride_intervals_apart >>
  disch_then (qspec_then `type_memory_size tv` mp_tac) >>
  simp[SUBSET_DEF, DISJOINT_DEF, EXTENSION] >> rpt strip_tac >>
  spose_not_then strip_assume_tac >> gvs[SUBSET_DEF] >>
  first_x_assum drule >> strip_tac >> first_x_assum drule >> decide_tac
QED

Theorem pop_sparse_support_rebuild:
  well_formed_type_value (ArrayTV tv (Fixed n)) /\
  value_has_type (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs')) /\
  j < n /\
  (!i. i < n ==> pop_live_support tv
    (case ALOOKUP kvs i of NONE => default_value tv | SOME v => v)
    (addr+i*type_memory_size tv) (supp i)) /\
  (!i. i < n ==> (case ALOOKUP kvs' i of NONE => default_value tv | SOME v => v) =
    if i = j then new else (case ALOOKUP kvs i of NONE => default_value tv | SOME v => v)) /\
  pop_live_support tv new (addr+j*type_memory_size tv) ns ==>
  pop_live_support (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs')) addr
    ((BIGUNION {supp i | i < n} DIFF supp j) UNION ns)
Proof
  strip_tac >>
  `!i. i < n /\ i <> j ==> DISJOINT (supp i) (supp j)` by
    (ho_match_mp_tac (BETA_RULE $ Q.INST
       [`v` |-> `\i. case ALOOKUP kvs i of NONE => default_value tv | SOME w => w`]
       (SPEC_ALL pop_stride_support_siblings)) >> simp[]) >>
  `((BIGUNION {supp i | i < n}) DIFF supp j) UNION ns =
    BIGUNION {(if i = j then ns else supp i) | i < n}` by
    (mp_tac (Q.INST [`head` |-> `{}`] (SPEC_ALL (INST_TYPE [alpha |-> ``:num``] pop_indexed_support_update))) >> simp[]) >>
  asm_rewrite_tac[] >> simp[Once pop_live_support_cases] >>
  qexists_tac `\i. if i = j then ns else supp i` >> simp[] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  Cases_on `j' = j` >> gvs[]
QED

Theorem pop_dynamic_support_rebuild:
  well_formed_type_value (ArrayTV tv (Dynamic n)) /\
  value_has_type (ArrayTV tv (Dynamic n)) (ArrayV (DynArrayV vs')) /\
  LENGTH vs' = LENGTH vs /\ j < LENGTH vs /\
  (!i. i < LENGTH vs ==> pop_live_support tv (EL i vs)
    (addr+32+i*type_memory_size tv) (supp i)) /\
  (!i. i < LENGTH vs ==> EL i vs' = if i = j then new else EL i vs) /\
  pop_live_support tv new (addr+32+j*type_memory_size tv) ns ==>
  pop_live_support (ArrayTV tv (Dynamic n)) (ArrayV (DynArrayV vs')) addr
    ((({x | addr <= x /\ x < addr+32} UNION BIGUNION {supp i | i < LENGTH vs}) DIFF supp j) UNION ns)
Proof
  strip_tac >>
  `!i. i < LENGTH vs /\ i <> j ==> DISJOINT (supp i) (supp j)` by
    (ho_match_mp_tac (BETA_RULE $ Q.INST
       [`v` |-> `\i. EL i vs`, `addr` |-> `addr+32`, `n` |-> `LENGTH vs`]
       (SPEC_ALL pop_stride_support_siblings)) >> simp[]) >>
  `DISJOINT {x | addr <= x /\ x < addr+32} (supp j)` by
    (`supp j SUBSET {x | addr+32+j*type_memory_size tv <= x /\
       x < addr+32+j*type_memory_size tv+type_memory_size tv}` by
        metis_tac[pop_live_support_bounds] >>
     gvs[SUBSET_DEF, DISJOINT_DEF, EXTENSION] >> rpt strip_tac >>
     spose_not_then strip_assume_tac >>
     qpat_x_assum `!x. x IN supp j ==> _` drule >> decide_tac) >>
  `(({x | addr <= x /\ x < addr+32} UNION BIGUNION {supp i | i < LENGTH vs}) DIFF supp j) UNION ns =
    {x | addr <= x /\ x < addr+32} UNION
    BIGUNION {(if i = j then ns else supp i) | i < LENGTH vs}` by
    (irule pop_indexed_support_update >> simp[]) >>
  asm_rewrite_tac[] >> simp[Once pop_live_support_cases] >>
  qexists_tac `\i. if i = j then ns else supp i` >> simp[] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  Cases_on `j' = j` >> gvs[AC ADD_ASSOC ADD_COMM]
QED

Theorem pop_fields_support_siblings:
  j < LENGTH fts /\
  (!i. i < LENGTH fts ==> pop_live_support (SND (EL i fts)) (v i)
    (addr+SUM (MAP (type_memory_size o SND) (TAKE i fts))) (supp i)) ==>
  !i. i < LENGTH fts /\ i <> j ==> DISJOINT (supp i) (supp j)
Proof
  rpt strip_tac >>
  `supp i SUBSET {x | addr+SUM (MAP (type_memory_size o SND) (TAKE i fts)) <= x /\
    x < addr+SUM (MAP (type_memory_size o SND) (TAKE i fts))+type_memory_size (SND (EL i fts))}` by
    metis_tac[pop_live_support_bounds] >>
  `supp j SUBSET {x | addr+SUM (MAP (type_memory_size o SND) (TAKE j fts)) <= x /\
    x < addr+SUM (MAP (type_memory_size o SND) (TAKE j fts))+type_memory_size (SND (EL j fts))}` by
    metis_tac[pop_live_support_bounds] >>
  drule_all pop_prefix_windows_apart >>
  disch_then (qspec_then `type_memory_size o SND` mp_tac) >>
  simp[SUBSET_DEF, DISJOINT_DEF, EXTENSION] >> rpt strip_tac >>
  spose_not_then strip_assume_tac >> gvs[SUBSET_DEF] >>
  first_x_assum drule >> strip_tac >> first_x_assum drule >> decide_tac
QED

Theorem pop_fields_support_rebuild:
  !(fields : (string # value) list) fts fields' j addr supp new ns.
  well_formed_type_value (StructTV fts) /\
  value_has_type (StructTV fts) (StructV fields') /\ j < LENGTH fts /\
  (!i. i < LENGTH fts ==> pop_live_support (SND (EL i fts)) (SND (EL i fields))
    (addr+SUM (MAP (type_memory_size o SND) (TAKE i fts))) (supp i)) /\
  (!i. i < LENGTH fts ==> SND (EL i fields') = if i = j then new else SND (EL i fields)) /\
  pop_live_support (SND (EL j fts)) new
    (addr+SUM (MAP (type_memory_size o SND) (TAKE j fts))) ns ==>
  pop_live_support (StructTV fts) (StructV fields') addr
    ((BIGUNION {supp i | i < LENGTH fts} DIFF supp j) UNION ns)
Proof
  rpt gen_tac >> strip_tac >>
  `!i. i < LENGTH fts /\ i <> j ==> DISJOINT (supp i) (supp j)` by
    (ho_match_mp_tac (BETA_RULE $ Q.INST
       [`v` |-> `\i. SND (EL i (fields : (string # value) list))`]
       (SPEC_ALL pop_fields_support_siblings)) >> simp[]) >>
  `((BIGUNION {supp i | i < LENGTH fts}) DIFF supp j) UNION ns =
    BIGUNION {(if i = j then ns else supp i) | i < LENGTH fts}` by
    (irule (SRULE [] (Q.INST [`head` |-> `{}`]
       (SPEC_ALL (INST_TYPE [alpha |-> ``:num``] pop_indexed_support_update)))) >> simp[]) >>
  asm_rewrite_tac[] >> simp[Once pop_live_support_cases] >>
  qexists_tac `\i. if i = j then ns else supp i` >> simp[] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  Cases_on `j' = j` >> gvs[]
QED

Theorem pop_step_replace_typed:
  !rt root sb k ct new updated.
  well_formed_type_value rt /\ value_has_type rt root /\
  mem_step_offset rt sb = SOME (k,ct) /\ value_has_type ct new /\
  assign_subscripts rt root [sb] (Replace new) = INL updated ==>
  value_has_type rt updated
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `sb`
  >- (rename1 `ValueSubscript key` >> Cases_on `key` >> Cases_on `rt` >>
      gvs[mem_step_offset_def, AllCaseEqs()]
      >- (Cases_on `root` >> gvs[value_has_type_def] >>
          Cases_on `a` >> gvs[value_has_type_def, assign_subscripts_def,
            array_set_index_def, AllCaseEqs()]) >>
      Cases_on `b` >> gvs[mem_step_offset_def, AllCaseEqs()] >>
      irule assign_subscripts_preserves_type >> simp[] >>
      qexistsl_tac [`root`, `Replace new`, `[ValueSubscript (IntV i)]`] >>
      simp[leaf_type_def]) >>
  Cases_on `rt` >> gvs[mem_step_offset_def] >>
  drule mem_field_offset_sound >> strip_tac >>
  irule assign_subscripts_preserves_type >> simp[] >>
  qexistsl_tac [`root`, `Replace new`, `[AttrSubscript s]`] >> simp[leaf_type_def]
QED

Theorem pop_attr_step_support_replace:
  !rt root addr supp fld child k ct cs new ns updated.
  pop_live_support rt root addr supp /\
  evaluate_subscripts rt root [AttrSubscript fld] = INL child /\
  mem_step_offset rt (AttrSubscript fld) = SOME (k,ct) /\
  pop_live_support ct child (addr+k) cs /\
  assign_subscripts rt root [AttrSubscript fld] (Replace new) = INL updated /\
  pop_live_support ct new (addr+k) ns ==>
  pop_live_support rt updated addr ((supp DIFF cs) UNION ns)
Proof
  rpt gen_tac >> strip_tac >>
  `well_formed_type_value rt /\ value_has_type rt root` by
    metis_tac[pop_live_support_typed] >>
  `value_has_type ct new` by metis_tac[pop_live_support_typed] >>
  `value_has_type rt updated` by metis_tac[pop_step_replace_typed] >>
  Cases_on `rt` >> gvs[mem_step_offset_def] >>
  qpat_x_assum `pop_live_support (StructTV _) _ _ _` mp_tac >>
  simp[Once pop_live_support_cases] >> strip_tac >> gvs[] >>
  gvs[evaluate_subscripts_def, assign_subscripts_def, AllCaseEqs(), value_has_type_def] >>
  drule_all pop_fields_selected_index >> strip_tac >> gvs[] >>
  `cs = supp' j` by
    (irule pop_live_support_unique >> goal_assum (drule_at Any) >>
     first_x_assum irule >> simp[]) >> gvs[] >>
  irule pop_fields_support_rebuild >>
  goal_assum (drule_at Any) >> simp[value_has_type_def] >>
  qexistsl_tac [`fields`, `new`] >> simp[] >>
  `LENGTH fields = LENGTH l` by
    metis_tac[struct_has_type_map_fst, LENGTH_MAP] >>
  simp[EL_LUPDATE] >> rpt strip_tac >> Cases_on `i = j` >> simp[]
QED

Theorem pop_dynamic_update_support:
  well_formed_type_value (ArrayTV tv (Dynamic n)) /\
  value_has_type (ArrayTV tv (Dynamic n)) (ArrayV (DynArrayV (LUPDATE new j vs))) /\
  j < LENGTH vs /\
  (!i. i < LENGTH vs ==> pop_live_support tv (EL i vs)
    (addr+32+i*type_memory_size tv) (supp i)) /\
  pop_live_support tv (EL j vs) (addr+32+j*type_memory_size tv) cs /\
  pop_live_support tv new (addr+32+j*type_memory_size tv) ns ==>
  pop_live_support (ArrayTV tv (Dynamic n)) (ArrayV (DynArrayV (LUPDATE new j vs))) addr
    ((({x | addr <= x /\ x < addr+32} UNION BIGUNION {supp i | i < LENGTH vs}) DIFF cs) UNION ns)
Proof
  strip_tac >> `cs = supp j` by
    (irule pop_live_support_unique >> goal_assum (drule_at Any) >>
     first_x_assum irule >> simp[]) >> gvs[] >>
  irule pop_dynamic_support_rebuild >> simp[] >>
  qexists_tac `new` >> simp[EL_LUPDATE]
QED

Theorem pop_sparse_update_support:
  well_formed_type_value (ArrayTV tv (Fixed n)) /\
  value_has_type (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs')) /\
  kvs' = (if new = default_value tv then ADELKEY j kvs else insert_sarray j new kvs) /\
  j < n /\
  (!i. i < n ==> pop_live_support tv
    (case ALOOKUP kvs i of NONE => default_value tv | SOME v => v)
    (addr+i*type_memory_size tv) (supp i)) /\
  pop_live_support tv (case ALOOKUP kvs j of NONE => default_value tv | SOME v => v)
    (addr+j*type_memory_size tv) cs /\
  pop_live_support tv new (addr+j*type_memory_size tv) ns ==>
  pop_live_support (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs')) addr
    ((BIGUNION {supp i | i < n} DIFF cs) UNION ns)
Proof
  strip_tac >> `cs = supp j` by
    (irule pop_live_support_unique >> goal_assum (drule_at Any) >>
     first_x_assum irule >> simp[]) >> gvs[] >>
  irule pop_sparse_support_rebuild >> simp[] >>
  qexistsl_tac [`kvs`, `new`] >> simp[pop_sparse_update_lookup] >>
  rpt strip_tac >> Cases_on `i = j` >> simp[] >>
  Cases_on `new = default_value tv` >> simp[]
QED

Theorem pop_value_step_support_replace:
  !rt root addr supp key child k ct cs new ns updated.
  pop_live_support rt root addr supp /\
  evaluate_subscripts rt root [ValueSubscript key] = INL child /\
  mem_step_offset rt (ValueSubscript key) = SOME (k,ct) /\
  pop_live_support ct child (addr+k) cs /\
  assign_subscripts rt root [ValueSubscript key] (Replace new) = INL updated /\
  pop_live_support ct new (addr+k) ns ==>
  pop_live_support rt updated addr ((supp DIFF cs) UNION ns)
Proof
  rpt gen_tac >> strip_tac >>
  `well_formed_type_value rt /\ value_has_type rt root` by
    metis_tac[pop_live_support_typed] >>
  `value_has_type ct new` by metis_tac[pop_live_support_typed] >>
  `value_has_type rt updated` by metis_tac[pop_step_replace_typed] >>
  Cases_on `key` >> Cases_on `rt` >> gvs[mem_step_offset_def, AllCaseEqs()] >>
  qpat_x_assum `pop_live_support _ root _ _` mp_tac >>
  simp[Once pop_live_support_cases] >> strip_tac >> gvs[] >>
  gvs[evaluate_subscripts_def, assign_subscripts_def, array_index_def,
    AllCaseEqs(), listTheory.oEL_THM]
  >- gvs[array_set_index_def] 
  >- (gvs[mem_step_offset_def, array_set_index_def, pop_replace_index_list] >>
      irule pop_dynamic_update_support >> simp[] >>
      FULL_SIMP_TAC bool_ss [AC ADD_ASSOC ADD_COMM] >> metis_tac[]) >>
  gvs[mem_step_offset_def, array_set_index_def] >>
  irule pop_sparse_update_support >> simp[] >>
  qexistsl_tac [`Num i`, `kvs`, `new`] >> simp[]
QED

Theorem pop_step_support_replace:
  !rt root addr supp sb child k ct cs new ns updated.
  pop_live_support rt root addr supp /\
  evaluate_subscripts rt root [sb] = INL child /\
  mem_step_offset rt sb = SOME (k,ct) /\
  pop_live_support ct child (addr+k) cs /\
  assign_subscripts rt root [sb] (Replace new) = INL updated /\
  pop_live_support ct new (addr+k) ns ==>
  pop_live_support rt updated addr ((supp DIFF cs) UNION ns)
Proof
  rpt gen_tac >> Cases_on `sb` >>
  metis_tac[pop_value_step_support_replace, pop_attr_step_support_replace]
QED
