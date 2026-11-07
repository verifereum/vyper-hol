Theory bodyPtrPopPathStep
Ancestors bodyPtrDefs robustCopyTransportPtr normalizationPrefixPtr pred_set typedCopyLayoutPtr exprSimProps loweringPosts valueEncoding
  valueEncodingProofs exprSimAggregateEncoding vyperState vyperTyping
  vyperValueOperation tupleMemoryLayout vyperPlaceStatePreservation

Theorem pop_fields_memory_offset:
  !fs vals base mem fld child k ct.
    struct_has_type fs vals /\ fields_in_memory vals fs base mem /\
    ALOOKUP vals fld = SOME child /\ mem_field_offset fs fld = SOME (k,ct) ==>
    val_in_memory ct child (base+k) mem
Proof
  Induct_on `fs` >> simp[mem_field_offset_def] >>
  PairCases >> Cases_on `vals` >> simp[value_has_type_def] >>
  PairCases_on `h` >>
  simp[value_has_type_def, val_in_memory_def, mem_field_offset_def] >>
  rpt strip_tac >> Cases_on `h0 = fld` >> gvs[AllCaseEqs()] >>
  PairCases_on `z` >> gvs[] >>
  first_x_assum drule_all >>
  `base' + type_memory_size h1 + z0 = base' + (z0 + type_memory_size h1)` by
    decide_tac >> asm_rewrite_tac []
QED

Theorem pop_step_memory_extract:
  !rt root sb child k ct base mem.
  value_has_type rt root /\
  evaluate_subscripts rt root [sb] = INL child /\
  mem_step_offset rt sb = SOME (k,ct) /\
  val_in_memory rt root base mem ==>
  val_in_memory ct child (base+k) mem
Proof
  Cases_on `sb`
  >- (rename1 `ValueSubscript key` >> Cases_on `key` >> Cases_on `rt` >>
      simp[mem_step_offset_def] >> rpt strip_tac >>
      gvs[AllCaseEqs()] >> Cases_on `root` >> gvs[value_has_type_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >>
      gvs[value_has_type_def, evaluate_subscripts_def, array_index_def,
          val_in_memory_def, AllCaseEqs(), listTheory.oEL_THM]
      >- (simp[type_memory_size_list_sum] >> irule tuple_in_memory_element >>
          simp[] >> metis_tac[values_have_types_length])
      >- (Cases_on `b` >> gvs[value_has_type_def, mem_step_offset_def] >>
          drule_all elems_in_memory_EL >> simp[])
      >- gvs[mem_step_offset_def]
      >> gvs[mem_step_offset_def] >> irule kvs_in_memory_lookup >>
         goal_assum (drule_at Any) >> simp[]) >>
  Cases_on `rt` >> simp[mem_step_offset_def] >> rpt strip_tac >>
  Cases_on `root` >> gvs[value_has_type_def, evaluate_subscripts_def,
    val_in_memory_def, AllCaseEqs()] >>
  irule pop_fields_memory_offset >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem pop_path_memory_extract:
  !path rt root child k ct base mem.
  well_formed_type_value rt /\ value_has_type rt root /\
  evaluate_subscripts rt root path = INL child /\
  mem_path_offset rt path = SOME (k,ct) /\
  val_in_memory rt root base mem ==>
  val_in_memory ct child (base+k) mem
Proof
  Induct_on `path` >- simp[mem_path_offset_def, evaluate_subscripts_def] >>
  rpt gen_tac >> strip_tac >>
  rename1 `val_in_memory rt root addr mem` >>
  gvs[Once mem_path_offset_def, AllCaseEqs()] >>
  rename1 `mem_step_offset rt h = SOME (step0,step1)` >>
  rename1 `mem_path_offset step1 path = SOME tail` >> PairCases_on `tail` >>
  gvs[] >>
  `mem_path_offset rt [h] = SOME (step0,step1)` by
    simp[mem_path_offset_def] >>
  drule mem_path_offset_sound >>
  simp[subscripts_type_def] >> strip_tac >> gvs[AllCaseEqs()] >>
  drule evaluate_subscripts_cons_typed >>
  disch_then (qspecl_then [`path`, `root`] mp_tac) >>
  strip_tac >> gvs[AllCaseEqs()] >>
  `val_in_memory step1 v (addr+step0) mem` by
    (irule pop_step_memory_extract >> goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `well_formed_type_value step1` by
    (irule subscripts_type_well_formed >> goal_assum (drule_at Any) >>
     qexists_tac `[h]` >> simp[subscripts_type_def]) >>
  `value_has_type step1 v` by
    (irule evaluate_subscripts_type >>
     qexistsl_tac [`root`, `[h]`, `rt`] >> simp[subscripts_type_def]) >>
  `evaluate_subscripts step1 v path = INL child` by metis_tac[] >>
  first_x_assum drule_all >>
  pure_rewrite_tac[arithmeticTheory.ADD_ASSOC] >> simp[]
QED

Theorem pop_step_robust_memory_extract:
  !rt root sb child k ct base mem dirty.
  value_has_type rt root /\
  evaluate_subscripts rt root [sb] = INL child /\
  mem_step_offset rt sb = SOME (k,ct) /\
  (!m. mem_agree_outside dirty mem m ==> val_in_memory rt root base m) ==>
  !m. mem_agree_outside dirty mem m ==>
    val_in_memory ct child (base+k) m
Proof
  metis_tac[pop_step_memory_extract]
QED

Theorem pop_path_robust_memory_extract:
  !path rt root child k ct base mem dirty.
  well_formed_type_value rt /\ value_has_type rt root /\
  evaluate_subscripts rt root path = INL child /\
  mem_path_offset rt path = SOME (k,ct) /\
  (!m. mem_agree_outside dirty mem m ==> val_in_memory rt root base m) ==>
  !m. mem_agree_outside dirty mem m ==>
    val_in_memory ct child (base+k) m
Proof
  metis_tac[pop_path_memory_extract]
QED

Theorem pop_stride_intervals_apart:
  !i j stride. i <> j ==>
    i * stride + stride <= j * stride \/
    j * stride + stride <= i * stride
Proof
  rpt strip_tac >> Cases_on `i < j`
  >- (disj1_tac >>
      `SUC i <= j` by decide_tac >>
      drule arithmeticTheory.LESS_MONO_MULT >> disch_then (qspec_then `stride` mp_tac) >>
      pure_rewrite_tac[arithmeticTheory.MULT_CLAUSES] >> decide_tac) >>
  disj2_tac >> `SUC j <= i` by decide_tac >>
  drule arithmeticTheory.LESS_MONO_MULT >> disch_then (qspec_then `stride` mp_tac) >>
  pure_rewrite_tac[arithmeticTheory.MULT_CLAUSES] >> decide_tac
QED

Theorem pop_array_sibling_robust_frame:
  !i j tv v base dirty mem mem' writes.
  i <> j /\ val_wf tv v /\
  (!x. x IN writes ==>
    base+j*type_memory_size tv <= x /\
    x < base+j*type_memory_size tv+type_memory_size tv) /\
  mem_agree_outside writes mem' mem /\
  (!m. mem_agree_outside dirty mem m ==>
    val_in_memory tv v (base+i*type_memory_size tv) m) ==>
  !m. mem_agree_outside dirty mem' m ==>
    val_in_memory tv v (base+i*type_memory_size tv) m
Proof
  rpt gen_tac >> strip_tac >>
  `val_footprint tv v <= type_memory_size tv` by
    metis_tac[val_footprint_le] >>
  `i*type_memory_size tv+type_memory_size tv <= j*type_memory_size tv \/
   j*type_memory_size tv+type_memory_size tv <= i*type_memory_size tv` by
    (irule pop_stride_intervals_apart >> simp[]) >>
  rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
  simp[] >> qexistsl_tac [`mem`, `mem'`, `dirty`, `dirty`, `writes`] >>
  simp[mem_agree_outside_def] >> rpt strip_tac >>
  fs[mem_agree_outside_def] >>
  qpat_x_assum `!x. x IN writes ==> _` drule >> decide_tac
QED

Theorem pop_elems_robust_replace:
  !vs tv j new off dirty mem mem' writes.
  elems_val_wf vs tv /\ j < LENGTH vs /\
  (!x. x IN writes ==>
    off+j*type_memory_size tv <= x /\
    x < off+j*type_memory_size tv+type_memory_size tv) /\
  mem_agree_outside writes mem' mem /\
  (!m. mem_agree_outside dirty mem m ==> elems_in_memory vs off tv m) /\
  (!m. mem_agree_outside dirty mem' m ==>
    val_in_memory tv new (off+j*type_memory_size tv) m) ==>
  !m. mem_agree_outside dirty mem' m ==>
    elems_in_memory (LUPDATE new j vs) off tv m
Proof
  rpt strip_tac >> irule elems_in_memory_intro >>
  simp[] >> rpt strip_tac >> rename1 `i < LENGTH vs` >>
  Cases_on `i = j` >- gvs[listTheory.EL_LUPDATE] >>
  simp[listTheory.EL_LUPDATE] >>
  `val_wf tv (EL i vs)` by
    (irule exprSimPopTheory.elems_val_wf_EL >> goal_assum (drule_at Any) >> simp[]) >>
  `!m. mem_agree_outside dirty mem m ==>
    val_in_memory tv (EL i vs) (off+i*type_memory_size tv) m` by
    (rpt strip_tac >> qpat_x_assum `!m. _ ==> elems_in_memory _ _ _ _` drule >>
     strip_tac >> irule elems_in_memory_EL >>
     goal_assum (drule_at Any) >> simp[]) >>
  drule_all pop_array_sibling_robust_frame >> simp[]
QED
