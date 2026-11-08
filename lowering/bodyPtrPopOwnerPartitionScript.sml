Theory bodyPtrPopOwnerPartition
Ancestors bodyPtrPopLivePath bodyPtrPopLiveSupport bodyPtrPopOwnerSelection
  bodyPtrPopPathLift exprSimProps loweringPosts vyperState vyperTyping
  vyperPlaceStatePreservation vyperValueOperation vyperLookup list arithmetic pred_set

Theorem pop_field_offset_complete:
  !fts fld ct. ALOOKUP fts fld = SOME ct ==>
    ?k. mem_field_offset fts fld = SOME (k,ct)
Proof
  Induct_on `fts` >> simp[] >> PairCases >>
  simp[mem_field_offset_def] >> rpt gen_tac >>
  Cases_on `h0 = fld` >> simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >> simp[]
QED

Theorem pop_step_offset_complete:
  !rt sb ct. subscript_type rt sb = SOME ct ==>
    ?k. mem_step_offset rt sb = SOME (k,ct)
Proof
  Cases_on `sb`
  >- (rename1 `ValueSubscript key` >> Cases_on `key` >> Cases_on `rt` >>
      simp[subscript_type_def, mem_step_offset_def] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >> Cases_on `b` >>
      gvs[subscript_type_def, vyperASTTheory.bound_length_def, mem_step_offset_def]) >>
  Cases_on `rt` >> simp[subscript_type_def, mem_step_offset_def] >>
  metis_tac[pop_field_offset_complete]
QED

Theorem pop_path_offset_complete:
  !path rt ct. subscripts_type rt path = SOME ct ==>
    ?k. mem_path_offset rt path = SOME (k,ct)
Proof
  Induct_on `path` >> simp[subscripts_type_def, mem_path_offset_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  drule pop_step_offset_complete >> strip_tac >> simp[] >>
  first_x_assum drule >> strip_tac >> simp[]
QED

Theorem pop_supported_array_offset:
  pop_live_support rt root addr supp /\
  evaluate_subscripts rt root path = INL (ArrayV (DynArrayV vs)) ==>
  ?k et cap. mem_path_offset rt path = SOME (k,ArrayTV et (Dynamic cap))
Proof
  strip_tac >> drule pop_live_support_typed >> strip_tac >>
  `?ptv. subscripts_type rt path = SOME ptv /\
    value_has_type ptv (ArrayV (DynArrayV vs))` by
    metis_tac[evaluate_subscripts_declared_type_exists] >>
  Cases_on `ptv` >> gvs[value_has_type_def] >>
  Cases_on `b` >> gvs[value_has_type_def] >>
  drule pop_path_offset_complete >> metis_tac[]
QED

Theorem pop_source_support_split:
  pop_live_support rt root addr supp /\
  evaluate_subscripts rt root path = INL (ArrayV (DynArrayV vs)) /\ vs <> [] /\
  popped_value (ArrayV (DynArrayV vs)) = INL child /\
  pop_element (ArrayV (DynArrayV vs)) = INL short /\
  assign_subscripts rt root path (Replace short) = INL updated ==>
  ?k et cap left right.
    mem_path_offset rt path = SOME (k,ArrayTV et (Dynamic cap)) /\
    supp = left UNION right /\ DISJOINT left right /\
    pop_live_support rt updated addr left /\
    pop_live_support et child (addr+k+32+(LENGTH vs-1)*type_memory_size et) right
Proof
  strip_tac >> drule_all pop_supported_array_offset >> strip_tac >>
  drule_all assign_subscripts_pop_replace >>
  disch_then (fn th => rule_assum_tac (PURE_REWRITE_RULE [GSYM th])) >>
  `vs = FRONT vs ++ [LAST vs]` by metis_tac[APPEND_FRONT_LAST] >>
  `child = LAST vs` by gvs[popped_value_def] >>
  qpat_x_assum `evaluate_subscripts _ _ _ = _` mp_tac >>
  once_asm_rewrite_tac[] >> strip_tac >>
  drule_all pop_path_support_split >> strip_tac >>
  qexistsl_tac [`k`, `et`, `cap`, `left`, `right`] >>
  gvs[LENGTH_FRONT]
QED

Theorem pop_path_offset_append:
  !p rt kp ptv q kq qtv.
  mem_path_offset rt p = SOME (kp,ptv) /\
  mem_path_offset ptv q = SOME (kq,qtv) ==>
  mem_path_offset rt (p ++ q) = SOME (kp+kq,qtv)
Proof
  Induct_on `p` >> simp[mem_path_offset_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  PairCases_on `z` >> gvs[] >> first_x_assum drule_all >>
  strip_tac >> qexists_tac `(z0+kq,qtv)` >> simp[AC ADD_ASSOC ADD_COMM]
QED

Theorem pop_recorded_child_offset:
  pop_live_support rt root addr supp /\
  evaluate_subscripts rt root path = INL (ArrayV (DynArrayV vs)) /\ vs <> [] /\
  mem_path_offset rt path = SOME (k,ArrayTV et (Dynamic cap)) ==>
  mem_path_offset rt (path ++ [ValueSubscript (IntV &(LENGTH vs-1))]) =
    SOME (k+32+(LENGTH vs-1)*type_memory_size et,et)
Proof
  strip_tac >> drule_all pop_path_support_extract >> strip_tac >>
  drule pop_live_support_typed >> simp[value_has_type_def] >> strip_tac >>
  `0 < LENGTH vs` by simp[LENGTH_NON_NIL] >>
  irule mem_path_offset_snoc >> goal_assum (drule_at Any) >>
  simp[mem_step_offset_def] >> decide_tac
QED

Theorem pop_historical_update_zipper:
  read_popped rt q fresh = SOME arr /\
  replace_popped rt q short fresh = SOME fresh' ==>
  ?pre p old post ptv updated.
    fresh = pre ++ (p,old)::post /\
    fresh' = pre ++ (p,updated)::post /\
    read_popped rt q pre = NONE /\ IS_PREFIX q p /\
    subscripts_type rt p = SOME ptv /\
    evaluate_subscripts ptv old (DROP (LENGTH p) q) = INL arr /\
    assign_subscripts ptv old (DROP (LENGTH p) q) (Replace short) = INL updated
Proof
  strip_tac >> drule pop_owner_read_decompose >> strip_tac >> gvs[] >>
  drule_all pop_owner_replace_exact >>
  disch_then (qspec_then `short` mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `!post' hs'. _` (qspecl_then [`post`,`fresh'`] mp_tac) >>
  simp[] >> strip_tac >> metis_tac[]
QED

Theorem pop_prefix_drop_offset:
  IS_PREFIX q p /\ mem_path_offset rt p = SOME (kp,ptv) /\
  mem_path_offset ptv (DROP (LENGTH p) q) = SOME (kr,ct) ==>
  mem_path_offset rt q = SOME (kp+kr,ct)
Proof
  strip_tac >>
  `q = p ++ DROP (LENGTH p) q` by
    (drule rich_listTheory.IS_PREFIX_IMP_TAKE >>
     metis_tac[TAKE_DROP]) >>
  metis_tac[pop_path_offset_append]
QED

Theorem pop_relative_source_split:
  IS_PREFIX q p /\ mem_path_offset rt p = SOME (kp,ptv) /\
  pop_live_support ptv old (addr+kp) supp /\
  evaluate_subscripts ptv old (DROP (LENGTH p) q) = INL (ArrayV (DynArrayV vs)) /\ vs <> [] /\
  popped_value (ArrayV (DynArrayV vs)) = INL child /\
  pop_element (ArrayV (DynArrayV vs)) = INL short /\
  assign_subscripts ptv old (DROP (LENGTH p) q) (Replace short) = INL updated ==>
  ?k kc et cap left right.
    mem_path_offset rt q = SOME (k,ArrayTV et (Dynamic cap)) /\
    mem_path_offset rt (q ++ [ValueSubscript (IntV &(LENGTH vs-1))]) = SOME (kc,et) /\
    supp = left UNION right /\ DISJOINT left right /\
    pop_live_support ptv updated (addr+kp) left /\
    pop_live_support et child (addr+kc) right
Proof
  strip_tac >> drule_all pop_source_support_split >> strip_tac >>
  drule_all pop_recorded_child_offset >> strip_tac >>
  `mem_path_offset rt q = SOME (kp+k,ArrayTV et (Dynamic cap))` by
    (irule pop_prefix_drop_offset >> goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `q = p ++ DROP (LENGTH p) q` by
    (drule rich_listTheory.IS_PREFIX_IMP_TAKE >> metis_tac[TAKE_DROP]) >>
  `mem_path_offset rt (q ++ [ValueSubscript (IntV &(LENGTH vs-1))]) =
    SOME (kp+(k+32+(LENGTH vs-1)*type_memory_size et),et)` by
    (once_asm_rewrite_tac[] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
     irule pop_path_offset_append >> goal_assum (drule_at Any) >> simp[]) >>
  qexistsl_tac [`kp+k`, `kp+(k+32+(LENGTH vs-1)*type_memory_size et)`,
    `et`, `cap`, `left`, `right`] >>
  FULL_SIMP_TAC bool_ss [ADD_ASSOC]
QED

Theorem pop_historical_support_split:
  read_popped rt q fresh = SOME (ArrayV (DynArrayV vs)) /\ vs <> [] /\
  popped_value (ArrayV (DynArrayV vs)) = INL child /\
  pop_element (ArrayV (DynArrayV vs)) = INL short /\
  replace_popped rt q short fresh = SOME fresh' /\
  (!j p v. j < LENGTH fresh /\ EL j fresh = (p,v) ==>
    ?kp ptv. mem_path_offset rt p = SOME (kp,ptv) /\
      pop_live_support ptv v (addr+kp) (supps (SUC j))) ==>
  ?pre p old post ptv kp updated k kc et cap left right.
    fresh = pre ++ (p,old)::post /\ fresh' = pre ++ (p,updated)::post /\
    mem_path_offset rt p = SOME (kp,ptv) /\
    mem_path_offset rt q = SOME (k,ArrayTV et (Dynamic cap)) /\
    mem_path_offset rt (q ++ [ValueSubscript (IntV &(LENGTH vs-1))]) = SOME (kc,et) /\
    supps (SUC (LENGTH pre)) = left UNION right /\ DISJOINT left right /\
    pop_live_support ptv updated (addr+kp) left /\
    pop_live_support et child (addr+kc) right
Proof
  strip_tac >> drule_all pop_historical_update_zipper >> strip_tac >>
  `?kp ot. mem_path_offset rt p = SOME (kp,ot) /\
      pop_live_support ot old (addr+kp) (supps (SUC (LENGTH pre)))` by
    (first_x_assum (qspecl_then [`LENGTH pre`, `p`, `old`] mp_tac) >>
     simp[EL_APPEND_EQN]) >>
  drule mem_path_offset_sound >> strip_tac >> gvs[] >>
  drule_all pop_relative_source_split >> strip_tac >> metis_tac[]
QED
