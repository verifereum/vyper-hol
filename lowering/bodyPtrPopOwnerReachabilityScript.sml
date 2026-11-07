Theory bodyPtrPopOwnerReachability
Ancestors bodyPtrPopOwnerSelection bodyPtrPopForestSelect bodyPtrPopHistoryStore
  vyperPlaceResultTyping vyperState list

(* Source-only transitions record how trusted owners were obtained. The
   observation predicate pop_retained_forest alone has no such history.
   Opaque pre-capture snapshots and all memory properties stay external. *)
Inductive pop_owner_step:
  (!rt root fresh q vs child short root'.
    evaluate_subscripts rt root q = INL (ArrayV (DynArrayV vs)) /\ vs <> [] /\
    popped_value (ArrayV (DynArrayV vs)) = INL child /\
    pop_element (ArrayV (DynArrayV vs)) = INL short /\
    assign_subscripts rt root q (Replace short) = INL root' ==>
    pop_owner_step rt root fresh q root'
      (record_pop q (ArrayV (DynArrayV vs)) child fresh)) /\
  (!rt root fresh q vs child short fresh' err.
    evaluate_subscripts rt root q = INR err /\
    read_popped rt q fresh = SOME (ArrayV (DynArrayV vs)) /\ vs <> [] /\
    popped_value (ArrayV (DynArrayV vs)) = INL child /\
    pop_element (ArrayV (DynArrayV vs)) = INL short /\
    replace_popped rt q short fresh = SOME fresh' ==>
    pop_owner_step rt root fresh q root
      (record_pop q (ArrayV (DynArrayV vs)) child fresh'))
End

(* Reflexive finite iteration starts from exactly one live root. *)
Inductive pop_owner_reachable:
  (!rt initial. pop_owner_reachable rt initial initial []) /\
  (!rt initial root fresh q root' fresh'.
    pop_owner_reachable rt initial root fresh /\
    pop_owner_step rt root fresh q root' fresh' ==>
    pop_owner_reachable rt initial root' fresh')
End

Theorem pop_owner_reachable_init:
  pop_owner_reachable rt initial initial []
Proof
  simp[pop_owner_reachable_rules]
QED

Theorem pop_owner_step_invert:
  pop_owner_step rt root fresh q root' next ==>
  ?vs child short.
    vs <> [] /\ popped_value (ArrayV (DynArrayV vs)) = INL child /\
    pop_element (ArrayV (DynArrayV vs)) = INL short /\
    ((evaluate_subscripts rt root q = INL (ArrayV (DynArrayV vs)) /\
      assign_subscripts rt root q (Replace short) = INL root' /\
      next = record_pop q (ArrayV (DynArrayV vs)) child fresh) \/
     (?err fresh'. evaluate_subscripts rt root q = INR err /\ root' = root /\
      read_popped rt q fresh = SOME (ArrayV (DynArrayV vs)) /\
      replace_popped rt q short fresh = SOME fresh' /\
      next = record_pop q (ArrayV (DynArrayV vs)) child fresh'))
Proof
  simp[Once pop_owner_step_cases] >> metis_tac[]
QED

Theorem pop_owner_replace_append:
  read_popped rt q fresh = SOME v /\
  replace_popped rt q replacement fresh = SOME fresh' ==>
  replace_popped rt q replacement (fresh ++ old) = SOME (fresh' ++ old)
Proof
  strip_tac >> drule pop_owner_read_decompose >> strip_tac >> gvs[] >>
  drule_all pop_owner_replace_exact >>
  disch_then (qspec_then `replacement` mp_tac) >>
  simp[] >> strip_tac >>
  `?updated. assign_subscripts ptv old' (DROP (LENGTH p) q) (Replace replacement) = INL updated /\
    fresh' = pre ++ (p,updated)::post` by
    (qpat_x_assum `!post' hs'. _` (qspecl_then [`post`,`fresh'`] mp_tac) >>
     simp[]) >>
  gvs[] >> first_x_assum (qspecl_then [`post ++ old`,`pre ++ (p,updated)::(post ++ old)`] mp_tac) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[]
QED

Theorem pop_owner_record_append:
  record_pop q arr child (fresh ++ old) = record_pop q arr child fresh ++ old
Proof
  Cases_on `arr` >> simp[record_pop_def] >> Cases_on `a` >> simp[record_pop_def]
QED

Theorem pop_owner_step_entry_bridge:
  pop_owner_step rt root fresh q root' next /\
  entry.type = rt /\ entry.value = root /\ entry.popped = fresh ++ old ==>
  entry_pop_step entry q (entry with <|value := root'; popped := next ++ old|>)
Proof
  strip_tac >> drule pop_owner_step_invert >> strip_tac
  >- (simp[entry_pop_step_def] >>
      qexistsl_tac [`ArrayV (DynArrayV vs)`,`child`,`short`,`root'`] >>
      simp[read_memory_path_def, pop_owner_record_append]) >>
  `read_popped rt q (fresh ++ old) = SOME (ArrayV (DynArrayV vs))` by
    (irule read_popped_prefix_noninterference >> simp[]) >>
  `replace_popped rt q short (fresh ++ old) = SOME (fresh' ++ old)` by
    (irule pop_owner_replace_append >> goal_assum (drule_at Any) >> simp[]) >>
  simp[entry_pop_step_def] >>
  qexistsl_tac [`ArrayV (DynArrayV vs)`,`child`,`short`,`fresh' ++ old`] >>
  simp[read_memory_path_def, pop_owner_record_append]
QED

Theorem pop_owner_step_pop_place:
  pop_owner_step rt root fresh q root' next /\
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
  entry.assignable /\ entry.type = rt /\ entry.value = root /\
  entry.popped = fresh ++ old ==>
  ?vs:value list. vs <> [] /\
    pop_place cx (MemoryPlace id q) es =
      (INL (PlaceR (MemoryPlace id
        (q ++ [ValueSubscript (IntV &(LENGTH vs - 1))]))),
       es with scopes := pre ++
         (sc |+ (id,entry with <|value := root'; popped := next ++ old|>))::rest)
Proof
  strip_tac >> drule pop_owner_step_invert >> strip_tac
  >- (qexists_tac `vs` >>
      gvs[vyperValueOperationTheory.pop_element_def, vyperValueOperationTheory.popped_value_def] >>
      drule pop_live_owner_source_step >>
      disch_then (qspecl_then [`vs`,`root'`,`q`,`cx`] mp_tac) >>
      simp[pop_owner_record_append]) >>
  qexists_tac `vs` >> simp[] >>
  `read_memory_path entry q = INL (ArrayV (DynArrayV vs))` by
    (drule read_popped_prefix_noninterference >>
     disch_then (qspec_then `old` assume_tac) >> simp[read_memory_path_def]) >>
  `replace_popped rt q short (fresh ++ old) = SOME (fresh' ++ old)` by
    (irule pop_owner_replace_append >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[vyperValueOperationTheory.pop_element_def, vyperValueOperationTheory.popped_value_def] >>
  `replace_popped entry.type q (ArrayV (DynArrayV (FRONT vs))) entry.popped =
    SOME (fresh' ++ old)` by simp[] >>
  drule_all pop_historical_owner_source_step >>
  simp[pop_owner_record_append]
QED
