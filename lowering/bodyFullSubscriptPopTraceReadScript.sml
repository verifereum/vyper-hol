Theory bodyFullSubscriptPopTraceRead
Ancestors
  exprSimPopNestedLocalPath vyperPlaceResultTyping vyperPlaceStatePreservation
  vyperEvalExprPreservesScopesDom vyperTyping vyperState vyperValueOperation
  vyperAssignPreservesType rich_list

(* The read and the replacement follow the same first successful owner. *)
Theorem replace_popped_tracks_live[local]:
  !hist tv path arr short hist' live P dt.
    well_formed_type_value tv /\ subscripts_type tv path = SOME dt /\
    value_has_type dt short /\
    (!k t v r u. subscripts_type tv k = SOME t /\ value_has_type t v /\
       P k t v /\ subscripts_type t r = SOME dt /\
       evaluate_subscripts t v r = INL arr /\
       assign_subscripts t v r (Replace short) = INL u ==> P k t u) /\
    EVERY (\(k,v). live k ==> ?t. subscripts_type tv k = SOME t /\
                                 value_has_type t v /\ P k t v) hist /\
    read_popped tv path hist = SOME arr /\
    replace_popped tv path short hist = SOME hist' ==>
    EVERY (\(k,v). live k ==> ?t. subscripts_type tv k = SOME t /\
                                 value_has_type t v /\ P k t v) hist'
Proof
  Induct >- simp[replace_popped_def] >>
  qx_gen_tac `head` >> PairCases_on `head` >> rpt gen_tac >> simp[] >>
  strip_tac >>
  gvs[read_popped_def, replace_popped_def, AllCaseEqs()]
  >~ [`live _ ==> value_has_type _ _ /\ _`] >-
   (strip_tac >> gvs[IS_PREFIX_APPEND, DROP_LENGTH_APPEND] >>
    `subscripts_type ptv l = SOME dt` by
      metis_tac[vyperPlaceResultTypingTheory.subscripts_type_append] >>
    `well_formed_type_value ptv` by metis_tac[subscripts_type_well_formed] >>
    conj_tac
    >- metis_tac[assign_subscripts_replace_type_metadata] >>
    first_assum irule >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem live_read_tracks[local]:
  (!k r. live (k ++ r) ==> live k) /\
  (!k t v r tr w. value_has_type t v /\ P k t v /\
       subscripts_type t r = SOME tr /\ evaluate_subscripts t v r = INL w /\
       live (k ++ r) ==> P (k ++ r) tr w) /\
  value_has_type entry.type entry.value /\ P [] entry.type entry.value /\
  EVERY (\(k,v). live k ==> ?t. subscripts_type entry.type k = SOME t /\
                               value_has_type t v /\ P k t v) entry.popped /\
  live path /\ subscripts_type entry.type path = SOME t /\
  read_memory_path entry path = INL w ==>
  P path t w
Proof
  simp[read_memory_path_def, AllCaseEqs()] >> rpt strip_tac
  >- (qpat_assum `!k t v r tr w. value_has_type t v /\ _ ==> _`
        (qspec_then `[]` (irule o SRULE [])) >>
      simp[] >> qexistsl [`entry.type`, `entry.value`] >> simp[]) >>
  drule read_popped_owner >> strip_tac >>
  `live prefix` by metis_tac[] >>
  gvs[listTheory.EVERY_MEM] >>
  qpat_x_assum `!e. MEM e _ ==> _` (drule_then mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  `subscripts_type ptv suffix = SOME t` by
    metis_tac[vyperPlaceResultTypingTheory.subscripts_type_append] >>
  metis_tac[]
QED

Theorem typed_dynamic_pop_last[local]:
  value_has_type (ArrayTV et (Dynamic n)) (ArrayV (DynArrayV vs)) /\ vs <> [] ==>
  subscripts_type (ArrayTV et (Dynamic n))
    [ValueSubscript (IntV &(LENGTH vs - 1))] = SOME et /\
  evaluate_subscripts (ArrayTV et (Dynamic n)) (ArrayV (DynArrayV vs))
    [ValueSubscript (IntV &(LENGTH vs - 1))] = INL (LAST vs) /\
  value_has_type et (LAST vs)
Proof
  strip_tac >>
  `LENGTH vs <= n` by fs[value_has_type_def] >>
  `0 < LENGTH vs` by simp[listTheory.LENGTH_NON_NIL] >>
  `LENGTH vs - 1 < n` by decide_tac >>
  `LENGTH vs - 1 < LENGTH vs` by decide_tac >>
  conj_tac >- simp[subscripts_type_def, subscript_type_def] >>
  conj_tac
  >- simp[evaluate_subscripts_def, array_index_def, listTheory.oEL_THM,
          listTheory.LAST_EL, arithmeticTheory.PRE_SUB1] >>
  irule vyperTypeStatePreservationTheory.popped_value_well_typed >>
  qexistsl [`ArrayV (DynArrayV vs)`, `n`] >> simp[popped_value_def]
QED

(* Track the newly detached last child using the pre-pop read, then
   preserve the predicate on the roots which remain after the update. *)
Theorem entry_pop_step_tracks_live[local]:
  (!k r. live (k ++ r) ==> live k) /\
  (!k t v r tr w. value_has_type t v /\ P k t v /\
       subscripts_type t r = SOME tr /\ evaluate_subscripts t v r = INL w /\
       live (k ++ r) ==> P (k ++ r) tr w) /\
  (!k t v r et n vs u. value_has_type t v /\ P k t v /\
       subscripts_type t r = SOME (ArrayTV et (Dynamic n)) /\ vs <> [] /\
       evaluate_subscripts t v r = INL (ArrayV (DynArrayV vs)) /\
       assign_subscripts t v r (Replace (ArrayV (DynArrayV (FRONT vs)))) = INL u ==>
       P k t u) /\
  P [] entry.type entry.value /\
  EVERY (\(k,v). live k ==> ?t. subscripts_type entry.type k = SOME t /\
                               value_has_type t v /\ P k t v) entry.popped /\
  entry_pop_event_valid (entry,path) /\ entry_pop_step entry path next ==>
  value_has_type next.type next.value /\ P [] next.type next.value /\
  EVERY (\(k,v). live k ==> ?t. subscripts_type next.type k = SOME t /\
                               value_has_type t v /\ P k t v) next.popped
Proof
  strip_tac >>
  `value_has_type next.type next.value` by
    metis_tac[vyperPlaceMutationSoundnessTheory.entry_pop_step_value_type,
              entry_pop_event_valid_def] >>
  qpat_x_assum `entry_pop_event_valid _` mp_tac >>
  simp[entry_pop_event_valid_def] >> strip_tac >>
  qpat_x_assum `entry_pop_step _ _ _` mp_tac >> simp[entry_pop_step_def] >>
  disch_then (REPEAT_TCL CHOOSE_THEN
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)))) >>
  qpat_x_assum `(?v. _) \/ (?err. _)` mp_tac >>
  rename1 `subscripts_type entry.type path = SOME (ArrayTV et (Dynamic n))` >>
  `?vs. arr = ArrayV (DynArrayV vs)` by
    (Cases_on `arr` >> gvs[value_has_type_def] >>
     rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def]) >>
  gvs[popped_value_def, pop_element_def, record_pop_def, AllCaseEqs()] >>
  drule_all typed_dynamic_pop_last >> strip_tac >>
  qabbrev_tac `last_step = [ValueSubscript (IntV &(LENGTH vs - 1))]` >>
  `live (path ++ last_step) ==> P (path ++ last_step) et (LAST vs)` by
    (strip_tac >>
     `live path` by metis_tac[] >>
     `P path (ArrayTV et (Dynamic n)) (ArrayV (DynArrayV vs))` by
       (irule live_read_tracks >> metis_tac[]) >>
     metis_tac[]) >>
  `subscripts_type entry.type (path ++ last_step) = SOME et` by
    metis_tac[vyperPlaceResultTypingTheory.subscripts_type_append] >>
  simp[] >> strip_tac >> gvs[read_memory_path_def]
  >- metis_tac[listTheory.APPEND] >>
  `read_popped entry.type path entry.popped = SOME (ArrayV (DynArrayV vs))` by
    fs[AllCaseEqs()] >>
  `value_has_type (ArrayTV et (Dynamic n)) (ArrayV (DynArrayV (FRONT vs)))` by
    (irule pop_element_preserves_type >>
     qexists `ArrayV (DynArrayV vs)` >> simp[pop_element_def]) >>
  irule replace_popped_tracks_live >>
  qpat_assum `replace_popped _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `read_popped _ _ _ = _` (irule_at Any) >>
  qpat_assum `subscripts_type entry.type path = _` (irule_at Any) >>
  simp[] >> metis_tac[]
QED

Theorem entry_pop_trace_tracks_live[local]:
  !events entry next live P.
    (!k r. live (k ++ r) ==> live k) /\
    (!k t v r tr w. value_has_type t v /\ P k t v /\
         subscripts_type t r = SOME tr /\ evaluate_subscripts t v r = INL w /\
         live (k ++ r) ==> P (k ++ r) tr w) /\
    (!k t v r et n vs u. value_has_type t v /\ P k t v /\
         subscripts_type t r = SOME (ArrayTV et (Dynamic n)) /\ vs <> [] /\
         evaluate_subscripts t v r = INL (ArrayV (DynArrayV vs)) /\
         assign_subscripts t v r (Replace (ArrayV (DynArrayV (FRONT vs)))) = INL u ==>
         P k t u) /\
    value_has_type entry.type entry.value /\ P [] entry.type entry.value /\
    EVERY (\(k,v). live k ==> ?t. subscripts_type entry.type k = SOME t /\
                                 value_has_type t v /\ P k t v) entry.popped /\
    entry_pop_trace entry events next /\ entry_pop_trace_valid events ==>
    value_has_type next.type next.value /\ P [] next.type next.value /\
    EVERY (\(k,v). live k ==> ?t. subscripts_type next.type k = SOME t /\
                                 value_has_type t v /\ P k t v) next.popped
Proof
  Induct >- simp[] >> qx_gen_tac `ev` >> PairCases_on `ev` >>
  rpt gen_tac >> simp[entry_pop_trace_def] >> strip_tac >>
  qpat_x_assum `ev0 = entry` (SUBST_ALL_TAC o SYM) >>
  drule_all entry_pop_step_tracks_live >> strip_tac >>
  first_x_assum (drule_at (Pat `entry_pop_trace _ _ _`)) >>
  disch_then (qspecl_then [`live`, `P`] irule) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* Only an initially live key can supply an initially live read. Thus no
   snapshot present in the initial entry needs to satisfy P. *)
Theorem subscript_pop_trace_tracks_read:
  value_has_type initial.type initial.value /\
  EVERY (\k. ?err. evaluate_subscripts initial.type initial.value k = INR err)
    (MAP FST initial.popped) /\
  entry_pop_trace initial events entry /\ entry_pop_trace_valid events /\
  (?old. evaluate_subscripts initial.type initial.value p = INL old) /\
  subscripts_type entry.type p = SOME t /\ read_memory_path entry p = INL v /\
  P [] initial.type initial.value /\
  (!k t0 u r t1 w. value_has_type t0 u /\ P k t0 u /\
       subscripts_type t0 r = SOME t1 /\ evaluate_subscripts t0 u r = INL w /\
       (?old. evaluate_subscripts initial.type initial.value (k ++ r) = INL old) ==>
       P (k ++ r) t1 w) /\
  (!k t0 u r et n vs u'. value_has_type t0 u /\ P k t0 u /\
       subscripts_type t0 r = SOME (ArrayTV et (Dynamic n)) /\ vs <> [] /\
       evaluate_subscripts t0 u r = INL (ArrayV (DynArrayV vs)) /\
       assign_subscripts t0 u r (Replace (ArrayV (DynArrayV (FRONT vs)))) = INL u' ==>
       P k t0 u') ==>
  P p t v
Proof
  strip_tac >>
  qabbrev_tac `live = \k. ?old. evaluate_subscripts initial.type initial.value k = INL old` >>
  `!k r. live (k ++ r) ==> live k` by
    (rw[Abbr `live`] >> Cases_on `evaluate_subscripts initial.type initial.value k` >>
     metis_tac[evaluate_subscripts_append_err, sumTheory.sum_distinct]) >>
  `EVERY (\(k,v). live k ==> ?t. subscripts_type initial.type k = SOME t /\
                               value_has_type t v /\ P k t v) initial.popped` by
    (simp[listTheory.EVERY_MEM, pairTheory.FORALL_PROD, Abbr `live`] >> rpt strip_tac >>
     qpat_assum `EVERY _ (MAP FST _)`
       (drule_then strip_assume_tac o SRULE [listTheory.EVERY_MAP, listTheory.EVERY_MEM]) >>
     gvs[]) >>
  `(!k t v r tr w. value_has_type t v /\ P k t v /\
       subscripts_type t r = SOME tr /\ evaluate_subscripts t v r = INL w /\
       live (k ++ r) ==> P (k ++ r) tr w)` by
    (simp[Abbr `live`] >> first_assum ACCEPT_TAC) >>
  drule_all entry_pop_trace_tracks_live >> strip_tac >>
  irule live_read_tracks >> qexistsl [`entry`, `live`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[Abbr `live`] >> metis_tac[]
QED

Theorem front_replace_success_old[local]:
  vs <> [] /\ evaluate_subscripts tv a path = INL (ArrayV (DynArrayV vs)) /\
  assign_subscripts tv a path (Replace (ArrayV (DynArrayV (FRONT vs)))) = INL updated /\
  evaluate_subscripts tv updated r = INL w ==>
  ?w0. evaluate_subscripts tv a r = INL w0
Proof
  strip_tac >> Cases_on `evaluate_subscripts tv a r` >> simp[] >>
  `!ty k e. evaluate_subscripts ty (ArrayV (DynArrayV vs)) k = INR e ==>
           ?e'. evaluate_subscripts ty (ArrayV (DynArrayV (FRONT vs))) k = INR e'` by
    metis_tac[evaluate_subscripts_front_dead] >>
  metis_tac[assign_subscripts_replace_dead, sumTheory.sum_distinct]
QED

Theorem subscript_pop_read_extension_live:
  value_has_type initial.type initial.value /\
  EVERY (\k. ?err. evaluate_subscripts initial.type initial.value k = INR err)
    (MAP FST initial.popped) /\
  entry_pop_trace initial events entry /\ entry_pop_trace_valid events /\
  (?old. evaluate_subscripts initial.type initial.value p = INL old) /\
  subscripts_type entry.type p = SOME t /\ read_memory_path entry p = INL v /\
  evaluate_subscripts t v suffix = INL w ==>
  ?old. evaluate_subscripts initial.type initial.value (p ++ suffix) = INL old
Proof
  strip_tac >>
  qabbrev_tac `P = \k tv u. !r w. evaluate_subscripts tv u r = INL w ==>
    ?old. evaluate_subscripts initial.type initial.value (k ++ r) = INL old` >>
  `P [] initial.type initial.value` by (simp[Abbr `P`] >> metis_tac[]) >>
  `!k t0 u r t1 w. value_has_type t0 u /\ P k t0 u /\
       subscripts_type t0 r = SOME t1 /\ evaluate_subscripts t0 u r = INL w /\
       (?old. evaluate_subscripts initial.type initial.value (k ++ r) = INL old) ==>
       P (k ++ r) t1 w` by
    (simp[NoAsms, Abbr `P`] >> rpt strip_tac >>
     metis_tac[evaluate_subscripts_append, listTheory.APPEND_ASSOC]) >>
  `!k t0 u r et n vs u'. value_has_type t0 u /\ P k t0 u /\
       subscripts_type t0 r = SOME (ArrayTV et (Dynamic n)) /\ vs <> [] /\
       evaluate_subscripts t0 u r = INL (ArrayV (DynArrayV vs)) /\
       assign_subscripts t0 u r (Replace (ArrayV (DynArrayV (FRONT vs)))) = INL u' ==>
       P k t0 u'` by
    (simp[Abbr `P`] >> rpt strip_tac >> metis_tac[front_replace_success_old]) >>
  `P p t v` by
    (irule subscript_pop_trace_tracks_read >>
     qpat_assum `entry_pop_trace initial events entry` (irule_at Any) >>
     qexists `old` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `P p t v` mp_tac >> simp[NoAsms, Abbr `P`] >>
  disch_then (qspecl_then [`suffix`, `w`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC
QED
