Theory bodyPtrPopNestedLiveSource
Ancestors
  bodyPtrPopTargetDefs bodySimAugPlaceMemory targetPlaceSimCasesBase
  targetPlaceLive targetPlaceSim vyperPlaceFrames vyperInterpreter vyperState
  list pair sum

Theorem local_target_live_base_resolves:
  !bt cx id s path t entry.
    target_root bt = NameTarget id /\ local_target_live cx id bt /\
    eval_base_place cx bt s = (INL (PlaceR (MemoryPlace id path)),t) /\
    lookup_scopes id t.scopes = SOME entry ==>
    ?v. evaluate_subscripts entry.type entry.value path = INL v
Proof
  recInduct base_assignment_target_induct >> rpt conj_tac >> rpt gen_tac
  >- (simp[Once evaluate_def, target_root_def, get_scopes_def, bind_def,
           ignore_bind_def, type_check_def, assert_def, return_def,
           raise_def, AllCaseEqs()] >> rpt strip_tac >>
      gvs[evaluate_subscripts_def])
  >- simp[target_root_def]
  >- suspend "subscript"
  >> suspend "attribute"
QED
Resume local_target_live_base_resolves[subscript]:
  rpt strip_tac >>
  qpat_x_assum `eval_base_place _ (SubscriptTarget _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  strip_tac >>
  drule aug_place_extend_memory_inversion >> strip_tac >> gvs[] >>
  drule extend_place_state >> strip_tac >> gvs[] >>
  gvs[local_target_live_def, target_root_def] >>
  `?w. evaluate_subscripts entry.type entry.value old = INL w` by
    (first_x_assum (drule_then mp_tac) >>
     simp[bind_def] >>
     Cases_on `evaluate_subscripts entry.type entry.value old` >> simp[]) >>
  drule_all aug_place_extend_memory_live >> strip_tac >> gvs[]
QED
Resume local_target_live_base_resolves[attribute]:
  rpt strip_tac >>
  qpat_x_assum `eval_base_place _ (AttributeTarget _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  strip_tac >>
  drule aug_place_extend_memory_inversion >> strip_tac >> gvs[] >>
  drule extend_place_state >> strip_tac >> gvs[] >>
  gvs[local_target_live_def, target_root_def] >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  drule_all aug_place_extend_memory_live >> strip_tac >> gvs[]
QED
Finalise local_target_live_base_resolves

Theorem local_target_live_resolves:
  !bt cx id s path t entry.
    target_root bt = NameTarget id /\ local_target_live cx id bt /\
    eval_target_place cx bt s = (INL (MemoryPlace id path),t) /\
    lookup_scopes id t.scopes = SOME entry ==>
    ?v. evaluate_subscripts entry.type entry.value path = INL v
Proof
  rpt gen_tac >> simp[Once evaluate_def, bind_def, AllCaseEqs()] >>
  rpt strip_tac >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
  drule_all local_target_live_base_resolves >> simp[]
QED

Theorem local_target_live_no_popped_fallback:
  !bt cx id s path t entry err.
    target_root bt = NameTarget id /\ local_target_live cx id bt /\
    eval_target_place cx bt s = (INL (MemoryPlace id path),t) /\
    lookup_scopes id t.scopes = SOME entry /\
    evaluate_subscripts entry.type entry.value path = INR err ==>
    read_popped entry.type path entry.popped = NONE
Proof
  rpt strip_tac >> drule_all local_target_live_resolves >> simp[]
QED
