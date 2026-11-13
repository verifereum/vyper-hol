Theory bodyPtrPopNestedLiveSource
Ancestors
  bodyPtrPopTargetDefs bodySimAugPlaceMemory targetPlaceSimCasesBase
  targetLocalLive targetPlaceLive targetPlaceSim vyperPlaceFrames vyperInterpreter vyperState
  list pair sum

Theorem local_target_live_base_resolves:
  !bt cenv cx env id s path t entry vt.
    target_root bt = NameTarget id /\ target_pre cenv cx env bt s /\
    type_place_target env bt = SOME vt /\
    eval_base_place cx bt s = (INL (PlaceR (MemoryPlace id path)),t) /\
    lookup_scopes id t.scopes = SOME entry ==>
    ?v. evaluate_subscripts entry.type entry.value path = INL v
Proof
  rpt strip_tac >> drule_all local_base_place_live >> simp[]
QED

Theorem local_target_live_resolves:
  !bt cenv cx env id s path t entry vt.
    target_root bt = NameTarget id /\ target_pre cenv cx env bt s /\
    type_place_target env bt = SOME vt /\
    eval_target_place cx bt s = (INL (MemoryPlace id path),t) /\
    lookup_scopes id t.scopes = SOME entry ==>
    ?v. evaluate_subscripts entry.type entry.value path = INL v
Proof
  metis_tac[targetLocalLiveTheory.local_target_live]
QED

Theorem local_target_live_no_popped_fallback:
  !bt cenv cx env id s path t entry err vt.
    target_root bt = NameTarget id /\ target_pre cenv cx env bt s /\
    type_place_target env bt = SOME vt /\
    eval_target_place cx bt s = (INL (MemoryPlace id path),t) /\
    lookup_scopes id t.scopes = SOME entry /\
    evaluate_subscripts entry.type entry.value path = INR err ==>
    read_popped entry.type path entry.popped = NONE
Proof
  rpt strip_tac >> drule_all local_target_live_resolves >> simp[]
QED
