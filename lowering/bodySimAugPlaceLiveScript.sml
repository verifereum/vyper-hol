Theory bodySimAugPlaceLive
Ancestors
  targetLocalLive targetPlaceSim vyperInterpreter vyperState vyperMisc pair sum

Theorem aug_place_base_memory_live:
  !t cenv cx env s vt id path s'.
    target_pre cenv cx env t s /\ type_place_target env t = SOME vt /\
    eval_base_place cx t s = (INL (PlaceR (MemoryPlace id path)),s') ==>
    ?entry v. lookup_scopes id s'.scopes = SOME entry /\
      evaluate_subscripts entry.type entry.value path = INL v
Proof
  rpt strip_tac >>
  drule_then assume_tac target_base_memory_root_ptr >>
  drule_all local_base_place_live >> simp[]
QED

Theorem aug_place_target_memory_live:
  !t cenv cx env s vt id path s'.
    target_pre cenv cx env t s /\ type_place_target env t = SOME vt /\
    eval_target_place cx t s = (INL (MemoryPlace id path),s') ==>
    ?entry v. lookup_scopes id s'.scopes = SOME entry /\
      evaluate_subscripts entry.type entry.value path = INL v
Proof
  rpt gen_tac >> simp[Once evaluate_def, bind_def, AllCaseEqs()] >>
  rpt strip_tac >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
  drule_all aug_place_base_memory_live >> simp[]
QED
