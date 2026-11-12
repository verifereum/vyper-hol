(* Pointwise immutable-cell frames, including constructor execution. *)
Theory vyperProtectedImmutableFrame
Ancestors
  list pair option finite_map alist vyperState vyperContext
  vyperInterpreter vyperBareGlobalName vyperPlaceFrames
  vyperScopePreservation vyperImmutablesPreservation
  vyperRuntimeWriteSafety vyperMachineFrame
  vyperStoragePlaceProvenance vyperCallOutcomeFrame

Theorem set_immutable_other_cell:
  set_immutable cx src id tv v st = (res,st') /\
  (src <> sid \/ id <> nm) ==>
  lookup_immutable cx st' sid nm = lookup_immutable cx st sid nm
Proof
  simp[set_immutable_def, bind_def, get_address_immutables_def,
       lift_option_type_def, set_address_immutables_def, return_def, raise_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]) >>
  rpt strip_tac >> gvs[] >>
  simp[lookup_immutable_def, set_source_immutables_def,
       get_source_immutables_def, ALOOKUP_ADELKEY, FLOOKUP_UPDATE] >>
  Cases_on `src = sid` >> gvs[FLOOKUP_UPDATE]
QED

Theorem write_immutable_place_other_cell:
  write_place cx (ImmutablePlace src id path) v st = (res,st') /\
  (src <> sid \/ id <> nm) ==>
  lookup_immutable cx st' sid nm = lookup_immutable cx st sid nm
Proof
  simp[write_place_def, bind_def, get_immutables_def,
       get_address_immutables_def, lift_option_type_def, lift_sum_def,
       return_def, raise_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]) >>
  rpt strip_tac >> gvs[] >>
  metis_tac[set_immutable_other_cell]
QED

Theorem pop_immutable_place_other_cell:
  pop_place cx (ImmutablePlace src id path) st = (res,st') /\
  (src <> sid \/ id <> nm) ==>
  lookup_immutable cx st' sid nm = lookup_immutable cx st sid nm
Proof
  simp[pop_place_def, bind_def, ignore_bind_def, get_immutables_def,
       get_address_immutables_def, lift_option_type_def, lift_sum_def,
       return_def, raise_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]) >>
  rpt strip_tac >> gvs[] >>
  metis_tac[set_immutable_other_cell]
QED

Theorem write_place_protected_cell:
  write_place cx pl v st = (res,st') /\
  (!src id path. pl = ImmutablePlace src id path ==> ~protected src id) ==>
  !sid nm. protected sid nm ==>
  lookup_immutable cx st' sid nm = lookup_immutable cx st sid nm
Proof
  Cases_on `pl` >> rpt strip_tac
  >- (drule write_storage_place_immutables >>
      simp[lookup_immutable_def])
  >- (drule write_memory_place_immutables >>
      simp[lookup_immutable_def]) >>
  irule write_immutable_place_other_cell >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem pop_place_protected_cell:
  pop_place cx pl st = (res,st') /\
  (!src id path. pl = ImmutablePlace src id path ==> ~protected src id) ==>
  !sid nm. protected sid nm ==>
  lookup_immutable cx st' sid nm = lookup_immutable cx st sid nm
Proof
  Cases_on `pl` >> rpt strip_tac
  >- (drule pop_storage_place_scopes_immutables >>
      simp[lookup_immutable_def])
  >- (rename1 `pop_place cx (MemoryPlace id path) st = _` >>
      mp_tac machine_frame_pop_memory_place >>
      simp[state_rel_frame_def] >>
      disch_then (qspec_then `st` mp_tac) >>
      simp[machine_frame_def, lookup_immutable_def]) >>
  irule pop_immutable_place_other_cell >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem lookup_global_immutable_root:
  lookup_global cx src id st =
    (INL (PlaceR (ImmutablePlace sid nm path)),st') ==>
  sid = src /\ nm = id /\ path = []
Proof
  simp[lookup_global_def, bind_def, ignore_bind_def, lift_option_type_def,
       get_immutables_def, get_address_immutables_def, return_def, raise_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >>
       gvs[bind_def, ignore_bind_def, lift_option_type_def,
           record_storage_event_def, return_def, raise_def]) >>
  rpt strip_tac >> gvs[bind_def, ignore_bind_def, record_storage_event_def,
                       return_def, raise_def]
QED

Theorem extend_place_immutable_root:
  extend_place cx operand sb st =
    (INL (PlaceR (ImmutablePlace sid nm path)),st') ==>
  ?pre. operand = PlaceR (ImmutablePlace sid nm pre) /\ path = pre ++ [sb]
Proof
  Cases_on `operand`
  >- (simp[extend_place_def, raise_def])
  >- (rename1 `PlaceR pl` >> Cases_on `pl`
      >- (simp[extend_place_def, bind_def, return_def, raise_def] >>
          rpt strip_tac >> gvs[AllCaseEqs()] >>
          drule extend_storage_place_subregion >> strip_tac >> gvs[]) >>
      simp[extend_place_def, bind_def, ignore_bind_def, lift_sum_def,
           return_def, raise_def, extend_memory_place_def] >>
      rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]) >>
      rpt strip_tac >> gvs[]) >>
  Cases_on `sb` >>
  simp[extend_place_def, bind_def, lift_option_type_def,
       record_storage_event_def, return_def, raise_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]) >>
  rpt strip_tac >> gvs[bind_def, ignore_bind_def, record_storage_event_def,
                       return_def, raise_def]
QED

Theorem eval_name_target_memory_root:
  eval_base_place cx (NameTarget id) st = (INL operand,st') ==>
  operand = PlaceR (MemoryPlace id [])
Proof
  simp[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
       type_check_def, assert_def, check_def, return_def, raise_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED
