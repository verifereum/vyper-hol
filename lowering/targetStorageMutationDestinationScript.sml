Theory targetStorageMutationDestination
Ancestors
  targetStorageReadRoot stmtSimAugAssignPlace targetPlaceSim targetPlaceSimCasesBase vyperAST vyperInterpreter vyperSubscriptOverlap vyperState

Theorem target_root_write_member[local]:
  !bt ns. target_root bt = TopLevelNameTarget ns ==>
    MEM (WriteAcc (StateRef ns)) (accesses_target bt)
Proof
  ho_match_mp_tac base_assignment_target_induct >>
  simp[target_root_def, accesses_expr_def] >> metis_tac[]
QED

Theorem eval_base_place_storage_mutation_destination:
  !bt cx st tr slot tv sm.
    eval_base_place cx bt st = (INL (PlaceR (StoragePlace tr slot tv)),sm) ==>
    ?mid name keys root rtv path delta.
      MEM (WriteAcc (StateRef (mid,name))) (accesses_target bt) /\
      declared_storage_region cx mid name keys = SOME (tr,root,rtv) /\
      storage_subregion rtv path delta tv /\ slot = root + n2w delta
Proof
  rpt strip_tac >>
  `(?id. target_root bt = NameTarget id) \/
   (?mid name. target_root bt = TopLevelNameTarget (mid,name))` by
    (qid_spec_tac `bt` >> recInduct base_assignment_target_induct >>
     simp[target_root_def] >> Cases_on `nsid` >> simp[]) 
  >- (drule_all aug_place_name_root_base >> simp[]) >>
  drule_all eval_base_place_named_region >> simp[] >> strip_tac >>
  goal_assum (drule_at Any) >>
  metis_tac[target_root_write_member]
QED

Theorem eval_target_place_storage_mutation_destination:
  !bt cx st tr slot tv sm.
    eval_target_place cx bt st = (INL (StoragePlace tr slot tv),sm) ==>
    ?mid name keys root rtv path delta.
      MEM (WriteAcc (StateRef (mid,name))) (accesses_target bt) /\
      declared_storage_region cx mid name keys = SOME (tr,root,rtv) /\
      storage_subregion rtv path delta tv /\ slot = root + n2w delta
Proof
  rpt gen_tac >> simp[Once evaluate_def, bind_def, get_place_def,
                         return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
  drule eval_base_place_storage_mutation_destination >> simp[]
QED
