Theory vyperPlaceStorage
Ancestors
  vyperPlaceTyping vyperPlaceFrames vyperStorageWritePreservation
  vyperStorageBackend vyperState

(* Raw resolved-slot boundaries deliberately retain region provenance. *)
Theorem read_storage_place_success_type:
  well_formed_type_value tv /\
  read_place cx (StoragePlace b slot tv) st = (INL v,st') ==>
    value_has_type tv v
Proof
  simp[read_place_def] >>
  metis_tac[vyperTypeStatePreservationTheory.read_storage_slot_success_type]
QED

Theorem write_storage_place_establishes_region:
  value_has_type tv v /\ well_formed_type_value tv /\
  write_place cx (StoragePlace b slot tv) v st = (INL (),st') ==>
    slots_in_range (get_storage cx st' b) (w2n slot) tv
Proof
  simp[write_place_def] >>
  metis_tac[typed_write_storage_slot_establishes_region]
QED

Theorem write_storage_place_preserves_disjoint_region:
  slots_in_range (get_storage cx st b2) (w2n slot2) tv2 /\
  value_has_type tv1 v /\
  write_place cx (StoragePlace b1 slot1 tv1) v st = (INL (),st') /\
  (b1 <> b2 \/ ranges_disjoint (w2n slot1) (type_slot_size tv1)
                             (w2n slot2) (type_slot_size tv2)) ==>
    slots_in_range (get_storage cx st' b2) (w2n slot2) tv2
Proof
  simp[write_place_def] >>
  metis_tac[typed_write_storage_slot_preserves_disjoint_region]
QED

Theorem write_storage_place_contained_preserves_contract_storage:
  contract_storage_well_formed cx st /\ storage_layout_safe cx /\
  declared_storage_region cx mid n [] = SOME (b,root_slot,tv) /\
  value_has_type wr_tv wr_v /\
  write_place cx (StoragePlace b wr_slot wr_tv) wr_v st = (INL (),st') /\
  w2n root_slot <= w2n wr_slot /\
  w2n wr_slot + type_slot_size wr_tv <= w2n root_slot + type_slot_size tv /\
  slots_in_range (get_storage cx st' b) (w2n root_slot) tv ==>
    contract_storage_well_formed cx st'
Proof
  pure_rewrite_tac[write_place_def] >>
  rpt strip_tac >>
  irule contained_ordinary_write_preserves_contract_storage_well_formed >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[] >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[arithmeticTheory.ADD_COMM] >> metis_tac[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if List.all (fn s => s = "DISK_THM") oracles andalso null axioms
     then print ("Kernel-closed place storage: " ^ name ^ "\n")
     else raise Fail ("Incomplete place storage: " ^ name)
  end) (DB.thms "vyperPlaceStorage");
