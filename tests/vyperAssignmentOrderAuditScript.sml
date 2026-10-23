(* Issue #550: closed semantic proofs and source-derived regression certificates. *)
Theory vyperAssignmentOrderAudit
Ancestors
  vyperSmallStep vyperTypeEvalSoundness vyperTypeEvalStoragePreservation
  vyperStorageRegionWrite vyperStoragePlaceProvenance vyperPlaceStoragePreservation
  evalAssignmentOrder

fun check_closed (thy,name) =
  let
    val th = DB.fetch thy name
    val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then
      ()
    else raise Fail ("assignment-order proof is not closed: " ^ thy ^ "." ^ name)
  end;

val () = List.app check_closed
  [("vyperSmallStep","eval_cps_eq"),
   ("vyperTypeEvalSoundness","eval_scc_type_sound_mutual"),
   ("vyperTypeEvalSoundness","eval_all_type_sound_mutual"),
   ("vyperTypeEvalStoragePreservation","eval_scc_storage_preservation_mutual"),
   ("vyperTypeEvalStoragePreservation","eval_all_storage_preservation_mutual"),
   ("vyperStorageRegionWrite","storage_subregion_typed_write_preserves_root"),
   ("vyperStoragePlaceProvenance","eval_target_place_region"),
   ("vyperPlaceStoragePreservation","write_place_preserves_contract_storage")];

val () = List.app (fn (name,_) => check_closed ("evalAssignmentOrder",name))
  (DB.thms "evalAssignmentOrder");
