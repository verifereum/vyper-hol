(* The ordinary value case retains ownership from the raw image and uses
   the header install frame only to transport the length endpoint's bytes. *)
Theory bodyForArrayCaptureOwnedSnapshotMods
Ancestors
  bodyForArrayInstallBackingMods bodyForArrayOwnedInstallRouteMods
  vyperTypeValues vyperState compileEnv

Theorem for_array_capture_owned_snapshot_mods:
  evaluate_type (get_tenv cx) (ArrayT sty bd) = SOME (ArrayTV tv bd) /\
  value_has_type (ArrayTV tv bd) (ArrayV av) /\
  vs = MAP Value (array_elements (ArrayTV tv bd) av) /\
  vv_own c cx (ArrayT sty bd) sa0 sbExpr em (Value (ArrayV av)) vv r /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) /\
  array_length_frame sbExpr r Gr traw z Gz tz /\
  local_ptrs_reserved c sbExpr /\ local_ptrs_reserved c saL /\
  copy_old_operand sbExpr (vv_operand vv) /\ copy_old_operand saL (vv_operand vv) /\
  eval_operand (vv_operand vv) z = SOME a /\
  ptr_mem_ok cx (ArrayT sty bd) (ArrayV av) (vv_operand vv) Gz tz z /\
  (0 < type_memory_size (ArrayTV tv bd) ==>
    w2n a + type_memory_size (ArrayTV tv bd) <= z.vs_alloca_next) /\
  for_array_install_frame_mods saL z Gz tz G' tn' t ==>
  for_array_entry_route_mods c cx lo (sty,bd,LocMemory) (em,sbExpr,z,Gz,tz)
    (vv_operand vv,a) vs (ForArrayOwned av) horizon vs em G' tn' t
Proof
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  `evaluate_type (get_tenv cx) sty = SOME tv` by
    (drule evaluate_type_ArrayT_cases >> simp[]) >>
  `~is_word_type (ArrayT sty bd)` by simp[is_word_type_def] >>
  `read_result cx (Value (ArrayV av)) em = (INL (ArrayV av),em)` by
    simp[read_result_def,return_def] >>
  drule_all_then assume_tac for_array_install_backing_mods >>
  drule_all_then irule for_array_owned_install_route_mods
QED
