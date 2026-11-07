(* Captured source-result adapter for the ordinary completed-copy boundary.
   stmt_state_rel is the existing copy_buffer_storage_contents semantic
   precondition; no pointer ghost or clean-payload premise is needed. *)
Theory storageCopyContentsPtr
Ancestors
  exprSimCopy exprSimStorageCopy loweringPosts compileEnv
  vyperInterpreter vyperState vyperValue

Theorem storage_holds_read_value:
  storage_holds cx tr t tv a es s /\
  read_result cx tv es = (INL v,es) ==>
  storage_holds cx tr t (Value v) a es s
Proof
  simp[storage_holds_def, read_result_def, return_def] >>
  rpt strip_tac >> gvs[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem completed_storage_copy_contents:
  stmt_state_rel ctx func cenv cx es u /\
  storage_holds cx tr t tv a es u /\
  read_result cx tv es = (INL v,es) /\
  evaluate_type (get_tenv cx) t = SOME ty /\
  copy_prefix (if tr then LocTransient else LocStorage)
    a b (type_slot_size ty) u (type_slot_size ty) z ==>
  val_wf ty v /\ val_in_memory ty v b z.vs_memory /\
  val_footprint ty v <= type_memory_size ty
Proof
  rpt strip_tac >>
  `storage_holds cx tr t (Value v) a es u` by
    (irule storage_holds_read_value >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all copy_buffer_storage_contents >> simp[]
QED
