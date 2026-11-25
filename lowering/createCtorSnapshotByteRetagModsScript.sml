(* Retag a saved bytestring value at the linked constructor boundary. *)
Theory createCtorSnapshotByteRetagMods
Ancestors
  bodyFullPostsMods exprSimProps exprSimMemDefs bodyPtrDefs loweringPosts
  exprLowering valueCopyBytes valueEncodingProps compileEnv context
  vyperState vyperTypeSystem

Theorem snapshot_local_base_retag[local]:
  local_val_at ce cx n k (BaseTV bt1) v /\
  val_wf (BaseTV bt1) v /\
  val_footprint (BaseTV bt1) v = val_footprint (BaseTV bt2) v ==>
  local_val_at ce cx n k (BaseTV bt2) v
Proof
  simp[local_val_at_def] >> rpt strip_tac >> disj2_tac
  >- (qexists `bt1` >> simp[] >> metis_tac[val_footprint_le]) >>
  qexists `bt0` >> simp[]
QED

Theorem snapshot_bytes_val_at_retag[local]:
  is_bytestring_type src /\ is_bytestring_type dst /\
  evaluate_type (get_tenv cx) src = SOME a /\
  evaluate_type (get_tenv cx) dst = SOME b /\
  value_has_type a v /\ value_has_type b v /\ val_wf b v /\
  expr_val_at ce cx src sa sb ee v op t ==>
  expr_val_at ce cx dst sa sb ee v op t
Proof
  strip_tac >>
  `~is_word_type src /\ ~is_word_type dst` by metis_tac[is_bytestring_word_type] >>
  `val_footprint a v = val_footprint b v` by metis_tac[bytestring_val_footprint_eq] >>
  `!n k. local_val_at ce cx n k a v ==> local_val_at ce cx n k b v` by
    (`?bt1. a = BaseTV bt1` by metis_tac[bytestring_type_value] >>
     `?bt2. b = BaseTV bt2` by metis_tac[bytestring_type_value] >>
     `val_wf a v` by fs[expr_val_at_def] >>
     gvs[] >> metis_tac[snapshot_local_base_retag]) >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def] >> rpt strip_tac >> metis_tac[]
QED

Theorem snapshot_bytes_ptr_retag[local]:
  is_bytestring_type src /\ is_bytestring_type dst /\
  evaluate_type (get_tenv cx) src = SOME a /\
  evaluate_type (get_tenv cx) dst = SOME b /\
  value_has_type a v /\ value_has_type b v /\
  ptr_mem_ok cx src v op G tn t ==>
  ptr_mem_ok cx dst v op G tn t
Proof
  strip_tac >>
  `val_footprint a v = val_footprint b v` by metis_tac[bytestring_val_footprint_eq] >>
  `val_store_size a v = val_store_size b v` by metis_tac[bytestring_val_store_size_eq] >>
  fs[ptr_mem_ok_def] >> rpt strip_tac >> gvs[] >>
  metis_tac[bytestring_val_in_memory_transfer]
QED

Theorem ctor_snapshot_bytes_retag_mods:
  is_bytestring_type src /\ is_bytestring_type dst /\
  evaluate_type (get_tenv cx) src = SOME a /\
  evaluate_type (get_tenv cx) dst = SOME b /\
  value_has_type a v /\ value_has_type b v /\ val_wf b v /\
  read_result cx raw ee = (INL v,ee) /\
  ((?tag op. vv = StackValue tag op) \/
   (?tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory)) /\
  vv_holds_mods ce cx src raw vv ee t /\
  vv_at ce cx src sa sb ee raw vv t /\
  ptr_vv_ok cx src raw vv ee G tn t /\
  vv_store_bound cx src dst ee raw vv t ==>
  vv_holds_mods ce cx dst (Value v) (ext_call_arg_value dst vv) ee t /\
  vv_at ce cx dst sa sb ee (Value v) (ext_call_arg_value dst vv) t /\
  ptr_vv_ok cx dst (Value v) (ext_call_arg_value dst vv) ee G tn t /\
  vv_store_bound cx dst dst ee (Value v) (ext_call_arg_value dst vv) t
Proof
  strip_tac >>
  `~is_word_type src /\ ~is_word_type dst` by metis_tac[is_bytestring_word_type] >>
  `expr_val_at ce cx src sa sb ee v (vv_operand vv) t` by
    (Cases_on `vv` >> gvs[vv_operand_def] >> metis_tac[vv_at_def, vv_at_memory_val_at]) >>
  `expr_val_rel cx src v (vv_operand vv) t` by
    (Cases_on `vv` >> gvs[vv_operand_def, vv_holds_mods_def, vv_holds_def,
       expr_val_rel_def] >> metis_tac[]) >>
  `expr_val_at ce cx dst sa sb ee v (vv_operand vv) t` by
    (irule snapshot_bytes_val_at_retag >> metis_tac[]) >>
  `expr_val_rel cx dst v (vv_operand vv) t` by
    (qpat_x_assum `expr_val_rel cx src _ _ _` mp_tac >>
     simp[expr_val_rel_def] >> metis_tac[bytestring_val_in_memory_transfer]) >>
  `val_store_size a v = val_store_size b v` by metis_tac[bytestring_val_store_size_eq] >>
  `read_result cx (Value v) ee = (INL v,ee)` by simp[read_result_def, return_def] >>
  gvs[ext_call_arg_value_def, vv_operand_def] >>
  (conj_tac >-
     (simp[vv_holds_mods_def, vv_holds_def] >> fs[expr_val_rel_def] >> metis_tac[])) >>
  (conj_tac >-
     (simp[vv_at_def] >>
      qpat_assum `expr_val_at ce cx dst _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [expr_val_at_def]) >> simp[local_place_at_def])) >>
  (conj_tac >-
     (gvs[ptr_vv_ok_def, ptr_val_ok_def] >> metis_tac[snapshot_bytes_ptr_retag])) >>
  gvs[vv_store_bound_def]
QED
