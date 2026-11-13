(* Narrow declared struct-region liveness to the actual field slot. *)
Theory augAssignPtrStorageFieldLive
Ancestors
  augAssignPtrLoad accountsRelProps exprSimTopLevelProps bodyPtrDefs
  exprLoweringProps vyperStorageLayoutSafety vyperLookupStorage
  vyperStorageBackend vyperState compileEnv

Theorem declared_storage_field_live_ptr:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr (StructT sid),id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
  struct_field_slot fs fld = SOME (off,ftv) /\ storage_layout_safe cx ==>
  !st. storage_read_live cx tr st (n2w slot + n2w off) ftv
Proof
  strip_tac >>
  `storage_var_info cx src id = SOME (tr,slot,StructTV fs)` by
    simp[storage_var_info_def] >>
  `declared_storage_region cx src id [] = SOME (tr,n2w slot,StructTV fs)` by
    (irule declared_storage_region_ordinary >> simp[]) >>
  gen_tac >> irule storage_read_live_field >>
  goal_assum (drule_at Any) >>
  irule declared_storage_region_read_live >> metis_tac[]
QED

Theorem declared_storage_field_clean_ptr:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr (StructT sid),id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
  struct_field_slot fs fld = SOME (off,ftv) /\ storage_layout_safe cx /\
  0 < type_slot_size ftv /\ ghost_inv d cenv cx es G tn s ==>
  key_taint (if tr then tn.t_trans else tn.t_stor) (n2w slot + n2w off) = {}
Proof
  strip_tac >> drule_all declared_storage_field_live_ptr >> disch_tac >>
  irule live_storage_head_clean >>
  qexistsl [`cx`, `s`, `ftv`] >> fs[ghost_inv_def]
QED
