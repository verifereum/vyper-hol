Theory bodyPtrAttributeStorage
Ancestors
  bodyPtrAttributeCase accountsRelProps vyperStoragePlaceRegion
  exprSimProps loweringPosts compileEnv words arithmetic

(* Agreement, unlike slots_in_range, includes an address-end bound.
   A zero-slot tail may wrap, but has no byte taint obligation. *)
Theorem attribute_storage_field_address:
  storage_holds cx tr ty btv w es s /\
  evaluate_type (get_tenv cx) ty = SOME (StructTV fs) /\
  struct_field_slot fs fld = SOME (off,ftv) /\
  0 < type_slot_size ftv ==>
  w2n (w + n2w off) = w2n w + off
Proof
  strip_tac >> drule struct_field_slot_end_bound >> strip_tac >>
  gvs[storage_holds_def, storage_range_agree_def] >>
  once_rewrite_tac[ADD_COMM] >> irule buffer_offset_no_wrap >>
  qexists_tac `off` >> simp[] >> decide_tac
QED
