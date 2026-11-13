(* Physical bytestring capacities do not change pointer representations. *)
Theory abiEncTuplePtrMaterializeStore
Ancestors
  assignTuplePtrLocalCompat abiEncodeMaterialize bodyPtrDefs
  valueCopyBytes valueEncodingDefs valueEncodingProps compileEnv context
  vyperValue vyperTyping loweringPosts exprSimProps

Theorem materialize_bytestring_ptr_layout:
  is_bytestring_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  is_bytestring_type dt /\ evaluate_type (get_tenv cx) dt = SOME dtv /\
  value_has_type tv v /\ value_has_type dtv v /\
  ptr_val_ok cx ty v op G tn s ==>
  ptr_val_ok cx dt v op G tn s
Proof
  strip_tac >>
  `~is_word_type ty /\ ~is_word_type dt` by
    metis_tac[is_bytestring_word_type] >>
  `(?n. tv = BaseTV (StringT n)) \/
   (?n. tv = BaseTV (BytesT (Dynamic n)))` by
    metis_tac[bytestring_evaluated_shape_ptr] >>
  `(?n. dtv = BaseTV (StringT n)) \/
   (?n. dtv = BaseTV (BytesT (Dynamic n)))` by
    metis_tac[bytestring_evaluated_shape_ptr] >>
  gvs[ptr_val_ok_def, ptr_mem_ok_def] >> rpt strip_tac
  >- metis_tac[bytestring_robust_representation_compat_ptr] >>
  Cases_on `v` >>
  gvs[value_has_type_def, val_footprint_def, val_store_size_def, val_in_memory_def]
QED
