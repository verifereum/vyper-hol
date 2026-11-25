(* Header, payload, and allocation ranges for a linked bytestring hash. *)
Theory bodyBopBytestringHashRangesMods
Ancestors
  bodyPtrBopHashSemantic bodyPtrBopHashFootprint abiEncodeOwnership
  bodyPtrDefs loweringPosts exprSimProps exprLoweringProps compileEnv
  vyperValue vyperTyping venomState words list

Theorem bytestring_hash_ranges_mods:
  is_bytestring_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\
  (v = BytesV bs \/ (?str. v = StringV str /\ bs = MAP (n2w o ORD) str)) /\
  eval_operand (Var p) t = SOME (n2w b) /\
  b + 32 < dimword(:256) /\
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list)
    ctx func cenv cx es t /\
  expr_val_at cenv cx ty sa sb es v (Var p) t /\
  ptr_val_ok cx ty v (Var p) G tn t ==>
  32 + LENGTH bs <= val_footprint tv v /\
  ptr_covers G tn p t 32 /\
  (?base sz. FLOOKUP G p = SOME (base,sz) /\
    (0 < LENGTH bs ==> base <= b+32 /\ b+32+LENGTH bs <= base+sz)) /\
  b + 32 + LENGTH bs <= t.vs_alloca_next /\
  (!i. b <= i /\ i < b+32 ==> i NOTIN tn.t_mem) /\
  (!i. b+32 <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn.t_mem)
Proof
  strip_tac >>
  `~is_word_type ty` by
    (Cases_on `ty` >> gvs[is_bytestring_type_def, is_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[is_bytestring_type_def, is_word_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[is_bytestring_type_def, is_word_type_def]) >>
  `lookup_var p t = SOME (n2w b)` by metis_tac[eval_operand_def] >>
  `32 + LENGTH bs <= val_footprint tv v` by
    (Cases_on `ty` >> gvs[is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[is_bytestring_type_def, evaluate_type_def, value_has_type_def,
       val_footprint_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[is_bytestring_type_def, evaluate_type_def, value_has_type_def,
       val_footprint_def]) >>
  drule_all bop_hash_semantic_ranges >> strip_tac >>
  `ptr_mem_ok cx ty v (Var p) G tn t` by gvs[ptr_val_ok_def] >>
  `(!i. b <= i /\ i < b+32 ==> i NOTIN tn.t_mem) /\
   (!i. b+32 <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn.t_mem)` by
    (Cases_on `ty` >> gvs[is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[is_bytestring_type_def, evaluate_type_def] >-
       (gvs[value_has_type_def] >> drule ptr_mem_ok_string_clean >>
        simp[evaluate_type_def]) >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[is_bytestring_type_def, evaluate_type_def, value_has_type_def] >>
     drule ptr_mem_ok_bytes_clean >> simp[evaluate_type_def]) >>
  `b + 32 + LENGTH bs <= t.vs_alloca_next` by
    (drule_all abi_encode_owned_footprint_frontier >>
     `b < dimword(:256)` by decide_tac >>
     gvs[] >> decide_tac) >>
  `w2n (n2w b + 32w : bytes32) = b + 32` by simp[word_add_n2w] >>
  gvs[]
QED
