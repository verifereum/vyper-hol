Theory bodyFullTargetMappingRep
Ancestors
  exprSimMapKey bodyPtrDefs exprSimMemDefs representationCleanPtr
  loweringPosts vyperTypeSystem vyperValue vyperTyping vyperStorage
  valueEncoding valueEncodingDefs exprSimProps words finite_map compileEnv

Theorem mapping_index_key_input:
  hashmap_key_type kt /\ expr_type e = kt /\
  evaluate_type (get_tenv cx) kt = SOME tv /\ value_has_type tv v /\
  expr_post H ctx func cenv cx e mid1 sm sn t1 mid2 v iop t2 /\
  expr_store_bound cx kt v iop t2 /\
  ptr_val_ok cx (post_value_type cenv e) v iop G2 tn2 t2 /\
  (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e iop G2 t2) ==>
  (if is_bytestring_type kt then
     ?x b base cap bs.
       iop = Var x /\ eval_operand iop t2 = SOME (n2w b) /\
       FLOOKUP G2 x = SOME (base,cap) /\ base <= b /\
       b+32+LENGTH bs <= base+cap /\
       b+32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
       b+32+LENGTH bs <= t2.vs_alloca_next /\
       op_taint tn2 iop = {} /\
       (!i. b <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn2.t_mem) /\
       mem_word_at b t2.vs_memory = n2w (LENGTH bs) /\
       mem_bytes_at (b+32) (LENGTH bs) t2.vs_memory = bs /\
       encode_hashmap_key kt v = word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)
   else eval_operand iop t2 = SOME (encode_hashmap_key kt v) /\
        op_taint tn2 iop = {} /\ op_prov G2 iop = NONE)
Proof
  strip_tac >> Cases_on `is_bytestring_type kt`
  >- (simp[] >>
      `post_value_type cenv e = kt` by metis_tac[post_value_type_bytestring] >>
      fs[] >>
      Cases_on `expr_type e` >> gvs[is_bytestring_type_def] >>
      rename1 `BaseT bt` >> Cases_on `bt` >>
      gvs[is_bytestring_type_def, evaluate_type_def]
      >- (Cases_on `v` >> gvs[value_has_type_def] >>
          `evaluate_type (get_tenv cx) (expr_type e) =
             SOME (BaseTV (StringT n))` by simp[evaluate_type_def] >>
          drule_all exprSimHashBoundaryTheory.hash_string_post_view >> strip_tac >>
          gvs[ptr_val_ok_def, is_word_type_def, ptr_mem_ok_def,
              expr_store_bound_def, val_footprint_def, val_store_size_def] >>
          drule robust_val_in_memory_string_clean >> strip_tac >>
          qexistsl_tac [`b`, `MAP (n2w o ORD) s`] >>
          simp[encode_hashmap_key_def] >>
          qspec_then `LENGTH s` assume_tac le_word_size_mul >>
          rpt conj_tac >> TRY decide_tac
          >- (rpt strip_tac >> Cases_on `i < b+32` >> gvs[] >>
              qpat_x_assum `!i. b+32 <= i /\ _ ==> _`
                (qspec_then `i` mp_tac) >> simp[] >> decide_tac) >>
          simp[vyperMiscTheory.n2w_o_ORD_eq, byteTheory.word_of_bytes_be_def]) >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      gvs[is_bytestring_type_def, evaluate_type_def] >>
      rename1 `BaseT (BytesT (Dynamic n))` >>
      Cases_on `v` >> gvs[value_has_type_def] >>
      rename1 `BytesV bs` >>
      `evaluate_type (get_tenv cx) (expr_type e) =
         SOME (BaseTV (BytesT (Dynamic n)))` by simp[evaluate_type_def] >>
      drule_all exprSimHashBoundaryTheory.hash_dynamic_post_view >> strip_tac >>
      gvs[ptr_val_ok_def, is_word_type_def, ptr_mem_ok_def,
          expr_store_bound_def, val_footprint_def, val_store_size_def] >>
      drule robust_val_in_memory_bytes_clean >> simp[] >> strip_tac >>
      qexistsl_tac [`b`, `bs`] >>
      simp[encode_hashmap_key_def, byteTheory.word_of_bytes_be_def] >>
      qspec_then `LENGTH bs` assume_tac le_word_size_mul >>
      rpt conj_tac >> TRY decide_tac >>
      rpt strip_tac >> Cases_on `i < b+32` >> gvs[] >>
      qpat_x_assum `!i. b+32 <= i /\ _ ==> _`
        (qspec_then `i` mp_tac) >> simp[] >> decide_tac) >>
  `is_word_type kt` by
    (Cases_on `kt` >> gvs[hashmap_key_type_def, is_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[hashmap_key_type_def, is_word_type_def, is_bytestring_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[is_bytestring_type_def, is_word_type_def, evaluate_type_def, AllCaseEqs()]) >>
  `post_value_type cenv e = kt` by metis_tac[post_value_type_word] >>
  simp[] >> conj_tac
  >- (irule expr_val_rel_hashmap_scalar >>
      gvs[expr_post_def] >> metis_tac[]) >>
  gvs[ptr_val_ok_def]
QED
