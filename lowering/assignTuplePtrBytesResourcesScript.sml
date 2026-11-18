(* Recover the concrete header and rounded read extent needed by a
   bytestring member store from its robust pointer-value contract. *)
Theory assignTuplePtrBytesResources
Ancestors
  bodyPtrDefs representationCleanPtr exprSimBufferStore exprSimProps
  compileEnv venomState venomExecSemantics valueEncoding vyperTyping
  valueEncodingProps vyperValue words arithmetic vfmConstants

Theorem robust_bytestring_header_clean_ptr:
  is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv /\
  value_has_type tv v /\
  (!mem. mem_agree_outside tm s.vs_memory mem ==> val_in_memory tv v a mem) ==>
  !i. a <= i /\ i < a+32 ==> i NOTIN tm
Proof
  strip_tac >> Cases_on `ty` >> gvs[is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> gvs[is_bytestring_type_def]
  >- (gvs[evaluate_type_def] >> Cases_on `v` >> gvs[value_has_type_def] >>
      drule robust_val_in_memory_string_clean >> simp[]) >>
  rename1 `BytesT bd` >> Cases_on `bd` >> gvs[is_bytestring_type_def] >>
  gvs[evaluate_type_def] >> Cases_on `v` >> gvs[value_has_type_def] >>
  drule robust_val_in_memory_bytes_clean >> simp[]
QED

Theorem tuple_bytestring_member_resources_ptr:
  is_bytestring_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_size tv + 64 < dimword (:256) /\
  ptr_val_ok cx ty v (Var src) G tn s /\ lookup_var src s = SOME sw ==>
  ?len. mload (w2n sw) s = n2w len /\
    len+31 < dimword (:256) /\
    32 + 32 * ((len+31) DIV 32) < dimword (:256) /\
    32 + 32 * ((len+31) DIV 32) <= type_memory_size tv /\
    val_footprint tv v <= 32 + 32 * ((len+31) DIV 32) /\
    (!i. w2n sw <= i /\ i < w2n sw+32 ==> i NOTIN tn.t_mem)
Proof
  strip_tac >>
  `~is_word_type ty` by
    (Cases_on `ty` >> gvs[is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> gvs[is_bytestring_type_def, is_word_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[is_bytestring_type_def, is_word_type_def]) >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv v (w2n sw) mem` by
    (fs[ptr_val_ok_def, ptr_mem_ok_def, eval_operand_def] >> metis_tac[]) >>
  `val_in_memory tv v (w2n sw) s.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `!i. w2n sw <= i /\ i < w2n sw+32 ==> i NOTIN tn.t_mem` by
    metis_tac[robust_bytestring_header_clean_ptr] >>
  drule_all buffer_typed_bytestring_header >> strip_tac >>
  `val_store_size tv v <= type_memory_size tv /\
   val_footprint tv v <= val_store_size tv v` by
    metis_tac[val_store_size_le, val_footprint_le_store_size] >>
  `32 + 32 * word_size len < dimword (:256)` by decide_tac >>
  drule buffer_round_no_wrap >> strip_tac >>
  qexists_tac `len` >> fs[word_size_def] >> decide_tac
QED
