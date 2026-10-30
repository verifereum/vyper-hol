(* TOP-LEVEL: whole-array bounds and separation imply the actual element
   pointer, header and copy-safety conditions. Helpers transport live values
   across capacity widening; no element-size agreement is assumed here. *)
Theory typedSArrayDynSafety
Ancestors
  typedArrayCopyMemory typedArrayLoopAddress memoryValueTyping valueEncoding vyperValue vyperTyping
  list words arithmetic

Theorem array_copy_count_bound:
  !copy_count stride offset.
    0 < stride /\ offset + copy_count * stride < dimword(:256) ==>
    copy_count < dimword(:256)
Proof
  rpt gen_tac >> strip_tac >>
  `copy_count * 1 <= copy_count * stride` by simp[LE_MULT_LCANCEL] >>
  qpat_x_assum `copy_count * 1 <= _` (mp_tac o PURE_REWRITE_RULE [MULT_CLAUSES]) >>
  strip_tac >> decide_tac
QED

Theorem array_copy_element_pointer_bounds:
  !(addr:bytes32) copy_count i stride.
    i < copy_count /\ 32 <= stride /\ w2n addr + copy_count * stride < dimword(:256) ==>
    w2n (addr + n2w i * n2w stride) = w2n addr + i * stride /\
    w2n (addr + n2w i * n2w stride) + 32 < dimword(:256) /\ stride < dimword(:256)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  mp_tac (Q.SPECL [`w2n (addr:bytes32)`, `i`, `copy_count`, `stride`]
    array_copy_element_window) >> impl_tac >- simp[] >> strip_tac >>
  `w2n addr + i * stride < dimword(:256)` by decide_tac >>
  `w2n (addr + n2w i * n2w stride) = w2n addr + i * stride` by
    (irule typed_array_loop_address_natural >> simp[]) >>
  `w2n addr + i * stride + 32 < dimword(:256)` by
    (drule_all array_copy_element_header_bound >> simp[]) >>
  asm_simp_tac bool_ss [] >> decide_tac
QED

Theorem value_has_type_dynarray_cases:
  !elem_tv capacity v.
    value_has_type (ArrayTV elem_tv (Dynamic capacity)) v ==>
    ?vs. v = ArrayV (DynArrayV vs)
Proof
  rpt gen_tac >> Cases_on `v` >> simp[value_has_type_inv] >>
  qmatch_goalsub_rename_tac `ArrayV av` >> Cases_on `av` >> simp[value_has_type_inv]
QED

Theorem dynarray_capacity_value_type:
  !elem_tv src_capacity dst_capacity v.
    src_capacity <= dst_capacity /\
    value_has_type (ArrayTV elem_tv (Dynamic src_capacity)) v ==>
    value_has_type (ArrayTV elem_tv (Dynamic dst_capacity)) v
Proof
  rpt gen_tac >> strip_tac >> drule value_has_type_dynarray_cases >> strip_tac >>
  gvs[value_has_type_def] >> decide_tac
QED

Theorem dynarray_values_wf:
  !elem_tv src_capacity dst_capacity at_index copy_count.
    src_capacity <= dst_capacity /\
    (!j. j < copy_count ==> value_has_type (ArrayTV elem_tv (Dynamic src_capacity)) (at_index j)) ==>
    (!j. j < copy_count ==> val_wf (ArrayTV elem_tv (Dynamic src_capacity)) (at_index j)) /\
    (!j. j < copy_count ==> val_wf (ArrayTV elem_tv (Dynamic dst_capacity)) (at_index j))
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (rpt gen_tac >> DISCH_TAC >> irule value_has_type_val_wf >>
      qpat_x_assum `!j. _` (qspec_then `j` mp_tac) >> simp[]) >>
  rpt gen_tac >> DISCH_TAC >>
  `value_has_type (ArrayTV elem_tv (Dynamic src_capacity)) (at_index j)` by
    (qpat_x_assum `!j. _` (qspec_then `j` mp_tac) >> simp[]) >>
  `value_has_type (ArrayTV elem_tv (Dynamic dst_capacity)) (at_index j)` by
    (drule_all dynarray_capacity_value_type >> simp[]) >>
  irule value_has_type_val_wf >> first_assum MATCH_ACCEPT_TAC
QED

Theorem sarray_dynarray_element_safety:
  !elem_tv src_capacity dst_capacity vs copy_count i (dst_addr:bytes32) (src_addr:bytes32).
    let atv = ArrayTV elem_tv (Dynamic src_capacity) in
    let ftv = ArrayTV elem_tv (Dynamic dst_capacity) in
    let src_word = src_addr + n2w i * n2w (type_memory_size atv) in
    let dst_word = dst_addr + n2w i * n2w (type_memory_size ftv) in
    i < copy_count /\ value_has_type atv (ArrayV (DynArrayV vs)) /\
    w2n src_addr + copy_count * type_memory_size atv < dimword(:256) /\
    w2n dst_addr + copy_count * type_memory_size ftv < dimword(:256) /\
    (w2n src_addr + copy_count * type_memory_size atv <= w2n dst_addr \/
      w2n dst_addr + copy_count * type_memory_size ftv <= w2n src_addr) ==>
    w2n src_word = w2n src_addr + i * type_memory_size atv /\
    w2n dst_word = w2n dst_addr + i * type_memory_size ftv /\
    w2n src_addr + i * type_memory_size atv + 32 < dimword(:256) /\
    w2n dst_addr + i * type_memory_size ftv + 32 < dimword(:256) /\
    type_memory_size atv < dimword(:256) /\
    (LENGTH vs * type_memory_size elem_tv = 0 \/
      w2n src_addr + i * type_memory_size atv + 32 + LENGTH vs * type_memory_size elem_tv <=
        w2n dst_addr + i * type_memory_size ftv \/
      w2n dst_addr + i * type_memory_size ftv <= w2n src_addr + i * type_memory_size atv)
Proof
  rpt gen_tac >> simp_tac bool_ss [LET_THM] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  mp_tac (Q.SPECL [`src_addr`, `copy_count`, `i`, `type_memory_size (ArrayTV elem_tv (Dynamic src_capacity))`]
    array_copy_element_pointer_bounds) >>
  impl_tac >- simp[type_memory_size_def] >> strip_tac >>
  mp_tac (Q.SPECL [`dst_addr`, `copy_count`, `i`, `type_memory_size (ArrayTV elem_tv (Dynamic dst_capacity))`]
    array_copy_element_pointer_bounds) >>
  impl_tac >- simp[type_memory_size_def] >> strip_tac >>
  mp_tac (Q.SPECL [`w2n (src_addr:bytes32)`, `w2n (dst_addr:bytes32)`, `copy_count`,
    `type_memory_size (ArrayTV elem_tv (Dynamic src_capacity))`,
    `type_memory_size (ArrayTV elem_tv (Dynamic dst_capacity))`, `i`, `i`]
    array_copy_elements_disjoint) >> impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  mp_tac (Q.SPECL [`elem_tv`, `src_capacity`, `dst_capacity`, `vs`,
    `w2n (src_addr:bytes32) + i * type_memory_size (ArrayTV elem_tv (Dynamic src_capacity))`,
    `w2n (dst_addr:bytes32) + i * type_memory_size (ArrayTV elem_tv (Dynamic dst_capacity))`]
    array_copy_dynamic_overlap) >> impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  asm_simp_tac bool_ss [] >> decide_tac
QED
