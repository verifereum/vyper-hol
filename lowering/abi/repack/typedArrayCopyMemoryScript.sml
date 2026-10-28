(* TOP-LEVEL: a recursive element store advances the complete typed array
   prefix while preserving the source array. Source and target strides may
   differ, and zero-sized layouts are included.
   Helpers give exact element windows and fixed/dynamic array projections. *)
Theory typedArrayCopyMemory
Ancestors
  memoryValueDefs valueEncoding vyperValue vyperTyping list alist arithmetic words

Definition array_copy_prefix_def:
  array_copy_prefix tv at_index copied offset mem <=>
    !j. j < copied ==>
      memory_value_rel tv (at_index j) (offset + j * type_memory_size tv) mem
End

Theorem array_copy_prefix_zero[simp]:
  !tv at_index offset mem. array_copy_prefix tv at_index 0 offset mem
Proof
  simp[array_copy_prefix_def]
QED

Theorem array_copy_fixed_layout:
  !tv sparse copy_count offset mem.
    memory_value_rel (ArrayTV tv (Fixed copy_count)) (ArrayV (SArrayV sparse)) offset mem <=>
    array_copy_prefix tv
      (\j. case ALOOKUP sparse j of NONE => default_value tv | SOME v => v) copy_count offset mem
Proof
  ONCE_REWRITE_TAC [memory_value_rel_def] >> simp[array_copy_prefix_def]
QED

Theorem array_copy_dynamic_layout:
  !tv vs capacity offset mem.
    memory_value_rel (ArrayTV tv (Dynamic capacity)) (ArrayV (DynArrayV vs)) offset mem <=>
    mem_word_at offset mem = n2w (LENGTH vs) /\
    array_copy_prefix tv (\j. EL j vs) (LENGTH vs) (offset + 32) mem
Proof
  ONCE_REWRITE_TAC [memory_value_rel_def] >> simp_tac bool_ss [array_copy_prefix_def]
QED

Theorem array_copy_element_window:
  !offset j (copy_count:num) stride.
    j < copy_count ==>
    offset <= offset + j * stride /\
    offset + j * stride + stride <= offset + copy_count * stride
Proof
  rpt gen_tac >> strip_tac >>
  `(j + 1) * stride <= copy_count * stride` by simp[LE_MULT_RCANCEL] >>
  qpat_x_assum `(j + 1) * stride <= copy_count * stride`
    (mp_tac o PURE_REWRITE_RULE [RIGHT_ADD_DISTRIB, MULT_CLAUSES]) >>
  strip_tac >> decide_tac
QED

Theorem array_copy_elements_disjoint:
  !src_off dst_off (copy_count:num) src_size dst_size i j.
    i < copy_count /\ j < copy_count /\
    (src_off + copy_count * src_size <= dst_off \/
      dst_off + copy_count * dst_size <= src_off) ==>
    src_off + j * src_size + src_size <= dst_off + i * dst_size \/
      dst_off + i * dst_size + dst_size <= src_off + j * src_size
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  mp_tac (Q.SPECL [`src_off`, `j`, `copy_count`, `src_size`] array_copy_element_window) >>
  impl_tac >- simp[] >> strip_tac >>
  mp_tac (Q.SPECL [`dst_off`, `i`, `copy_count`, `dst_size`] array_copy_element_window) >>
  impl_tac >- simp[] >> strip_tac >> decide_tac
QED

Theorem array_copy_step_source:
  !ftv atv at_index copy_count i src_off dst_off before_mem after_mem.
    i < copy_count /\ array_copy_prefix atv at_index copy_count src_off before_mem /\
    (!j. j < copy_count ==> val_wf atv (at_index j)) /\
    (src_off + copy_count * type_memory_size atv <= dst_off \/
      dst_off + copy_count * type_memory_size ftv <= src_off) /\
    (!other_tv other_v offset.
      memory_value_rel other_tv other_v offset before_mem /\ val_wf other_tv other_v /\
      (offset + type_memory_size other_tv <= dst_off + i * type_memory_size ftv \/
        dst_off + i * type_memory_size ftv + type_memory_size ftv <= offset) ==>
      memory_value_rel other_tv other_v offset after_mem) ==>
    array_copy_prefix atv at_index copy_count src_off after_mem
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  rewrite_tac[array_copy_prefix_def] >> qx_gen_tac `j` >> DISCH_TAC >>
  `memory_value_rel atv (at_index j) (src_off + j * type_memory_size atv) before_mem` by
    fs[array_copy_prefix_def] >>
  `src_off + j * type_memory_size atv + type_memory_size atv <= dst_off + i * type_memory_size ftv \/
    dst_off + i * type_memory_size ftv + type_memory_size ftv <= src_off + j * type_memory_size atv` by
    (mp_tac (Q.SPECL [`src_off`, `dst_off`, `copy_count`, `type_memory_size atv`,
       `type_memory_size ftv`, `i`, `j`] array_copy_elements_disjoint) >> simp[]) >>
  qpat_x_assum `!other_tv other_v offset. _`
    (qspecl_then [`atv`, `at_index j`, `src_off + j * type_memory_size atv`] mp_tac) >> simp[]
QED

Theorem array_copy_step_target:
  !ftv at_index i dst_off before_mem after_mem.
    array_copy_prefix ftv at_index i dst_off before_mem /\
    (!j. j < i ==> val_wf ftv (at_index j)) /\
    memory_value_rel ftv (at_index i) (dst_off + i * type_memory_size ftv) after_mem /\
    (!other_tv other_v offset.
      memory_value_rel other_tv other_v offset before_mem /\ val_wf other_tv other_v /\
      (offset + type_memory_size other_tv <= dst_off + i * type_memory_size ftv \/
        dst_off + i * type_memory_size ftv + type_memory_size ftv <= offset) ==>
      memory_value_rel other_tv other_v offset after_mem) ==>
    array_copy_prefix ftv at_index (SUC i) dst_off after_mem
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  rewrite_tac[array_copy_prefix_def] >> qx_gen_tac `j` >> DISCH_TAC >>
  Cases_on `j = i` >- gvs[] >> `j < i` by decide_tac >>
  `memory_value_rel ftv (at_index j) (dst_off + j * type_memory_size ftv) before_mem` by
    fs[array_copy_prefix_def] >>
  `dst_off + j * type_memory_size ftv + type_memory_size ftv <= dst_off + i * type_memory_size ftv` by
    (mp_tac (Q.SPECL [`dst_off`, `j`, `i`, `type_memory_size ftv`] array_copy_element_window) >> simp[]) >>
  qpat_x_assum `!other_tv other_v offset. _`
    (qspecl_then [`ftv`, `at_index j`, `dst_off + j * type_memory_size ftv`] mp_tac) >> simp[]
QED

Theorem array_copy_element_header_bound:
  !offset i (copy_count:num) stride.
    i < copy_count /\ 32 <= stride /\ offset + copy_count * stride < dimword(:256) ==>
    offset + i * stride + 32 < dimword(:256)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`offset`, `i`, `copy_count`, `stride`] array_copy_element_window) >>
  impl_tac >- simp[] >> strip_tac >> decide_tac
QED

Theorem array_copy_dynamic_overlap:
  !elem_tv src_capacity dst_capacity vs src_off dst_off.
    value_has_type (ArrayTV elem_tv (Dynamic src_capacity)) (ArrayV (DynArrayV vs)) /\
    (src_off + type_memory_size (ArrayTV elem_tv (Dynamic src_capacity)) <= dst_off \/
      dst_off + type_memory_size (ArrayTV elem_tv (Dynamic dst_capacity)) <= src_off) ==>
    src_off + 32 + LENGTH vs * type_memory_size elem_tv <= dst_off \/ dst_off <= src_off
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `LENGTH vs <= src_capacity` by fs[value_has_type_def] >>
  `LENGTH vs * type_memory_size elem_tv <= src_capacity * type_memory_size elem_tv` by
    simp[LE_MULT_RCANCEL] >>
  qpat_x_assum `_ \/ _` mp_tac >> simp_tac bool_ss [type_memory_size_def] >>
  strip_tac >> decide_tac
QED

Theorem array_copy_step_frame:
  !ftv copy_count i dst_off before_mem after_mem.
    i < copy_count /\
    (!other_tv other_v offset.
      memory_value_rel other_tv other_v offset before_mem /\ val_wf other_tv other_v /\
      (offset + type_memory_size other_tv <= dst_off + i * type_memory_size ftv \/
        dst_off + i * type_memory_size ftv + type_memory_size ftv <= offset) ==>
      memory_value_rel other_tv other_v offset after_mem) ==>
    !other_tv other_v offset.
      memory_value_rel other_tv other_v offset before_mem /\ val_wf other_tv other_v /\
      (offset + type_memory_size other_tv <= dst_off \/
        dst_off + copy_count * type_memory_size ftv <= offset) ==>
      memory_value_rel other_tv other_v offset after_mem
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  mp_tac (Q.SPECL [`dst_off`, `i`, `copy_count`, `type_memory_size ftv`] array_copy_element_window) >>
  impl_tac >- simp[] >> strip_tac >>
  qpat_x_assum `!other_tv other_v offset. _`
    (qspecl_then [`other_tv`, `other_v`, `offset`] mp_tac) >>
  impl_tac >- (simp[] >> decide_tac) >> simp[]
QED

Theorem array_copy_progress:
  !ftv atv at_index copy_count i src_off dst_off before_mem after_mem.
    i < copy_count /\ array_copy_prefix atv at_index copy_count src_off before_mem /\
    array_copy_prefix ftv at_index i dst_off before_mem /\
    (!j. j < copy_count ==> val_wf atv (at_index j)) /\
    (!j. j < i ==> val_wf ftv (at_index j)) /\
    (src_off + copy_count * type_memory_size atv <= dst_off \/
      dst_off + copy_count * type_memory_size ftv <= src_off) /\
    memory_value_rel ftv (at_index i) (dst_off + i * type_memory_size ftv) after_mem /\
    (!other_tv other_v offset.
      memory_value_rel other_tv other_v offset before_mem /\ val_wf other_tv other_v /\
      (offset + type_memory_size other_tv <= dst_off + i * type_memory_size ftv \/
        dst_off + i * type_memory_size ftv + type_memory_size ftv <= offset) ==>
      memory_value_rel other_tv other_v offset after_mem) ==>
    array_copy_prefix atv at_index copy_count src_off after_mem /\
    array_copy_prefix ftv at_index (SUC i) dst_off after_mem /\
    (!other_tv other_v offset.
      memory_value_rel other_tv other_v offset before_mem /\ val_wf other_tv other_v /\
      (offset + type_memory_size other_tv <= dst_off \/
        dst_off + copy_count * type_memory_size ftv <= offset) ==>
      memory_value_rel other_tv other_v offset after_mem)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >> conj_tac
  >- (mp_tac (Q.SPECL [`ftv`, `atv`, `at_index`, `copy_count`, `i`, `src_off`, `dst_off`,
        `before_mem`, `after_mem`] array_copy_step_source) >>
      impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >> conj_tac
  >- (mp_tac (Q.SPECL [`ftv`, `at_index`, `i`, `dst_off`, `before_mem`, `after_mem`]
        array_copy_step_target) >>
      impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  mp_tac (Q.SPECL [`ftv`, `copy_count`, `i`, `dst_off`, `before_mem`, `after_mem`]
    array_copy_step_frame) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed typed array-copy memory theorem: " ^ name)
  end) (DB.thms "typedArrayCopyMemory")
