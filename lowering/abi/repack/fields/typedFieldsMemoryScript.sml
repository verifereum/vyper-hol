(* TOP-LEVEL: compose the complete memory layouts and typed frames of
   sequential tuple fields, including empty and zero-sized tails. *)
Theory typedFieldsMemory
Ancestors
  typedSArrayDynInvariant memoryValueDefs memoryValueTyping
  valueEncoding vyperTyping vyperValue list arithmetic

Theorem array_copy_frame_contained:
  !inner_tv inner_count inner_off outer_tv outer_count outer_off before_mem after_mem.
    outer_off <= inner_off /\
    inner_off + inner_count * type_memory_size inner_tv <=
      outer_off + outer_count * type_memory_size outer_tv /\
    array_copy_frame inner_tv inner_count inner_off before_mem after_mem ==>
    array_copy_frame outer_tv outer_count outer_off before_mem after_mem
Proof
  rpt gen_tac >> simp_tac bool_ss [array_copy_frame_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >> first_x_assum irule >>
  rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, decide_tac]
QED

Theorem tuple_copy_frame_cons:
  !ftv ftvs dst_off before_mem mid_mem after_mem.
    array_copy_frame ftv 1 dst_off before_mem mid_mem /\
    array_copy_frame (TupleTV ftvs) 1 (dst_off + type_memory_size ftv) mid_mem after_mem ==>
    array_copy_frame (TupleTV (ftv::ftvs)) 1 dst_off before_mem after_mem
Proof
  rpt gen_tac >> strip_tac >>
  irule array_copy_frame_trans >> qexists_tac `mid_mem` >> conj_tac >>
  FIRST [
    mp_tac (Q.SPECL [`ftv`, `1`, `dst_off`, `TupleTV (ftv::ftvs)`, `1`, `dst_off`,
      `before_mem`, `mid_mem`] array_copy_frame_contained) >> simp[type_memory_size_def] >> NO_TAC,
    mp_tac (Q.SPECL [`TupleTV ftvs`, `1`, `dst_off + type_memory_size ftv`,
      `TupleTV (ftv::ftvs)`, `1`, `dst_off`, `mid_mem`, `after_mem`]
      array_copy_frame_contained) >> simp[type_memory_size_def]]
QED

Theorem tuple_copy_source_tail:
  !atv atvs v vs src_off ftv ftvs dst_off before_mem after_mem.
    values_have_types (atv::atvs) (v::vs) /\
    memory_tuple_rel (atv::atvs) (v::vs) src_off before_mem /\
    (src_off + type_memory_size (TupleTV (atv::atvs)) <= dst_off \/
      dst_off + type_memory_size (TupleTV (ftv::ftvs)) <= src_off) /\
    array_copy_frame ftv 1 dst_off before_mem after_mem ==>
    memory_tuple_rel atvs vs (src_off + type_memory_size atv) after_mem
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `value_has_type (TupleTV atvs) (ArrayV (TupleV vs))` by
    fs[value_has_type_def] >>
  drule value_has_type_val_wf >> DISCH_TAC >>
  qpat_x_assum `array_copy_frame _ _ _ _ _` (mp_tac o REWRITE_RULE [array_copy_frame_def]) >>
  disch_then (qspecl_then [`TupleTV atvs`, `ArrayV (TupleV vs)`, `src_off + type_memory_size atv`] mp_tac) >>
  impl_tac
  >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC,
        fs[memory_value_rel_def] >> NO_TAC, fs[type_memory_size_def] >> decide_tac]) >>
  simp[memory_value_rel_def]
QED

Theorem tuple_copy_target_cons:
  !ftv ftvs v vs dst_off mid_mem after_mem.
    value_has_type ftv v /\ memory_value_rel ftv v dst_off mid_mem /\
    memory_tuple_rel ftvs vs (dst_off + type_memory_size ftv) after_mem /\
    array_copy_frame (TupleTV ftvs) 1 (dst_off + type_memory_size ftv) mid_mem after_mem ==>
    memory_tuple_rel (ftv::ftvs) (v::vs) dst_off after_mem
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [memory_value_rel_def] >>
  asm_rewrite_tac [] >> drule value_has_type_val_wf >> DISCH_TAC >>
  qpat_x_assum `array_copy_frame _ _ _ _ _` (mp_tac o REWRITE_RULE [array_copy_frame_def]) >>
  disch_then (qspecl_then [`ftv`, `v`, `dst_off`] mp_tac) >> simp[]
QED
