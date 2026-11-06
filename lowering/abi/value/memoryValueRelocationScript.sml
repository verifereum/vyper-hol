(* TOP-LEVEL: a complete typed memory layout can be copied to another offset.
   Helpers: equality of relative memory windows transports recursive layouts. *)
Theory memoryValueRelocation
Ancestors
  memoryValueDefs memoryValueFrame valueEncoding valueEncodingProofs
  memoryReadProps venomState list rich_list arithmetic pair

Definition memory_window_equiv_def:
  memory_window_equiv src_off src_mem dst_off dst_mem <=>
    !delta len.
      mem_bytes_at (src_off + delta) len src_mem =
        mem_bytes_at (dst_off + delta) len dst_mem
End

Theorem memory_window_equiv_shift:
  !src_off src_mem dst_off dst_mem extra.
    memory_window_equiv src_off src_mem dst_off dst_mem ==>
    memory_window_equiv (src_off + extra) src_mem (dst_off + extra) dst_mem
Proof
  simp_tac bool_ss [memory_window_equiv_def] >> rpt strip_tac >>
  PURE_REWRITE_TAC [GSYM ADD_ASSOC] >> first_x_assum MATCH_ACCEPT_TAC
QED

Theorem memory_window_equiv_reads:
  !src_off src_mem dst_off dst_mem.
    memory_window_equiv src_off src_mem dst_off dst_mem ==>
    mem_word_at src_off src_mem = mem_word_at dst_off dst_mem /\
    (!len. mem_bytes_at (src_off + 32) len src_mem =
      mem_bytes_at (dst_off + 32) len dst_mem)
Proof
  rpt gen_tac >> PURE_REWRITE_TAC [memory_window_equiv_def] >> DISCH_TAC >>
  conj_tac
  >- (simp_tac bool_ss [mem_word_at_def, GSYM mem_bytes_at_def] >>
      AP_TERM_TAC >> first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  first_x_assum (qspec_then `32` ACCEPT_TAC)
QED

Theorem memory_window_equiv_base:
  !bt v src_off src_mem dst_off dst_mem.
    memory_window_equiv src_off src_mem dst_off dst_mem ==>
    (val_in_memory (BaseTV bt) v src_off src_mem <=>
      val_in_memory (BaseTV bt) v dst_off dst_mem)
Proof
  rpt gen_tac >> DISCH_TAC >> drule memory_window_equiv_reads >> strip_tac >>
  Cases_on `v` >> simp[val_in_memory_def] >>
  FIRST [Cases_on `bt` >> simp[val_in_memory_def] >>
           rename1 `BytesT byte_bound` >> Cases_on `byte_bound` >>
           simp[val_in_memory_def],
         rename1 `ArrayV array_value` >> Cases_on `array_value` >>
           simp[val_in_memory_def]]
QED

Theorem memory_window_equiv_flag:
  !flag_width v src_off src_mem dst_off dst_mem.
    memory_window_equiv src_off src_mem dst_off dst_mem ==>
    (val_in_memory (FlagTV flag_width) v src_off src_mem <=>
      val_in_memory (FlagTV flag_width) v dst_off dst_mem)
Proof
  rpt gen_tac >> DISCH_TAC >> drule memory_window_equiv_reads >> strip_tac >>
  Cases_on `v` >> simp[val_in_memory_def] >>
  rename1 `ArrayV array_value` >> Cases_on `array_value` >>
  simp[val_in_memory_def]
QED

Theorem memory_value_rel_window_transport:
  (!tv v src_off src_mem.
    !dst_off dst_mem.
      memory_value_rel tv v src_off src_mem /\
      memory_window_equiv src_off src_mem dst_off dst_mem ==>
      memory_value_rel tv v dst_off dst_mem) /\
  (!tvs vs src_off src_mem.
    !dst_off dst_mem.
      memory_fields_rel tvs vs src_off src_mem /\
      memory_window_equiv src_off src_mem dst_off dst_mem ==>
      memory_fields_rel tvs vs dst_off dst_mem) /\
  (!tvs vs src_off src_mem.
    !dst_off dst_mem.
      memory_tuple_rel tvs vs src_off src_mem /\
      memory_window_equiv src_off src_mem dst_off dst_mem ==>
      memory_tuple_rel tvs vs dst_off dst_mem)
Proof
  ho_match_mp_tac memory_value_rel_ind >>
  simp_tac bool_ss [memory_value_rel_def] >> rpt strip_tac
  >| [metis_tac [memory_window_equiv_base],
      metis_tac [memory_window_equiv_flag],
      metis_tac [memory_window_equiv_shift],
      metis_tac [memory_window_equiv_reads],
      `memory_window_equiv (src_off + 32) src_mem (dst_off + 32) dst_mem` by
        (irule memory_window_equiv_shift >> fs[]) >>
      metis_tac [memory_window_equiv_shift],
      metis_tac [memory_window_equiv_shift],
      metis_tac [memory_window_equiv_shift]]
QED

Theorem mem_bytes_at_drop:
  !offset len base_offset mem.
    mem_bytes_at offset len (DROP base_offset mem) =
      mem_bytes_at (base_offset + offset) len mem
Proof
  simp[mem_bytes_at_def, DROP_DROP_T, ADD_COMM]
QED

Theorem memory_window_equiv_drop:
  !offset mem.
    memory_window_equiv offset mem 0 (DROP offset mem) /\
    memory_window_equiv 0 (DROP offset mem) offset mem
Proof
  simp[memory_window_equiv_def, mem_bytes_at_drop]
QED

Theorem memory_value_rel_relocate:
  !tv v src_off src_mem dst_off dst_mem.
    memory_value_rel tv v src_off src_mem /\ val_wf tv v /\
    mem_bytes_at src_off (type_memory_size tv) src_mem =
      mem_bytes_at dst_off (type_memory_size tv) dst_mem ==>
    memory_value_rel tv v dst_off dst_mem
Proof
  rpt gen_tac >> DISCH_TAC >>
  `memory_value_rel tv v 0 (DROP src_off src_mem)` by
    (mp_tac (Q.SPECL [`tv`, `v`, `src_off`, `src_mem`, `0`, `DROP src_off src_mem`]
       (CONJUNCT1 memory_value_rel_window_transport)) >>
     impl_tac >- fs[memory_window_equiv_drop] >> simp[]) >>
  `memory_value_rel tv v 0 (DROP dst_off dst_mem)` by
    (mp_tac (Q.SPECL [`tv`, `v`, `0`, `DROP src_off src_mem`, `DROP dst_off dst_mem`]
       memory_value_rel_mem_agree) >>
     impl_tac >- fs[mem_bytes_at_drop] >> simp[]) >>
  mp_tac (Q.SPECL [`tv`, `v`, `0`, `DROP dst_off dst_mem`, `dst_off`, `dst_mem`]
    (CONJUNCT1 memory_value_rel_window_transport)) >>
  impl_tac >- fs[memory_window_equiv_drop] >> simp[]
QED

Theorem read_memory_mcopy_prefix:
  !dst src copied_count read_len (ss:venom_state).
    read_len <= copied_count ==>
    read_memory dst read_len (mcopy dst src copied_count ss) =
      read_memory src read_len ss
Proof
  rpt gen_tac >> DISCH_TAC >>
  mp_tac (Q.SPECL [`dst`, `copied_count`, `0`, `read_len`,
    `mcopy dst src copied_count ss`] read_memory_subwindow) >>
  mp_tac (Q.SPECL [`src`, `copied_count`, `0`, `read_len`, `ss`]
    read_memory_subwindow) >>
  simp[read_memory_mcopy_self]
QED

Theorem mcopy_establishes_memory_value_rel:
  !tv v src_off dst_off copied_count ss.
    memory_value_rel tv v src_off ss.vs_memory /\ val_wf tv v /\
    type_memory_size tv <= copied_count ==>
    memory_value_rel tv v dst_off (mcopy dst_off src_off copied_count ss).vs_memory
Proof
  rpt gen_tac >> DISCH_TAC >>
  `read_memory dst_off (type_memory_size tv) (mcopy dst_off src_off copied_count ss) =
    read_memory src_off (type_memory_size tv) ss` by
    (irule read_memory_mcopy_prefix >> fs[]) >>
  mp_tac (Q.SPECL [`tv`, `v`, `src_off`, `ss.vs_memory`, `dst_off`,
    `(mcopy dst_off src_off copied_count ss).vs_memory`] memory_value_rel_relocate) >>
  impl_tac >- fs[read_memory_eq_mem_bytes_at] >> simp[]
QED
