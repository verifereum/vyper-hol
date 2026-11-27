(* Frame the counted calldata copy and header store at their fixed endpoints. *)
Theory bodyCalldataSliceWritesFrameMods
Ancestors
  exprSimCalldataSlice exprSimHash immutableMemoryFrame valueEncodingProps
  venomState venomInst venomExecSemantics codegenRel ptrDiscipline
  words list pred_set

Theorem calldata_slice_writes_frame_mods:
  u = (write_memory_with_expansion (w2n wd) bytes v)
        with vs_inst_idx := SUC v.vs_inst_idx /\
  z = (mstore b wn u) with vs_inst_idx := SUC u.vs_inst_idx /\
  tf.t_mem = (tv.t_mem DIFF
    range_bytes (source_memory_write_ranges
      (mk_inst iid CALLDATACOPY [Var dst;start;cnt] []) v))
    DIFF {i | b <= i /\ i < b + 32} /\
  eval_operand (Var dst) v = SOME wd /\
  eval_operand start v = SOME wa /\ eval_operand cnt v = SOME wn /\
  w2n wd = b + 32 /\ w2n wn = n /\ LENGTH bytes = n /\ 32 + n <= N ==>
  (!a sz. a + sz <= b \/ b + N <= a ==>
     mem_bytes_at a sz z.vs_memory = mem_bytes_at a sz v.vs_memory) /\
  z.vs_data_section = v.vs_data_section /\
  LENGTH v.vs_memory <= LENGTH z.vs_memory /\
  z.vs_allocas = v.vs_allocas /\ z.vs_alloca_next = v.vs_alloca_next /\
  tf.t_mem SUBSET tv.t_mem /\
  mem_word_at b z.vs_memory = wn /\
  mem_bytes_at (b + 32) n z.vs_memory = bytes /\
  (!i. b <= i /\ i < b + 32 + n ==> i NOTIN tf.t_mem)
Proof
  strip_tac >>
  `z.vs_memory = (mstore b wn
       (write_memory_with_expansion (b + 32) bytes v)).vs_memory /\
   z.vs_data_section = v.vs_data_section /\ z.vs_allocas = v.vs_allocas /\
   z.vs_alloca_next = v.vs_alloca_next` by
    asm_simp_tac bool_ss [mstore_def, write_memory_with_expansion_def,
                         LET_THM, venom_state_accfupds] >>
  qpat_x_assum `z = _` kall_tac >> qpat_x_assum `u = _` kall_tac >>
  `source_memory_write_ranges
      (mk_inst iid CALLDATACOPY [Var dst;start;cnt] []) v = [(b + 32,n)]` by
    simp[source_memory_write_ranges_def, mk_inst_def, sized_source_write_range_def] >>
  qpat_x_assum `tf.t_mem = _` mp_tac >>
  asm_simp_tac bool_ss [] >> disch_tac >> conj_tac
  >- (rpt strip_tac >> `wn = n2w (LENGTH bytes)` by metis_tac[n2w_w2n] >>
      qpat_assum `wn = n2w _` SUBST1_TAC >>
      irule bytes_buffer_write_frame >> decide_tac) >>
  conj_tac
  >- simp[immutable_mstore_capacity, immutable_write_memory_capacity,
          arithmeticTheory.MAX_LE] >>
  conj_tac >- simp[SUBSET_DEF] >>
  simp[mstore_mem_word_at_same, mstore_mem_bytes_at_disjoint] >>
  conj_tac
  >- (qpat_assum `LENGTH bytes = n` (SUBST1_TAC o SYM) >>
      simp[hash_write_memory_read_self]) >>
  simp[range_bytes_def] >> decide_tac
QED
