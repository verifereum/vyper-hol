(* Section-bounded data copies used by constructor bytestring decoding. *)
Theory ctorDeployMemoryRunMemPrefixBytes
Ancestors
  ctorDeployMemoryRunMemPrefixPrimitive fragExecMem emitHelperProps
  unitTransformDefs contextCodegenRel codegenRel memSafeRun
  venomState venomInst words arithmetic freshWrites abiDecoderBytes
  abiDecoderBytesBound abiDecoderGuards abiDecoderGuard finite_map list instMemFrontier compileEnv abiEncoder emitHelper exprLoweringProps
  abiDecoderContract abiDecoderReservation

Theorem ctor_prefix_dloadbytes_mem_ok:
  emit_void DLOADBYTES [dst;src;Lit (n2w n)] st = ((),st') /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME p /\
  w2n a <= LENGTH s.vs_data_section /\
  w2n p + n <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  simp[run_inst_seq_mem_ok_last, inst_dload_in_section_def, mk_inst_def] >>
  simp[inst_mem_below_frontier_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, eval_operand_def] >>
  simp[sized_source_write_range_def, eval_operand_def, w2n_n2w] >>
  `n MOD dimword (:256) <= n` by simp[MOD_LESS_EQ] >> decide_tac
QED

Theorem ctor_prefix_pure_mem_ok[local]:
  writes_fresh st is ==> run_inst_seq_mem_ok is s
Proof
  strip_tac >> irule run_inst_seq_mem_ok_every >>
  fs[writes_fresh_def, EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >>
  simp[fresh_write_op_def] >> strip_tac >>
  simp[inst_dload_in_section_def] >> irule below_frontier_no_ranges >> simp[]
QED

Theorem ctor_prefix_pure_frame[local]:
  writes_fresh st is /\ fresh_vars_wrt st s /\
  run_inst_seq is s = OK t ==>
  t.vs_data_section = s.vs_data_section /\
  t.vs_alloca_next = s.vs_alloca_next /\
  (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  strip_tac >> drule_all run_inst_seq_writes_fresh >> strip_tac >>
  `t.vs_data_section = s.vs_data_section /\
   t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels` by
    (qpat_x_assum `t = _` mp_tac >> simp[venom_state_component_equality]) >>
  qpat_x_assum `t = _` kall_tac >> simp[] >>
  Cases >> simp[eval_operand_def] >> rpt strip_tac >>
  fs[lookup_var_def] >>
  rename1 `FLOOKUP s.vs_vars x = SOME w` >>
  `not_fresh_at st x` by
    (rw[not_fresh_at_def] >> irule fresh_vars_wrt_eval_operand >>
     qexistsl_tac [`Var x`, `s`, `st`, `w`] >> simp[eval_operand_def, lookup_var_def]) >>
  metis_tac[]
QED


Theorem ctor_prefix_assert_shape[local]:
  emit_void ASSERT ops st = ((),st') ==>
  inst_extends st st' /\ st.cs_next_var <= st'.cs_next_var /\
  writes_fresh st (emitted_insts st st')
Proof
  strip_tac >> drule inst_extends_emit_void >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  simp[writes_fresh_def, fresh_write_op_def, mk_inst_def]
QED

Theorem ctor_prefix_emit_shape[local]:
  emit_op opc ops st = (v,st') /\ fresh_write_op opc ==>
  inst_extends st st' /\ st.cs_next_var <= st'.cs_next_var /\
  writes_fresh st (emitted_insts st st')
Proof
  strip_tac >> drule inst_extends_emit_op >> strip_tac >>
  drule_all writes_fresh_emit_op >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >> simp[]
QED

Theorem ctor_prefix_pure_shape_chain[local]:
  inst_extends st c /\ inst_extends c t /\
  st.cs_next_var <= c.cs_next_var /\ c.cs_next_var <= t.cs_next_var /\
  writes_fresh st (emitted_insts st c) /\
  writes_fresh c (emitted_insts c t) ==>
  inst_extends st t /\ st.cs_next_var <= t.cs_next_var /\
  writes_fresh st (emitted_insts st t)
Proof
  strip_tac >>
  `emitted_insts st t = emitted_insts st c ++ emitted_insts c t` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  conj_tac >- metis_tac[inst_extends_trans] >>
  conj_tac >- decide_tac >> simp[writes_fresh_append] >>
  irule writes_fresh_mono >> qexists_tac `c` >> simp[]
QED

Theorem ctor_prefix_le_guard_shape[local]:
  abi_decode_le_guard a b st = ((),st') ==>
  inst_extends st st' /\ st.cs_next_var <= st'.cs_next_var /\
  writes_fresh st (emitted_insts st st')
Proof
  simp[abi_decode_le_guard_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rename1 `emit_op GT [a;b] st = (oob,c1)` >>
  rename1 `emit_op ISZERO [oob] c1 = (ok,c2)` >>
  drule (Q.INST [`opc` |-> `GT`] ctor_prefix_emit_shape) >>
  simp[fresh_write_op_def] >> strip_tac >>
  drule (Q.INST [`opc` |-> `ISZERO`] ctor_prefix_emit_shape) >>
  simp[fresh_write_op_def] >> strip_tac >>
  drule ctor_prefix_assert_shape >> strip_tac >>
  `inst_extends st c2 /\ st.cs_next_var <= c2.cs_next_var /\
   writes_fresh st (emitted_insts st c2)` by
    (irule ctor_prefix_pure_shape_chain >> qexists_tac `c1` >> simp[]) >>
  irule ctor_prefix_pure_shape_chain >> qexists_tac `c2` >> simp[]
QED

Theorem ctor_prefix_bytes_end_shape[local]:
  abi_decode_bytes_end src len st = (v,st') ==>
  inst_extends st st' /\ st.cs_next_var <= st'.cs_next_var /\
  writes_fresh st (emitted_insts st st')
Proof
  simp[abi_decode_bytes_end_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  imp_res_tac (SRULE[fresh_write_op_def]
    (Q.INST [`opc` |-> `ADD`] ctor_prefix_emit_shape)) >>
  irule ctor_prefix_pure_shape_chain >> metis_tac[]
QED

Theorem ctor_prefix_bytes_end_guard_shape[local]:
  abi_decode_bytes_end_guard src len hi st = ((),st') ==>
  inst_extends st st' /\ st.cs_next_var <= st'.cs_next_var /\
  writes_fresh st (emitted_insts st st')
Proof
  Cases_on `hi = Lit 0w`
  >- simp[abi_decode_bytes_end_guard_def, comp_return_def,
          inst_extends_def, emitted_insts_def, writes_fresh_def] >>
  simp[abi_decode_bytes_end_guard_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule ctor_prefix_bytes_end_shape >> strip_tac >>
  drule ctor_prefix_le_guard_shape >> strip_tac >>
  irule ctor_prefix_pure_shape_chain >> metis_tac[]
QED

Theorem ctor_prefix_bytes_phases[local]:
  compile_abi_decode_to_buf dst src DLOAD hi (DecBytestring n) =
    do len <- emit_op DLOAD [src];
       abi_decode_le_guard len (Lit (n2w n));
       abi_decode_bytes_end_guard src len hi;
       emit_void DLOADBYTES [dst;src;Lit (n2w (32 + 32 * ((n + 31) DIV 32)))]
    od
Proof
  Cases_on `hi = Lit 0w` >>
  simp[FUN_EQ_THM, compile_abi_decode_to_buf_def, abi_decode_le_guard_def,
       abi_decode_bytes_end_guard_def, abi_decode_bytes_end_def,
       comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem ctor_prefix_bytestring_shape[local]:
  compile_abi_decode_to_buf dst src DLOAD hi (DecBytestring n) st = ((),st') ==>
  ?v c1 c2.
    emit_op DLOAD [src] st = (v,c1) /\
    emit_void DLOADBYTES [dst;src;Lit (n2w (32 + 32 * ((n + 31) DIV 32)))] c2 = ((),st') /\
    emitted_insts st st' = emitted_insts st c1 ++
      emitted_insts c1 c2 ++ emitted_insts c2 st' /\
    writes_fresh c1 (emitted_insts c1 c2)
Proof
  simp[ctor_prefix_bytes_phases, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `emit_op DLOAD [src] st = (v,c1)` >>
  rename1 `emit_void DLOADBYTES _ c2 = ((),st')` >>
  qexists_tac `c2` >> simp[] >>
  drule ctor_prefix_le_guard_shape >> strip_tac >>
  drule ctor_prefix_bytes_end_guard_shape >> strip_tac >>
  `inst_extends c1 c2 /\ c1.cs_next_var <= c2.cs_next_var /\
   writes_fresh c1 (emitted_insts c1 c2)` by
    (irule ctor_prefix_pure_shape_chain >> metis_tac[]) >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends c1 st'` by metis_tac[inst_extends_trans] >>
  `emitted_insts st st' = emitted_insts st c1 ++ emitted_insts c1 st' /\
   emitted_insts c1 st' = emitted_insts c1 c2 ++ emitted_insts c2 st'` by
    (conj_tac >> irule emitted_insts_append >> fs[inst_extends_def]) >>
  simp[]
QED

Theorem ctor_prefix_bytestring_mem_ok:
  compile_abi_decode_to_buf dst src DLOAD hi (DecBytestring max_len) st = ((),st') /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME p /\
  fresh_vars_wrt st s /\ w2n a <= LENGTH s.vs_data_section /\
  w2n p + (32 + 32 * ((max_len + 31) DIV 32)) <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  strip_tac >> drule ctor_prefix_bytestring_shape >> strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_read >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `s1.vs_alloca_next = s.vs_alloca_next` by
    (irule (cj 2 abi_decode_sequence_allocation_frame) >>
     qexists_tac `emitted_insts st c1` >> simp[] >>
     drule emitted_insts_emit_op >> simp[mk_inst_def, is_terminator_def,
       is_alloca_op_def]) >>
  asm_rewrite_tac[] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  match_mp_tac run_inst_seq_mem_ok_append >> conj_tac
  >- (irule ctor_prefix_dload_mem_ok >> metis_tac[]) >>
  gen_tac >> strip_tac >> gvs[] >>
  match_mp_tac run_inst_seq_mem_ok_append >> conj_tac
  >- metis_tac[ctor_prefix_pure_mem_ok] >>
  gen_tac >> strip_tac >> drule_all ctor_prefix_pure_frame >> strip_tac >>
  irule ctor_prefix_dloadbytes_mem_ok >> metis_tac[]
QED
