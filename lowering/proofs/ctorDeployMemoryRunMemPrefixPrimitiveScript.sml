(* Memory traces for constructor primitive-word decoding, including rejection. *)
Theory ctorDeployMemoryRunMemPrefixPrimitive
Ancestors
  entryHaltMem entryDecodeProps moduleLoweringProps abiDecoderContract abiDecoderReservation
  abiDecoderClampedWord fragExecMem instMemFrontier emitHelperProps
  exprLoweringProps abiEncoder emitHelper compileEnv venomExecSemantics
  venomState venomInst memSafeRun words list rich_list

Theorem ctor_prefix_dload_mem_ok:
  emit_op DLOAD [src] st = (v,st') /\
  eval_operand src s = SOME a /\
  w2n a <= LENGTH s.vs_data_section ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  simp[run_inst_seq_mem_ok_last] >> conj_tac
  >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  simp[inst_dload_in_section_def, mk_inst_def]
QED

Theorem ctor_prefix_clamp_store_mem_ok:
  compile_abi_clamp_basetype value clamp st = ((),st') /\
  eval_operand value s = SOME w /\ fresh_vars_wrt st s /\
  eval_operand dst s = SOME p /\ w2n p + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok
    (emitted_insts st st' ++ [mk_inst id MSTORE [dst;value] []]) s
Proof
  strip_tac >> match_mp_tac run_inst_seq_mem_ok_append >> conj_tac
  >- metis_tac[compile_abi_clamp_basetype_mem_ok] >>
  gen_tac >> strip_tac >> drule_all decode_clamp_frame >>
  Cases_on `abi_clamp_ok clamp w` >> simp[] >> strip_tac >> gvs[] >>
  simp[run_inst_seq_mem_ok_last, below_frontier_MSTORE] >>
  qpat_x_assum `vars_pc_only s t` mp_tac >>
  simp[vars_pc_only_def, venom_state_component_equality] >>
  rpt strip_tac >> metis_tac[optionTheory.SOME_11]
QED

Theorem ctor_prefix_static_word_mem_ok:
  compile_abi_decode_to_buf dst src DLOAD hi (DecPrimWord clamp) st = ((),st') /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME p /\
  fresh_vars_wrt st s /\ w2n a <= LENGTH s.vs_data_section /\
  w2n p + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  simp_tac bool_ss [compile_abi_decode_to_buf_def, compile_abi_decode_static_def,
    comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op DLOAD [src] st = (value,c1)` >>
  rename1 `compile_abi_clamp_basetype value clamp c1 = ((),c2)` >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_read >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  drule compile_abi_clamp_structure >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends c1 st'` by metis_tac[inst_extends_trans] >>
  `emitted_insts st st' = emitted_insts st c1 ++ emitted_insts c1 st' /\
   emitted_insts c1 st' = emitted_insts c1 c2 ++ emitted_insts c2 st'` by
    (conj_tac >> irule emitted_insts_append >> fs[inst_extends_def]) >>
  `s1.vs_alloca_next = s.vs_alloca_next` by
    (irule (cj 2 abi_decode_sequence_allocation_frame) >>
     qexists_tac `emitted_insts st c1` >> simp[] >>
     drule emitted_insts_emit_op >> simp[mk_inst_def, is_terminator_def,
       is_alloca_op_def]) >>
  asm_rewrite_tac[] >> match_mp_tac run_inst_seq_mem_ok_append >> conj_tac
  >- metis_tac[ctor_prefix_dload_mem_ok] >>
  rpt strip_tac >> gvs[] >>
  drule emitted_insts_emit_void >> strip_tac >> simp[] >>
  irule ctor_prefix_clamp_store_mem_ok >>
  metis_tac[]
QED
