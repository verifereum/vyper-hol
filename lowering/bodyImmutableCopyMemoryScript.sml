(* Runtime immutable copying: actual DLOAD/MSTORE memory footprints. *)
Theory bodyImmutableCopyMemory
Ancestors
  valueEncodingProps memSafeRun
  exprSimCopy exprSimStorageCopy immutableCopyExecution bodyCopyMemory storageDecodeMemory fragExecMem instMemFrontier
  context compileEnv exprLoweringProps emitHelper emitHelperProps venomExecSemantics
  venomState venomInst words arithmetic list rich_list

Theorem body_immutable_copy_aligned_size:
  !tv. 32 * ((type_memory_size tv + 31) DIV 32) = type_memory_size tv
Proof
  simp[type_memory_size_slots, MULT_DIV]
QED

Theorem body_immutable_copy_zero_mem:
  compile_imm_copy_to_memory F imm src dst 0 off sa = ((),sb) ==>
  frag_exec_mem ctx sa sb P P R
Proof
  simp[compile_imm_copy_to_memory_def, comp_return_def] >>
  strip_tac >> gvs[] >> irule frag_exec_mem_refl >> simp[]
QED

Theorem body_immutable_copy_one_mem_ok:
  compile_imm_copy_to_memory F imm src dst (SUC 0) 0 sa = ((),sb) /\
  eval_operand dst s = SOME b /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  w2n b + 32 <= s.vs_alloca_next /\
  (!a. eval_operand src s = SOME a ==> w2n a <= LENGTH s.vs_data_section) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  simp[compile_imm_copy_to_memory_def, compile_lit_byte_offset_def,
       compile_imm_load_word_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
  `LENGTH sa.cs_current_insts - (LENGTH sa.cs_current_insts + 1) = 0` by decide_tac >>
  simp[emitted_insts_def, DROP_APPEND] >>
  rewrite_tac[run_inst_seq_mem_ok_cons] >> conj_tac
  >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  conj_tac
  >- (rw[inst_dload_in_section_def, mk_inst_def] >> metis_tac[]) >>
  simp[step_inst_base_def, exec_read1_def] >>
  Cases_on `eval_operand src s` >> simp[] >>
  rewrite_tac[run_inst_seq_mem_ok_last] >>
  `!y. not_fresh_at sa y ==>
       y <> STRING #"%" (toString sa.cs_next_var)` by
    (simp[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  simp[below_frontier_MSTORE, update_var_def] >>
  Cases_on `dst` >>
  gvs[eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  IF_CASES_TAC >> gvs[]
QED

Theorem body_immutable_byte_offset_mem_ok:
  compile_lit_byte_offset op off sa = (r,sb) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  Cases_on `off = 0`
  >- simp[compile_lit_byte_offset_def, comp_return_def, emitted_insts_def,
           run_inst_seq_mem_ok_def] >>
  Cases_on `op` >>
  simp[compile_lit_byte_offset_def, comp_return_def, emitted_insts_def,
       run_inst_seq_mem_ok_def] >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  simp[DROP_APPEND, run_inst_seq_mem_ok_last] >>
  irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem body_immutable_copy_offset_range:
  w2n b + off + 32 <= limit /\ w2n b + off < dimword (:256) ==>
  w2n (b + n2w off : bytes32) + 32 <= limit
Proof
  simp[wordsTheory.w2n_add, wordsTheory.w2n_n2w] >>
  strip_tac >>
  `off < dimword (:256)` by decide_tac >>
  simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w,
       arithmeticTheory.LESS_MOD]
QED

Theorem body_immutable_load_mem_ok:
  compile_imm_load_word F imm op sa = (r,sb) /\
  (!a. eval_operand op s = SOME a ==> w2n a <= LENGTH s.vs_data_section) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  simp[compile_imm_load_word_def] >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  simp[run_inst_seq_mem_ok_last] >> conj_tac
  >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  rw[inst_dload_in_section_def, mk_inst_def] >> metis_tac[]
QED

Theorem body_immutable_store_mem_ok:
  emit_void MSTORE [dst;value] sa = ((),sb) /\
  eval_operand dst s = SOME b /\ w2n b + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  simp[run_inst_seq_mem_ok_last, below_frontier_MSTORE]
QED

Theorem body_copy_frame_frontier:
  copy_runtime_frame sa s sb t ==> t.vs_alloca_next = s.vs_alloca_next
Proof
  simp[copy_runtime_frame_def] >> strip_tac >>
  drule copy_static_fields >> simp[]
QED

Theorem body_copy_frame_data_section:
  copy_runtime_frame sa s sb t ==> t.vs_data_section = s.vs_data_section
Proof
  simp[copy_runtime_frame_def] >> strip_tac >>
  drule copy_static_fields >> simp[]
QED

Theorem body_copy_frame_mem_append:
  copy_runtime_frame sa s sm t /\ copy_runtime_frame sm t sb u /\
  run_inst_seq_mem_ok (emitted_insts sa sm) s /\
  run_inst_seq_mem_ok (emitted_insts sm sb) t ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> fs[copy_runtime_frame_def]) >>
  simp[] >> irule run_inst_seq_mem_ok_append >>
  fs[copy_runtime_frame_def]
QED

Theorem body_immutable_one_mem_ok:
  immutable_copy_one F imm src dst off sa = ((),sb) /\
  copy_old_operand sa src /\ copy_old_operand sa dst /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  w2n b + off + 32 <= s.vs_alloca_next /\
  w2n b + off + 32 < dimword (:256) /\
  w2n a + off + 32 <= LENGTH s.vs_data_section /\
  w2n a + off + 32 < dimword (:256) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  simp[immutable_copy_one_def, immutable_comp_bind_cases] >> strip_tac >>
  drule_all copy_runtime_offset >> strip_tac >>
  drule_all copy_runtime_load >> strip_tac >>
  rename1 `compile_lit_byte_offset src off sa = (sop,s1)` >>
  rename1 `compile_imm_load_word F imm sop s1 = (value,s2)` >>
  rename1 `copy_runtime_frame sa s s1 t1` >>
  rename1 `copy_runtime_frame s1 t1 s2 t2` >>
  `copy_runtime_frame sa s s2 t2` by metis_tac[copy_runtime_frame_trans] >>
  `copy_old_operand s2 dst` by
    metis_tac[copy_old_operand_mono, copy_runtime_frame_def] >>
  `eval_operand dst t2 = SOME b` by metis_tac[copy_runtime_frame_operand] >>
  `run_inst_seq_mem_ok (emitted_insts sa s1) s` by
    metis_tac[body_immutable_byte_offset_mem_ok] >>
  qpat_x_assum `compile_lit_byte_offset src off sa = _` kall_tac >>
  drule_all copy_runtime_offset >> strip_tac >>
  rename1 `compile_lit_byte_offset dst off s2 = (dop,s3)` >>
  rename1 `copy_runtime_frame s2 t2 s3 t3` >>
  `copy_old_operand s3 value` by
    metis_tac[copy_old_operand_mono, copy_runtime_frame_def] >>
  `eval_operand value t3 = SOME (immutable_copy_read F (a + n2w off) t1)` by
    metis_tac[copy_runtime_frame_operand] >>
  drule_all copy_runtime_store >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts s3 sb) t3` by
    (drule body_immutable_store_mem_ok >> disch_then irule >>
     goal_assum (drule_at Any) >>
     `t3.vs_alloca_next = s.vs_alloca_next` by
       metis_tac[body_copy_frame_frontier] >>
     irule body_immutable_copy_offset_range >> simp[] >> decide_tac) >>
  `run_inst_seq_mem_ok (emitted_insts s2 sb) t2` by
    (irule body_copy_frame_mem_append >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[] >>
     metis_tac[body_immutable_byte_offset_mem_ok]) >>
  `t1.vs_data_section = s.vs_data_section` by
    metis_tac[body_copy_frame_data_section] >>
  `w2n (a + n2w off) <= LENGTH t1.vs_data_section` by
    (`off < dimword (:256) /\ w2n a + off < dimword (:256)` by decide_tac >>
     simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w]) >>
  `run_inst_seq_mem_ok (emitted_insts s1 s2) t1` by
    (drule_then irule body_immutable_load_mem_ok >> rw[] >> gvs[]) >>
  `run_inst_seq_mem_ok (emitted_insts s1 sb) t1` by
    (irule body_copy_frame_mem_append >>
     qexistsl [`s2`,`t2`] >> simp[] >>
     metis_tac[copy_runtime_frame_trans, body_immutable_load_mem_ok]) >>
  irule body_copy_frame_mem_append >> qexistsl [`s1`,`t1`] >> simp[] >>
  metis_tac[copy_runtime_frame_trans]
QED

Theorem body_immutable_copy_mem_ok:
  !n off sa sb s a b.
    compile_imm_copy_to_memory F imm src dst n off sa = ((),sb) /\
    copy_old_operand sa src /\ copy_old_operand sa dst /\
    eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
    w2n b + off + 32 * n <= s.vs_alloca_next /\
    w2n b + off + 32 * n < dimword (:256) /\
    w2n a + off + 32 * n <= LENGTH s.vs_data_section /\
    w2n a + off + 32 * n < dimword (:256) ==>
    run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  Induct
  >- simp[compile_imm_copy_to_memory_def, comp_return_def, emitted_insts_def,
           run_inst_seq_mem_ok_def] >>
  simp[immutable_copy_suc, comp_ignore_bind_def, immutable_comp_bind_cases] >>
  rpt strip_tac >> drule_all copy_runtime_one >> strip_tac >>
  rename1 `immutable_copy_one F imm src dst off sa = ((),sm)` >>
  rename1 `copy_runtime_frame sa s sm t` >>
  `copy_old_operand sm src /\ copy_old_operand sm dst` by
    metis_tac[copy_old_operand_mono, copy_runtime_frame_def] >>
  `eval_operand src t = SOME a /\ eval_operand dst t = SOME b` by
    metis_tac[copy_runtime_frame_operand] >>
  `t.vs_alloca_next = s.vs_alloca_next` by metis_tac[body_copy_frame_frontier] >>
  `t.vs_data_section = s.vs_data_section` by
    metis_tac[body_copy_frame_data_section] >>
  `run_inst_seq_mem_ok (emitted_insts sa sm) s` by
    (drule body_immutable_one_mem_ok >> disch_then irule >>
     goal_assum (drule_at Any) >> simp[MULT_SUC] >> decide_tac) >>
  `run_inst_seq_mem_ok (emitted_insts sm sb) t` by
    (first_x_assum drule >> disch_then irule >>
     goal_assum (drule_at Any) >> simp[] >> gvs[MULT_SUC]) >>
  drule_all copy_runtime_run >> strip_tac >>
  irule body_copy_frame_mem_append >> metis_tac[]
QED

