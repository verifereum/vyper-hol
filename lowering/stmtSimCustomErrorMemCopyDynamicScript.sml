Theory stmtSimCustomErrorMemCopyDynamic
Ancestors
  stmtSimCustomErrorMemCopyInterface stmtSimCustomErrorMemCopyLoop
  placeTypedCopyRecursivePath context compileEnv venomState venomExecSemantics
  fragGasMode fragGasPathMem exprSimMemUnwrap fragExecMem emitHelperProps
  allocaFootprint allocaHistory memSafeRun loweringStateRelDefs emitHelper
  contextCodegenRel venomInst codegenRel venomMemDefs words list arithmetic
  exprLoweringProps typedMemoryCopy placeTypedCopyPath rich_list fragExec
  externalReturnNormalizeMem unitTransformDefs valueEncodingProps

Theorem typed_copy_assert_checked[local]:
  emit_void ASSERT [ok] a = ((),b) /\ eval_operand ok s = SOME 1w /\
  fn_has_code a b func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      t.vs_memory = s.vs_memory /\ typed_copy_state_frame a off len s t /\
      ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
      t.vs_inst_idx = LENGTH b.cs_current_insts /\
      alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `same_blocks a b /\
   b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
   emitted_insts a b = [mk_inst a.cs_next_id ASSERT [ok] []]` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_id_def, emit_def] >>
     strip_tac >> gvs[same_blocks_def, emitted_insts_def, DROP_LENGTH_APPEND]) >>
  `run_inst_seq (emitted_insts a b) s = OK s` by
    simp[run_inst_seq_def, step_inst_base_def, mk_inst_def] >>
  `run_inst_seq_mem_ok (emitted_insts a b) s` by
    (irule run_inst_seq_mem_ok_every >>
     simp[inst_mem_below_frontier_def, source_memory_read_ranges_def,
          source_memory_write_ranges_def, inst_dload_in_section_def, mk_inst_def]) >>
  `gas_path_mem ctx func s 0 (OK (s with vs_inst_idx := LENGTH b.cs_current_insts)) /\
   alloca_history func (s with vs_inst_idx := LENGTH b.cs_current_insts) /\
   ~s.vs_halted /\ s.vs_current_bb = b.cs_current_bb` by
    (irule straight_path_mem >> simp[] >> qexists_tac `a` >>
     gvs[mk_inst_def, is_terminator_def]) >>
  qexists_tac `s with vs_inst_idx := LENGTH b.cs_current_insts` >>
  gvs[typed_copy_state_frame_def, lookup_var_def, venom_state_component_equality]
QED

Theorem typed_copy_mload_checked[local]:
  emit_op MLOAD [addr] a = (op,b) /\
  eval_operand addr s = SOME p /\ w2n p + 32 <= s.vs_alloca_next /\
  fn_has_code a b func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      eval_operand op t = SOME (mload (w2n p) s) /\
      t.vs_memory = s.vs_memory /\ typed_copy_state_frame a off len s t /\
      ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
      t.vs_inst_idx = LENGTH b.cs_current_insts /\
      alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> irule typed_copy_emit_op_checked >> simp[] >>
  conj_tac
  >- (qexistsl_tac [`[addr]`, `MLOAD`] >>
      simp[is_terminator_def, step_inst_base_def, mk_inst_def,
           exec_read1_def, eval_operands_def]) >>
  irule emit_mload_mem_ok >> qexistsl_tac [`p`, `addr`, `op`] >> simp[]
QED

Theorem typed_copy_mstore_checked[local]:
  emit_void MSTORE [dst; value] a = ((),b) /\
  eval_operand dst s = SOME d /\ eval_operand value s = SOME w /\
  w2n d + 32 <= s.vs_alloca_next /\
  fn_has_code a b func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      mem_word_at (w2n d) t.vs_memory = w /\
      typed_copy_state_frame a (w2n d) 32 s t /\
      ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
      t.vs_inst_idx = LENGTH b.cs_current_insts /\
      alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `same_blocks a b /\
   b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
   emitted_insts a b = [mk_inst a.cs_next_id MSTORE [dst; value] []]` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_id_def, emit_def] >>
     strip_tac >> gvs[same_blocks_def, emitted_insts_def, DROP_LENGTH_APPEND]) >>
  `run_inst_seq (emitted_insts a b) s = OK (mstore (w2n d) w s)` by
    simp[run_inst_seq_def, step_inst_base_def, mk_inst_def,
         exec_write2_def, eval_operands_def] >>
  `run_inst_seq_mem_ok (emitted_insts a b) s` by
    (irule emit_mstore_mem_ok >> metis_tac[]) >>
  `gas_path_mem ctx func s 0
      (OK ((mstore (w2n d) w s) with vs_inst_idx := LENGTH b.cs_current_insts)) /\
   alloca_history func ((mstore (w2n d) w s) with vs_inst_idx := LENGTH b.cs_current_insts) /\
   ~(mstore (w2n d) w s).vs_halted /\
   (mstore (w2n d) w s).vs_current_bb = b.cs_current_bb` by
    (irule straight_path_mem >> simp[] >> qexists_tac `a` >>
     gvs[mk_inst_def, is_terminator_def]) >>
  qexists_tac `(mstore (w2n d) w s) with vs_inst_idx := LENGTH b.cs_current_insts` >>
  simp[typed_copy_mstore_state_frame, mstore_mem_word_at_same]
QED

Theorem typed_copy_dyn_check_checked[local]:
  emit_op GT [length; Lit (n2w C)] a = (too_long,b) /\
  emit_op ISZERO [too_long] b = (ok,c) /\
  emit_void ASSERT [ok] c = ((),d) /\
  eval_operand length s = SOME (n2w N) /\ N <= C /\ C < dimword (:256) /\
  fn_has_code a d func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      t.vs_memory = s.vs_memory /\ typed_copy_state_frame a off len s t /\
      ~t.vs_halted /\ t.vs_current_bb = d.cs_current_bb /\
      t.vs_inst_idx = LENGTH d.cs_current_insts /\
      alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d` by
    metis_tac[typed_copy_emit_op_mono, ci_mono_emit_void, pairTheory.SND] >>
  `cs_extends a c /\ cs_extends c d` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code a c func /\ fn_has_code c d func` by metis_tac[fn_has_code_split] >>
  `N < dimword (:256)` by decide_tac >>
  `?t. gas_path_mem ctx func s 0 (OK t) /\
       eval_operand too_long t = SOME 0w /\ eval_operand ok t = SOME 1w /\
       t.vs_memory = s.vs_memory /\ typed_copy_state_frame a off len s t /\
       ~t.vs_halted /\ t.vs_current_bb = c.cs_current_bb /\
       t.vs_inst_idx = LENGTH c.cs_current_insts /\
       alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next` by
    (irule typed_copy_two_ops_checked >> simp[] >>
     qexistsl_tac [`[length; Lit (n2w C)]`, `[too_long]`, `b`, `GT`, `ISZERO`] >>
     simp[] >> conj_tac
     >- simp[step_inst_base_def, mk_inst_def, exec_pure2_def,
             eval_operand_def, w2n_n2w, LESS_MOD, bool_to_word_def, NOT_LESS] >>
     rpt strip_tac >>
     simp[step_inst_base_def, mk_inst_def, exec_pure1_def, bool_to_word_def]) >>
  `alloca_inv t` by
    (gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
         typed_copy_state_frame_def, venom_state_component_equality] >> metis_tac[]) >>
  drule_all typed_copy_assert_checked >>
  disch_then (qspecl_then [`off`, `len`, `ctx`] strip_assume_tac) >>
  `typed_copy_state_frame a off len s t'` by
    (irule typed_copy_state_frame_trans >> qexists_tac `t` >> simp[] >>
     irule typed_copy_state_frame_mono >> qexists_tac `c` >>
     fs[ci_mono_def] >> decide_tac) >>
  qpat_assum `gas_path_mem ctx func s 0 (OK t)`
    (mp_then Any mp_tac gas_path_mem_then) >>
  disch_then drule >> simp[] >> strip_tac >> qexists_tac `t'` >> simp[]
QED

Theorem typed_copy_dyn_read_check_checked[local]:
  emit_op MLOAD [src] a = (length,b) /\
  emit_op GT [length; Lit (n2w C)] b = (too_long,c) /\
  emit_op ISZERO [too_long] c = (ok,d) /\
  emit_void ASSERT [ok] d = ((),e) /\
  N <= C /\ C < dimword (:256) /\
  eval_operand src s = SOME sw /\ mload (w2n sw) s = n2w N /\
  w2n sw + 32 <= s.vs_alloca_next /\
  fn_has_code a e func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      eval_operand length t = SOME (n2w N) /\ t.vs_memory = s.vs_memory /\
      typed_copy_state_frame a off len s t /\
      ~t.vs_halted /\ t.vs_current_bb = e.cs_current_bb /\
      t.vs_inst_idx = LENGTH e.cs_current_insts /\
      alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d /\ ci_mono d e` by
    metis_tac[typed_copy_emit_op_mono, ci_mono_emit_void, pairTheory.SND] >>
  `cs_extends a b /\ cs_extends b e` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code a b func /\ fn_has_code b e func` by metis_tac[fn_has_code_split] >>
  drule_all typed_copy_mload_checked >>
  disch_then (qspecl_then [`off`, `len`, `ctx`] strip_assume_tac) >>
  `alloca_inv t` by
    (gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
         typed_copy_state_frame_def, venom_state_component_equality] >> metis_tac[]) >>
  `eval_operand length t = SOME (n2w N)` by metis_tac[] >>
  drule_all typed_copy_dyn_check_checked >>
  disch_then (qspecl_then [`off`, `len`, `ctx`] strip_assume_tac) >>
  `eval_operand length t' = SOME (n2w N)` by
    metis_tac[typed_copy_state_frame_operand, typed_copy_emit_op_fresh] >>
  `typed_copy_state_frame a off len s t'` by
    (irule typed_copy_state_frame_trans >> qexists_tac `t` >> simp[] >>
     irule typed_copy_state_frame_mono >> qexists_tac `b` >> simp[]) >>
  qpat_assum `gas_path_mem ctx func s 0 (OK t)`
    (mp_then Any mp_tac gas_path_mem_then) >>
  disch_then drule >> simp[] >> strip_tac >> qexists_tac `t'` >> simp[]
QED
