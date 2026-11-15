Theory stmtSimCustomErrorMemCopyDynamic
Ancestors
  stmtSimCustomErrorMemCopyInterface stmtSimCustomErrorMemCopyLoop
  placeTypedCopyRecursivePath context compileEnv venomState venomExecSemantics
  fragGasMode fragGasPathMem exprSimMemUnwrap fragExecMem emitHelperProps
  allocaFootprint allocaHistory memSafeRun loweringStateRelDefs emitHelper
  contextCodegenRel venomInst codegenRel venomMemDefs words list arithmetic
  exprLoweringProps typedMemoryCopy placeTypedCopyPath rich_list fragExec
  externalReturnNormalizeMem unitTransformDefs valueEncodingProps valueEncoding

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

Theorem typed_copy_dyn_data_checked[local]:
  emit_void MSTORE [dst; length] a = ((),b) /\
  emit_op ADD [src; Lit 32w] b = (sd,c) /\
  emit_op ADD [dst; Lit 32w] c = (dd,d) /\
  (!x. src = Var x ==> not_fresh_at a x) /\
  (!x. dst = Var x ==> not_fresh_at a x) /\
  (!x. length = Var x ==> not_fresh_at a x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  eval_operand length s = SOME w /\ w2n dw + 32 <= s.vs_alloca_next /\
  fn_has_code a d func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      eval_operand length t = SOME w /\
      eval_operand sd t = SOME (sw + 32w) /\ eval_operand dd t = SOME (dw + 32w) /\
      mem_word_at (w2n dw) t.vs_memory = w /\
      typed_copy_state_frame a (w2n dw) 32 s t /\
      ~t.vs_halted /\ t.vs_current_bb = d.cs_current_bb /\
      t.vs_inst_idx = LENGTH d.cs_current_insts /\
      alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d` by
    metis_tac[typed_copy_emit_op_mono, ci_mono_emit_void, pairTheory.SND] >>
  `cs_extends a b /\ cs_extends b d` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code a b func /\ fn_has_code b d func` by metis_tac[fn_has_code_split] >>
  drule_all typed_copy_mstore_checked >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `eval_operand src t = SOME sw /\ eval_operand dst t = SOME dw` by
    metis_tac[typed_copy_state_frame_operand] >>
  `alloca_inv t` by
    (gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
         typed_copy_state_frame_def, venom_state_component_equality] >> metis_tac[]) >>
  suspend "adds"
QED

Resume typed_copy_dyn_data_checked[adds]:
  `?u. gas_path_mem ctx func t 0 (OK u) /\
       eval_operand sd u = SOME (sw + 32w) /\ eval_operand dd u = SOME (dw + 32w) /\
       u.vs_memory = t.vs_memory /\ typed_copy_state_frame b (w2n dw) 32 t u /\
       ~u.vs_halted /\ u.vs_current_bb = d.cs_current_bb /\
       u.vs_inst_idx = LENGTH d.cs_current_insts /\
       alloca_history func u /\ u.vs_alloca_next = t.vs_alloca_next` by
    (irule typed_copy_two_ops_checked >> simp[] >>
     qexistsl_tac [`[src; Lit 32w]`, `[dst; Lit 32w]`, `c`, `ADD`, `ADD`] >>
     simp[] >> conj_tac
     >- simp[step_inst_base_def, mk_inst_def, exec_pure2_def, eval_operand_def] >>
     rpt strip_tac >>
     `eval_operand dst t' = SOME dw` by
       metis_tac[typed_copy_state_frame_operand, typed_copy_operand_fresh_mono] >>
     simp[step_inst_base_def, mk_inst_def, exec_pure2_def, eval_operand_def]) >>
  `typed_copy_state_frame a (w2n dw) 32 s u` by
    (irule typed_copy_state_frame_trans >> qexists_tac `t` >> simp[] >>
     irule typed_copy_state_frame_mono >> qexists_tac `b` >> simp[]) >>
  `eval_operand length u = SOME w` by metis_tac[typed_copy_state_frame_operand] >>
  qpat_assum `gas_path_mem ctx func s 0 (OK t)`
    (mp_then Any mp_tac gas_path_mem_then) >>
  disch_then drule >> simp[] >> strip_tac >> qexists_tac `u` >> simp[]
QED

Finalise typed_copy_dyn_data_checked

Theorem typed_copy_dyn_prefix_checked:
  emit_op MLOAD [src] a = (length,a1) /\
  emit_op GT [length; Lit (n2w C)] a1 = (too_long,a2) /\
  emit_op ISZERO [too_long] a2 = (ok,a3) /\
  emit_void ASSERT [ok] a3 = ((),a4) /\
  emit_void MSTORE [dst; length] a4 = ((),a5) /\
  emit_op ADD [src; Lit 32w] a5 = (sd,a6) /\
  emit_op ADD [dst; Lit 32w] a6 = (dd,b) /\
  (!x. src = Var x ==> not_fresh_at a x) /\
  (!x. dst = Var x ==> not_fresh_at a x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  N <= C /\ C < dimword (:256) /\ mload (w2n sw) s = n2w N /\
  w2n sw + 32 <= s.vs_alloca_next /\ w2n dw + 32 <= s.vs_alloca_next /\
  fn_has_code a b func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      eval_operand length t = SOME (n2w N) /\
      eval_operand sd t = SOME (sw + 32w) /\ eval_operand dd t = SOME (dw + 32w) /\
      mem_word_at (w2n dw) t.vs_memory = n2w N /\
      typed_copy_state_frame a (w2n dw) 32 s t /\
      ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
      t.vs_inst_idx = LENGTH b.cs_current_insts /\
      alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule_all typed_copy_dyn_prefix_mono >> strip_tac >>
  `cs_extends a a4 /\ cs_extends a4 b` by gvs[ci_mono_def] >>
  `fn_has_code a a4 func /\ fn_has_code a4 b func` by metis_tac[fn_has_code_split] >>
  drule_all typed_copy_dyn_read_check_checked >>
  disch_then (qspecl_then [`w2n dw`, `32`, `ctx`] strip_assume_tac) >>
  `eval_operand src t = SOME sw /\ eval_operand dst t = SOME dw` by
    metis_tac[typed_copy_state_frame_operand] >>
  `(!x. src = Var x ==> not_fresh_at a4 x) /\
   (!x. dst = Var x ==> not_fresh_at a4 x)` by
    metis_tac[typed_copy_operand_fresh_mono] >>
  `alloca_inv t` by
    (gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
         typed_copy_state_frame_def, venom_state_component_equality] >> metis_tac[]) >>
  `w2n dw + 32 <= t.vs_alloca_next` by simp[] >>
  drule_all typed_copy_dyn_data_checked >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `typed_copy_state_frame a (w2n dw) 32 s t'` by
    (irule typed_copy_state_frame_trans >> qexists_tac `t` >> simp[] >>
     irule typed_copy_state_frame_mono >> qexists_tac `a4` >> simp[]) >>
  qpat_assum `gas_path_mem ctx func s 0 (OK t)`
    (mp_then Any mp_tac gas_path_mem_then) >>
  disch_then drule >> simp[] >> strip_tac >> qexists_tac `t'` >> simp[]
QED

Theorem typed_copy_dyn_slow_data_checked:
  fresh_label "typed_dyn_cond" sa = (hdr,l1) /\
  fresh_label "typed_dyn_body" l1 = (blabel,l2) /\
  fresh_label "typed_dyn_exit" l2 = (exit,l3) /\
  fresh_var l3 = (counter,init) /\
  emit_inst ASSIGN [Lit 0w] [counter] init = ((),st0) /\
  emit_inst JMP [Label hdr] [] st0 = ((),st1) /\
  new_block hdr st1 = (u1,sth) /\
  emit_op LT [Var counter; length] sth = (lt,h1) /\
  emit_op ISZERO [lt] h1 = (done,stj) /\
  emit_inst JNZ [done; Label exit; Label blabel] [] stj = ((),st2) /\
  new_block blabel st2 = (u2,stb) /\
  emit_op MUL [Var counter; Lit (n2w (type_memory_size stv))] stb = (so,b1) /\
  emit_op MUL [Var counter; Lit (n2w (type_memory_size dtv))] b1 = (doff,b2) /\
  emit_op ADD [src;so] b2 = (sp,b3) /\
  emit_op ADD [dst;doff] b3 = (dp,b4) /\
  compile_store_memory_typed cenv dp dty sp sty b4 = ((),b5) /\
  emit_op ADD [Var counter; Lit 1w] b5 = (inc,b6) /\
  emit_inst ASSIGN [inc] [counter] b6 = ((),ste) /\
  emit_inst JMP [Label hdr] [] ste = ((),st3) /\
  new_block exit st3 = (u3,stx) /\
  (!x. length = Var x ==> not_fresh_at sa x) /\
  eval_operand length s = SOME (n2w N) /\ N < dimword (:256) /\
  (!i. i < N ==> typed_copy_checked_entry cenv ctx dty sty dtv stv (f i) /\
                   val_wf stv (f i) /\ val_wf dtv (f i)) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  (!i. i < N ==> val_in_memory stv (f i)
     (w2n sw + i * type_memory_size stv) s.vs_memory) /\
  w2n sw + N * type_memory_size stv < dimword (:256) /\
  w2n dw + N * type_memory_size dtv < dimword (:256) /\
  w2n sw + N * type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + N * type_memory_size dtv <= s.vs_alloca_next /\
  (w2n sw + N * type_memory_size stv <= w2n dw \/
   w2n dw + N * type_memory_size dtv <= w2n sw) /\
  fn_has_code sa stx func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      (!i. i < N ==> val_in_memory dtv (f i)
         (w2n dw + i * type_memory_size dtv) t.vs_memory) /\
      typed_copy_state_frame sa (w2n dw) (N * type_memory_size dtv) s t /\
      ~t.vs_halted /\ t.vs_current_bb = stx.cs_current_bb /\
      t.vs_inst_idx = LENGTH stx.cs_current_insts /\
      alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all typed_copy_dynarray_slow_layout >> strip_tac >>
  irule typed_copy_index_loop_checked >> simp[] >>
  qpat_assum `emit_inst ASSIGN [Lit 0w] _ _ = _`
    (irule_at (Pat `emit_inst ASSIGN [Lit 0w] _ _ = _`)) >>
  qpat_assum `emit_op LT _ _ = _` (irule_at (Pat `emit_op LT _ _ = _`)) >>
  qpat_assum `emit_op ISZERO _ _ = _` (irule_at (Pat `emit_op ISZERO _ _ = _`)) >>
  qpat_assum `emit_inst JNZ _ _ _ = _` (irule_at (Pat `emit_inst JNZ _ _ _ = _`)) >>
  qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = _`
    (irule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem typed_copy_mcopy_checked[local]:
  emit_void MCOPY [dst; src; bytes] a = ((),b) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  eval_operand bytes s = SOME (n2w n) /\ n < dimword (:256) /\
  w2n sw + n <= s.vs_alloca_next /\ w2n dw + n <= s.vs_alloca_next /\
  fn_has_code a b func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  let t = (mcopy (w2n dw) (w2n sw) n s) with vs_inst_idx := LENGTH b.cs_current_insts in
  gas_path_mem ctx func s 0 (OK t) /\
  alloca_history func t /\ ~t.vs_halted /\
  t.vs_current_bb = b.cs_current_bb /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `same_blocks a b /\
   b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
   emitted_insts a b = [mk_inst a.cs_next_id MCOPY [dst; src; bytes] []]` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_id_def, emit_def] >>
     strip_tac >> gvs[same_blocks_def, emitted_insts_def, DROP_LENGTH_APPEND]) >>
  `run_inst_seq (emitted_insts a b) s = OK (mcopy (w2n dw) (w2n sw) n s)` by
    simp[run_inst_seq_def, step_inst_base_def, mk_inst_def, w2n_n2w, LESS_MOD] >>
  `run_inst_seq_mem_ok (emitted_insts a b) s` by
    (irule emit_mcopy_mem_ok >>
     qexistsl_tac [`sw`, `dw`, `dst`, `bytes`, `n2w n`, `src`] >>
     simp[w2n_n2w, LESS_MOD]) >>
  simp[LET_THM] >>
  `gas_path_mem ctx func s 0
      (OK ((mcopy (w2n dw) (w2n sw) n s) with vs_inst_idx := LENGTH b.cs_current_insts)) /\
   alloca_history func ((mcopy (w2n dw) (w2n sw) n s) with vs_inst_idx := LENGTH b.cs_current_insts) /\
   ~(mcopy (w2n dw) (w2n sw) n s).vs_halted /\
   (mcopy (w2n dw) (w2n sw) n s).vs_current_bb = b.cs_current_bb` by
    (irule straight_path_mem >> simp[] >> qexists_tac `a` >>
     gvs[mk_inst_def, is_terminator_def]) >>
  gvs[mcopy_def, write_memory_with_expansion_def]
QED

Theorem typed_copy_dynarray_checked_path:
  compile_copy_dynarray_typed cenv dst dty C src sty sa = ((),sb) /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  (dty = sty ==> dtv = stv) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  LENGTH vs <= C /\ C < dimword (:256) /\
  val_wf (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs)) /\
  val_wf (ArrayTV dtv (Dynamic C)) (ArrayV (DynArrayV vs)) /\
  val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs))
    (w2n sw) s.vs_memory /\
  (!i. i < LENGTH vs ==> typed_copy_checked_entry cenv ctx dty sty dtv stv (EL i vs)) /\
  w2n sw + type_memory_size (ArrayTV stv (Dynamic scap)) < dimword (:256) /\
  w2n dw + type_memory_size (ArrayTV dtv (Dynamic C)) < dimword (:256) /\
  w2n sw + type_memory_size (ArrayTV stv (Dynamic scap)) <= s.vs_alloca_next /\
  w2n dw + type_memory_size (ArrayTV dtv (Dynamic C)) <= s.vs_alloca_next /\
  (w2n sw + type_memory_size (ArrayTV stv (Dynamic scap)) <= w2n dw \/
   w2n dw + type_memory_size (ArrayTV dtv (Dynamic C)) <= w2n sw) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      val_in_memory (ArrayTV dtv (Dynamic C)) (ArrayV (DynArrayV vs))
        (w2n dw) t.vs_memory /\
      typed_copy_state_frame sa (w2n dw)
        (type_memory_size (ArrayTV dtv (Dynamic C))) s t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `compile_copy_dynarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gnvs[]) >>
  rename1 `emit_op ADD [dst; Lit 32w] a6 = (dd,b)` >>
  rename1 `emit_op ADD [src; Lit 32w] a5 = (sd,a6)` >> disch_tac >>
  drule_all typed_copy_dyn_prefix_mono >> strip_tac >>
  `ci_mono b sb` by
    (qmatch_asmsub_abbrev_tac `suffix b = ((),sb)` >>
     `ci_mono b (SND (suffix b))` suffices_by gvs[] >>
     unabbrev_all_tac >> IF_CASES_TAC >>
     rpt (FIRST [irule ci_mono_bind, irule ci_mono_ignore_bind] >>
          rpt conj_tac >> rpt gen_tac >> BETA_TAC) >>
     simp[ci_mono_emit_op, ci_mono_emit_inst, ci_mono_new_block,
          ci_mono_fresh_label, ci_mono_fresh_var, ci_mono_comp_return,
          cj 1 ci_mono_typed_memory_family,
          contextTheory.compile_copy_memory_dynamic_def, ci_mono_emit_void]) >>
  `cs_extends sa b /\ cs_extends b sb` by gvs[ci_mono_def] >>
  `fn_has_code sa b func /\ fn_has_code b sb func` by metis_tac[fn_has_code_split] >>
  `mload (w2n sw) s = n2w (LENGTH vs)` by
    gvs[typed_copy_dynarray_representation, mem_word_at_eq_mload] >>
  `w2n sw + 32 <= s.vs_alloca_next /\ w2n dw + 32 <= s.vs_alloca_next` by
    (gvs[type_memory_size_def] >> decide_tac) >>
  drule_all typed_copy_dyn_prefix_checked >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  suspend "suffix"
QED

Resume typed_copy_dynarray_checked_path[suffix]:
  rpt (qpat_x_assum `emit_op _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `emit_void _ _ _ = _` kall_tac) >>
  `val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs))
      (w2n sw) t.vs_memory` by
    (irule typed_copy_frame_preserves_source >> conj_tac >- simp[] >>
     qexistsl_tac [`32`, `w2n dw`, `s.vs_memory`] >> simp[] >> conj_tac
     >- (fs[type_memory_size_def] >> decide_tac) >>
     gvs[typed_copy_state_frame_def]) >>
  `LENGTH vs <= scap` by gvs[typed_copy_dynarray_wf] >>
  `LENGTH vs * type_memory_size stv <= scap * type_memory_size stv /\
   LENGTH vs * type_memory_size dtv <= C * type_memory_size dtv` by
    simp[arithmeticTheory.LE_MULT_RCANCEL] >>
  `w2n (sw + 32w) = w2n sw + 32 /\
   w2n (dw + 32w) = w2n dw + 32` by
    (fs[type_memory_size_def] >> simp[word_add_def, w2n_n2w, LESS_MOD]) >>
  `w2n (sw + 32w) + LENGTH vs * type_memory_size stv < dimword (:256) /\
   w2n (dw + 32w) + LENGTH vs * type_memory_size dtv < dimword (:256) /\
   w2n (sw + 32w) + LENGTH vs * type_memory_size stv <= t.vs_alloca_next /\
   w2n (dw + 32w) + LENGTH vs * type_memory_size dtv <= t.vs_alloca_next /\
   (w2n (sw + 32w) + LENGTH vs * type_memory_size stv <= w2n (dw + 32w) \/
    w2n (dw + 32w) + LENGTH vs * type_memory_size dtv <= w2n (sw + 32w))` by
    (gns[type_memory_size_def, Excl "LE_MULT_RCANCEL"] >> decide_tac) >>
  `alloca_inv t` by
    (gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
         typed_copy_state_frame_def, venom_state_component_equality] >> metis_tac[]) >>
  `?u. gas_path_mem ctx func t 0 (OK u) /\
       (!i. i < LENGTH vs ==> val_in_memory dtv (EL i vs)
          (w2n (dw + 32w) + i * type_memory_size dtv) u.vs_memory) /\
       typed_copy_state_frame b (w2n (dw + 32w))
          (LENGTH vs * type_memory_size dtv) t u /\
       ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
       u.vs_inst_idx = LENGTH sb.cs_current_insts /\
       alloca_history func u /\ u.vs_alloca_next = t.vs_alloca_next` by suspend "data" >>
  suspend "reconstruct"
QED

Resume typed_copy_dynarray_checked_path[data]:
  markerLib.RESUME_TAC >>
  rpt (qpat_x_assum `ci_mono _ _` kall_tac) >>
  qpat_x_assum `val_in_memory _ _ _ s.vs_memory` kall_tac >>
  qpat_x_assum `typed_copy_state_frame sa _ _ s t` kall_tac >>
  `LENGTH vs < dimword (:256)` by decide_tac >>
  `!i. i < LENGTH vs ==> val_in_memory stv (EL i vs)
     (w2n (sw + 32w) + i * type_memory_size stv) t.vs_memory` by
    gvs[typed_copy_dynarray_representation] >>
  (Cases_on `type_memory_size dtv = type_memory_size stv /\ dty = sty`
   >- suspend "bulk" >> suspend "slow")
QED

Resume typed_copy_dynarray_checked_path[slow]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `w2n (dw + 32w) = _` kall_tac >>
  qpat_x_assum `w2n (sw + 32w) = _` kall_tac >>
  qpat_x_assum `_ b = ((),sb)` mp_tac >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> gnvs[] >> pairarg_tac >> gnvs[] >>
  pairarg_tac >> gnvs[] >> pairarg_tac >> gnvs[] >>
  pairarg_tac >> gnvs[] >> pairarg_tac >> gnvs[] >>
  pairarg_tac >> gnvs[] >> pairarg_tac >> gnvs[] >>
  pairarg_tac >> gnvs[] >> pairarg_tac >> gnvs[] >>
  pairarg_tac >> gnvs[] >> pairarg_tac >> gnvs[] >>
  pairarg_tac >> gnvs[] >> pairarg_tac >> gnvs[] >>
  pairarg_tac >> gnvs[] >> pairarg_tac >> gnvs[] >>
  pairarg_tac >> gnvs[] >> pairarg_tac >> gnvs[] >>
  pairarg_tac >> gnvs[] >> pairarg_tac >> gnvs[] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> gnvs[] >>
  `!i. i < LENGTH vs ==> typed_copy_checked_entry cenv ctx dty sty dtv stv (EL i vs) /\
        val_wf stv (EL i vs) /\ val_wf dtv (EL i vs)` by
    gvs[typed_copy_dynarray_wf] >>
  qpat_x_assum `t.vs_alloca_next = s.vs_alloca_next` (assume_tac o GSYM) >>
  simp[] >>
  irule (SRULE [gas_marked_path_def] (BETA_RULE (Q.INST [`f` |-> `\i. EL i vs`]
    typed_copy_dyn_slow_data_checked))) >>
  qpat_assum `fresh_label "typed_dyn_cond" _ = _`
    (irule_at (Pat `fresh_label "typed_dyn_cond" _ = _`)) >>
  qpat_assum `fresh_label "typed_dyn_body" _ = _`
    (irule_at (Pat `fresh_label "typed_dyn_body" _ = _`)) >>
  qpat_assum `fresh_label "typed_dyn_exit" _ = _`
    (irule_at (Pat `fresh_label "typed_dyn_exit" _ = _`)) >>
  qpat_assum `emit_inst ASSIGN [Lit 0w] _ _ = _`
    (irule_at (Pat `emit_inst ASSIGN [Lit 0w] _ _ = _`)) >>
  qpat_assum `emit_op LT _ _ = _` (irule_at (Pat `emit_op LT _ _ = _`)) >>
  qpat_assum `emit_op ISZERO _ _ = _` (irule_at (Pat `emit_op ISZERO _ _ = _`)) >>
  qpat_assum `emit_inst JNZ _ _ _ = _` (irule_at (Pat `emit_inst JNZ _ _ _ = _`)) >>
  qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = _`
    (irule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  rpt (goal_assum (drule_at Any)) >> simp[] >> decide_tac
QED

Resume typed_copy_dynarray_checked_path[bulk]:
  markerLib.RESUME_TAC >> (
  `dtv = stv` by simp[] >>
  qpat_x_assum `dtv = stv` SUBST_ALL_TAC >>
  qpat_x_assum `_ b = ((),sb)` mp_tac >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gnvs[]) >> strip_tac >>
  rename1 `emit_op MUL _ b = (bytes,c)` >>
  `ci_mono b c /\ ci_mono c sb` by
    metis_tac[typed_copy_emit_op_mono, ci_mono_compile_copy_memory_dynamic, pairTheory.SND] >>
  `cs_extends b c /\ cs_extends c sb` by gvs[ci_mono_def] >>
  `fn_has_code b c func /\ fn_has_code c sb func` by metis_tac[fn_has_code_split] >>
  `?r. gas_path_mem ctx func t 0 (OK r) /\
       eval_operand bytes r = SOME (n2w (LENGTH vs * type_memory_size stv)) /\
       r.vs_memory = t.vs_memory /\
       typed_copy_state_frame b (w2n (dw + 32w)) (LENGTH vs * type_memory_size stv) t r /\
       ~r.vs_halted /\ r.vs_current_bb = c.cs_current_bb /\
       r.vs_inst_idx = LENGTH c.cs_current_insts /\
       alloca_history func r /\ r.vs_alloca_next = t.vs_alloca_next` by
    (irule typed_copy_control_emit_op_checked >> simp[] >>
     qexistsl_tac [`[length; Lit (n2w (type_memory_size stv))]`, `MUL`] >>
     simp[step_inst_base_opcode_eqs, mk_inst_def,
          exec_pure2_def, eval_operand_def, GSYM word_mul_n2w]) >>
  `eval_operand sd r = SOME (sw + 32w) /\ eval_operand dd r = SOME (dw + 32w)` by
    metis_tac[typed_copy_state_frame_operand] >>
  suspend "mcopy")
QED

Resume typed_copy_dynarray_checked_path[reconstruct]:
  markerLib.RESUME_TAC >> (
  `typed_copy_state_frame b (w2n dw + 32)
      (LENGTH vs * type_memory_size dtv) t u` by metis_tac[] >>
  qexists_tac `u` >> conj_tac
  >- (qpat_assum `gas_path_mem ctx func s 0 (OK t)`
        (mp_then Any mp_tac gas_path_mem_then) >>
      disch_then drule >> simp[gas_marked_path_def]) >>
  conj_tac
  >- (irule typed_copy_dynarray_reconstruct >> conj_tac
      >- (qpat_assum `!i. _ ==> val_in_memory dtv _ _ u.vs_memory` mp_tac >>
          simp_tac std_ss [AC ADD_ASSOC ADD_COMM] >> simp[]) >>
      qpat_assum `typed_copy_state_frame b (w2n dw + 32) _ t u`
        (irule_at (Pat `typed_copy_state_frame _ _ _ _ _`)) >> simp[]) >>
  simp[] >>
  `typed_copy_state_frame sa (w2n dw + 32)
      (LENGTH vs * type_memory_size dtv) t u` by
    (irule typed_copy_state_frame_mono >> goal_assum (drule_at Any) >> simp[]) >>
  irule typed_copy_state_frame_trans >> qexists_tac `t` >> conj_tac
  >- (irule typed_copy_state_frame_subinterval >>
      goal_assum (drule_at (Pat `typed_copy_state_frame _ _ _ s t`)) >>
      simp[type_memory_size_def]) >>
  irule typed_copy_state_frame_subinterval >>
  goal_assum (drule_at (Pat `typed_copy_state_frame sa _ _ t _`)) >>
  simp[type_memory_size_def, Excl "LE_MULT_RCANCEL"])
QED

Resume typed_copy_dynarray_checked_path[mcopy]:
  markerLib.RESUME_TAC >> (
  `LENGTH vs * type_memory_size stv < dimword (:256)` by decide_tac >>
  `eval_operand bytes r = SOME (n2w (LENGTH vs * type_memory_size stv))` by simp[] >>
  `emit_void MCOPY [dd; sd; bytes] c = ((),sb)` by
    gvs[compile_copy_memory_dynamic_def] >>
  `same_blocks c sb` by
    gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_id_def, emit_def, same_blocks_def] >>
  `alloca_inv r` by
    (gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
         typed_copy_state_frame_def, venom_state_component_equality] >> metis_tac[]) >>
  `w2n (sw + 32w) + LENGTH vs * type_memory_size stv <= r.vs_alloca_next /\
   w2n (dw + 32w) + LENGTH vs * type_memory_size stv <= r.vs_alloca_next` by
    (gvs[type_memory_size_def, Excl "LE_MULT_RCANCEL"] >>
     `LENGTH vs * type_memory_size stv <= C * type_memory_size stv` by
       simp[arithmeticTheory.LE_MULT_RCANCEL] >> decide_tac) >>
  drule_all typed_copy_mcopy_checked >>
  disch_then (qspec_then `ctx` mp_tac) >> simp[LET_THM] >> strip_tac >>
  qabbrev_tac `u = (mcopy (w2n dw + 32) (w2n sw + 32)
    (LENGTH vs * type_memory_size stv) r) with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `typed_copy_state_frame c (w2n (dw + 32w))
      (LENGTH vs * type_memory_size stv) r u` by
    simp[Abbr `u`, typed_copy_mcopy_state_frame] >>
  `typed_copy_state_frame b (w2n (dw + 32w))
      (LENGTH vs * type_memory_size stv) t u` by
    (gvs[] >> irule typed_copy_state_frame_trans >> qexists_tac `r` >> simp[] >>
     irule typed_copy_state_frame_mono >> qexists_tac `c` >> simp[]) >>
  qexists_tac `u` >> conj_tac
  >- (qpat_assum `gas_path_mem ctx func t 0 (OK r)`
        (mp_then Any mp_tac gas_path_mem_then) >>
      disch_then drule >> simp[]) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> irule valueCopyTheory.val_in_memory_relocate >>
      conj_tac >- gvs[typed_copy_dynarray_wf] >>
      qexistsl_tac [`w2n (sw + 32w) + i * type_memory_size stv`,
                    `type_memory_size stv`, `r.vs_memory`] >>
      simp[] >> conj_tac
      >- gvs[typed_copy_dynarray_wf, exprSimPropsTheory.val_footprint_le] >>
      `mem_bytes_at (w2n (dw + 32w)) (LENGTH vs * type_memory_size stv) u.vs_memory =
       mem_bytes_at (w2n (sw + 32w)) (LENGTH vs * type_memory_size stv) r.vs_memory` by
        simp[Abbr `u`, mcopy_mem_bytes_at_same] >>
      drule valueEncodingProofsTheory.mem_bytes_at_translated_window >>
      disch_then (qspecl_then [`i * type_memory_size stv`, `type_memory_size stv`] mp_tac) >>
      (impl_tac >-
        (`SUC i <= LENGTH vs` by decide_tac >>
         `SUC i * type_memory_size stv <= LENGTH vs * type_memory_size stv` by
           simp[arithmeticTheory.LE_MULT_RCANCEL] >>
         qpat_x_assum `SUC i * _ <= _` mp_tac >>
         pure_rewrite_tac[arithmeticTheory.MULT_CLAUSES] >> decide_tac)) >>
      simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  gvs[Abbr `u`, mcopy_def, write_memory_with_expansion_def, same_blocks_def])
QED

Finalise typed_copy_dynarray_checked_path
