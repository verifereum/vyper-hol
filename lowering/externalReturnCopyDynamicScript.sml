(* Task-owned dynamic-array operational boundaries. *)
Theory externalReturnCopyDynamic
Ancestors
  externalReturnCopyArrayLoop externalReturnCopyFrame venomState compileEnv loweringStateRelDefs
  arithmetic fragExec emitHelper emitHelperProps context venomExecSemantics
  venomInst words finite_map externalReturnCopyTransport exprLoweringProps
  valueEncoding valueEncodingDefs valueEncodingProps list pair

Theorem return_copy_dynamic_header_frag:
  !ctx counter length N k a lt b done c s off len.
    emit_op LT [Var counter; length] a = (lt,b) /\
    emit_op ISZERO [lt] b = (done,c) /\
    not_fresh_at a counter /\ lookup_var counter s = SOME (n2w k) /\
    eval_operand length s = SOME (n2w N) /\
    k <= N /\ N < dimword (:256) ==>
    frag_exec ctx a c (\u. u = s)
      (\t. eval_operand done t = SOME (if k < N then 0w else 1w) /\
           t.vs_memory = s.vs_memory /\
           return_copy_frame a off len s t) (\r. F)
Proof
  rpt strip_tac >>
  `k < dimword (:256)` by decide_tac >>
  `frag_exec ctx a b (\u. u = s)
     (\t. eval_operand lt t = SOME (bool_to_word (k < N)) /\
          t.vs_memory = s.vs_memory /\
          return_copy_frame a off len s t) (\r. F)` by
    (irule return_copy_emit_op_frag >> simp[venomInstTheory.is_terminator_def] >>
     goal_assum (drule_at Any) >>
     simp[venomInstTheory.is_terminator_def, step_inst_base_def, mk_inst_def,
          exec_pure2_def, eval_operand_def, w2n_n2w, LESS_MOD]) >>
  drule frag_exec_then >> disch_then irule >>
  simp[emit_op_extends] >> conj_tac
  >- (rpt strip_tac >>
      `frag_exec ctx b c (\u. u = t)
         (\u. eval_operand done u = SOME (bool_to_word (bool_to_word (k < N) = 0w)) /\
              u.vs_memory = t.vs_memory /\
              return_copy_frame b off len t u) (\r. F)` by
        (irule return_copy_emit_op_frag >> simp[venomInstTheory.is_terminator_def] >>
         goal_assum (drule_at Any) >>
         simp[venomInstTheory.is_terminator_def, step_inst_base_def, mk_inst_def, exec_pure1_def]) >>
      pop_assum (mp_then Any irule frag_exec_conseq) >>
      simp[] >> rpt strip_tac >>
      fs[bool_to_word_def] >> Cases_on `k < N` >> gvs[] >>
      irule return_copy_frame_trans >> qexists_tac `t` >> simp[] >>
      irule return_copy_frame_mono >> goal_assum (drule_at Any) >>
      metis_tac[return_copy_emit_op_mono]) >>
  metis_tac[return_copy_emit_op_mono, ci_mono_def]
QED

Theorem return_copy_dynamic_load_frag:
  emit_op MLOAD [src] a = (length,b) /\
  eval_operand src s = SOME sw /\ mload (w2n sw) s = n2w N ==>
  frag_exec ctx a b (\u. u = s)
    (\t. eval_operand length t = SOME (n2w N) /\
         t.vs_memory = s.vs_memory /\ return_copy_frame a off len s t) (\r. F)
Proof
  strip_tac >> irule return_copy_emit_op_frag >>
  simp[venomInstTheory.is_terminator_def] >> goal_assum (drule_at Any) >>
  simp[venomInstTheory.is_terminator_def, step_inst_base_def, mk_inst_def, exec_read1_def]
QED

Theorem return_copy_dynamic_assert_frag:
  emit_void ASSERT [ok] a = ((),b) /\ eval_operand ok s = SOME 1w ==>
  frag_exec ctx a b (\u. u = s)
    (\t. t.vs_memory = s.vs_memory /\ return_copy_frame a off len s t) (\r. F)
Proof
  strip_tac >>
  qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
  simp[emit_void_def, comp_bind_def, fresh_id_def, emit_def] >> strip_tac >>
  gvs[] >> irule frag_exec_run_inst_seq >>
  simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND,
       mk_inst_def, venomInstTheory.is_terminator_def,
       run_inst_seq_def, step_inst_base_def] >>
  rpt strip_tac >> gvs[] >>
  simp[return_copy_frame_def, return_copy_memory_frame_def,
       venom_state_component_equality, lookup_var_def] >>
  simp[mstore_def]
QED

Theorem return_copy_dynamic_capacity_frag:
  emit_op GT [length; Lit (n2w capacity)] a = (too_long,b) /\
  emit_op ISZERO [too_long] b = (ok,c) /\
  eval_operand length s = SOME (n2w N) /\
  N <= capacity /\ capacity < dimword (:256) ==>
  frag_exec ctx a c (\u. u = s)
    (\t. eval_operand ok t = SOME 1w /\ t.vs_memory = s.vs_memory /\
         return_copy_frame a off len s t) (\r. F)
Proof
  rpt strip_tac >>
  `N < dimword (:256)` by decide_tac >>
  `frag_exec ctx a b (\u. u = s)
    (\t. eval_operand too_long t = SOME 0w /\ t.vs_memory = s.vs_memory /\
         return_copy_frame a off len s t) (\r. F)` by
    (irule return_copy_emit_op_frag >> simp[venomInstTheory.is_terminator_def] >>
     goal_assum (drule_at Any) >>
     simp[venomInstTheory.is_terminator_def, step_inst_base_def, mk_inst_def,
          exec_pure2_def, eval_operand_def, w2n_n2w, LESS_MOD, bool_to_word_def]) >>
  drule frag_exec_then >> disch_then irule >>
  simp[emit_op_extends] >> conj_tac
  >- (rpt strip_tac >>
      `frag_exec ctx b c (\u. u = t)
        (\u. eval_operand ok u = SOME 1w /\ u.vs_memory = t.vs_memory /\
             return_copy_frame b off len t u) (\r. F)` by
        (irule return_copy_emit_op_frag >> simp[venomInstTheory.is_terminator_def] >>
         goal_assum (drule_at Any) >>
         simp[venomInstTheory.is_terminator_def, step_inst_base_def, mk_inst_def,
              exec_pure1_def, bool_to_word_def]) >>
      pop_assum (mp_then Any irule frag_exec_conseq) >> simp[] >> rpt strip_tac >>
      irule return_copy_frame_trans >> qexists_tac `t` >> simp[] >>
      irule return_copy_frame_mono >> goal_assum (drule_at Any) >>
      metis_tac[return_copy_emit_op_mono]) >>
  metis_tac[return_copy_emit_op_mono, ci_mono_def]
QED

Theorem return_copy_dynamic_mstore_frame:
  return_copy_frame sa off 32 s (mstore off w s)
Proof
  simp[return_copy_frame_def] >> conj_tac
  >- simp[mstore_def, venom_state_component_equality] >>
  rewrite_tac[return_copy_memory_frame_def] >> conj_tac
  >- (rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> simp[]) >>
  simp[mstore_def, byteTheory.LENGTH_word_to_bytes] >>
  Cases_on `off + 32 > LENGTH s.vs_memory` >> simp[LENGTH_TAKE, LENGTH_DROP] >>
  decide_tac
QED

Theorem return_copy_dynamic_store_frag:
  emit_void MSTORE [dst; length] a = ((),b) /\
  eval_operand dst s = SOME dw /\ eval_operand length s = SOME (n2w N) ==>
  frag_exec ctx a b (\u. u = s)
    (\t. mem_word_at (w2n dw) t.vs_memory = n2w N /\
         return_copy_frame a (w2n dw) 32 s t) (\r. F)
Proof
  strip_tac >>
  qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
  simp[emit_void_def, comp_bind_def, fresh_id_def, emit_def] >> strip_tac >>
  gvs[] >> irule frag_exec_run_inst_seq >>
  simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND,
       mk_inst_def, venomInstTheory.is_terminator_def,
       run_inst_seq_def, step_inst_base_def, exec_write2_def] >>
  rpt strip_tac >> gvs[] >>
  simp[mstore_mem_word_at_same] >>
  irule return_copy_frame_trans >> qexists_tac `mstore (w2n dw) (n2w N) s` >>
  simp[return_copy_dynamic_mstore_frame, return_copy_frame_def,
       venom_state_component_equality, lookup_var_def] >>
  simp[mstore_def]
QED

Theorem return_copy_dynamic_index_header_frag:
  emit_op LT [Var counter; length] a = (lt,b) /\
  emit_op ISZERO [lt] b = (done,c) /\ ci_mono sa a /\
  not_fresh_at a counter /\
  (!x. src = Var x ==> not_fresh_at a x) /\
  (!x. dst = Var x ==> not_fresh_at a x) /\
  (!x. length = Var x ==> not_fresh_at a x) /\ N < dimword (:256) ==>
  frag_exec ctx a c
    (\s. return_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k s /\
         eval_operand length s = SOME (n2w N))
    (\t. return_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k t /\
         eval_operand length t = SOME (n2w N) /\
         eval_operand done t = SOME (if k < N then 0w else 1w)) (\r. F)
Proof
  rpt strip_tac >> irule frag_exec_pointwise >> qx_gen_tac `s` >> strip_tac >>
  gvs[] >>
  `k <= N /\ lookup_var counter s = SOME (n2w k)` by
    gvs[return_copy_index_inv_def] >>
  drule_all return_copy_dynamic_header_frag >>
  disch_then (qspecl_then [`ctx`, `w2n dw`, `N * type_memory_size dtv`] mp_tac) >>
  disch_then (mp_then Any irule frag_exec_conseq) >> simp[] >>
  rpt strip_tac
  >- (irule return_copy_index_inv_preserve >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  metis_tac[return_copy_frame_operand]
QED

Theorem return_copy_dynamic_header_frame:
  return_copy_frame sa dst len s t /\
  (hdr + 32 <= dst \/ dst + len <= hdr) ==>
  mem_word_at hdr t.vs_memory = mem_word_at hdr s.vs_memory
Proof
  rw[return_copy_frame_def, return_copy_memory_frame_def, mem_word_at_def] >>
  first_x_assum (qspecl_then [`hdr`, `32`] mp_tac) >> simp[] >>
  simp[mem_bytes_at_def]
QED

Theorem return_copy_dynamic_index_length:
  return_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k t /\
  (!x. length = Var x ==> not_fresh_at sa x) ==>
  eval_operand length t = eval_operand length s0
Proof
  rw[return_copy_index_inv_def] >> metis_tac[return_copy_frame_operand]
QED

Theorem return_copy_dynamic_loop_header_frag:
  emit_op LT [Var counter; length] a = (lt,b) /\
  emit_op ISZERO [lt] b = (done,c) /\ ci_mono sa a /\
  not_fresh_at a counter /\
  (!x. src = Var x ==> not_fresh_at a x) /\
  (!x. dst = Var x ==> not_fresh_at a x) /\
  (!x. length = Var x ==> not_fresh_at sa x) /\
  eval_operand length s0 = SOME (n2w N) /\ N < dimword (:256) ==>
  frag_exec ctx a c
    (return_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k)
    (\t. return_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k t /\
         eval_operand done t = SOME (if k < N then 0w else 1w)) (\r. F)
Proof
  rpt strip_tac >>
  `!x. length = Var x ==> not_fresh_at a x` by
    metis_tac[return_copy_operand_fresh_mono] >>
  `frag_exec ctx a c
    (\s. return_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k s /\
         eval_operand length s = SOME (n2w N))
    (\t. return_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k t /\
         eval_operand length t = SOME (n2w N) /\
         eval_operand done t = SOME (if k < N then 0w else 1w)) (\r. F)` by
    (irule return_copy_dynamic_index_header_frag >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  pop_assum (mp_then Any irule frag_exec_conseq) >> simp[] >>
  metis_tac[return_copy_dynamic_index_length]
QED

Theorem return_copy_dynamic_source_data:
  val_wf tv v /\
  val_in_memory tv v (w2n (sw:bytes32) + 32 + i * type_memory_size tv) mem /\
  (0 < val_footprint tv v ==>
    w2n sw + 32 + i * type_memory_size tv + val_footprint tv v < dimword (:256)) ==>
  val_in_memory tv v (w2n (sw + 32w) + i * type_memory_size tv) mem
Proof
  strip_tac >> Cases_on `val_footprint tv v = 0`
  >- (`type_memory_size tv = 0` by
        (Cases_on `v` >> gvs[loweringPostsTheory.val_footprint_def, AllCaseEqs()]) >>
      metis_tac[externalReturnCopyFrameTheory.return_zero_layout_memory_address]) >>
  `w2n sw + 32 < dimword (:256)` by gvs[] >>
  `w2n (sw + 32w) = w2n sw + 32` by
    (irule return_copy_offset_nonwrap >> simp[]) >>
  qpat_x_assum `w2n (sw + 32w) = _` SUBST1_TAC >>
  first_assum ACCEPT_TAC
QED

Theorem return_copy_dynamic_check_frag:
  emit_op GT [length; Lit (n2w capacity)] a = (too_long,b) /\
  emit_op ISZERO [too_long] b = (ok,c) /\
  emit_void ASSERT [ok] c = ((),d) /\
  eval_operand length s = SOME (n2w N) /\
  N <= capacity /\ capacity < dimword (:256) ==>
  frag_exec ctx a d (\u. u = s)
    (\t. t.vs_memory = s.vs_memory /\ return_copy_frame a off len s t) (\r. F)
Proof
  rpt strip_tac >>
  `frag_exec ctx a c (\u. u = s)
    (\t. eval_operand ok t = SOME 1w /\ t.vs_memory = s.vs_memory /\
         return_copy_frame a off len s t) (\r. F)` by
    (irule return_copy_dynamic_capacity_frag >>
     qexistsl_tac [`N`, `b`, `capacity`, `length`, `too_long`] >> simp[]) >>
  `ci_mono a c` by
    (`ci_mono a b /\ ci_mono b c` by metis_tac[return_copy_emit_op_mono] >>
     gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  drule frag_exec_then >> disch_then irule >> conj_tac
  >- (rpt strip_tac >> gvs[] >>
      `frag_exec ctx c d (\u. u = t)
        (\u. u.vs_memory = t.vs_memory /\ return_copy_frame c off len t u) (\r. F)` by
        (irule return_copy_dynamic_assert_frag >> qexists_tac `ok` >> simp[]) >>
      pop_assum (mp_then Any irule frag_exec_conseq) >> simp[] >> rpt strip_tac >>
      irule return_copy_frame_trans >> qexists_tac `t` >> simp[] >>
      irule return_copy_frame_mono >> qexists_tac `c` >> simp[]) >>
  `ci_mono c d` by metis_tac[ci_mono_emit_void, SND] >>
  gvs[ci_mono_def]
QED

Theorem return_copy_dynamic_load_check_frag:
  emit_op MLOAD [src] a = (length,b) /\
  emit_op GT [length; Lit (n2w capacity)] b = (too_long,c) /\
  emit_op ISZERO [too_long] c = (ok,d) /\
  emit_void ASSERT [ok] d = ((),e) /\
  eval_operand src s = SOME sw /\ mload (w2n sw) s = n2w N /\
  N <= capacity /\ capacity < dimword (:256) ==>
  frag_exec ctx a e (\u. u = s)
    (\t. eval_operand length t = SOME (n2w N) /\
         t.vs_memory = s.vs_memory /\ return_copy_frame a off len s t) (\r. F)
Proof
  rpt strip_tac >>
  `frag_exec ctx a b (\u. u = s)
    (\t. eval_operand length t = SOME (n2w N) /\
         t.vs_memory = s.vs_memory /\ return_copy_frame a off len s t) (\r. F)` by
    (irule return_copy_dynamic_load_frag >> qexistsl_tac [`src`, `sw`] >> simp[]) >>
  `ci_mono a b` by metis_tac[return_copy_emit_op_mono] >>
  `!x. length = Var x ==> not_fresh_at b x` by
    metis_tac[return_copy_emit_op_fresh] >>
  drule frag_exec_then >> disch_then irule >> conj_tac
  >- (rpt strip_tac >> gvs[] >>
      `frag_exec ctx b e (\u. u = t)
        (\u. u.vs_memory = t.vs_memory /\ return_copy_frame b off len t u) (\r. F)` by
        (irule return_copy_dynamic_check_frag >>
         qexistsl_tac [`N`, `c`, `d`, `capacity`, `length`, `ok`, `too_long`] >> simp[]) >>
      pop_assum (mp_then Any irule frag_exec_conseq) >> simp[] >> rpt strip_tac
      >- metis_tac[return_copy_frame_operand] >>
      irule return_copy_frame_trans >> qexists_tac `t` >> simp[] >>
      irule return_copy_frame_mono >> qexists_tac `b` >> simp[]) >>
  `ci_mono b c /\ ci_mono c d /\ ci_mono d e` by
    metis_tac[return_copy_emit_op_mono, ci_mono_emit_void, SND] >>
  gvs[ci_mono_def] >> metis_tac[cs_extends_trans]
QED

Theorem return_copy_dynamic_prefix_frag:
  emit_op MLOAD [src] a = (length,b) /\
  emit_op GT [length; Lit (n2w capacity)] b = (too_long,c) /\
  emit_op ISZERO [too_long] c = (ok,d) /\
  emit_void ASSERT [ok] d = ((),e) /\
  emit_void MSTORE [dst; length] e = ((),z) /\
  (!x. dst = Var x ==> not_fresh_at a x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  mload (w2n sw) s = n2w N /\ N <= capacity /\ capacity < dimword (:256) ==>
  frag_exec ctx a z (\u. u = s)
    (\t. eval_operand length t = SOME (n2w N) /\
         mem_word_at (w2n dw) t.vs_memory = n2w N /\
         return_copy_frame a (w2n dw) 32 s t) (\r. F)
Proof
  rpt strip_tac >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d /\ ci_mono d e /\ ci_mono e z` by
    metis_tac[return_copy_emit_op_mono, ci_mono_emit_void, SND] >>
  `ci_mono a e /\ ci_mono b e` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  `!x. length = Var x ==> not_fresh_at b x` by
    metis_tac[return_copy_emit_op_fresh] >>
  `!x. length = Var x ==> not_fresh_at e x` by
    metis_tac[return_copy_operand_fresh_mono] >>
  `frag_exec ctx a e (\u. u = s)
    (\t. eval_operand length t = SOME (n2w N) /\
         t.vs_memory = s.vs_memory /\ return_copy_frame a (w2n dw) 32 s t) (\r. F)` by
    (irule return_copy_dynamic_load_check_frag >>
     qexistsl_tac [`b`, `c`, `capacity`, `d`, `ok`, `src`, `sw`, `too_long`] >> simp[]) >>
  drule frag_exec_then >> disch_then irule >> conj_tac
  >- (rpt strip_tac >> gvs[] >>
      `eval_operand dst t = SOME dw` by metis_tac[return_copy_frame_operand] >>
      `frag_exec ctx e z (\u. u = t)
        (\u. mem_word_at (w2n dw) u.vs_memory = n2w N /\
             return_copy_frame e (w2n dw) 32 t u) (\r. F)` by
        (irule return_copy_dynamic_store_frag >> qexistsl_tac [`dst`, `length`] >> simp[]) >>
      pop_assum (mp_then Any irule frag_exec_conseq) >> simp[] >> rpt strip_tac
      >- metis_tac[return_copy_frame_operand] >>
      irule return_copy_frame_trans >> qexists_tac `t` >> simp[] >>
      irule return_copy_frame_mono >> qexists_tac `e` >> simp[]) >>
  gvs[ci_mono_def]
QED

Theorem return_copy_dynamic_data_frag:
  emit_op ADD [src; Lit 32w] a = (sp,b) /\
  emit_op ADD [dst; Lit 32w] b = (dp,c) /\
  (!x. dst = Var x ==> not_fresh_at a x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw ==>
  frag_exec ctx a c (\u. u = s)
    (\t. eval_operand sp t = SOME (sw + 32w) /\
         eval_operand dp t = SOME (dw + 32w) /\
         t.vs_memory = s.vs_memory /\ return_copy_frame a off len s t) (\r. F)
Proof
  rpt strip_tac >> irule return_copy_index_adds_frag >>
  qexistsl_tac [`b`, `Lit 32w`, `dst`, `Lit 32w`, `src`] >>
  simp[eval_operand_def]
QED

Theorem return_copy_dynamic_setup_frag:
  emit_op MLOAD [src] a = (length,b) /\
  emit_op GT [length; Lit (n2w capacity)] b = (too_long,c) /\
  emit_op ISZERO [too_long] c = (ok,d) /\
  emit_void ASSERT [ok] d = ((),e) /\
  emit_void MSTORE [dst; length] e = ((),z) /\
  emit_op ADD [src; Lit 32w] z = (sp,p) /\
  emit_op ADD [dst; Lit 32w] p = (dp,q) /\
  (!x. src = Var x ==> not_fresh_at a x) /\
  (!x. dst = Var x ==> not_fresh_at a x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  mload (w2n sw) s = n2w N /\ N <= capacity /\ capacity < dimword (:256) ==>
  frag_exec ctx a q (\u. u = s)
    (\t. eval_operand length t = SOME (n2w N) /\
         eval_operand sp t = SOME (sw + 32w) /\
         eval_operand dp t = SOME (dw + 32w) /\
         mem_word_at (w2n dw) t.vs_memory = n2w N /\
         return_copy_frame a (w2n dw) 32 s t) (\r. F)
Proof
  rpt strip_tac >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d /\ ci_mono d e /\
   ci_mono e z /\ ci_mono z p /\ ci_mono p q` by
    metis_tac[return_copy_emit_op_mono, ci_mono_emit_void, SND] >>
  `ci_mono a z /\ ci_mono b z` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  `!x. length = Var x ==> not_fresh_at b x` by
    metis_tac[return_copy_emit_op_fresh] >>
  `!x. length = Var x ==> not_fresh_at z x` by
    metis_tac[return_copy_operand_fresh_mono] >>
  `!x. dst = Var x ==> not_fresh_at z x` by
    metis_tac[return_copy_operand_fresh_mono] >>
  `frag_exec ctx a z (\u. u = s)
    (\t. eval_operand length t = SOME (n2w N) /\
         mem_word_at (w2n dw) t.vs_memory = n2w N /\
         return_copy_frame a (w2n dw) 32 s t) (\r. F)` by
    (irule return_copy_dynamic_prefix_frag >>
     qexistsl_tac [`b`, `c`, `capacity`, `d`, `dst`, `e`, `ok`, `src`, `sw`, `too_long`] >> simp[]) >>
  drule frag_exec_then >> disch_then irule >> conj_tac
  >- (rpt strip_tac >> gvs[] >>
      `eval_operand src t = SOME sw /\ eval_operand dst t = SOME dw` by
        metis_tac[return_copy_frame_operand] >>
      `frag_exec ctx z q (\u. u = t)
        (\u. eval_operand sp u = SOME (sw + 32w) /\
             eval_operand dp u = SOME (dw + 32w) /\
             u.vs_memory = t.vs_memory /\ return_copy_frame z (w2n dw) 32 t u) (\r. F)` by
        (irule return_copy_dynamic_data_frag >>
         qexistsl_tac [`p`, `dst`, `src`] >> simp[]) >>
      pop_assum (mp_then Any irule frag_exec_conseq) >> simp[] >> rpt strip_tac
      >- metis_tac[return_copy_frame_operand] >>
      irule return_copy_frame_trans >> qexists_tac `t` >> simp[] >>
      irule return_copy_frame_mono >> qexists_tac `z` >> simp[]) >>
  gvs[ci_mono_def] >> metis_tac[cs_extends_trans]
QED

Theorem return_copy_dynamic_slow_layout:
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
  new_block exit st3 = (u3,stx) ==>
  ci_mono sa init /\ ci_mono sa st0 /\ ci_mono sa sth /\ ci_mono sa stb /\
  ci_mono init st0 /\ ci_mono st0 stx /\
  cs_extends sth stj /\ cs_extends stb ste /\
  ~not_fresh_at sa counter /\ not_fresh_at sth counter /\ not_fresh_at stb counter /\
  sa.cs_current_bb = init.cs_current_bb /\
  sa.cs_current_insts = init.cs_current_insts /\ sa.cs_blocks = init.cs_blocks
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `ci_mono sa l1 /\ ci_mono l1 l2 /\ ci_mono l2 l3 /\ ci_mono l3 init` by
    metis_tac[ci_mono_fresh_label, ci_mono_fresh_var, SND] >>
  `ci_mono init st0 /\ ci_mono st0 st1 /\ ci_mono stj st2 /\
   ci_mono b6 ste /\ ci_mono ste st3` by
    metis_tac[ci_mono_emit_inst, SND] >>
  `ci_mono st1 sth /\ ci_mono st2 stb /\ ci_mono st3 stx` by
    metis_tac[ci_mono_new_block, SND] >>
  `ci_mono sth h1 /\ ci_mono h1 stj /\ ci_mono stb b1 /\
   ci_mono b1 b2 /\ ci_mono b2 b3 /\ ci_mono b3 b4 /\ ci_mono b5 b6` by
    metis_tac[return_copy_emit_op_mono] >>
  `ci_mono b4 b5` by metis_tac[cj 1 ci_mono_typed_memory_family, SND] >>
  rpt (qpat_x_assum `emit_inst _ _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `emit_op _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `new_block _ _ = _` kall_tac) >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` kall_tac >>
  `!a b c. ci_mono a b /\ ci_mono b c ==> ci_mono a c` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  `ci_mono sa l3` by metis_tac[] >>
  `ci_mono sa init /\ ci_mono st0 sth /\ ci_mono sth st2` by metis_tac[] >>
  `ci_mono sa st0 /\ ci_mono sth stb /\ ci_mono stb b4` by metis_tac[] >>
  `ci_mono sa sth /\ ci_mono stb b6 /\ ci_mono ste stx` by metis_tac[] >>
  `ci_mono sa stb /\ ci_mono stb ste /\ ci_mono st0 stb` by metis_tac[] >>
  `ci_mono st0 stx /\ ci_mono sth stj` by metis_tac[] >>
  qpat_x_assum `!a b c. ci_mono a b /\ ci_mono b c ==> ci_mono a c` kall_tac >>
  simp[] >>
  `cs_extends sth stj /\ cs_extends stb ste` by metis_tac[ci_mono_def] >>
  simp[] >>
  `~not_fresh_at sa counter /\ not_fresh_at init counter /\
   sa.cs_current_bb = init.cs_current_bb /\
   sa.cs_current_insts = init.cs_current_insts /\ sa.cs_blocks = init.cs_blocks` by
    (gvs[fresh_label_def, fresh_var_def, not_fresh_at_def,
         ASCIInumbersTheory.toString_inj] >> decide_tac) >>
  simp[] >> gvs[ci_mono_def, not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]
QED

Theorem return_copy_dynamic_index_init_frag:
  emit_inst ASSIGN [Lit 0w] [counter] init = ((),st0) /\
  ~not_fresh_at sa counter /\ sa.cs_current_bb = init.cs_current_bb /\
  sa.cs_current_insts = init.cs_current_insts /\ sa.cs_blocks = init.cs_blocks /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  (!i. i < N ==> val_in_memory stv (f i)
     (w2n sw + i * type_memory_size stv) s.vs_memory) ==>
  frag_exec ctx sa st0 (\u. u = s)
    (return_copy_index_inv sa counter src dst sw dw f stv dtv N s 0) (\r. F)
Proof
  rpt strip_tac >>
  `eval_operand (Lit 0w) s = SOME 0w` by simp[eval_operand_def] >>
  `frag_exec ctx init st0 (\u. u = s)
     (return_copy_index_inv sa counter src dst sw dw f stv dtv N s 0) (\r. F)` by
    (drule_all return_copy_assign_frag >> disch_then (qspec_then `ctx` mp_tac) >>
     disch_then (mp_then Any irule frag_exec_conseq) >> simp[] >>
     rpt strip_tac >> rename1 `lookup_var counter t = SOME 0w` >>
     `return_copy_frame sa (w2n dw) (N * type_memory_size dtv) s t` by
       (simp[return_copy_frame_def] >> metis_tac[]) >>
     `eval_operand src t = SOME sw /\ eval_operand dst t = SOME dw` by
       metis_tac[return_copy_frame_operand] >>
     simp[return_copy_index_inv_def, return_copy_index_prefix_def]) >>
  qpat_x_assum `frag_exec _ _ _ _ _ _` mp_tac >>
  simp[frag_exec_def, fn_has_code_def, emitted_blocks_def]
QED

Theorem return_copy_dynamic_loop_frag:
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
  (!i. i < N ==> val_wf stv (f i) /\ val_wf dtv (f i)) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  (!i. i < N ==> val_in_memory stv (f i)
     (w2n sw + i * type_memory_size stv) s.vs_memory) /\
  w2n dw + N * type_memory_size dtv < dimword (:256) /\
  (!i. i < N /\ 0 < val_footprint stv (f i) ==>
    w2n sw + i * type_memory_size stv + val_footprint stv (f i) < dimword (:256) /\
    (w2n sw + i * type_memory_size stv + val_footprint stv (f i) <= w2n dw \/
     w2n dw + N * type_memory_size dtv <= w2n sw + i * type_memory_size stv)) /\
  (!i dp sp a b s dw sw.
    i < N /\ compile_store_memory_typed cenv dp dty sp sty a = ((),b) /\
    (!x. dp = Var x ==> not_fresh_at a x) /\
    (!x. sp = Var x ==> not_fresh_at a x) /\
    eval_operand dp s = SOME dw /\ eval_operand sp s = SOME sw /\
    val_wf stv (f i) /\ val_in_memory stv (f i) (w2n sw) s.vs_memory /\
    w2n dw + type_memory_size dtv < dimword (:256) /\
    (0 < val_footprint stv (f i) ==>
      w2n sw + val_footprint stv (f i) < dimword (:256) /\
      (w2n sw + val_footprint stv (f i) <= w2n dw \/
       w2n dw + type_memory_size dtv <= w2n sw)) ==>
    frag_exec ctx a b (\u. u = s)
      (\t. val_in_memory dtv (f i) (w2n dw) t.vs_memory /\
        return_copy_frame a (w2n dw) (type_memory_size dtv) s t) (\r. F)) ==>
  frag_exec ctx sa stx (\u. u = s)
    (\t. (!i. i < N ==> val_in_memory dtv (f i)
       (w2n dw + i * type_memory_size dtv) t.vs_memory) /\
         return_copy_frame sa (w2n dw) (N * type_memory_size dtv) s t) (\r. F)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all return_copy_dynamic_slow_layout >> strip_tac >>
  `(!x. src = Var x ==> not_fresh_at sth x) /\
   (!x. dst = Var x ==> not_fresh_at sth x)` by
    metis_tac[return_copy_operand_fresh_mono] >>
  qmatch_goalsub_abbrev_tac `frag_exec ctx sa stx P Q R` >>
  qabbrev_tac `Inv = return_copy_index_inv sa counter src dst sw dw f stv dtv N s` >>
  qabbrev_tac `J = \k t. Inv k t /\ eval_operand done t = SOME (if k < N then 0w else 1w)` >>
  `frag_exec ctx sa st0 P (Inv 0) R` by
    (simp[Abbr `P`, Abbr `Inv`, Abbr `R`] >>
     irule return_copy_dynamic_index_init_frag >> simp[] >>
     goal_assum (drule_at (Pat `emit_inst ASSIGN _ _ init = _`)) >> simp[]) >>
  `frag_exec ctx st0 stx (Inv 0) (J N) R` by
    (irule frag_exec_loop >> conj_tac
     >- simp[Abbr `Inv`, return_copy_index_inv_jump] >>
     conj_tac
     >- simp[Abbr `J`, Abbr `Inv`, return_copy_index_inv_jump] >>
     qexistsl_tac [`blabel`, `done`, `exit`, `hdr`] >>
     goal_assum (drule_at (Pat `new_block exit _ = _`)) >>
     goal_assum (drule_at (Pat `emit_inst JMP _ _ ste = _`)) >>
     goal_assum (drule_at (Pat `emit_inst JMP _ _ st0 = _`)) >>
     goal_assum (drule_at (Pat `new_block hdr _ = _`)) >>
     goal_assum (drule_at (Pat `emit_inst JNZ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `new_block blabel _ = _`)) >> simp[] >>
     rpt (qpat_x_assum `fresh_label _ _ = _` kall_tac) >>
     qpat_x_assum `fresh_var _ = _` kall_tac >>
     rpt (qpat_x_assum `new_block _ _ = _` kall_tac) >>
     rpt (qpat_x_assum `emit_inst JMP _ _ _ = _` kall_tac) >>
     qpat_x_assum `emit_inst JNZ _ _ _ = _` kall_tac >>
     conj_tac
     >- (simp[Abbr `J`] >> rpt strip_tac >>
         Cases_on `k < N` >> simp[]) >>
     conj_tac
     >- suspend "body" >>
     rpt strip_tac >> simp[Abbr `Inv`, Abbr `J`, Abbr `R`] >>
     irule return_copy_dynamic_loop_header_frag >> simp[] >>
     goal_assum (drule_at (Pat `emit_op ISZERO _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op LT _ _ = _`)) >> simp[]) >>
  `cs_extends sa st0 /\ cs_extends st0 stx` by metis_tac[ci_mono_def] >>
  drule_all frag_exec_seq >>
  disch_then (mp_then Any irule frag_exec_conseq) >> simp[] >>
  simp[Abbr `J`, Abbr `Inv`, Abbr `Q`, return_copy_index_inv_def,
       return_copy_index_prefix_def]
QED

Resume return_copy_dynamic_loop_frag[body]:
  rpt strip_tac >> simp[Abbr `Inv`, Abbr `J`, Abbr `R`] >>
  irule frag_exec_pointwise >> rpt strip_tac >> gvs[] >>
  rename1 `return_copy_index_inv sa counter src dst sw dw f stv dtv N s k t` >>
  `ci_mono b3 b4 /\ ci_mono b4 b5` by
    metis_tac[return_copy_emit_op_mono, cj 1 ci_mono_typed_memory_family, SND] >>
  `!x. dp = Var x ==> not_fresh_at b4 x` by
    metis_tac[return_copy_emit_op_fresh] >>
  `!x. sp = Var x ==> not_fresh_at b4 x` by
    metis_tac[return_copy_emit_op_fresh, return_copy_operand_fresh_mono] >>
  `!u. eval_operand dp u = SOME (dw + n2w (k * type_memory_size dtv)) /\
       eval_operand sp u = SOME (sw + n2w (k * type_memory_size stv)) /\
       val_in_memory stv (f k) (w2n (sw + n2w (k * type_memory_size stv))) u.vs_memory ==>
       frag_exec ctx b4 b5 (\q. q = u)
         (\t. val_in_memory dtv (f k) (w2n dw + k * type_memory_size dtv) t.vs_memory /\
           return_copy_frame b4 (w2n dw + k * type_memory_size dtv)
             (type_memory_size dtv) u t) (\r. F)` by
    (rpt strip_tac >> irule return_copy_index_child_contract >> simp[] >>
     qexistsl_tac [`N`, `cenv`, `dp`, `dty`, `sp`, `stv`, `sty`, `sw`] >>
     simp[]
     >- (rpt strip_tac >> first_x_assum irule >> simp[] >>
         qexistsl_tac [`dp'`, `sp'`, `sw'`] >> simp[]) >>
     gvs[ADD_ASSOC]) >>
  rewrite_tac[ADD1] >>
  irule return_copy_index_body_frag >> simp[] >>
  qexistsl_tac [`inc`, `b6`, `b5`] >> simp[ADD_ASSOC] >>
  goal_assum (drule_at (Pat `emit_op MUL _ stb = _`)) >>
  goal_assum (drule_at (Pat `emit_op MUL _ b1 = _`)) >>
  goal_assum (drule_at (Pat `emit_op ADD _ b2 = _`)) >>
  goal_assum (drule_at (Pat `emit_op ADD _ b3 = _`)) >> simp[]
QED
Finalise return_copy_dynamic_loop_frag

Theorem return_copy_dynamic_source_after_setup:
  return_copy_frame sa (w2n (dw:bytes32)) 32 s t /\ val_wf tv v /\
  val_in_memory tv v (w2n (sw:bytes32) + 32 + i * type_memory_size tv) s.vs_memory /\
  (0 < val_footprint tv v ==>
    w2n (sw:bytes32) + 32 + i * type_memory_size tv + val_footprint tv v < dimword (:256) /\
    (w2n sw + 32 + i * type_memory_size tv + val_footprint tv v <= w2n dw \/
     w2n dw + 32 + capacity * ds <= w2n sw + 32 + i * type_memory_size tv)) ==>
  val_in_memory tv v (w2n (sw + 32w) + i * type_memory_size tv) t.vs_memory
Proof
  strip_tac >> irule return_copy_dynamic_source_data >> simp[] >>
  irule return_copy_preserves_conditional_source >> simp[] >>
  qexistsl_tac [`w2n dw`, `32`, `s`, `sa`] >>
  `w2n sw + (i * type_memory_size tv + 32) = w2n sw + 32 + i * type_memory_size tv` by decide_tac >>
  pop_assum SUBST1_TAC >> simp[] >>
  strip_tac >> first_x_assum drule >> decide_tac
QED

Theorem return_copy_dynamic_data_window:
  N <= capacity /\ w2n (dw:bytes32) + 32 + capacity * ds < dimword (:256) ==>
  w2n (dw + 32w) = w2n dw + 32 /\
  w2n (dw + 32w) + N * ds < dimword (:256)
Proof
  strip_tac >>
  `w2n (dw + 32w) = w2n dw + 32` by
    (irule return_copy_offset_nonwrap >> simp[] >> decide_tac) >>
  simp[] >>
  `N * ds <= capacity * ds` by metis_tac[LESS_MONO_MULT] >> decide_tac
QED

Theorem return_copy_dynamic_source_window:
  N <= capacity /\ w2n (dw:bytes32) + 32 + capacity * ds < dimword (:256) /\
  (0 < val_footprint tv v ==>
    w2n (sw:bytes32) + 32 + i * type_memory_size tv + val_footprint tv v < dimword (:256) /\
    (w2n sw + 32 + i * type_memory_size tv + val_footprint tv v <= w2n dw \/
     w2n dw + 32 + capacity * ds <= w2n sw + 32 + i * type_memory_size tv)) ==>
  (0 < val_footprint tv v ==>
    w2n (sw + 32w) + i * type_memory_size tv + val_footprint tv v < dimword (:256) /\
    (w2n (sw + 32w) + i * type_memory_size tv + val_footprint tv v <= w2n (dw + 32w) \/
     w2n (dw + 32w) + N * ds <= w2n (sw + 32w) + i * type_memory_size tv))
Proof
  strip_tac >> strip_tac >>
  `w2n (sw + 32w) = w2n sw + 32` by
    (irule return_copy_offset_nonwrap >> simp[] >> gvs[] >> decide_tac) >>
  drule_all return_copy_dynamic_data_window >> strip_tac >> simp[] >>
  `N * ds <= capacity * ds` by metis_tac[LESS_MONO_MULT] >> decide_tac
QED

Theorem return_copy_dynarray_slow_frag:
  compile_copy_dynarray_typed cenv dst dty capacity src sty sa = ((),sb) /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  ~(type_memory_size dtv = type_memory_size stv /\ dty = sty) /\
  N <= capacity /\ capacity < dimword (:256) /\
  (!i. i < N ==> val_wf stv (f i) /\ val_wf dtv (f i)) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  mload (w2n sw) s = n2w N /\
  (!i. i < N ==> val_in_memory stv (f i)
     (w2n sw + 32 + i * type_memory_size stv) s.vs_memory) /\
  w2n dw + 32 + capacity * type_memory_size dtv < dimword (:256) /\
  (!i. i < N /\ 0 < val_footprint stv (f i) ==>
    w2n sw + 32 + i * type_memory_size stv + val_footprint stv (f i) < dimword (:256) /\
    (w2n sw + 32 + i * type_memory_size stv + val_footprint stv (f i) <= w2n dw \/
     w2n dw + 32 + capacity * type_memory_size dtv <= w2n sw + 32 + i * type_memory_size stv)) /\
  (!i dp sp a b s dw sw.
    i < N /\ compile_store_memory_typed cenv dp dty sp sty a = ((),b) /\
    (!x. dp = Var x ==> not_fresh_at a x) /\
    (!x. sp = Var x ==> not_fresh_at a x) /\
    eval_operand dp s = SOME dw /\ eval_operand sp s = SOME sw /\
    val_wf stv (f i) /\ val_in_memory stv (f i) (w2n sw) s.vs_memory /\
    w2n dw + type_memory_size dtv < dimword (:256) /\
    (0 < val_footprint stv (f i) ==>
      w2n sw + val_footprint stv (f i) < dimword (:256) /\
      (w2n sw + val_footprint stv (f i) <= w2n dw \/
       w2n dw + type_memory_size dtv <= w2n sw)) ==>
    frag_exec ctx a b (\u. u = s)
      (\t. val_in_memory dtv (f i) (w2n dw) t.vs_memory /\
        return_copy_frame a (w2n dw) (type_memory_size dtv) s t) (\r. F)) ==>
  frag_exec ctx sa sb (\u. u = s)
    (\t. mem_word_at (w2n dw) t.vs_memory = n2w N /\
         (!i. i < N ==> val_in_memory dtv (f i)
           (w2n dw + 32 + i * type_memory_size dtv) t.vs_memory) /\
         return_copy_frame sa (w2n dw) (32 + capacity * type_memory_size dtv) s t) (\r. F)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `compile_copy_dynarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gnvs[]) >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> gnvs[] >>
  rename1 `emit_op MLOAD [src] sa = (length,a1)` >>
  rename1 `emit_op GT [length; Lit (n2w capacity)] a1 = (too_long,a2)` >>
  rename1 `emit_op ISZERO [too_long] a2 = (ok,a3)` >>
  rename1 `emit_void ASSERT [ok] a3 = ((),a4)` >>
  rename1 `emit_void MSTORE [dst; length] a4 = ((),a5)` >>
  rename1 `emit_op ADD [src; Lit 32w] a5 = (src_data,a6)` >>
  rename1 `emit_op ADD [dst; Lit 32w] a6 = (dst_data,start)` >>
  rename1 `new_block exit_lbl st3 = (u3,stx)` >>
  `ci_mono sa a1 /\ ci_mono a1 a2 /\ ci_mono a2 a3 /\ ci_mono a3 a4 /\
   ci_mono a4 a5 /\ ci_mono a5 a6 /\ ci_mono a6 start` by
    metis_tac[return_copy_emit_op_mono, ci_mono_emit_void, SND] >>
  `ci_mono sa start /\ ci_mono a1 start` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  `(!x. length = Var x ==> not_fresh_at start x) /\
   (!x. src_data = Var x ==> not_fresh_at start x) /\
   (!x. dst_data = Var x ==> not_fresh_at start x)` by
    metis_tac[return_copy_emit_op_fresh, return_copy_operand_fresh_mono] >>
  `frag_exec ctx sa start (\u. u = s)
    (\t. eval_operand length t = SOME (n2w N) /\
         eval_operand src_data t = SOME (sw + 32w) /\
         eval_operand dst_data t = SOME (dw + 32w) /\
         mem_word_at (w2n dw) t.vs_memory = n2w N /\
         return_copy_frame sa (w2n dw) 32 s t) (\r. F)` by
    (irule return_copy_dynamic_setup_frag >> simp[] >>
     goal_assum (drule_at (Pat `emit_op MLOAD _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op GT _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op ISZERO [too_long] _ = _`)) >>
     goal_assum (drule_at (Pat `emit_void ASSERT _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_void MSTORE _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op ADD [src; Lit 32w] _ = _`)) >> simp[]) >>
  drule frag_exec_then >> disch_then irule >> conj_tac
  >- suspend "continuation" >>
  drule_all return_copy_dynamic_slow_layout >> strip_tac >>
  gvs[ci_mono_def] >> metis_tac[cs_extends_trans]
QED

Resume return_copy_dynarray_slow_frag[continuation]:
  rpt strip_tac >> gvs[] >>
  `N < dimword (:256)` by decide_tac >>
  `w2n (dw + 32w) = w2n dw + 32 /\
   w2n (dw + 32w) + N * type_memory_size dtv < dimword (:256)` by
    (irule return_copy_dynamic_data_window >> qexists_tac `capacity` >> simp[]) >>
  `!i. i < N ==> val_in_memory stv (f i)
    (w2n (sw + 32w) + i * type_memory_size stv) t.vs_memory` by
    (rpt strip_tac >> irule return_copy_dynamic_source_after_setup >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`capacity`, `type_memory_size dtv`, `dw`, `s`, `sa`] >>
     simp[] >> metis_tac[]) >>
  `!i. i < N /\ 0 < val_footprint stv (f i) ==>
    w2n (sw + 32w) + i * type_memory_size stv + val_footprint stv (f i) < dimword (:256) /\
    (w2n (sw + 32w) + i * type_memory_size stv + val_footprint stv (f i) <= w2n (dw + 32w) \/
     w2n (dw + 32w) + N * type_memory_size dtv <= w2n (sw + 32w) + i * type_memory_size stv)` by
    (gen_tac >> disch_tac >> irule return_copy_dynamic_source_window >> simp[] >>
     qexists_tac `capacity` >> simp[] >> metis_tac[]) >>
  `frag_exec ctx start stx (\u. u = t)
    (\u. (!i. i < N ==> val_in_memory dtv (f i)
      (w2n (dw + 32w) + i * type_memory_size dtv) u.vs_memory) /\
      return_copy_frame start (w2n (dw + 32w)) (N * type_memory_size dtv) t u) (\r. F)` by
    (irule return_copy_dynamic_loop_frag >> simp[] >>
     goal_assum (drule_at (Pat `emit_op LT _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op ISZERO [lt_op] _ = _`)) >>
     goal_assum (drule_at (Pat `emit_inst JNZ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `new_block body_lbl _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op MUL [Var counter; Lit (n2w (type_memory_size stv))] _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op MUL [Var counter; Lit (n2w (type_memory_size dtv))] _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op ADD [src_data; src_off] _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op ADD [dst_data; dst_off] _ = _`)) >>
     goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_inst ASSIGN [new_ctr] _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_inst JMP _ _ _ = ((),st3)`)) >>
     simp[] >> qexistsl_tac [`src_data`, `sw + 32w`] >> simp[] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     gen_tac >> strip_tac >>
     qpat_x_assum `!i. i < N /\ 0 < _ ==> _`
       (qspec_then `i` mp_tac) >> simp[]) >>
  pop_assum (mp_then Any irule frag_exec_conseq) >> simp[] >>
  rpt strip_tac >> rename1 `return_copy_frame start _ _ t u` >>
  `mem_word_at (w2n dw) u.vs_memory = mem_word_at (w2n dw) t.vs_memory` by
    (irule return_copy_dynamic_header_frame >>
     goal_assum (drule_at Any) >> simp[]) >>
  simp[] >>
  `N * type_memory_size dtv <= capacity * type_memory_size dtv` by
    simp[LE_MULT_RCANCEL] >>
  irule return_copy_frame_trans >> qexists_tac `t` >> conj_tac
  >- (irule return_copy_frame_subinterval >>
      qexistsl_tac [`w2n dw`, `32`] >> simp[]) >>
  irule return_copy_frame_subinterval >>
  qexistsl_tac [`w2n dw + 32`, `N * type_memory_size dtv`] >>
  simp[] >> irule return_copy_frame_mono >>
  qexists_tac `start` >> simp[]
QED
Finalise return_copy_dynarray_slow_frag
