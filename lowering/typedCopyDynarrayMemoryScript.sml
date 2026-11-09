(* Joint memory execution for dynamic-array typed-copy prefixes. *)
Theory typedCopyDynarrayMemory
Ancestors
  typedCopyIndexMemory typedCopyControlMemory typedMemoryCopy fragExecMem
  instMemFrontier memSafeRun context compileEnv emitHelper emitHelperProps
  exprLoweringProps venomExecSemantics venomInst venomState venomMemDefs
  valueEncoding valueEncodingProps words list finite_map arithmetic

Theorem typed_copy_dyn_check_frag_mem[local]:
  emit_op GT [length; Lit (n2w C)] a = (too_long,b) /\
  emit_op ISZERO [too_long] b = (ok,c) /\
  emit_void ASSERT [ok] c = ((),d) /\
  eval_operand length s = SOME (n2w N) /\ N <= C /\ C < dimword (:256) ==>
  frag_exec_mem ctx a d (\u. u = s)
    (\t. t.vs_memory = s.vs_memory /\ typed_copy_state_frame a off len s t) (\r. F)
Proof
  strip_tac >>
  `N < dimword (:256)` by decide_tac >>
  `ci_mono a b /\ ci_mono b c` by metis_tac[typed_copy_emit_op_mono] >>
  `ci_mono c d` by metis_tac[ci_mono_emit_void, pairTheory.SND] >>
  `frag_exec_mem ctx a b (\u. u = s)
     (\t. eval_operand too_long t = SOME 0w /\ t.vs_memory = s.vs_memory /\
          typed_copy_state_frame a off len s t) (\r. F)` by
    (irule typed_copy_emit_op_frag_mem >> simp[venomInstTheory.is_terminator_def] >>
     goal_assum (drule_at Any) >>
     simp[below_frontier_no_ranges, venomInstTheory.is_terminator_def,
          step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
          eval_operand_def, w2n_n2w, LESS_MOD, bool_to_word_def, NOT_LESS]) >>
  drule frag_exec_mem_then >> disch_then irule >> conj_tac
  >- (simp[] >> rpt strip_tac >>
      `frag_exec_mem ctx b c (\u. u = t)
         (\u. eval_operand ok u = SOME 1w /\ u.vs_memory = t.vs_memory /\
              typed_copy_state_frame b off len t u) (\r. F)` by
        (irule typed_copy_emit_op_frag_mem >> simp[venomInstTheory.is_terminator_def] >>
         goal_assum (drule_at Any) >>
         simp[below_frontier_no_ranges, venomInstTheory.is_terminator_def,
              step_inst_base_opcode_eqs, mk_inst_def, exec_pure1_def, bool_to_word_def]) >>
      drule frag_exec_mem_then >> disch_then irule >> conj_tac
      >- (simp[] >> rpt strip_tac >> drule_all typed_copy_assert_frag_mem >>
          disch_then (qspecl_then [`off`, `len`, `ctx`] mp_tac) >>
          disch_then (mp_then Any irule frag_exec_mem_conseq) >> simp[] >>
          rpt strip_tac >>
          metis_tac[typed_copy_state_frame_trans, typed_copy_state_frame_mono]) >>
      gvs[ci_mono_def]) >>
  gvs[ci_mono_def] >> metis_tac[cs_extends_trans]
QED

Theorem typed_copy_dyn_read_check_frag_mem[local]:
  emit_op MLOAD [src] a = (length,b) /\
  emit_op GT [length; Lit (n2w C)] b = (too_long,c) /\
  emit_op ISZERO [too_long] c = (ok,d) /\
  emit_void ASSERT [ok] d = ((),e) /\
  N <= C /\ C < dimword (:256) /\
  (!out. inst_mem_below_frontier (mk_inst a.cs_next_id MLOAD [src] [out]) s) /\
  (!out. step_inst_base (mk_inst a.cs_next_id MLOAD [src] [out]) s =
     OK (update_var out (n2w N) s)) ==>
  frag_exec_mem ctx a e (\u. u = s)
    (\t. eval_operand length t = SOME (n2w N) /\ t.vs_memory = s.vs_memory /\
      typed_copy_state_frame a off len s t) (\r. F)
Proof
  strip_tac >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d` by
    metis_tac[typed_copy_emit_op_mono] >>
  `ci_mono d e` by metis_tac[ci_mono_emit_void, pairTheory.SND] >>
  `!x. length = Var x ==> not_fresh_at b x` by
    metis_tac[typed_copy_emit_op_fresh] >>
  `frag_exec_mem ctx a b (\u. u = s)
    (\t. eval_operand length t = SOME (n2w N) /\ t.vs_memory = s.vs_memory /\
      typed_copy_state_frame a off len s t) (\r. F)` by
    (irule typed_copy_emit_op_frag_mem >> simp[venomInstTheory.is_terminator_def] >>
     goal_assum (drule_at Any) >> simp[venomInstTheory.is_terminator_def]) >>
  drule frag_exec_mem_then >> disch_then irule >> conj_tac
  >- (simp[] >> rpt strip_tac >>
      drule_all typed_copy_dyn_check_frag_mem >>
      disch_then (qspecl_then [`off`, `len`, `ctx`] mp_tac) >>
      disch_then (mp_then Any irule frag_exec_mem_conseq) >> simp[] >> rpt strip_tac
      >- metis_tac[typed_copy_state_frame_operand] >>
      irule typed_copy_state_frame_trans >> qexists_tac `t` >> simp[] >>
      irule typed_copy_state_frame_mono >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[ci_mono_def] >> metis_tac[cs_extends_trans]
QED

Theorem typed_copy_dyn_data_frag_mem[local]:
  emit_void MSTORE [dst; length] a = ((),b) /\
  emit_op ADD [src; Lit 32w] b = (sd,c) /\
  emit_op ADD [dst; Lit 32w] c = (dd,d) /\
  (!x. src = Var x ==> not_fresh_at a x) /\
  (!x. dst = Var x ==> not_fresh_at a x) /\
  (!x. length = Var x ==> not_fresh_at a x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  eval_operand length s = SOME w /\ w2n dw + 32 <= s.vs_alloca_next ==>
  frag_exec_mem ctx a d (\u. u = s)
    (\t. eval_operand length t = SOME w /\
      eval_operand sd t = SOME (sw + 32w) /\ eval_operand dd t = SOME (dw + 32w) /\
      mem_word_at (w2n dw) t.vs_memory = w /\
      typed_copy_state_frame a (w2n dw) 32 s t) (\r. F)
Proof
  strip_tac >>
  `ci_mono a b` by metis_tac[ci_mono_emit_void, pairTheory.SND] >>
  `ci_mono b c /\ ci_mono c d` by metis_tac[typed_copy_emit_op_mono] >>
  drule_all typed_copy_mstore_frag_mem >> disch_then (qspec_then `ctx` mp_tac) >>
  disch_then (mp_then Any mp_tac frag_exec_mem_then) >>
  disch_then irule >> conj_tac
  >- (simp[] >> rpt strip_tac >>
      `eval_operand src t = SOME sw /\ eval_operand dst t = SOME dw` by
        metis_tac[typed_copy_state_frame_operand] >>
      `frag_exec_mem ctx b d (\u. u = t)
         (\u. eval_operand sd u = SOME (sw + 32w) /\
           eval_operand dd u = SOME (dw + 32w) /\ u.vs_memory = t.vs_memory /\
           typed_copy_state_frame b (w2n dw) 32 t u) (\r. F)` by
        (irule typed_copy_index_adds_frag_mem >> simp[eval_operand_def] >>
         goal_assum (drule_at (Pat `emit_op ADD _ b = _`)) >>
         goal_assum (drule_at Any) >> simp[] >>
         qexistsl_tac [`Lit 32w`, `src`] >> simp[eval_operand_def] >>
         metis_tac[typed_copy_operand_fresh_mono]) >>
      pop_assum (mp_then Any irule frag_exec_mem_conseq) >> simp[] >> rpt strip_tac
      >- (drule_all typed_copy_state_frame_mono >> strip_tac >>
          metis_tac[typed_copy_state_frame_operand]) >>
      irule typed_copy_state_frame_trans >> qexists_tac `t` >> simp[] >>
      irule typed_copy_state_frame_mono >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[ci_mono_def] >> metis_tac[cs_extends_trans]
QED

Theorem typed_copy_dyn_prefix_frag_mem[local]:
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
  N <= C /\ C < dimword (:256) /\
  w2n sw + 32 < dimword (:256) /\ w2n dw + 32 < dimword (:256) /\
  w2n sw + 32 <= s.vs_alloca_next /\ w2n dw + 32 <= s.vs_alloca_next /\
  (!out. step_inst_base (mk_inst a.cs_next_id MLOAD [src] [out]) s =
     OK (update_var out (n2w N) s)) ==>
  frag_exec_mem ctx a b (\u. u = s)
    (\t. eval_operand length t = SOME (n2w N) /\
      eval_operand sd t = SOME (sw + 32w) /\ eval_operand dd t = SOME (dw + 32w) /\
      mem_bytes_at (w2n dw) 32 t.vs_memory = word_to_bytes (n2w N : bytes32) T /\
      typed_copy_state_frame a (w2n dw) 32 s t) (\r. F)
Proof
  strip_tac >> drule_all typed_copy_dyn_prefix_mono >> strip_tac >>
  `frag_exec_mem ctx a a4 (\u. u = s)
    (\t. eval_operand length t = SOME (n2w N) /\ t.vs_memory = s.vs_memory /\
      typed_copy_state_frame a (w2n dw) 32 s t) (\r. F)` by
    (irule typed_copy_dyn_read_check_frag_mem >>
     goal_assum (drule_at (Pat `emit_op MLOAD _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op GT _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op ISZERO _ _ = _`)) >> simp[] >>
     simp[below_frontier_MLOAD]) >>
  drule frag_exec_mem_then >> disch_then irule >> conj_tac
  >- (simp[] >> rpt strip_tac >>
      `eval_operand src t = SOME sw /\ eval_operand dst t = SOME dw` by
        metis_tac[typed_copy_state_frame_operand] >>
      `frag_exec_mem ctx a4 b (\u. u = t)
        (\u. eval_operand length u = SOME (n2w N) /\
          eval_operand sd u = SOME (sw + 32w) /\ eval_operand dd u = SOME (dw + 32w) /\
          mem_word_at (w2n dw) u.vs_memory = n2w N /\
          typed_copy_state_frame a4 (w2n dw) 32 t u) (\r. F)` by
        (irule typed_copy_dyn_data_frag_mem >> simp[] >>
         (conj_tac >- gvs[typed_copy_state_frame_def, venom_state_component_equality]) >>
         goal_assum (drule_at (Pat `emit_void MSTORE _ _ = _`)) >>
         goal_assum (drule_at (Pat `emit_op ADD _ a5 = _`)) >>
         goal_assum (drule_at Any) >> simp[] >>
         metis_tac[typed_copy_operand_fresh_mono]) >>
      pop_assum (mp_then Any irule frag_exec_mem_conseq) >> simp[] >> rpt strip_tac
      >- (rename1 `mem_bytes_at (w2n dw) 32 u.vs_memory` >>
          `mem_bytes_at (w2n dw) 32 u.vs_memory =
             word_to_bytes (mem_word_at (w2n dw) u.vs_memory) T` suffices_by simp[] >>
          simp_tac bool_ss [mem_word_at_def, GSYM mem_bytes_at_def] >> irule EQ_SYM >>
          irule venomMemPropsTheory.word_bytes_roundtrip_256 >> simp[]) >>
      irule typed_copy_state_frame_trans >> qexists_tac `t` >> simp[] >>
      irule typed_copy_state_frame_mono >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[ci_mono_def]
QED

Theorem typed_copy_dynarray_prefix_rep_frag_mem:
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
  LENGTH vs <= C /\ C < dimword (:256) /\
  val_wf (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs)) /\
  val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs))
    (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size (ArrayTV stv (Dynamic scap)) < dimword (:256) /\
  w2n dw + type_memory_size (ArrayTV dtv (Dynamic C)) < dimword (:256) /\
  (w2n sw + type_memory_size (ArrayTV stv (Dynamic scap)) <= w2n dw \/
   w2n dw + type_memory_size (ArrayTV dtv (Dynamic C)) <= w2n sw) /\
  w2n sw + type_memory_size (ArrayTV stv (Dynamic scap)) <= s.vs_alloca_next /\
  w2n dw + type_memory_size (ArrayTV dtv (Dynamic C)) <= s.vs_alloca_next ==>
  frag_exec_mem ctx a b (\u. u = s)
    (\t. eval_operand length t = SOME (n2w (LENGTH vs)) /\
      eval_operand sd t = SOME (sw + 32w) /\ eval_operand dd t = SOME (dw + 32w) /\
      mem_bytes_at (w2n dw) 32 t.vs_memory = word_to_bytes (n2w (LENGTH vs) : bytes32) T /\
      (!i. i < LENGTH vs ==> val_in_memory stv (EL i vs)
         (w2n sw + 32 + i * type_memory_size stv) t.vs_memory) /\
      typed_copy_state_frame a (w2n dw) 32 s t) (\r. F)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `w2n sw + 32 < dimword (:256) /\ w2n dw + 32 < dimword (:256) /\
   w2n sw + 32 <= s.vs_alloca_next /\ w2n dw + 32 <= s.vs_alloca_next` by
    (fs[type_memory_size_def] >> decide_tac) >>
  `!out. step_inst_base (mk_inst a.cs_next_id MLOAD [src] [out]) s =
     OK (update_var out (n2w (LENGTH vs)) s)` by
    metis_tac[typed_copy_dynarray_mload_step] >>
  drule_all typed_copy_dyn_prefix_frag_mem >>
  disch_then (qspec_then `ctx` (mp_then Any irule frag_exec_mem_conseq)) >>
  simp[] >> rpt strip_tac >>
  rename1 `typed_copy_state_frame a (w2n dw) 32 s t` >>
  `val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs))
      (w2n sw) t.vs_memory` suffices_by
    simp[typed_copy_dynarray_representation] >>
  irule typed_copy_frame_preserves_source >> conj_tac >- simp[] >>
  qexistsl_tac [`32`, `w2n dw`, `s.vs_memory`] >>
  simp[] >> conj_tac
  >- (fs[type_memory_size_def] >> decide_tac) >>
  gvs[typed_copy_state_frame_def]
QED

Theorem typed_copy_runtime_header_frag_mem[local]:
  emit_op LT [Var counter; length] a = (lt,b) /\
  emit_op ISZERO [lt] b = (done,c) /\
  not_fresh_at a counter /\ lookup_var counter s = SOME (n2w k) /\
  eval_operand length s = SOME (n2w N) /\ k <= N /\ N < dimword (:256) ==>
  frag_exec_mem ctx a c (\u. u = s)
    (\t. eval_operand done t = SOME (if k < N then 0w else 1w) /\
      t.vs_memory = s.vs_memory /\ typed_copy_state_frame a off len s t) (\r. F)
Proof
  strip_tac >> `k < dimword (:256)` by decide_tac >>
  `frag_exec_mem ctx a b (\u. u = s)
     (\t. eval_operand lt t = SOME (bool_to_word (k < N)) /\
          t.vs_memory = s.vs_memory /\ typed_copy_state_frame a off len s t) (\r. F)` by
    (irule typed_copy_emit_op_frag_mem >> simp[venomInstTheory.is_terminator_def] >>
     goal_assum (drule_at Any) >>
     simp[below_frontier_no_ranges, venomInstTheory.is_terminator_def,
          step_inst_base_opcode_eqs, mk_inst_def,
          exec_pure2_def, eval_operand_def, w2n_n2w, LESS_MOD]) >>
  drule frag_exec_mem_then >> disch_then irule >> conj_tac
  >- (simp[] >> rpt strip_tac >>
      `frag_exec_mem ctx b c (\u. u = t)
         (\u. eval_operand done u = SOME (bool_to_word (bool_to_word (k < N) = 0w)) /\
              u.vs_memory = t.vs_memory /\ typed_copy_state_frame b off len t u) (\r. F)` by
        (irule typed_copy_emit_op_frag_mem >> simp[venomInstTheory.is_terminator_def] >>
         goal_assum (drule_at Any) >>
         simp[below_frontier_no_ranges, venomInstTheory.is_terminator_def,
              step_inst_base_opcode_eqs, mk_inst_def, exec_pure1_def]) >>
      pop_assum (mp_then Any irule frag_exec_mem_conseq) >> simp[] >> rpt strip_tac >>
      fs[bool_to_word_def] >> Cases_on `k < N` >> gvs[] >>
      irule typed_copy_state_frame_trans >> qexists_tac `t` >> simp[] >>
      irule typed_copy_state_frame_mono >> goal_assum (drule_at Any) >>
      metis_tac[typed_copy_emit_op_mono]) >>
  metis_tac[typed_copy_emit_op_mono, ci_mono_def]
QED

Theorem typed_copy_runtime_index_header_frag_mem[local]:
  emit_op LT [Var counter; length] a = (lt,b) /\
  emit_op ISZERO [lt] b = (done,c) /\ ci_mono sa a /\
  not_fresh_at a counter /\
  (!x. src = Var x ==> not_fresh_at a x) /\
  (!x. dst = Var x ==> not_fresh_at a x) /\
  (!x. length = Var x ==> not_fresh_at sa x) /\ N < dimword (:256) ==>
  frag_exec_mem ctx a c
    (\t. typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k t /\
         eval_operand length t = SOME (n2w N))
    (\t. (typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k t /\
          eval_operand length t = SOME (n2w N)) /\
         eval_operand done t = SOME (if k < N then 0w else 1w)) (\r. F)
Proof
  strip_tac >> irule frag_exec_mem_pointwise >> qx_gen_tac `s` >> strip_tac >> fs[] >>
  `k <= N /\ lookup_var counter s = SOME (n2w k)` by
    gvs[typed_copy_index_inv_def] >>
  `!x. length = Var x ==> not_fresh_at a x` by
    metis_tac[typed_copy_operand_fresh_mono] >>
  drule_all typed_copy_runtime_header_frag_mem >>
  disch_then (qspecl_then [`w2n dw`, `N * type_memory_size dtv`, `ctx`] mp_tac) >>
  disch_then (mp_then Any irule frag_exec_mem_conseq) >> simp[] >> rpt strip_tac
  >- (irule typed_copy_index_inv_preserve >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  metis_tac[typed_copy_state_frame_operand]
QED
