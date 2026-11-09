(* Joint memory execution for dynamic-array typed-copy prefixes. *)
Theory typedCopyDynarrayMemory
Ancestors
  typedCopyIndexMemory typedCopyControlMemory typedMemoryCopy fragExecMem
  instMemFrontier memSafeRun context compileEnv emitHelper emitHelperProps
  exprLoweringProps venomExecSemantics venomInst venomState venomMemDefs
  valueEncoding valueEncodingProps words list finite_map arithmetic
  vyperTypeSystem vyperTypeArgFits vyperValue vyperTyping typedCopyDomain

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

Theorem typed_copy_runtime_index_body_frag_mem[local]:
  emit_op MUL [Var counter; Lit (n2w (type_memory_size stv))] a = (so,b) /\
  emit_op MUL [Var counter; Lit (n2w (type_memory_size dtv))] b = (doff,c) /\
  emit_op ADD [src;so] c = (sp,d) /\ emit_op ADD [dst;doff] d = (dp,e) /\
  compile_store_memory_typed cenv dp dty sp sty e = ((),z) /\
  emit_op ADD [Var counter; Lit 1w] z = (inc,z1) /\
  emit_inst ASSIGN [inc] [counter] z1 = ((),endst) /\
  ci_mono sa a /\ not_fresh_at a counter /\ ~not_fresh_at sa counter /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. length = Var x ==> not_fresh_at sa x) /\
  eval_operand length s0 = SOME (n2w N) /\
  (!i. i < N ==>
    (!dst src sa sb s dw sw.
      compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
      (!x. dst = Var x ==> not_fresh_at sa x) /\
      (!x. src = Var x ==> not_fresh_at sa x) /\
      eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
      val_in_memory stv (f i) (w2n sw) s.vs_memory /\
      w2n sw + type_memory_size stv < dimword (:256) /\
      w2n dw + type_memory_size dtv < dimword (:256) /\
      (w2n sw + type_memory_size stv <= w2n dw \/
       w2n dw + type_memory_size dtv <= w2n sw) /\
      w2n sw + type_memory_size stv <= s.vs_alloca_next /\
      w2n dw + type_memory_size dtv <= s.vs_alloca_next ==>
      frag_exec_mem ctx sa sb (\u. u = s)
        (\t. val_in_memory dtv (f i) (w2n dw) t.vs_memory /\
             typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t) (\r. F)) /\
    val_wf stv (f i) /\ val_wf dtv (f i)) /\
  N < dimword (:256) /\ k < N /\
  w2n sw + N * type_memory_size stv < dimword (:256) /\
  w2n dw + N * type_memory_size dtv < dimword (:256) /\
  (w2n sw + N * type_memory_size stv <= w2n dw \/
   w2n dw + N * type_memory_size dtv <= w2n sw) /\
  w2n sw + N * type_memory_size stv <= s0.vs_alloca_next /\
  w2n dw + N * type_memory_size dtv <= s0.vs_alloca_next ==>
  frag_exec_mem ctx a endst
    (\t. typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k t /\
         eval_operand length t = SOME (n2w N))
    (\t. typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 (SUC k) t /\
         eval_operand length t = SOME (n2w N)) (\r. F)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all typed_copy_index_body_frag_mem >>
  disch_then (mp_then Any irule frag_exec_mem_conseq) >> simp[] >> rpt strip_tac >>
  fs[typed_copy_index_inv_def] >> metis_tac[typed_copy_state_frame_operand]
QED

Theorem typed_copy_dynarray_index_init_frag_mem[local]:
  fresh_label "typed_dyn_cond" sa = (hdr,l1) /\
  fresh_label "typed_dyn_body" l1 = (blabel,l2) /\
  fresh_label "typed_dyn_exit" l2 = (exit,l3) /\
  fresh_var l3 = (counter,init) /\
  emit_inst ASSIGN [Lit 0w] [counter] init = ((),st0) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. length = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  eval_operand length s = SOME (n2w N) /\
  (!i. i < N ==> val_in_memory stv (f i)
     (w2n sw + i * type_memory_size stv) s.vs_memory) ==>
  frag_exec_mem ctx sa st0 (\u. u = s)
    (\t. typed_copy_index_inv sa counter src dst sw dw f stv dtv N s 0 t /\
         eval_operand length t = SOME (n2w N)) (\r. F)
Proof
  strip_tac >>
  `~not_fresh_at sa counter /\ sa.cs_current_bb = init.cs_current_bb /\
   sa.cs_current_insts = init.cs_current_insts /\ sa.cs_blocks = init.cs_blocks` by
    (gvs[fresh_label_def, fresh_var_def, not_fresh_at_def,
         ASCIInumbersTheory.toString_inj]) >>
  `eval_operand (Lit 0w) s = SOME 0w` by simp[eval_operand_def] >>
  `frag_exec_mem ctx init st0 (\u. u = s)
     (\t. typed_copy_index_inv sa counter src dst sw dw f stv dtv N s 0 t /\
          eval_operand length t = SOME (n2w N)) (\r. F)` by
    (drule_all typed_copy_assign_frag_mem >> disch_then (qspec_then `ctx` mp_tac) >>
     disch_then (mp_then Any irule frag_exec_mem_conseq) >> simp[] >>
     rpt strip_tac >> rename1 `lookup_var counter t = SOME 0w` >>
     `typed_copy_state_frame sa (w2n dw) (N * type_memory_size dtv) s t` by
       (simp[typed_copy_state_frame_def, typed_copy_frame_def] >> metis_tac[]) >>
     `eval_operand src t = SOME sw /\ eval_operand dst t = SOME dw /\
      eval_operand length t = SOME (n2w N)` by
       metis_tac[typed_copy_state_frame_operand] >>
     simp[typed_copy_index_inv_def, typed_copy_index_prefix_zero]) >>
  qpat_x_assum `frag_exec_mem _ _ _ _ _ _` mp_tac >>
  simp[frag_exec_mem_def, fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def]
QED

Theorem typed_copy_dynarray_slow_data_sizes_frag_mem:
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
  emit_op ADD [src;so] b2 = (sp,b3) /\ emit_op ADD [dst;doff] b3 = (dp,b4) /\
  compile_store_memory_typed cenv dp dty sp sty b4 = ((),b5) /\
  emit_op ADD [Var counter; Lit 1w] b5 = (inc,b6) /\
  emit_inst ASSIGN [inc] [counter] b6 = ((),ste) /\
  emit_inst JMP [Label hdr] [] ste = ((),st3) /\
  new_block exit st3 = (u3,stx) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. length = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  eval_operand length s = SOME (n2w N) /\ N < dimword (:256) /\
  (!i. i < N ==>
    (!dst src sa sb s dw sw.
      compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
      (!x. dst = Var x ==> not_fresh_at sa x) /\
      (!x. src = Var x ==> not_fresh_at sa x) /\
      eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
      val_in_memory stv (f i) (w2n sw) s.vs_memory /\
      w2n sw + type_memory_size stv < dimword (:256) /\
      w2n dw + type_memory_size dtv < dimword (:256) /\
      (w2n sw + type_memory_size stv <= w2n dw \/
       w2n dw + type_memory_size dtv <= w2n sw) /\
      w2n sw + type_memory_size stv <= s.vs_alloca_next /\
      w2n dw + type_memory_size dtv <= s.vs_alloca_next ==>
      frag_exec_mem ctx sa sb (\u. u = s)
        (\t. val_in_memory dtv (f i) (w2n dw) t.vs_memory /\
             typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t) (\r. F)) /\
    val_wf stv (f i) /\ val_wf dtv (f i)) /\
  (!i. i < N ==> val_in_memory stv (f i)
     (w2n sw + i * type_memory_size stv) s.vs_memory) /\
  w2n sw + N * type_memory_size stv < dimword (:256) /\
  w2n dw + N * type_memory_size dtv < dimword (:256) /\
  (w2n sw + N * type_memory_size stv <= w2n dw \/
   w2n dw + N * type_memory_size dtv <= w2n sw) /\
  w2n sw + N * type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + N * type_memory_size dtv <= s.vs_alloca_next ==>
  frag_exec_mem ctx sa stx (\u. u = s)
    (\t. (!i. i < N ==> val_in_memory dtv (f i)
       (w2n dw + i * type_memory_size dtv) t.vs_memory) /\
      typed_copy_state_frame sa (w2n dw) (N * type_memory_size dtv) s t) (\r. F)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all typed_copy_dynarray_slow_layout >> strip_tac >>
  `(!x. src = Var x ==> not_fresh_at sth x) /\
   (!x. dst = Var x ==> not_fresh_at sth x)` by
    metis_tac[typed_copy_operand_fresh_mono] >>
  qmatch_goalsub_abbrev_tac `frag_exec_mem ctx sa stx P Q R` >>
  qabbrev_tac `Inv = \k t. typed_copy_index_inv sa counter src dst sw dw f stv dtv N s k t /\
                           eval_operand length t = SOME (n2w N)` >>
  qabbrev_tac `J = \k t. Inv k t /\ eval_operand done t = SOME (if k < N then 0w else 1w)` >>
  `frag_exec_mem ctx sa st0 P (Inv 0) R` by
    (simp[Abbr `P`, Abbr `Inv`, Abbr `R`] >>
     irule typed_copy_dynarray_index_init_frag_mem >> simp[] >>
     goal_assum (drule_at (Pat `fresh_var _ = _`)) >>
     goal_assum (drule_at (Pat `fresh_label "typed_dyn_exit" _ = _`)) >>
     goal_assum (drule_at (Pat `fresh_label "typed_dyn_body" _ = _`)) >>
     goal_assum (drule_at (Pat `fresh_label "typed_dyn_cond" _ = _`)) >> simp[]) >>
  `frag_exec_mem ctx st0 stx (Inv 0) (J N) R` by suspend "loop" >>
  `cs_extends sa st0 /\ cs_extends st0 stx` by metis_tac[ci_mono_def] >>
  drule_all frag_exec_mem_seq >>
  disch_then (mp_then Any irule frag_exec_mem_conseq) >> simp[] >>
  simp[Abbr `J`, Abbr `Inv`, Abbr `Q`, typed_copy_index_inv_def,
       typed_copy_index_prefix_complete]
QED

Resume typed_copy_dynarray_slow_data_sizes_frag_mem[loop]:
  irule fragLoopMemoryTheory.frag_exec_loop_mem >> conj_tac
  >- simp[Abbr `Inv`, typed_copy_index_inv_jump, typed_copy_eval_operand_jump] >>
  conj_tac
  >- simp[Abbr `J`, Abbr `Inv`, typed_copy_index_inv_jump, typed_copy_eval_operand_jump] >>
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
  >- (simp[Abbr `J`] >> rpt strip_tac >> Cases_on `k < N` >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> simp[Abbr `Inv`, Abbr `J`, Abbr `R`] >>
      drule_all typed_copy_runtime_index_body_frag_mem >>
      disch_then (mp_then Any irule frag_exec_mem_conseq) >> simp[]) >>
  rpt strip_tac >> simp[Abbr `Inv`, Abbr `J`, Abbr `R`] >>
  irule typed_copy_runtime_index_header_frag_mem >> simp[] >>
  goal_assum (drule_at (Pat `emit_op ISZERO _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_op LT _ _ = _`)) >> simp[]
QED

Finalise typed_copy_dynarray_slow_data_sizes_frag_mem

Theorem typed_copy_dynamic_raw_frag_mem[local]:
  compile_copy_memory_dynamic dst src len sa = ((),sb) /\
  eval_operand dst s0 = SOME d /\ eval_operand src s0 = SOME a /\
  eval_operand len s0 = SOME w /\
  w2n a + w2n w <= s0.vs_alloca_next /\
  w2n d + w2n w <= s0.vs_alloca_next ==>
  frag_exec_mem ctx sa sb (\s. s = s0)
    (\t. t = ((mcopy (w2n d) (w2n a) (w2n w) s0)
                with vs_inst_idx := LENGTH sb.cs_current_insts)) (\r. F)
Proof
  strip_tac >> drule_all typed_copy_dynamic_run_seq >> strip_tac >>
  irule fragExecMemTheory.frag_exec_mem_run_inst_seq >>
  gvs[same_blocks_def] >> simp[] >>
  qpat_x_assum `compile_copy_memory_dynamic _ _ _ _ = _` mp_tac >>
  simp[compile_copy_memory_dynamic_def] >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  simp[run_inst_seq_mem_ok_last, below_frontier_MCOPY]
QED

Theorem typed_copy_dynarray_bulk_data_frag_mem:
  emit_op MUL [length; Lit (n2w (type_memory_size tv))] sa = (bytes,b) /\
  compile_copy_memory_dynamic dst src bytes b = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  eval_operand length s = SOME (n2w N) /\
  (!i. i < N ==> val_wf tv (f i) /\
    val_in_memory tv (f i) (w2n sw + i * type_memory_size tv) s.vs_memory) /\
  w2n sw + N * type_memory_size tv < dimword (:256) /\
  w2n dw + N * type_memory_size tv < dimword (:256) /\
  w2n sw + N * type_memory_size tv <= s.vs_alloca_next /\
  w2n dw + N * type_memory_size tv <= s.vs_alloca_next ==>
  frag_exec_mem ctx sa sb (\u. u = s)
    (\t. (!i. i < N ==> val_in_memory tv (f i)
      (w2n dw + i * type_memory_size tv) t.vs_memory) /\
      typed_copy_state_frame sa (w2n dw) (N * type_memory_size tv) s t) (\r. F)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `N * type_memory_size tv < dimword (:256)` by decide_tac >>
  `frag_exec_mem ctx sa b (\u. u = s)
     (\t. eval_operand bytes t = SOME (n2w (N * type_memory_size tv)) /\
          t.vs_memory = s.vs_memory /\
          typed_copy_state_frame sa (w2n dw) (N * type_memory_size tv) s t) (\r. F)` by
    (irule typed_copy_emit_op_frag_mem >> simp[venomInstTheory.is_terminator_def] >>
     goal_assum (drule_at Any) >>
     simp[below_frontier_no_ranges, venomInstTheory.is_terminator_def,
          step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
          eval_operand_def, GSYM word_mul_n2w]) >>
  drule frag_exec_mem_then >> disch_then irule >> simp[emit_op_extends] >>
  conj_tac >- suspend "copy" >>
  conj_tac
  >- (gvs[compile_copy_memory_dynamic_def] >>
      `ci_mono b sb` by metis_tac[ci_mono_emit_void, pairTheory.SND] >>
      gvs[ci_mono_def]) >>
  drule typed_copy_emit_op_mono >> simp[ci_mono_def]
QED

Resume typed_copy_dynarray_bulk_data_frag_mem[copy]:
  rpt strip_tac >>
  `eval_operand src t = SOME sw /\ eval_operand dst t = SOME dw` by
    metis_tac[typed_copy_state_frame_operand] >>
  `t.vs_alloca_next = s.vs_alloca_next` by
    gvs[typed_copy_state_frame_def, venom_state_component_equality] >>
  `w2n sw + w2n (n2w (N * type_memory_size tv) : bytes32) <= t.vs_alloca_next /\
   w2n dw + w2n (n2w (N * type_memory_size tv) : bytes32) <= t.vs_alloca_next` by
    simp[w2n_n2w, LESS_MOD] >>
  drule_all typed_copy_dynamic_raw_frag_mem >>
  disch_then (qspec_then `ctx` (mp_then Any irule frag_exec_mem_conseq)) >>
  simp[w2n_n2w, LESS_MOD] >>
  conj_tac
  >- (rpt strip_tac >>
      irule valueCopyTheory.val_in_memory_relocate >>
      conj_tac >- metis_tac[] >>
      qexistsl_tac [`w2n sw + i * type_memory_size tv`,
                    `type_memory_size tv`, `t.vs_memory`] >>
      simp[] >> conj_tac
      >- metis_tac[exprSimPropsTheory.val_footprint_le] >>
      irule valueEncodingProofsTheory.mem_bytes_at_translated_window >>
      qexists_tac `N * type_memory_size tv` >>
      simp[mcopy_mem_bytes_at_same] >>
      `SUC i <= N` by decide_tac >>
      `SUC i * type_memory_size tv <= N * type_memory_size tv` by
        simp[arithmeticTheory.LE_MULT_RCANCEL] >>
      qpat_x_assum `SUC i * _ <= _` mp_tac >>
      pure_rewrite_tac[arithmeticTheory.MULT_CLAUSES] >> decide_tac) >>
  irule typed_copy_state_frame_trans >>
  qexists_tac `t` >> simp[typed_copy_mcopy_state_frame]
QED

Finalise typed_copy_dynarray_bulk_data_frag_mem

Theorem typed_copy_dynarray_frag_mem:
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
  (!i. i < LENGTH vs ==>
    !dst src sa sb s dw sw.
      compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
      (!x. dst = Var x ==> not_fresh_at sa x) /\
      (!x. src = Var x ==> not_fresh_at sa x) /\
      eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
      val_in_memory stv (EL i vs) (w2n sw) s.vs_memory /\
      w2n sw + type_memory_size stv < dimword (:256) /\
      w2n dw + type_memory_size dtv < dimword (:256) /\
      (w2n sw + type_memory_size stv <= w2n dw \/
       w2n dw + type_memory_size dtv <= w2n sw) /\
      w2n sw + type_memory_size stv <= s.vs_alloca_next /\
      w2n dw + type_memory_size dtv <= s.vs_alloca_next ==>
      frag_exec_mem ctx sa sb (\u. u = s)
        (\t. val_in_memory dtv (EL i vs) (w2n dw) t.vs_memory /\
             typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t) (\r. F)) /\
  w2n sw + type_memory_size (ArrayTV stv (Dynamic scap)) < dimword (:256) /\
  w2n dw + type_memory_size (ArrayTV dtv (Dynamic C)) < dimword (:256) /\
  (w2n sw + type_memory_size (ArrayTV stv (Dynamic scap)) <= w2n dw \/
   w2n dw + type_memory_size (ArrayTV dtv (Dynamic C)) <= w2n sw) /\
  w2n sw + type_memory_size (ArrayTV stv (Dynamic scap)) <= s.vs_alloca_next /\
  w2n dw + type_memory_size (ArrayTV dtv (Dynamic C)) <= s.vs_alloca_next ==>
  frag_exec_mem ctx sa sb (\u. u = s)
    (\t. val_in_memory (ArrayTV dtv (Dynamic C)) (ArrayV (DynArrayV vs))
           (w2n dw) t.vs_memory /\
      typed_copy_state_frame sa (w2n dw)
        (type_memory_size (ArrayTV dtv (Dynamic C))) s t) (\r. F)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `compile_copy_dynarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gnvs[]) >>
  rename1 `emit_op ADD [dst; Lit 32w] a6 = (dd,b)` >>
  rename1 `emit_op ADD [src; Lit 32w] a5 = (sd,a6)` >> disch_tac >>
  drule_all typed_copy_dyn_prefix_mono >> strip_tac >>
  `frag_exec_mem ctx sa b (\u. u = s)
    (\t. eval_operand length t = SOME (n2w (LENGTH vs)) /\
      eval_operand sd t = SOME (sw + 32w) /\ eval_operand dd t = SOME (dw + 32w) /\
      mem_bytes_at (w2n dw) 32 t.vs_memory = word_to_bytes (n2w (LENGTH vs) : bytes32) T /\
      (!i. i < LENGTH vs ==> val_in_memory stv (EL i vs)
         (w2n sw + 32 + i * type_memory_size stv) t.vs_memory) /\
      typed_copy_state_frame sa (w2n dw) 32 s t) (\r. F)` by
    (irule typed_copy_dynarray_prefix_rep_frag_mem >>
     goal_assum (drule_at (Pat `emit_op MLOAD _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op GT _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op ISZERO _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_void MSTORE _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op ADD _ a5 = _`)) >>
     goal_assum (drule_at Any) >> qexistsl_tac [`dtv`, `scap`] >> simp[]) >>
  drule frag_exec_mem_then >> disch_then irule >>
  conj_tac >- suspend "suffix" >> suspend "extensions"
QED

Resume typed_copy_dynarray_frag_mem[suffix]:
  simp[] >> rpt gen_tac >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  rename1 `typed_copy_state_frame sa (w2n dw) 32 s t` >>
  qpat_x_assum `frag_exec_mem ctx sa b _ _ _` kall_tac >>
  rpt (qpat_x_assum `emit_op _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `emit_void _ _ _ = _` kall_tac) >>
  `LENGTH vs <= scap` by gvs[typed_copy_dynarray_wf] >>
  `LENGTH vs * type_memory_size stv <= scap * type_memory_size stv /\
   LENGTH vs * type_memory_size dtv <= C * type_memory_size dtv` by
    simp[arithmeticTheory.LE_MULT_RCANCEL] >>
  `w2n (sw + 32w) = w2n sw + 32 /\
   w2n (dw + 32w) = w2n dw + 32` by
    (fs[type_memory_size_def] >> simp[word_add_def, w2n_n2w, LESS_MOD]) >>
  `t.vs_alloca_next = s.vs_alloca_next` by
    gvs[typed_copy_state_frame_def, venom_state_component_equality] >>
  `w2n (sw + 32w) + LENGTH vs * type_memory_size stv < dimword (:256) /\
   w2n (dw + 32w) + LENGTH vs * type_memory_size dtv < dimword (:256) /\
   (w2n (sw + 32w) + LENGTH vs * type_memory_size stv <= w2n (dw + 32w) \/
    w2n (dw + 32w) + LENGTH vs * type_memory_size dtv <= w2n (sw + 32w)) /\
   w2n (sw + 32w) + LENGTH vs * type_memory_size stv <= t.vs_alloca_next /\
   w2n (dw + 32w) + LENGTH vs * type_memory_size dtv <= t.vs_alloca_next` by
    (gns[type_memory_size_def, Excl "LE_MULT_RCANCEL"] >> decide_tac) >>
  (`frag_exec_mem ctx b sb (\u. u = t)
    (\u. (!i. i < LENGTH vs ==> val_in_memory dtv (EL i vs)
       (w2n (dw + 32w) + i * type_memory_size dtv) u.vs_memory) /\
      typed_copy_state_frame b (w2n (dw + 32w))
        (LENGTH vs * type_memory_size dtv) t u) (\r. F)` by
    suspend "data") >> suspend "reconstruct"
QED

Resume typed_copy_dynarray_frag_mem[data]:
  markerLib.RESUME_TAC >>
  rpt (qpat_x_assum `ci_mono _ _` kall_tac) >>
  qpat_x_assum `val_in_memory _ _ _ s.vs_memory` kall_tac >>
  qpat_x_assum `typed_copy_state_frame sa _ _ s t` kall_tac >>
  qpat_x_assum `mem_bytes_at _ _ _ = _` kall_tac >>
  `LENGTH vs < dimword (:256)` by decide_tac >>
  (Cases_on `type_memory_size dtv = type_memory_size stv /\ dty = sty`
   >- suspend "bulk_data" >> suspend "slow_data")
QED

Resume typed_copy_dynarray_frag_mem[bulk_data]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `w2n (dw + 32w) = _` kall_tac >>
  qpat_x_assum `w2n (sw + 32w) = _` kall_tac >>
  `dtv = stv` by simp[] >> gvs[] >>
  qpat_x_assum `_ b = ((),sb)` mp_tac >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gnvs[]) >> strip_tac >>
  ho_match_mp_tac (GEN_ALL typed_copy_dynarray_bulk_data_frag_mem) >>
  goal_assum (drule_at (Pat `emit_op MUL _ _ = _`)) >>
  goal_assum (drule_at (Pat `compile_copy_memory_dynamic _ _ _ _ = _`)) >>
  qexists_tac `sw + 32w` >> simp[] >>
  `w2n (sw + 32w) = w2n sw + 32` by
    (fs[type_memory_size_def] >> simp[word_add_def, w2n_n2w, LESS_MOD]) >>
  gvs[typed_copy_dynarray_wf]
QED

Resume typed_copy_dynarray_frag_mem[slow_data]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `w2n (dw + 32w) = _` kall_tac >>
  qpat_x_assum `w2n (sw + 32w) = _` kall_tac >>
  qpat_x_assum `_ b = ((),sb)` mp_tac >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  ntac 5 (pairarg_tac >> asm_simp_tac std_ss []) >>
  ntac 5 (pairarg_tac >> asm_simp_tac std_ss []) >>
  ntac 5 (pairarg_tac >> asm_simp_tac std_ss []) >>
  rpt (pairarg_tac >> asm_simp_tac std_ss []) >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> gnvs[] >>
  `LENGTH vs < dimword (:256)` by decide_tac >>
  ho_match_mp_tac (GEN_ALL typed_copy_dynarray_slow_data_sizes_frag_mem) >>
  goal_assum (drule_at (Pat `fresh_label "typed_dyn_cond" _ = _`)) >>
  goal_assum (drule_at (Pat `fresh_label "typed_dyn_body" _ = _`)) >>
  goal_assum (drule_at (Pat `fresh_label "typed_dyn_exit" _ = _`)) >>
  goal_assum (drule_at (Pat `fresh_var _ = _`)) >>
  goal_assum (drule_at (Pat `emit_inst ASSIGN [Lit 0w] _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_inst JMP _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `new_block _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_op LT _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_op ISZERO _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_inst JNZ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `new_block _ _ = _`)) >>
  goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_op MUL [Var _; Lit (n2w (type_memory_size stv))] _ = _`)) >>
  goal_assum (drule_at (Pat `emit_op MUL _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_op ADD _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_op ADD _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_op ADD _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_inst ASSIGN _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_inst JMP _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `new_block _ _ = _`)) >>
  qexists_tac `sw + 32w` >> simp[] >>
  `w2n (sw + 32w) = w2n sw + 32` by
    (fs[type_memory_size_def] >> simp[word_add_def, w2n_n2w, LESS_MOD]) >>
  gvs[typed_copy_dynarray_wf] >>
  metis_tac[]
QED

Resume typed_copy_dynarray_frag_mem[reconstruct]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `_ b = ((),sb)` kall_tac >>
  qpat_x_assum `frag_exec_mem ctx b sb _ _ _` mp_tac >>
  disch_then (mp_then Any irule frag_exec_mem_conseq) >> simp[] >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  (conj_tac
  >- (irule typed_copy_dynarray_reconstruct >> conj_tac
      >- (qpat_assum `!i. _ ==> val_in_memory dtv _ _ _` mp_tac >>
          simp_tac std_ss [AC ADD_ASSOC ADD_COMM]) >>
      goal_assum (drule_at (Pat `typed_copy_state_frame _ _ _ _ _`)) >>
      simp[mem_word_at_def, GSYM mem_bytes_at_def]) >>
  `typed_copy_state_frame sa (w2n dw + 32)
      (LENGTH vs * type_memory_size dtv) t s''` by
    (irule typed_copy_state_frame_mono >> goal_assum (drule_at Any) >> simp[]) >>
  irule (GEN_ALL typed_copy_state_frame_trans) >> qexists_tac `t` >> conj_tac
  >- (irule typed_copy_state_frame_subinterval >>
      goal_assum (drule_at (Pat `typed_copy_state_frame _ _ _ s t`)) >>
      simp[type_memory_size_def]) >>
  irule typed_copy_state_frame_subinterval >>
  goal_assum (drule_at (Pat `typed_copy_state_frame sa _ _ t _`)) >>
  simp[type_memory_size_def, Excl "LE_MULT_RCANCEL"])
QED

Resume typed_copy_dynarray_frag_mem[extensions]:
  reverse conj_tac >- gvs[ci_mono_def] >>
  qmatch_asmsub_abbrev_tac `suffix b = ((),sb)` >>
  `ci_mono b (SND (suffix b))` suffices_by gvs[ci_mono_def] >>
  unabbrev_all_tac >>
  IF_CASES_TAC >>
  rpt (FIRST [irule ci_mono_bind, irule ci_mono_ignore_bind] >>
       rpt conj_tac >> rpt gen_tac >> BETA_TAC) >>
  simp[ci_mono_emit_op, ci_mono_emit_inst, ci_mono_new_block,
       ci_mono_fresh_label, ci_mono_fresh_var, ci_mono_comp_return,
       cj 1 ci_mono_typed_memory_family,
       contextTheory.compile_copy_memory_dynamic_def, ci_mono_emit_void]
QED

Finalise typed_copy_dynarray_frag_mem


Theorem typed_copy_dynarray_entry_mem:
  !cenv tenv ctx de cap sty dtv stv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname, fty, sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty (ArrayT de (Dynamic cap)) /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv (ArrayT de (Dynamic cap)) = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
    (!cd cs cdt cst cv.
      type_rank cenv.ce_struct_fields cd <
        type_rank cenv.ce_struct_fields (ArrayT de (Dynamic cap)) ==>
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv ==>
      !dst src sa sb s dw sw.
        compile_store_memory_typed cenv dst cd src cs sa = ((),sb) /\
        (!x. dst = Var x ==> not_fresh_at sa x) /\
        (!x. src = Var x ==> not_fresh_at sa x) /\
        eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
        val_in_memory cst cv (w2n sw) s.vs_memory /\
        w2n sw + type_memory_size cst < dimword (:256) /\
        w2n dw + type_memory_size cdt < dimword (:256) /\
        (w2n sw + type_memory_size cst <= w2n dw \/
         w2n dw + type_memory_size cdt <= w2n sw) /\
        w2n sw + type_memory_size cst <= s.vs_alloca_next /\
        w2n dw + type_memory_size cdt <= s.vs_alloca_next ==>
        frag_exec_mem ctx sa sb (\u. u = s)
          (\t. val_in_memory cdt cv (w2n dw) t.vs_memory /\
               typed_copy_state_frame sa (w2n dw) (type_memory_size cdt) s t) (\r. F)) ==>
    !dst src sa sb s dw sw.
      compile_store_memory_typed cenv dst (ArrayT de (Dynamic cap)) src sty sa = ((),sb) /\
      (!x. dst = Var x ==> not_fresh_at sa x) /\
      (!x. src = Var x ==> not_fresh_at sa x) /\
      eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
      val_in_memory stv v (w2n sw) s.vs_memory /\
      w2n sw + type_memory_size stv < dimword (:256) /\
      w2n dw + type_memory_size dtv < dimword (:256) /\
      (w2n sw + type_memory_size stv <= w2n dw \/
       w2n dw + type_memory_size dtv <= w2n sw) /\
      w2n sw + type_memory_size stv <= s.vs_alloca_next /\
      w2n dw + type_memory_size dtv <= s.vs_alloca_next ==>
      frag_exec_mem ctx sa sb (\u. u = s)
        (\t. val_in_memory dtv v (w2n dw) t.vs_memory /\
             typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t) (\r. F)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all typed_copy_array_source >> strip_tac >> gvs[] >>
  `?scap. sb = Dynamic scap /\ scap <= cap` by
    (drule typed_copy_array_widening >> strip_tac >> gvs[]) >> gvs[] >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  `type_widens_to tenv se de` by
    (qpat_x_assum `type_widens_to _ _ _` mp_tac >>
     simp[type_widens_to_def, arg_type_fits_def, well_formed_type_def,
          evaluate_type_def] >> metis_tac[]) >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  `cap < dimword (:256)` by
    (qpat_x_assum `type_slot_size (ArrayTV tv' (Dynamic cap)) < _` mp_tac >>
     simp[type_slot_size_def] >>
     `cap <= cap * type_slot_size tv'` by
       (Cases_on `type_slot_size tv'` >> gvs[MULT_CLAUSES]) >> decide_tac) >>
  `type_memory_bytes cenv de = type_memory_size tv' /\
   type_memory_bytes cenv se = type_memory_size tv` by
    (conj_tac >> irule typed_copy_memory_size >>
     qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  suspend "children"
QED

Resume typed_copy_dynarray_entry_mem[children]:
  `!i. i < LENGTH l ==> !dst src sa sb s dw sw.
    compile_store_memory_typed cenv dst de src se sa = ((),sb) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
    val_in_memory tv (EL i l) (w2n sw) s.vs_memory /\
    w2n sw + type_memory_size tv < dimword (:256) /\
    w2n dw + type_memory_size tv' < dimword (:256) /\
    (w2n sw + type_memory_size tv <= w2n dw \/
     w2n dw + type_memory_size tv' <= w2n sw) /\
    w2n sw + type_memory_size tv <= s.vs_alloca_next /\
    w2n dw + type_memory_size tv' <= s.vs_alloca_next ==>
    frag_exec_mem ctx sa sb (\u. u = s)
      (\t. val_in_memory tv' (EL i l) (w2n dw) t.vs_memory /\
           typed_copy_state_frame sa (w2n dw) (type_memory_size tv') s t) (\r. F)` by
    (qx_gen_tac `i` >> strip_tac >> simp[ADD_COMM] >>
     qpat_x_assum `!cd cs cdt cst cv. _`
       (qspecl_then [`de`, `se`, `tv'`, `tv`, `EL i l`] mp_tac) >>
     simp[Once type_rank_def] >>
     (impl_tac >- gvs[typed_copy_dynarray_wf,
       vyperTypingTheory.all_have_type_EVERY, EVERY_EL]) >>
     disch_then MATCH_ACCEPT_TAC) >>
  suspend "execute"
QED

Resume typed_copy_dynarray_entry_mem[execute]:
  rpt strip_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, is_word_type_def,
       is_bytestring_type_def] >> strip_tac >>
  irule typed_copy_dynarray_frag_mem >>
  (conj_tac >- simp[]) >>
  (conj_tac >- simp[]) >>
  (conj_tac >- simp[]) >>
  (conj_tac >- simp[]) >>
  (conj_tac >- simp[]) >>
  goal_assum (drule_at (Pat `compile_copy_dynarray_typed _ _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`scap`, `tv`, `sw`] >> simp[] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `!i. i < LENGTH l ==> _` (drule_then irule) >>
  simp[] >> qexistsl_tac [`dst'`, `src'`, `sw'`] >> simp[] >> decide_tac
QED

Finalise typed_copy_dynarray_entry_mem
