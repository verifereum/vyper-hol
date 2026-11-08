(* Joint memory execution for typed-copy address and control instructions. *)
Theory typedCopyControlMemory
Ancestors
  typedCopyPrimitiveMemory typedMemoryCopy fragExecMem instMemFrontier memSafeRun
  context compileEnv emitHelper emitHelperProps exprLoweringProps
  venomExecSemantics venomInst venomState venomMemDefs
  valueEncodingProps words list finite_map arithmetic

Theorem typed_copy_offset_frag_mem:
  !ptr off sa op sb s0 w dst len.
  compile_with_byte_offset ptr off sa = (op,sb) /\
  eval_operand ptr s0 = SOME w ==>
  frag_exec_mem ctx sa sb (\s. s = s0)
    (\t. eval_operand op t = SOME (w + n2w off) /\
         t.vs_memory = s0.vs_memory /\
         typed_copy_state_frame sa dst len s0 t) (\r. F)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `off = 0`
  >- (gvs[compile_with_byte_offset_def, comp_return_def] >>
      irule frag_exec_mem_refl >> simp[wordsTheory.WORD_ADD_0]) >>
  drule_all typed_copy_offset_run_seq >> strip_tac >>
  irule fragExecMemTheory.frag_exec_mem_run_inst_seq >>
  gvs[same_blocks_def] >> simp[] >> conj_tac
  >- (qpat_x_assum `compile_with_byte_offset _ _ _ = _` mp_tac >>
      simp[compile_with_byte_offset_def] >> strip_tac >>
      drule emitted_insts_emit_op >> strip_tac >>
      simp[run_inst_seq_mem_ok_last, below_frontier_no_ranges, mk_inst_def]) >>
  simp[eval_operand_def, lookup_var_update_var, typed_copy_state_frame_def,
       update_var_def, lookup_var_def, venom_state_component_equality] >>
  simp[FLOOKUP_UPDATE] >> rpt strip_tac >>
  `x <> STRING #"%" (toString sa.cs_next_var)` by
    (gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  simp[FLOOKUP_UPDATE]
QED

Theorem typed_copy_mstore_frag_mem:
  emit_void MSTORE [dst; value] a = ((),b) /\
  eval_operand dst s = SOME dw /\ eval_operand value s = SOME w /\
  w2n dw + 32 <= s.vs_alloca_next ==>
  frag_exec_mem ctx a b (\u. u = s)
    (\t. mem_word_at (w2n dw) t.vs_memory = w /\
      typed_copy_state_frame a (w2n dw) 32 s t) (\r. F)
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  `same_blocks a b` by
    gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_id_def, emit_def, same_blocks_def] >>
  irule fragExecMemTheory.frag_exec_mem_run_inst_seq >> gvs[same_blocks_def] >>
  simp[mk_inst_def, venomInstTheory.is_terminator_def, run_inst_seq_def,
       step_inst_base_opcode_eqs, exec_write2_def] >>
  rewrite_tac[GSYM mk_inst_def] >>
  simp[run_inst_seq_mem_ok_last, below_frontier_MSTORE,
       mstore_mem_word_at_same, typed_copy_mstore_state_frame]
QED

Theorem typed_copy_assert_frag_mem:
  emit_void ASSERT [ok] a = ((),b) /\ eval_operand ok s = SOME 1w ==>
  frag_exec_mem ctx a b (\u. u = s)
    (\t. t.vs_memory = s.vs_memory /\ typed_copy_state_frame a off len s t) (\r. F)
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  `same_blocks a b` by
    gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_id_def, emit_def, same_blocks_def] >>
  irule fragExecMemTheory.frag_exec_mem_run_inst_seq >> gvs[same_blocks_def] >>
  simp[mk_inst_def, venomInstTheory.is_terminator_def, run_inst_seq_def,
       step_inst_base_opcode_eqs] >>
  rewrite_tac[GSYM mk_inst_def] >>
  simp[run_inst_seq_mem_ok_last, below_frontier_no_ranges, mk_inst_def,
       typed_copy_state_frame_def, lookup_var_def, venom_state_component_equality]
QED

Theorem typed_copy_emit_op_frag_mem:
  !ctx opc args a op b s w off len.
    emit_op opc args a = (op,b) /\
    opc <> INVOKE /\ opc <> DLOAD /\ opc <> DLOADBYTES /\ ~is_terminator opc /\
    (!out. inst_mem_below_frontier (mk_inst a.cs_next_id opc args [out]) s) /\
    (!out. step_inst_base (mk_inst a.cs_next_id opc args [out]) s =
           OK (update_var out w s)) ==>
    frag_exec_mem ctx a b (\u. u = s)
      (\t. eval_operand op t = SOME w /\ t.vs_memory = s.vs_memory /\
           typed_copy_state_frame a off len s t) (\r. F)
Proof
  rpt strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_same_blocks >> strip_tac >>
  irule fragExecMemTheory.frag_exec_mem_run_inst_seq >> gvs[same_blocks_def] >>
  simp[run_inst_seq_mem_ok_last] >>
  simp[mk_inst_def, run_inst_seq_def] >>
  simp[eval_operand_def, lookup_var_update_var,
       typed_copy_state_frame_def, update_var_def, lookup_var_def,
       venom_state_component_equality] >>
  simp[FLOOKUP_UPDATE] >> rpt strip_tac >>
  `x <> STRING #"%" (toString a.cs_next_var)` by
    (gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  simp[FLOOKUP_UPDATE]
QED

Theorem typed_copy_assign_frag_mem[local]:
  !ctx op counter a b s w.
    emit_inst ASSIGN [op] [counter] a = ((),b) /\
    eval_operand op s = SOME w ==>
    frag_exec_mem ctx a b (\u. u = s)
      (\t. lookup_var counter t = SOME w /\ t.vs_memory = s.vs_memory /\
        (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                  vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
                  vs_inst_idx := s.vs_inst_idx|>) = s /\
        (!x. x <> counter ==> lookup_var x t = lookup_var x s)) (\r. F)
Proof
  rpt strip_tac >>
  qpat_x_assum `emit_inst _ _ _ _ = _` mp_tac >>
  simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >> strip_tac >>
  gvs[] >> irule fragExecMemTheory.frag_exec_mem_run_inst_seq >>
  simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND,
       mk_inst_def, venomInstTheory.is_terminator_def] >>
  rewrite_tac[GSYM mk_inst_def] >>
  simp[run_inst_seq_mem_ok_last, below_frontier_no_ranges, mk_inst_def] >>
  simp[run_inst_seq_def, step_inst_base_def, mk_inst_def] >>
  simp[lookup_var_update_var, update_var_def, lookup_var_def,
       FLOOKUP_UPDATE, venom_state_component_equality] >>
  rpt strip_tac >> simp[FLOOKUP_UPDATE]
QED

Theorem typed_copy_counter_init_frag_mem:
  !ctx counter a b s off len.
    emit_inst ASSIGN [Lit 0w] [counter] a = ((),b) /\
    (!x. not_fresh_at a x ==> x <> counter) ==>
    frag_exec_mem ctx a b (\u. u = s)
      (\t. lookup_var counter t = SOME 0w /\ t.vs_memory = s.vs_memory /\
           typed_copy_state_frame a off len s t) (\r. F)
Proof
  rpt strip_tac >>
  `eval_operand (Lit 0w) s = SOME 0w` by simp[eval_operand_def] >>
  drule_all typed_copy_assign_frag_mem >> disch_then (qspec_then `ctx` mp_tac) >>
  disch_then (mp_then Any irule frag_exec_mem_conseq) >>
  simp[typed_copy_state_frame_def] >> rpt strip_tac >> simp[]
QED

Theorem typed_copy_header_frag_mem:
  !ctx counter N k a lt b done c s off len.
    emit_op LT [Var counter; Lit (n2w N)] a = (lt,b) /\
    emit_op ISZERO [lt] b = (done,c) /\
    not_fresh_at a counter /\ lookup_var counter s = SOME (n2w k) /\
    k <= N /\ N < dimword (:256) ==>
    frag_exec_mem ctx a c (\u. u = s)
      (\t. eval_operand done t = SOME (if k < N then 0w else 1w) /\
           t.vs_memory = s.vs_memory /\
           typed_copy_state_frame a off len s t) (\r. F)
Proof
  rpt strip_tac >>
  `k < dimword (:256)` by decide_tac >>
  `frag_exec_mem ctx a b (\u. u = s)
     (\t. eval_operand lt t = SOME (bool_to_word (k < N)) /\
          t.vs_memory = s.vs_memory /\
          typed_copy_state_frame a off len s t) (\r. F)` by
    (irule typed_copy_emit_op_frag_mem >> simp[venomInstTheory.is_terminator_def] >>
     goal_assum (drule_at Any) >>
     simp[below_frontier_no_ranges, venomInstTheory.is_terminator_def,
          step_inst_base_def, mk_inst_def, exec_pure2_def,
          eval_operand_def, w2n_n2w, LESS_MOD]) >>
  drule frag_exec_mem_then >> disch_then irule >>
  simp[emit_op_extends] >> conj_tac
  >- (rpt strip_tac >>
      `frag_exec_mem ctx b c (\u. u = t)
         (\u. eval_operand done u = SOME (bool_to_word (bool_to_word (k < N) = 0w)) /\
              u.vs_memory = t.vs_memory /\
              typed_copy_state_frame b off len t u) (\r. F)` by
        (irule typed_copy_emit_op_frag_mem >> simp[venomInstTheory.is_terminator_def] >>
         goal_assum (drule_at Any) >>
         simp[below_frontier_no_ranges, venomInstTheory.is_terminator_def,
              step_inst_base_def, mk_inst_def, exec_pure1_def]) >>
      pop_assum (mp_then Any irule frag_exec_mem_conseq) >>
      simp[] >> rpt strip_tac >>
      fs[bool_to_word_def] >> Cases_on `k < N` >> gvs[] >>
      irule typed_copy_state_frame_trans >> qexists_tac `t` >> simp[] >>
      irule typed_copy_state_frame_mono >> goal_assum (drule_at Any) >>
      metis_tac[typed_copy_emit_op_mono]) >>
  metis_tac[typed_copy_emit_op_mono, ci_mono_def]
QED

Theorem typed_copy_counter_increment_frag_mem[local]:
  !ctx counter k a inc b c s.
    emit_op ADD [Var counter; Lit 1w] a = (inc,b) /\
    emit_inst ASSIGN [inc] [counter] b = ((),c) /\
    not_fresh_at a counter /\ lookup_var counter s = SOME (n2w k) /\
    k + 1 < dimword (:256) ==>
    frag_exec_mem ctx a c (\u. u = s)
      (\t. lookup_var counter t = SOME (n2w (k + 1)) /\
        t.vs_memory = s.vs_memory /\
        (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                  vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
                  vs_inst_idx := s.vs_inst_idx|>) = s /\
        (!x. not_fresh_at a x /\ x <> counter ==>
             lookup_var x t = lookup_var x s)) (\r. F)
Proof
  rpt strip_tac >>
  `frag_exec_mem ctx a b (\u. u = s)
     (\t. eval_operand inc t = SOME (n2w (k + 1)) /\
          t.vs_memory = s.vs_memory /\
          typed_copy_state_frame a 0 0 s t) (\r. F)` by
    (irule typed_copy_emit_op_frag_mem >> simp[venomInstTheory.is_terminator_def] >>
     goal_assum (drule_at Any) >>
     simp[below_frontier_no_ranges, venomInstTheory.is_terminator_def,
          step_inst_base_def, mk_inst_def,
          exec_pure2_def, eval_operand_def, word_add_n2w]) >>
  drule frag_exec_mem_then >> disch_then irule >> conj_tac
  >- (rpt strip_tac >> fs[] >> drule_all typed_copy_assign_frag_mem >>
      disch_then (qspec_then `ctx` mp_tac) >>
      disch_then (mp_then Any irule frag_exec_mem_conseq) >>
      simp[] >> rpt strip_tac >>
      gvs[typed_copy_state_frame_def, venom_state_component_equality]) >>
  `ci_mono a b` by metis_tac[typed_copy_emit_op_mono] >>
  qspecl_then [`ASSIGN`, `[inc]`, `[counter]`, `b`] mp_tac ci_mono_emit_inst >>
  simp[] >> gvs[ci_mono_def]
QED

Theorem typed_copy_counter_increment_frame_frag_mem:
  emit_op ADD [Var counter; Lit 1w] a = (inc,b) /\
  emit_inst ASSIGN [inc] [counter] b = ((),c) /\
  ci_mono sa a /\ ~not_fresh_at sa counter /\ not_fresh_at a counter /\
  lookup_var counter s = SOME (n2w k) /\ k + 1 < dimword (:256) ==>
  frag_exec_mem ctx a c (\u. u = s)
    (\t. lookup_var counter t = SOME (n2w (k + 1)) /\
         t.vs_memory = s.vs_memory /\ typed_copy_state_frame sa off len s t) (\r. F)
Proof
  rpt strip_tac >> drule_all typed_copy_counter_increment_frag_mem >>
  disch_then (qspec_then `ctx` mp_tac) >>
  disch_then (mp_then Any irule frag_exec_mem_conseq) >> simp[] >>
  rpt strip_tac >> simp[typed_copy_state_frame_def] >>
  rpt strip_tac >> first_x_assum irule >>
  gvs[ci_mono_def, not_fresh_at_def] >> decide_tac
QED

Theorem typed_copy_two_ops_frag_mem[local]:
  !ctx opc1 args1 opc2 args2 a op1 b op2 c s w1 w2 off len.
    emit_op opc1 args1 a = (op1,b) /\ emit_op opc2 args2 b = (op2,c) /\
    opc1 <> INVOKE /\ opc1 <> DLOAD /\ opc1 <> DLOADBYTES /\ ~is_terminator opc1 /\
    opc2 <> INVOKE /\ opc2 <> DLOAD /\ opc2 <> DLOADBYTES /\ ~is_terminator opc2 /\
    (!out. inst_mem_below_frontier (mk_inst a.cs_next_id opc1 args1 [out]) s) /\
    (!t out. t.vs_memory = s.vs_memory /\ typed_copy_state_frame a off len s t ==>
       inst_mem_below_frontier (mk_inst b.cs_next_id opc2 args2 [out]) t) /\
    (!out. step_inst_base (mk_inst a.cs_next_id opc1 args1 [out]) s =
           OK (update_var out w1 s)) /\
    (!t out. t.vs_memory = s.vs_memory /\ typed_copy_state_frame a off len s t ==>
       step_inst_base (mk_inst b.cs_next_id opc2 args2 [out]) t =
       OK (update_var out w2 t)) ==>
    frag_exec_mem ctx a c (\u. u = s)
      (\t. eval_operand op1 t = SOME w1 /\ eval_operand op2 t = SOME w2 /\
           t.vs_memory = s.vs_memory /\ typed_copy_state_frame a off len s t) (\r. F)
Proof
  rpt strip_tac >>
  `ci_mono a b /\ ci_mono b c` by metis_tac[typed_copy_emit_op_mono] >>
  `!x. op1 = Var x ==> not_fresh_at b x` by metis_tac[typed_copy_emit_op_fresh] >>
  `frag_exec_mem ctx a b (\u. u = s)
     (\t. eval_operand op1 t = SOME w1 /\ t.vs_memory = s.vs_memory /\
          typed_copy_state_frame a off len s t) (\r. F)` by
    (irule typed_copy_emit_op_frag_mem >> goal_assum (drule_at Any) >> simp[]) >>
  drule frag_exec_mem_then >> disch_then irule >> conj_tac
  >- (simp[] >> rpt strip_tac >>
      `frag_exec_mem ctx b c (\u. u = t)
        (\u. eval_operand op2 u = SOME w2 /\ u.vs_memory = t.vs_memory /\
             typed_copy_state_frame b off len t u) (\r. F)` by
        (irule typed_copy_emit_op_frag_mem >> qexistsl_tac [`args2`, `opc2`] >> simp[]) >>
      pop_assum (mp_then Any irule frag_exec_mem_conseq) >> simp[] >> rpt gen_tac >> strip_tac >>
      conj_tac >- metis_tac[typed_copy_state_frame_operand] >>
      irule typed_copy_state_frame_trans >> qexists_tac `t` >> simp[] >>
      irule typed_copy_state_frame_mono >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[ci_mono_def]
QED

Theorem typed_copy_index_offsets_frag_mem[local]:
  !ctx counter ss ds a so b doff c s k off len.
    emit_op MUL [Var counter; Lit (n2w ss)] a = (so,b) /\
    emit_op MUL [Var counter; Lit (n2w ds)] b = (doff,c) /\
    not_fresh_at a counter /\ lookup_var counter s = SOME (n2w k) ==>
    frag_exec_mem ctx a c (\u. u = s)
      (\t. eval_operand so t = SOME (n2w (k * ss)) /\
           eval_operand doff t = SOME (n2w (k * ds)) /\
           t.vs_memory = s.vs_memory /\ typed_copy_state_frame a off len s t) (\r. F)
Proof
  rpt strip_tac >> irule typed_copy_two_ops_frag_mem >>
  qexistsl_tac [`[Var counter; Lit (n2w ss)]`, `[Var counter; Lit (n2w ds)]`,
               `b`, `MUL`, `MUL`] >>
  simp[venomInstTheory.is_terminator_def, below_frontier_no_ranges, mk_inst_def] >> conj_tac
  >- (rewrite_tac[GSYM word_mul_n2w, GSYM mk_inst_def] >>
      rpt gen_tac >> irule step_MUL >> simp[eval_operand_def]) >>
  rpt strip_tac >>
  `lookup_var counter t = SOME (n2w k)` by gvs[typed_copy_state_frame_def] >>
  simp[step_inst_base_def, mk_inst_def, exec_pure2_def, eval_operand_def] >>
  simp[word_mul_n2w]
QED

Theorem typed_copy_index_adds_frag_mem[local]:
  !ctx src dst so doff sw dw sv dv a sp b dp c s off len.
    emit_op ADD [src;so] a = (sp,b) /\
    emit_op ADD [dst;doff] b = (dp,c) /\
    (!x. dst = Var x ==> not_fresh_at a x) /\
    (!x. doff = Var x ==> not_fresh_at a x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    eval_operand so s = SOME sv /\ eval_operand doff s = SOME dv ==>
    frag_exec_mem ctx a c (\u. u = s)
      (\t. eval_operand sp t = SOME (sw + sv) /\
           eval_operand dp t = SOME (dw + dv) /\
           t.vs_memory = s.vs_memory /\ typed_copy_state_frame a off len s t) (\r. F)
Proof
  rpt strip_tac >> irule typed_copy_two_ops_frag_mem >>
  qexistsl_tac [`[src;so]`, `[dst;doff]`, `b`, `ADD`, `ADD`] >>
  simp[venomInstTheory.is_terminator_def, below_frontier_no_ranges, mk_inst_def] >> conj_tac
  >- (gen_tac >> rewrite_tac[step_inst_base_def] >> simp[exec_pure2_def]) >>
  rpt strip_tac >>
  `eval_operand dst t = SOME dw /\ eval_operand doff t = SOME dv` by
    metis_tac[typed_copy_state_frame_operand] >>
  rewrite_tac[step_inst_base_def] >> simp[exec_pure2_def]
QED

Theorem typed_copy_index_addresses_frag_mem:
  !ctx counter ss ds src dst a so b doff c sp d dp e s sw dw k off len.
    emit_op MUL [Var counter; Lit (n2w ss)] a = (so,b) /\
    emit_op MUL [Var counter; Lit (n2w ds)] b = (doff,c) /\
    emit_op ADD [src;so] c = (sp,d) /\ emit_op ADD [dst;doff] d = (dp,e) /\
    not_fresh_at a counter /\ lookup_var counter s = SOME (n2w k) /\
    (!x. src = Var x ==> not_fresh_at a x) /\
    (!x. dst = Var x ==> not_fresh_at a x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw ==>
    frag_exec_mem ctx a e (\u. u = s)
      (\t. eval_operand sp t = SOME (sw + n2w (k * ss)) /\
           eval_operand dp t = SOME (dw + n2w (k * ds)) /\
           t.vs_memory = s.vs_memory /\ typed_copy_state_frame a off len s t) (\r. F)
Proof
  rpt strip_tac >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d /\ ci_mono d e` by
    metis_tac[typed_copy_emit_op_mono] >>
  `ci_mono a c /\ ci_mono c e` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  drule_all typed_copy_index_offsets_frag_mem >>
  disch_then (qspecl_then [`ctx`, `off`, `len`] mp_tac) >>
  disch_then (mp_then Any irule frag_exec_mem_then) >> conj_tac
  >- (simp[] >> rpt strip_tac >>
      `eval_operand src t = SOME sw /\ eval_operand dst t = SOME dw` by
        metis_tac[typed_copy_state_frame_operand] >>
      `!x. dst = Var x ==> not_fresh_at c x` by
        metis_tac[typed_copy_operand_fresh_mono] >>
      `!x. doff = Var x ==> not_fresh_at c x` by
        metis_tac[typed_copy_emit_op_fresh] >>
      drule_all typed_copy_index_adds_frag_mem >>
      disch_then (qspecl_then [`ctx`, `off`, `len`] mp_tac) >>
      disch_then (mp_then Any irule frag_exec_mem_conseq) >> simp[] >>
      rpt strip_tac >> irule typed_copy_state_frame_trans >>
      qexists_tac `t` >> simp[] >> irule typed_copy_state_frame_mono >>
      goal_assum (drule_at Any) >> simp[]) >>
  gvs[ci_mono_def]
QED

Theorem typed_copy_dyn_check_frag_mem:
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
          eval_operand_def, w2n_n2w, LESS_MOD, bool_to_word_def] >>
     simp[NOT_LESS]) >>
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
