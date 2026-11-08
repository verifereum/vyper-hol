(* Task-owned operational invariant for array return normalization. *)
Theory externalReturnCopyArrayLoop
Ancestors
  externalReturnCopyTransport externalReturnCopyFrame loweringPosts
  valueEncoding valueEncodingDefs valueEncodingProps venomState compileEnv loweringStateRelDefs arithmetic
  fragExec emitHelper emitHelperProps context venomExecSemantics venomInst
  words finite_map exprLoweringProps pair

Definition return_copy_index_prefix_def:
  return_copy_index_prefix f tv dst k mem <=>
    !i. i < k ==> val_in_memory tv (f i)
      (dst + i * type_memory_size tv) mem
End

Definition return_copy_index_inv_def:
  return_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k t <=>
    k <= N /\ lookup_var counter t = SOME (n2w k) /\
    eval_operand src t = SOME sw /\ eval_operand dst t = SOME dw /\
    (!i. i < N ==> val_in_memory stv (f i)
      (w2n sw + i * type_memory_size stv) t.vs_memory) /\
    return_copy_index_prefix f dtv (w2n dw) k t.vs_memory /\
    return_copy_frame sa (w2n dw) (N * type_memory_size dtv) s0 t
End

Theorem return_copy_index_inv_jump:
  return_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k t ==>
  return_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k (jump_to l t)
Proof
  simp[return_copy_index_inv_def, jump_to_def, lookup_var_def,
       return_copy_frame_jump]
QED

Theorem return_copy_preserves_conditional_source:
  return_copy_frame sa dst len s t /\
  val_in_memory tv v src s.vs_memory /\ val_wf tv v /\
  (0 < val_footprint tv v ==>
    src + val_footprint tv v <= dst \/ dst + len <= src) ==>
  val_in_memory tv v src t.vs_memory
Proof
  strip_tac >> Cases_on `val_footprint tv v = 0`
  >- (irule return_memory_footprint_agree >> simp[] >>
      qexists_tac `s.vs_memory` >> simp[mem_bytes_at_def]) >>
  irule return_copy_preserves_source >> simp[] >>
  qexistsl_tac [`len`, `dst`, `s`, `sa`] >> simp[]
QED

Theorem return_copy_index_source_frame:
  (!i. i < N ==> val_in_memory stv (f i)
      (so + i * type_memory_size stv) s.vs_memory /\ val_wf stv (f i)) /\
  (!i. i < N /\ 0 < val_footprint stv (f i) ==>
    so + i * type_memory_size stv + val_footprint stv (f i) <= dst \/
    dst + len <= so + i * type_memory_size stv) /\
  return_copy_frame sa dst len s t ==>
  !i. i < N ==> val_in_memory stv (f i)
    (so + i * type_memory_size stv) t.vs_memory
Proof
  rpt strip_tac >> irule return_copy_preserves_conditional_source >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`dst`, `len`, `s`, `sa`] >> simp[] >> metis_tac[]
QED

Theorem return_copy_emit_op_frag:
  !ctx opc args a op b s w off len.
    emit_op opc args a = (op,b) /\
    opc <> INVOKE /\ ~is_terminator opc /\
    (!out. step_inst_base (mk_inst a.cs_next_id opc args [out]) s =
           OK (update_var out w s)) ==>
    frag_exec ctx a b (\u. u = s)
      (\t. eval_operand op t = SOME w /\ t.vs_memory = s.vs_memory /\
           return_copy_frame a off len s t) (\r. F)
Proof
  rpt strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_same_blocks >> strip_tac >>
  irule frag_exec_run_inst_seq >> gvs[same_blocks_def] >>
  simp[mk_inst_def, run_inst_seq_def] >>
  simp[eval_operand_def, lookup_var_update_var, return_copy_frame_def,
       update_var_def, lookup_var_def, venom_state_component_equality] >>
  simp[FLOOKUP_UPDATE] >> rpt strip_tac >>
  `x <> STRING #"%" (toString a.cs_next_var)` by
    (gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  simp[FLOOKUP_UPDATE]
QED

Theorem return_copy_emit_op_mono:
  emit_op opc args a = (op,b) ==> ci_mono a b
Proof
  strip_tac >> qspecl_then [`opc`, `args`, `a`] mp_tac ci_mono_emit_op >> simp[]
QED

Theorem return_copy_header_frag:
  !ctx counter N k a lt b done c s off len.
    emit_op LT [Var counter; Lit (n2w N)] a = (lt,b) /\
    emit_op ISZERO [lt] b = (done,c) /\
    not_fresh_at a counter /\ lookup_var counter s = SOME (n2w k) /\
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
     simp[venomInstTheory.is_terminator_def, step_inst_base_def, mk_inst_def, exec_pure2_def,
          eval_operand_def, w2n_n2w, LESS_MOD]) >>
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

Theorem return_copy_assign_frag:
  !ctx op counter a b s w.
    emit_inst ASSIGN [op] [counter] a = ((),b) /\
    eval_operand op s = SOME w ==>
    frag_exec ctx a b (\u. u = s)
      (\t. lookup_var counter t = SOME w /\ t.vs_memory = s.vs_memory /\
        (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                  vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
                  vs_inst_idx := s.vs_inst_idx|>) = s /\
        (!x. x <> counter ==> lookup_var x t = lookup_var x s)) (\r. F)
Proof
  rpt strip_tac >>
  qpat_x_assum `emit_inst _ _ _ _ = _` mp_tac >>
  simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >> strip_tac >>
  gvs[] >> irule frag_exec_run_inst_seq >>
  simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND,
       mk_inst_def, venomInstTheory.is_terminator_def] >>
  simp[run_inst_seq_def, step_inst_base_def, mk_inst_def] >>
  simp[lookup_var_update_var, update_var_def, lookup_var_def,
       FLOOKUP_UPDATE, venom_state_component_equality] >>
  rpt strip_tac >> simp[FLOOKUP_UPDATE]
QED

Theorem return_copy_counter_increment_frag:
  !ctx counter k a inc b c s.
    emit_op ADD [Var counter; Lit 1w] a = (inc,b) /\
    emit_inst ASSIGN [inc] [counter] b = ((),c) /\
    not_fresh_at a counter /\ lookup_var counter s = SOME (n2w k) /\
    k + 1 < dimword (:256) ==>
    frag_exec ctx a c (\u. u = s)
      (\t. lookup_var counter t = SOME (n2w (k + 1)) /\
        t.vs_memory = s.vs_memory /\
        (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                  vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
                  vs_inst_idx := s.vs_inst_idx|>) = s /\
        (!x. not_fresh_at a x /\ x <> counter ==>
             lookup_var x t = lookup_var x s)) (\r. F)
Proof
  rpt strip_tac >>
  `frag_exec ctx a b (\u. u = s)
     (\t. eval_operand inc t = SOME (n2w (k + 1)) /\
          t.vs_memory = s.vs_memory /\
          return_copy_frame a 0 0 s t) (\r. F)` by
    (irule return_copy_emit_op_frag >> simp[venomInstTheory.is_terminator_def] >>
     goal_assum (drule_at Any) >>
     simp[venomInstTheory.is_terminator_def, step_inst_base_def, mk_inst_def,
          exec_pure2_def, eval_operand_def, word_add_n2w]) >>
  drule frag_exec_then >> disch_then irule >> conj_tac
  >- (rpt strip_tac >> fs[] >> drule_all return_copy_assign_frag >>
      disch_then (qspec_then `ctx` mp_tac) >>
      disch_then (mp_then Any irule frag_exec_conseq) >>
      simp[] >> rpt strip_tac >>
      gvs[return_copy_frame_def, venom_state_component_equality]) >>
  `ci_mono a b` by metis_tac[return_copy_emit_op_mono] >>
  qspecl_then [`ASSIGN`, `[inc]`, `[counter]`, `b`] mp_tac ci_mono_emit_inst >>
  simp[] >> gvs[ci_mono_def]
QED

Theorem return_copy_counter_init_frag:
  !ctx counter a b s off len.
    emit_inst ASSIGN [Lit 0w] [counter] a = ((),b) /\
    (!x. not_fresh_at a x ==> x <> counter) ==>
    frag_exec ctx a b (\u. u = s)
      (\t. lookup_var counter t = SOME 0w /\ t.vs_memory = s.vs_memory /\
           return_copy_frame a off len s t) (\r. F)
Proof
  rpt strip_tac >>
  `eval_operand (Lit 0w) s = SOME 0w` by simp[eval_operand_def] >>
  drule_all return_copy_assign_frag >> disch_then (qspec_then `ctx` mp_tac) >>
  disch_then (mp_then Any irule frag_exec_conseq) >>
  simp[return_copy_frame_def] >> rpt strip_tac >> simp[]
QED

Theorem return_copy_index_prefix_step:
  return_copy_index_prefix f tv dst k s.vs_memory /\
  (!i. i < k ==> val_wf tv (f i)) /\
  return_copy_frame sa (dst + k * type_memory_size tv)
    (type_memory_size tv) s t /\
  val_in_memory tv (f k) (dst + k * type_memory_size tv) t.vs_memory ==>
  return_copy_index_prefix f tv dst (k + 1) t.vs_memory
Proof
  simp[return_copy_index_prefix_def] >> rpt strip_tac >>
  Cases_on `i = k` >- gvs[] >>
  `i < k` by decide_tac >>
  irule return_copy_preserves_conditional_source >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`dst + k * type_memory_size tv`, `type_memory_size tv`, `s`, `sa`] >>
  simp[] >> strip_tac >> disj1_tac >>
  `val_footprint tv (f i) <= type_memory_size tv` by
    metis_tac[return_footprint_le_layout] >>
  `dst + i * type_memory_size tv + type_memory_size tv <=
   dst + k * type_memory_size tv` by
    metis_tac[return_copy_array_child_window] >>
  decide_tac
QED

Theorem return_copy_index_inv_preserve:
  return_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k s /\
  ci_mono sa a /\ not_fresh_at a counter /\
  (!x. src = Var x ==> not_fresh_at a x) /\
  (!x. dst = Var x ==> not_fresh_at a x) /\
  return_copy_frame a off len s t /\ t.vs_memory = s.vs_memory ==>
  return_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k t
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `lookup_var counter t = lookup_var counter s` by
    gvs[return_copy_frame_def] >>
  `eval_operand src t = eval_operand src s /\
   eval_operand dst t = eval_operand dst s` by
    metis_tac[return_copy_frame_operand] >>
  gvs[return_copy_index_inv_def] >>
  irule return_copy_frame_trans >> qexists_tac `s` >> simp[] >>
  irule return_copy_frame_mono >> qexists_tac `a` >> simp[] >>
  gvs[return_copy_frame_def]
QED

Theorem return_copy_index_header_frag:
  emit_op LT [Var counter; Lit (n2w N)] a = (lt,b) /\
  emit_op ISZERO [lt] b = (done,c) /\ ci_mono sa a /\
  not_fresh_at a counter /\
  (!x. src = Var x ==> not_fresh_at a x) /\
  (!x. dst = Var x ==> not_fresh_at a x) /\ N < dimword (:256) ==>
  frag_exec ctx a c
    (return_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k)
    (\t. return_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k t /\
         eval_operand done t = SOME (if k < N then 0w else 1w)) (\r. F)
Proof
  rpt strip_tac >> irule frag_exec_pointwise >> qx_gen_tac `s` >> strip_tac >>
  `k <= N /\ lookup_var counter s = SOME (n2w k)` by
    gvs[return_copy_index_inv_def] >>
  drule_all return_copy_header_frag >>
  disch_then (qspecl_then [`ctx`, `w2n dw`, `N * type_memory_size dtv`] mp_tac) >>
  disch_then (mp_then Any irule frag_exec_conseq) >> simp[] >>
  rpt strip_tac >> irule return_copy_index_inv_preserve >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]
QED

Theorem return_copy_index_inv_step:
  return_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k s /\
  k < N /\
  (!i. i < N ==> val_wf stv (f i) /\ val_wf dtv (f i)) /\
  (!i. i < N /\ 0 < val_footprint stv (f i) ==>
    w2n sw + i * type_memory_size stv + val_footprint stv (f i) <= w2n dw \/
    w2n dw + N * type_memory_size dtv <= w2n sw + i * type_memory_size stv) /\
  return_copy_frame sa (w2n dw + k * type_memory_size dtv)
    (type_memory_size dtv) s t /\
  val_in_memory dtv (f k) (w2n dw + k * type_memory_size dtv) t.vs_memory /\
  lookup_var counter t = SOME (n2w (k + 1)) /\
  eval_operand src t = SOME sw /\ eval_operand dst t = SOME dw ==>
  return_copy_index_inv sa counter src dst sw dw f stv dtv N s0 (k + 1) t
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `return_copy_frame sa (w2n dw) (N * type_memory_size dtv) s t` by
    (irule return_copy_frame_subinterval >>
     qexistsl_tac [`w2n dw + k * type_memory_size dtv`, `type_memory_size dtv`] >>
     `w2n dw + k * type_memory_size dtv + type_memory_size dtv <=
       w2n dw + N * type_memory_size dtv` by
       metis_tac[return_copy_array_child_window] >> simp[] >> decide_tac) >>
  `!i. i < N ==> val_in_memory stv (f i)
    (w2n sw + i * type_memory_size stv) t.vs_memory` by
    (rpt strip_tac >> irule return_copy_preserves_conditional_source >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`w2n dw`, `N * type_memory_size dtv`, `s`, `sa`] >>
     gvs[return_copy_index_inv_def] >> metis_tac[]) >>
  `return_copy_index_prefix f dtv (w2n dw) (k + 1) t.vs_memory` by
    (irule return_copy_index_prefix_step >>
     conj_tac >- metis_tac[LESS_TRANS] >> conj_tac >- simp[] >>
     qexistsl_tac [`s`, `sa`] >> gvs[return_copy_index_inv_def]) >>
  gvs[return_copy_index_inv_def] >>
  irule return_copy_frame_trans >> qexists_tac `s` >> simp[]
QED

Theorem return_copy_index_init_frag:
  fresh_label "typed_sa_cond" sa = (hdr,l1) /\
  fresh_label "typed_sa_body" l1 = (blabel,l2) /\
  fresh_label "typed_sa_exit" l2 = (exit,l3) /\
  fresh_var l3 = (counter,init) /\
  emit_inst ASSIGN [Lit 0w] [counter] init = ((),st0) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  (!i. i < N ==> val_in_memory stv (f i)
     (w2n sw + i * type_memory_size stv) s.vs_memory) ==>
  frag_exec ctx sa st0 (\u. u = s)
    (return_copy_index_inv sa counter src dst sw dw f stv dtv N s 0) (\r. F)
Proof
  rpt strip_tac >>
  `~not_fresh_at sa counter /\ sa.cs_current_bb = init.cs_current_bb /\
   sa.cs_current_insts = init.cs_current_insts /\ sa.cs_blocks = init.cs_blocks` by
    (gvs[fresh_label_def, fresh_var_def, not_fresh_at_def,
         ASCIInumbersTheory.toString_inj]) >>
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

Theorem return_copy_emit_op_fresh:
  emit_op opc args a = (op,b) ==>
  (!x. op = Var x ==> not_fresh_at b x)
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
       emit_def, emit_inst_def, fresh_id_def, comp_return_def] >>
  rpt strip_tac >> gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj]
QED

Theorem return_copy_two_ops_frag:
  !ctx opc1 args1 opc2 args2 a op1 b op2 c s w1 w2 off len.
    emit_op opc1 args1 a = (op1,b) /\ emit_op opc2 args2 b = (op2,c) /\
    opc1 <> INVOKE /\ ~is_terminator opc1 /\
    opc2 <> INVOKE /\ ~is_terminator opc2 /\
    (!out. step_inst_base (mk_inst a.cs_next_id opc1 args1 [out]) s =
           OK (update_var out w1 s)) /\
    (!t out. t.vs_memory = s.vs_memory /\ return_copy_frame a off len s t ==>
       step_inst_base (mk_inst b.cs_next_id opc2 args2 [out]) t =
       OK (update_var out w2 t)) ==>
    frag_exec ctx a c (\u. u = s)
      (\t. eval_operand op1 t = SOME w1 /\ eval_operand op2 t = SOME w2 /\
           t.vs_memory = s.vs_memory /\ return_copy_frame a off len s t) (\r. F)
Proof
  rpt strip_tac >>
  `ci_mono a b /\ ci_mono b c` by metis_tac[return_copy_emit_op_mono] >>
  `!x. op1 = Var x ==> not_fresh_at b x` by metis_tac[return_copy_emit_op_fresh] >>
  `frag_exec ctx a b (\u. u = s)
     (\t. eval_operand op1 t = SOME w1 /\ t.vs_memory = s.vs_memory /\
          return_copy_frame a off len s t) (\r. F)` by
    (irule return_copy_emit_op_frag >> goal_assum (drule_at Any) >> simp[]) >>
  drule frag_exec_then >> disch_then irule >> conj_tac
  >- (simp[] >> rpt strip_tac >>
      `frag_exec ctx b c (\u. u = t)
        (\u. eval_operand op2 u = SOME w2 /\ u.vs_memory = t.vs_memory /\
             return_copy_frame b off len t u) (\r. F)` by
        (irule return_copy_emit_op_frag >> qexistsl_tac [`args2`, `opc2`] >> simp[]) >>
      pop_assum (mp_then Any irule frag_exec_conseq) >> simp[] >> rpt gen_tac >> strip_tac >>
      conj_tac
      >- metis_tac[return_copy_frame_operand] >>
      irule return_copy_frame_trans >> qexists_tac `t` >> simp[] >>
      irule return_copy_frame_mono >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[ci_mono_def]
QED

Theorem return_copy_index_offsets_frag:
  !ctx counter ss ds a so b doff c s k off len.
    emit_op MUL [Var counter; Lit (n2w ss)] a = (so,b) /\
    emit_op MUL [Var counter; Lit (n2w ds)] b = (doff,c) /\
    not_fresh_at a counter /\ lookup_var counter s = SOME (n2w k) ==>
    frag_exec ctx a c (\u. u = s)
      (\t. eval_operand so t = SOME (n2w (k * ss)) /\
           eval_operand doff t = SOME (n2w (k * ds)) /\
           t.vs_memory = s.vs_memory /\ return_copy_frame a off len s t) (\r. F)
Proof
  rpt strip_tac >> irule return_copy_two_ops_frag >>
  qexistsl_tac [`[Var counter; Lit (n2w ss)]`, `[Var counter; Lit (n2w ds)]`,
               `b`, `MUL`, `MUL`] >>
  simp[venomInstTheory.is_terminator_def] >> conj_tac
  >- (rewrite_tac[GSYM word_mul_n2w] >> rpt gen_tac >> irule step_MUL >>
      simp[eval_operand_def]) >>
  rpt strip_tac >>
  `lookup_var counter t = SOME (n2w k)` by gvs[return_copy_frame_def] >>
  simp[mk_inst_def] >> simp[step_inst_base_def] >>
  simp[exec_pure2_def, eval_operand_def] >>
  simp[word_mul_n2w]
QED

Theorem return_copy_index_adds_frag:
  !ctx src dst so doff sw dw sv dv a sp b dp c s off len.
    emit_op ADD [src;so] a = (sp,b) /\
    emit_op ADD [dst;doff] b = (dp,c) /\
    (!x. dst = Var x ==> not_fresh_at a x) /\
    (!x. doff = Var x ==> not_fresh_at a x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    eval_operand so s = SOME sv /\ eval_operand doff s = SOME dv ==>
    frag_exec ctx a c (\u. u = s)
      (\t. eval_operand sp t = SOME (sw + sv) /\
           eval_operand dp t = SOME (dw + dv) /\
           t.vs_memory = s.vs_memory /\ return_copy_frame a off len s t) (\r. F)
Proof
  rpt strip_tac >> irule return_copy_two_ops_frag >>
  qexistsl_tac [`[src;so]`, `[dst;doff]`, `b`, `ADD`, `ADD`] >>
  conj_tac
  >- (gen_tac >> rewrite_tac[mk_inst_def, step_inst_base_def] >>
      simp[exec_pure2_def]) >>
  simp[venomInstTheory.is_terminator_def] >> rpt strip_tac >>
  `eval_operand dst t = SOME dw /\ eval_operand doff t = SOME dv` by
    metis_tac[return_copy_frame_operand] >>
  rewrite_tac[mk_inst_def, step_inst_base_def] >> simp[exec_pure2_def]
QED

Theorem return_copy_index_addresses_frag:
  !ctx counter ss ds src dst a so b doff c sp d dp e s sw dw k off len.
    emit_op MUL [Var counter; Lit (n2w ss)] a = (so,b) /\
    emit_op MUL [Var counter; Lit (n2w ds)] b = (doff,c) /\
    emit_op ADD [src;so] c = (sp,d) /\ emit_op ADD [dst;doff] d = (dp,e) /\
    not_fresh_at a counter /\ lookup_var counter s = SOME (n2w k) /\
    (!x. src = Var x ==> not_fresh_at a x) /\
    (!x. dst = Var x ==> not_fresh_at a x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw ==>
    frag_exec ctx a e (\u. u = s)
      (\t. eval_operand sp t = SOME (sw + n2w (k * ss)) /\
           eval_operand dp t = SOME (dw + n2w (k * ds)) /\
           t.vs_memory = s.vs_memory /\ return_copy_frame a off len s t) (\r. F)
Proof
  rpt strip_tac >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d /\ ci_mono d e` by
    metis_tac[return_copy_emit_op_mono] >>
  `ci_mono a c /\ ci_mono c e` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  drule_all return_copy_index_offsets_frag >>
  disch_then (qspecl_then [`ctx`, `off`, `len`] mp_tac) >>
  disch_then (mp_then Any irule frag_exec_then) >> conj_tac
  >- (simp[] >> rpt strip_tac >>
      `eval_operand src t = SOME sw /\ eval_operand dst t = SOME dw` by
        metis_tac[return_copy_frame_operand] >>
      `!x. dst = Var x ==> not_fresh_at c x` by
        metis_tac[return_copy_operand_fresh_mono] >>
      `!x. doff = Var x ==> not_fresh_at c x` by
        metis_tac[return_copy_emit_op_fresh] >>
      drule_all return_copy_index_adds_frag >>
      disch_then (qspecl_then [`ctx`, `off`, `len`] mp_tac) >>
      disch_then (mp_then Any irule frag_exec_conseq) >> simp[] >>
      rpt strip_tac >> irule return_copy_frame_trans >>
      qexists_tac `t` >> simp[] >> irule return_copy_frame_mono >>
      goal_assum (drule_at Any) >> simp[]) >>
  gvs[ci_mono_def]
QED

Theorem return_copy_index_child_frag:
  emit_op MUL [Var counter; Lit (n2w (type_memory_size stv))] a = (so,b) /\
  emit_op MUL [Var counter; Lit (n2w (type_memory_size dtv))] b = (doff,c) /\
  emit_op ADD [src;so] c = (sp,d) /\ emit_op ADD [dst;doff] d = (dp,e) /\
  ci_mono e z /\ not_fresh_at a counter /\
  (!x. src = Var x ==> not_fresh_at a x) /\
  (!x. dst = Var x ==> not_fresh_at a x) /\
  lookup_var counter s = SOME (n2w k) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  val_wf stv v /\
  val_in_memory stv v (w2n sw + k * type_memory_size stv) s.vs_memory /\
  w2n dw + k * type_memory_size dtv + type_memory_size dtv < dimword (:256) /\
  (0 < val_footprint stv v ==>
    w2n sw + k * type_memory_size stv + val_footprint stv v < dimword (:256)) /\
  (!u. eval_operand dp u = SOME (dw + n2w (k * type_memory_size dtv)) /\
       eval_operand sp u = SOME (sw + n2w (k * type_memory_size stv)) /\
       val_in_memory stv v (w2n (sw + n2w (k * type_memory_size stv))) u.vs_memory ==>
       frag_exec ctx e z (\q. q = u)
         (\t. val_in_memory dtv v (w2n dw + k * type_memory_size dtv) t.vs_memory /\
           return_copy_frame e (w2n dw + k * type_memory_size dtv)
             (type_memory_size dtv) u t) (\r. F)) ==>
  frag_exec ctx a z (\u. u = s)
    (\t. val_in_memory dtv v (w2n dw + k * type_memory_size dtv) t.vs_memory /\
      return_copy_frame a (w2n dw + k * type_memory_size dtv)
        (type_memory_size dtv) s t) (\r. F)
Proof
  rpt gen_tac >> strip_tac >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d /\ ci_mono d e` by
    metis_tac[return_copy_emit_op_mono] >>
  `ci_mono a e` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  `val_in_memory stv v (w2n (sw + n2w (k * type_memory_size stv))) s.vs_memory` by
    (irule return_copy_source_offset >> simp[]) >>
  drule_all return_copy_index_addresses_frag >>
  disch_then (qspecl_then [`ctx`, `w2n dw + k * type_memory_size dtv`,
                          `type_memory_size dtv`] mp_tac) >>
  disch_then (mp_then Any irule frag_exec_then) >> conj_tac
  >- (simp[] >> rpt strip_tac >>
      `val_in_memory stv v (w2n (sw + n2w (k * type_memory_size stv))) t.vs_memory` by simp[] >>
      first_x_assum drule_all >>
      disch_then (mp_then Any irule frag_exec_conseq) >> simp[] >>
      rpt strip_tac >> irule return_copy_frame_trans >> qexists_tac `t` >> simp[] >>
      irule return_copy_frame_mono >> qexists_tac `e` >> simp[]) >>
  gvs[ci_mono_def] >> metis_tac[cs_extends_trans]
QED

Theorem return_copy_counter_increment_frame_frag:
  emit_op ADD [Var counter; Lit 1w] a = (inc,b) /\
  emit_inst ASSIGN [inc] [counter] b = ((),c) /\
  ci_mono sa a /\ ~not_fresh_at sa counter /\ not_fresh_at a counter /\
  lookup_var counter s = SOME (n2w k) /\ k + 1 < dimword (:256) ==>
  frag_exec ctx a c (\u. u = s)
    (\t. lookup_var counter t = SOME (n2w (k + 1)) /\
         t.vs_memory = s.vs_memory /\ return_copy_frame sa off len s t) (\r. F)
Proof
  rpt strip_tac >> drule_all return_copy_counter_increment_frag >>
  disch_then (qspec_then `ctx` mp_tac) >>
  disch_then (mp_then Any irule frag_exec_conseq) >> simp[] >>
  rpt strip_tac >> simp[return_copy_frame_def] >>
  rpt strip_tac >> first_x_assum irule >>
  gvs[ci_mono_def, not_fresh_at_def] >> decide_tac
QED

Theorem return_copy_sarray_slow_layout:
  fresh_label "typed_sa_cond" sa = (hdr,l1) /\
  fresh_label "typed_sa_body" l1 = (blabel,l2) /\
  fresh_label "typed_sa_exit" l2 = (exit,l3) /\
  fresh_var l3 = (counter,init) /\
  emit_inst ASSIGN [Lit 0w] [counter] init = ((),st0) /\
  emit_inst JMP [Label hdr] [] st0 = ((),st1) /\
  new_block hdr st1 = (u1,sth) /\
  emit_op LT [Var counter; Lit (n2w N)] sth = (lt,h1) /\
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

Theorem return_copy_index_body_frag:
  emit_op MUL [Var counter; Lit (n2w (type_memory_size stv))] a = (so,b) /\
  emit_op MUL [Var counter; Lit (n2w (type_memory_size dtv))] b = (doff,c) /\
  emit_op ADD [src;so] c = (sp,d) /\ emit_op ADD [dst;doff] d = (dp,e) /\
  ci_mono e z /\ ci_mono sa a /\ not_fresh_at a counter /\
  ~not_fresh_at sa counter /\
  emit_op ADD [Var counter; Lit 1w] z = (inc,j) /\
  emit_inst ASSIGN [inc] [counter] j = ((),last) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  return_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k s /\
  k < N /\ N < dimword (:256) /\
  (!i. i < N ==> val_wf stv (f i) /\ val_wf dtv (f i)) /\
  w2n dw + N * type_memory_size dtv < dimword (:256) /\
  (!i. i < N /\ 0 < val_footprint stv (f i) ==>
    w2n sw + i * type_memory_size stv + val_footprint stv (f i) < dimword (:256) /\
    (w2n sw + i * type_memory_size stv + val_footprint stv (f i) <= w2n dw \/
     w2n dw + N * type_memory_size dtv <= w2n sw + i * type_memory_size stv)) /\
  (!u. eval_operand dp u = SOME (dw + n2w (k * type_memory_size dtv)) /\
       eval_operand sp u = SOME (sw + n2w (k * type_memory_size stv)) /\
       val_in_memory stv (f k) (w2n (sw + n2w (k * type_memory_size stv))) u.vs_memory ==>
       frag_exec ctx e z (\q. q = u)
         (\t. val_in_memory dtv (f k) (w2n dw + k * type_memory_size dtv) t.vs_memory /\
           return_copy_frame e (w2n dw + k * type_memory_size dtv)
             (type_memory_size dtv) u t) (\r. F)) ==>
  frag_exec ctx a last (\u. u = s)
    (return_copy_index_inv sa counter src dst sw dw f stv dtv N s0 (k + 1)) (\r. F)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d /\ ci_mono d e /\ ci_mono z j` by
    metis_tac[return_copy_emit_op_mono] >>
  `ci_mono a e /\ ci_mono a z /\ ci_mono sa z` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  `not_fresh_at z counter` by
    (gvs[ci_mono_def, not_fresh_at_def] >> decide_tac) >>
  `!x. src = Var x ==> not_fresh_at a x` by
    metis_tac[return_copy_operand_fresh_mono] >>
  `!x. dst = Var x ==> not_fresh_at a x` by
    metis_tac[return_copy_operand_fresh_mono] >>
  `w2n dw + k * type_memory_size dtv + type_memory_size dtv < dimword (:256)` by
    (`w2n dw + k * type_memory_size dtv + type_memory_size dtv <=
       w2n dw + N * type_memory_size dtv` by
       metis_tac[return_copy_array_child_window] >> decide_tac) >>
  `frag_exec ctx a z (\u. u = s)
    (\t. val_in_memory dtv (f k) (w2n dw + k * type_memory_size dtv) t.vs_memory /\
      return_copy_frame a (w2n dw + k * type_memory_size dtv)
        (type_memory_size dtv) s t) (\r. F)` by
    (irule return_copy_index_child_frag >> simp[] >>
     qexistsl_tac [`b`, `c`, `counter`, `d`, `doff`, `dp`, `dst`, `e`, `so`, `sp`, `src`, `stv`, `sw`] >>
     gvs[return_copy_index_inv_def]) >>
  drule frag_exec_then >> disch_then irule >> conj_tac
  >- (simp[] >> rpt strip_tac >>
      `lookup_var counter t = SOME (n2w k)` by
        (gvs[return_copy_frame_def, return_copy_index_inv_def]) >>
      `k + 1 < dimword (:256)` by decide_tac >>
      `frag_exec ctx z last (\u. u = t)
        (\u. lookup_var counter u = SOME (n2w (k + 1)) /\
             u.vs_memory = t.vs_memory /\
             return_copy_frame sa (w2n dw + k * type_memory_size dtv)
               (type_memory_size dtv) t u) (\r. F)` by
        (irule return_copy_counter_increment_frame_frag >>
         simp[] >> qexistsl_tac [`j`, `inc`] >> simp[]) >>
      pop_assum (mp_then Any irule frag_exec_conseq) >> simp[] >>
      rpt strip_tac >> rename1 `lookup_var counter u = SOME (n2w (k + 1))` >>
      `return_copy_frame sa (w2n dw + k * type_memory_size dtv)
         (type_memory_size dtv) s t` by
        (irule return_copy_frame_mono >> qexists_tac `a` >> simp[]) >>
      `return_copy_frame sa (w2n dw + k * type_memory_size dtv)
         (type_memory_size dtv) s u` by
        (irule return_copy_frame_trans >> qexists_tac `t` >> simp[]) >>
      `eval_operand src u = SOME sw /\ eval_operand dst u = SOME dw` by
        (metis_tac[return_copy_frame_operand, return_copy_index_inv_def]) >>
      irule return_copy_index_inv_step >> simp[] >>
      qexists_tac `s` >> simp[]) >>
  `ci_mono j last` by metis_tac[ci_mono_emit_inst, SND] >>
  gvs[ci_mono_def] >> metis_tac[cs_extends_trans]
QED

Theorem return_copy_index_child_contract:
  compile_store_memory_typed cenv dp dty sp sty a = ((),b) /\
  (!x. dp = Var x ==> not_fresh_at a x) /\
  (!x. sp = Var x ==> not_fresh_at a x) /\
  k < N /\ val_wf stv (f k) /\
  w2n dw + N * type_memory_size dtv < dimword (:256) /\
  (0 < val_footprint stv (f k) ==>
    w2n sw + k * type_memory_size stv + val_footprint stv (f k) < dimword (:256) /\
    (w2n sw + k * type_memory_size stv + val_footprint stv (f k) <= w2n dw \/
     w2n dw + N * type_memory_size dtv <= w2n sw + k * type_memory_size stv)) /\
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
  !u. eval_operand dp u = SOME (dw + n2w (k * type_memory_size dtv)) /\
       eval_operand sp u = SOME (sw + n2w (k * type_memory_size stv)) /\
       val_in_memory stv (f k) (w2n (sw + n2w (k * type_memory_size stv))) u.vs_memory ==>
       frag_exec ctx a b (\q. q = u)
         (\t. val_in_memory dtv (f k) (w2n dw + k * type_memory_size dtv) t.vs_memory /\
           return_copy_frame a (w2n dw + k * type_memory_size dtv)
             (type_memory_size dtv) u t) (\r. F)
Proof
  rpt gen_tac >> strip_tac >>
  `w2n dw + k * type_memory_size dtv + type_memory_size dtv <=
     w2n dw + N * type_memory_size dtv` by
     metis_tac[return_copy_array_child_window] >>
  `w2n (dw + n2w (k * type_memory_size dtv)) = w2n dw + k * type_memory_size dtv` by
    (irule return_copy_offset_nonwrap >> decide_tac) >>
  `0 < val_footprint stv (f k) ==>
    w2n (sw + n2w (k * type_memory_size stv)) = w2n sw + k * type_memory_size stv` by
    (strip_tac >> irule return_copy_offset_nonwrap >> gvs[] >> decide_tac) >>
  rpt strip_tac >>
  qpat_assum `w2n (dw + _) = _` (fn th => once_rewrite_tac[GSYM th]) >>
  first_x_assum irule >> simp[] >>
  qexistsl_tac [`dp`, `sp`, `sw + n2w (k * type_memory_size stv)`] >>
  simp[] >> strip_tac >> gvs[] >> decide_tac
QED

Theorem return_copy_sarray_slow_frag:
  compile_copy_sarray_typed cenv dst dty src sty N sa = ((),sb) /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  ~(type_memory_size dtv = type_memory_size stv /\
    ~is_abi_dynamic cenv.ce_struct_fields dty) /\
  N < dimword (:256) /\
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
  frag_exec ctx sa sb (\u. u = s)
    (\t. (!i. i < N ==> val_in_memory dtv (f i)
       (w2n dw + i * type_memory_size dtv) t.vs_memory) /\
         return_copy_frame sa (w2n dw) (N * type_memory_size dtv) s t) (\r. F)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gnvs[]) >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> gnvs[] >>
  rename1 `fresh_label "typed_sa_cond" sa = (hdr,l1)` >>
  rename1 `fresh_label "typed_sa_body" l1 = (blabel,l2)` >>
  rename1 `fresh_label "typed_sa_exit" l2 = (exit,l3)` >>
  rename1 `fresh_var l3 = (counter,init)` >>
  rename1 `emit_inst ASSIGN [Lit 0w] [counter] init = ((),st0)` >>
  rename1 `emit_inst JMP [Label hdr] [] st0 = ((),st1)` >>
  rename1 `new_block hdr st1 = (u1,sth)` >>
  rename1 `emit_op LT [Var counter; Lit (n2w N)] sth = (lt,h1)` >>
  rename1 `emit_op ISZERO [lt] h1 = (done,stj)` >>
  rename1 `emit_inst JNZ [done; Label exit; Label blabel] [] stj = ((),st2)` >>
  rename1 `new_block blabel st2 = (u2,stb)` >>
  rename1 `emit_op MUL [Var counter; Lit (n2w (type_memory_size stv))] stb = (so,b1)` >>
  rename1 `emit_op MUL [Var counter; Lit (n2w (type_memory_size dtv))] b1 = (doff,b2)` >>
  rename1 `emit_op ADD [src;so] b2 = (sp,b3)` >>
  rename1 `emit_op ADD [dst;doff] b3 = (dp,b4)` >>
  rename1 `compile_store_memory_typed cenv dp dty sp sty b4 = ((),b5)` >>
  rename1 `emit_op ADD [Var counter; Lit 1w] b5 = (inc,b6)` >>
  rename1 `emit_inst ASSIGN [inc] [counter] b6 = ((),ste)` >>
  rename1 `emit_inst JMP [Label hdr] [] ste = ((),st3)` >>
  rename1 `new_block exit st3 = (u3,stx)` >>
  drule_all return_copy_sarray_slow_layout >> strip_tac >>
  `(!x. src = Var x ==> not_fresh_at sth x) /\
   (!x. dst = Var x ==> not_fresh_at sth x)` by
    metis_tac[return_copy_operand_fresh_mono] >>
  qmatch_goalsub_abbrev_tac `frag_exec ctx sa stx P Q R` >>
  qabbrev_tac `Inv = return_copy_index_inv sa counter src dst sw dw f stv dtv N s` >>
  qabbrev_tac `J = \k t. Inv k t /\ eval_operand done t = SOME (if k < N then 0w else 1w)` >>
  `frag_exec ctx sa st0 P (Inv 0) R` by
    (simp[Abbr `P`, Abbr `Inv`, Abbr `R`] >>
     irule return_copy_index_init_frag >> simp[] >>
     goal_assum (drule_at (Pat `fresh_var _ = _`)) >>
     goal_assum (drule_at (Pat `fresh_label "typed_sa_exit" _ = _`)) >>
     goal_assum (drule_at (Pat `fresh_label "typed_sa_body" _ = _`)) >>
     goal_assum (drule_at (Pat `fresh_label "typed_sa_cond" _ = _`)) >> simp[]) >>
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
     irule return_copy_index_header_frag >> simp[] >>
     goal_assum (drule_at (Pat `emit_op ISZERO _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op LT _ _ = _`)) >> simp[]) >>
  `cs_extends sa st0 /\ cs_extends st0 stx` by metis_tac[ci_mono_def] >>
  drule_all frag_exec_seq >>
  disch_then (mp_then Any irule frag_exec_conseq) >> simp[] >>
  simp[Abbr `J`, Abbr `Inv`, Abbr `Q`, return_copy_index_inv_def,
       return_copy_index_prefix_def]
QED

Resume return_copy_sarray_slow_frag[body]:
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
Finalise return_copy_sarray_slow_frag
