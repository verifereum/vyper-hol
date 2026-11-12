(* Same-endpoint postconditions for the bytestring continuation. *)
Theory assignBasePtrBytesPost
Ancestors assignBasePtrBytesCopy assignBasePtrMcopyTransport typedMemoryCopy
  typedCopyPtr venomState venomExecSemantics ptrDiscipline bodyPtrDefs
  emitHelper venomInst words valueEncoding valueEncodingProps

Theorem assign_base_bytes_mcopy_post:
  !dst src out q s b a n id u tn tf PG G sa tv v ix.
    eval_operand dst q = SOME b /\ eval_operand src q = SOME a /\
    eval_operand out q = SOME n /\
    u = mcopy (w2n b) (w2n a) (w2n n) q /\
    tf = step_taint (mk_inst id MCOPY [dst;src;out] []) q u tn /\
    (q with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
    val_wf tv v /\ val_footprint tv v <= w2n n /\
    (!m. mem_agree_outside tn.t_mem q.vs_memory m ==>
         val_in_memory tv v (w2n a) m) ==>
    typed_copy_state_frame sa (w2n b) (w2n n) s
      (u with vs_inst_idx := ix) /\
    (!m. mem_agree_outside tf.t_mem u.vs_memory m ==>
         val_in_memory tv v (w2n b) m) /\
    (!i. i < w2n n ==> (w2n b + i IN tf.t_mem <=> w2n a + i IN tn.t_mem)) /\
    (!i. i < w2n b \/ w2n b + w2n n <= i ==>
         (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    step_prov PG G (mk_inst id MCOPY [dst;src;out] []) u = G /\
    tf.t_var = tn.t_var /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    tf.t_imm = tn.t_imm /\
    (!x. lookup_var x (u with vs_inst_idx := ix) = lookup_var x q) /\
    (!i. i < w2n b \/ w2n b + w2n n <= i ==>
         mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all (Q.SPECL [`dst`, `src`] assign_base_mcopy_taint_window) >> strip_tac >>
  drule_all (Q.SPECL [`dst`, `src`] assign_base_mcopy_endpoint_frame) >>
  disch_then (qspecl_then [`PG`, `G`] strip_assume_tac) >>
  simp[] >> conj_tac
  >- (irule typed_copy_state_frame_trans >>
      qexists_tac `q` >> reverse conj_tac
      >- simp[typed_copy_mcopy_state_frame] >>
      simp[typed_copy_state_frame_def] >>
      fs[venom_state_component_equality]) >>
  conj_tac
  >- (rpt strip_tac >> irule assign_base_mcopy_robust_destination >>
      rpt (goal_assum (drule_at Any)) >> simp[] >> qexists_tac `id` >> simp[]) >>
  gvs[] >> conj_tac >- metis_tac[] >>
  conj_tac >- simp[step_taint_def, mk_inst_def, set_var_taint_def, imm_taint_def] >>
  rpt strip_tac >>
  `q.vs_memory = s.vs_memory` by fs[venom_state_component_equality] >>
  qpat_x_assum `q.vs_memory = s.vs_memory`
    (fn th => pure_rewrite_tac[GSYM th]) >>
  irule mcopy_mem_bytes_at_disjoint >> decide_tac
QED

Theorem assign_base_store_bytestring_robust_counted:
  !src dst sa sb fn s a d len G tn D ctx PG tv v.
    compile_store_bytestring (Var src) (Var dst) sa = ((),sb) /\
    fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
    ~ctx_has_dalloca ctx /\ not_fresh_at sa src /\ not_fresh_at sa dst /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME d /\
    mload (w2n a) s = n2w len /\
    32 + 32 * word_size len < dimword (:256) /\
    ptr_covers G tn src s 32 /\
    ptr_covers G tn src s (32 + 32 * word_size len) /\
    ptr_covers G tn dst s (32 + 32 * word_size len) /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
    val_wf tv v /\ val_footprint tv v <= 32 + 32 * word_size len /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
         val_in_memory tv v (w2n a) m) ==>
    ?Gf tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
      u.vs_prev_bb = s.vs_prev_bb /\
      typed_copy_state_frame sa (w2n d) (32 + 32 * word_size len) s u /\
      (!m. mem_agree_outside tf.t_mem u.vs_memory m ==>
           val_in_memory tv v (w2n d) m) /\
      (!i. i < 32 + 32 * word_size len ==>
           (w2n d + i IN tf.t_mem <=> w2n a + i IN tn.t_mem)) /\
      (!i. i < w2n d \/ w2n d + (32 + 32 * word_size len) <= i ==>
           (i IN tf.t_mem <=> i IN tn.t_mem)) /\
      tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      (!p. not_fresh_at sa p ==>
        lookup_var p u = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tf (Var p) = op_taint tn (Var p)) /\
      (!i. i < w2n d \/ w2n d + (32 + 32 * word_size len) <= i ==>
        mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory)
Proof
  rpt strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (drule assign_base_store_bytestring_split >> strip_tac >>
     drule_all assign_base_store_bytestring_layout >> strip_tac >> simp[]) >>
  drule_all assign_base_store_bytestring_counted >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  `eval_operand (Var dst) q = SOME d /\ eval_operand (Var src) q = SOME a` by
    (simp[eval_operand_def] >> metis_tac[]) >>
  `q.vs_memory = s.vs_memory /\
   q.vs_current_bb = sb.cs_current_bb /\ ~q.vs_halted` by
    (qpat_x_assum `q with vs_vars := _ = _` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  qabbrev_tac `u = mcopy (w2n d) (w2n a) (32 + 32 * word_size len) q` >>
  qabbrev_tac `tf = step_taint
    (mk_inst sm.cs_next_id MCOPY [Var dst;Var src;out] []) q u tn1` >>
  `u = mcopy (w2n d) (w2n a) (w2n (n2w (32 + 32 * word_size len) : bytes32)) q /\
   val_footprint tv v <= w2n (n2w (32 + 32 * word_size len) : bytes32) /\
   (!m. mem_agree_outside tn1.t_mem q.vs_memory m ==>
        val_in_memory tv v (w2n a) m)` by simp[Abbr `u`] >>
  `tf = step_taint (mk_inst sm.cs_next_id MCOPY [Var dst;Var src;out] []) q u tn1 /\
   (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s)` by
    (simp[Abbr `tf`] >> metis_tac[]) >>
  drule_all (Q.SPECL [`Var dst`, `Var src`] assign_base_bytes_mcopy_post) >>
  disch_then (qspecl_then [`PG`, `G1`, `LENGTH sb.cs_current_insts`] strip_assume_tac) >>
  `u.vs_current_bb = sb.cs_current_bb /\ ~u.vs_halted` by
    simp[Abbr `u`, mcopy_def, write_memory_with_expansion_def] >>
  `u.vs_prev_bb = s.vs_prev_bb` by
    (simp[Abbr `u`, mcopy_def, write_memory_with_expansion_def] >>
     qpat_x_assum `q with vs_vars := _ = s` mp_tac >>
     simp_tac (srw_ss()) [venom_state_component_equality]) >>
  qexistsl_tac [`G1`, `tf`, `u with vs_inst_idx := LENGTH sb.cs_current_insts`] >>
  qpat_x_assum `u = mcopy _ _ _ _` kall_tac >>
  qpat_x_assum `tf = step_taint _ _ _ _` kall_tac >>
  `!p. op_taint tf (Var p) = op_taint tn1 (Var p)` by simp[op_taint_def] >>
  gs[] >> rpt strip_tac >> metis_tac[]
QED
