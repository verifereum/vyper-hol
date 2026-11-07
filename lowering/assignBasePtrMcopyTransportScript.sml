(* Endpoint facts for the supplied MCOPY step; no second run is chosen. *)
Theory assignBasePtrMcopyTransport
Ancestors
  typedCopyPtr robustCopyTransportPtr assignBasePtrMcopy valueEncodingProps
  emitHelper venomInst venomState venomExecSemantics pred_set

Theorem assign_base_mcopy_endpoint:
  !dst src count_op s b a n id u.
    eval_operand dst s = SOME b /\ eval_operand src s = SOME a /\
    eval_operand count_op s = SOME n /\
    step_inst_base (mk_inst id MCOPY [dst;src;count_op] []) s = OK u ==>
    u = mcopy (w2n b) (w2n a) (w2n n) s
Proof
  rpt strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[mk_inst_def, eval_operand_def]
QED

Theorem assign_base_mcopy_taint_window:
  !dst src count_op s b a n id u tn tf.
    eval_operand dst s = SOME b /\ eval_operand src s = SOME a /\
    eval_operand count_op s = SOME n /\
    u = mcopy (w2n b) (w2n a) (w2n n) s /\
    tf = step_taint (mk_inst id MCOPY [dst;src;count_op] []) s u tn ==>
    (!i. i < w2n n ==> (w2n b + i IN tf.t_mem <=> w2n a + i IN tn.t_mem)) /\
    (!i. (i < w2n b \/ w2n b + w2n n <= i) ==>
         (i IN tf.t_mem <=> i IN tn.t_mem))
Proof
  rpt strip_tac >>
  `tf.t_mem =
     (tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + w2n n}) UNION
     {w2n b + i | i < w2n n /\ w2n a + i IN tn.t_mem}` by
    (asm_rewrite_tac[] >> irule (cj 5 mcopy_operand_ghost_frame) >> simp[]) >>
  gvs[IN_UNION, IN_DIFF, GSPECIFICATION] >>
  eq_tac >> strip_tac >> gvs[] >> decide_tac
QED

Theorem assign_base_mcopy_robust_destination:
  !dst src count_op s b a n id u tn tf tv v.
    eval_operand dst s = SOME b /\ eval_operand src s = SOME a /\
    eval_operand count_op s = SOME n /\
    u = mcopy (w2n b) (w2n a) (w2n n) s /\
    tf = step_taint (mk_inst id MCOPY [dst;src;count_op] []) s u tn /\
    val_wf tv v /\ val_footprint tv v <= w2n n /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
         val_in_memory tv v (w2n a) m) ==>
    !m. mem_agree_outside tf.t_mem u.vs_memory m ==>
        val_in_memory tv v (w2n b) m
Proof
  rpt strip_tac >>
  `!i. i < w2n n ==> (w2n b + i IN tf.t_mem <=> w2n a + i IN tn.t_mem)` by
    (match_mp_tac (cj 1 assign_base_mcopy_taint_window) >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`dst`, `src`, `count_op`] >> simp[]) >>
  irule robust_val_in_memory_copy_transport >> simp[] >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`s.vs_memory`, `w2n n`, `w2n a`, `tn.t_mem`] >>
  asm_rewrite_tac[mcopy_mem_bytes_at_same] >>
  rpt strip_tac >> gvs[]
QED

Theorem assign_base_mcopy_robust_exterior:
  !dst src count_op s b a n id u tn tf tv v p.
    eval_operand dst s = SOME b /\ eval_operand src s = SOME a /\
    eval_operand count_op s = SOME n /\
    u = mcopy (w2n b) (w2n a) (w2n n) s /\
    tf = step_taint (mk_inst id MCOPY [dst;src;count_op] []) s u tn /\
    val_wf tv v /\
    (p + val_footprint tv v <= w2n b \/ w2n b + w2n n <= p) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
         val_in_memory tv v p m) ==>
    !m. mem_agree_outside tf.t_mem u.vs_memory m ==>
        val_in_memory tv v p m
Proof
  rpt strip_tac >>
  `!i. (i < w2n b \/ w2n b + w2n n <= i) ==>
       (i IN tf.t_mem <=> i IN tn.t_mem)` by
    (match_mp_tac (cj 2 assign_base_mcopy_taint_window) >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`dst`, `src`, `count_op`] >> simp[]) >>
  irule robust_val_in_memory_exterior_frame >> simp[] >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`s.vs_memory`, `tn.t_mem`,
    `{i | w2n b <= i /\ i < w2n b + w2n n}`] >>
  simp[] >>
  (conj_tac
   >- (rpt strip_tac >> gvs[])
   >> rpt strip_tac >> irule mcopy_mem_bytes_at_disjoint >> decide_tac)
QED

Theorem assign_base_mcopy_endpoint_frame:
  !dst src count_op s b a n id u tn tf PG G.
    eval_operand dst s = SOME b /\ eval_operand src s = SOME a /\
    eval_operand count_op s = SOME n /\
    u = mcopy (w2n b) (w2n a) (w2n n) s /\
    tf = step_taint (mk_inst id MCOPY [dst;src;count_op] []) s u tn ==>
    step_prov PG G (mk_inst id MCOPY [dst;src;count_op] []) u = G /\
    tf.t_var = tn.t_var /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!x ix. lookup_var x (u with vs_inst_idx := ix) = lookup_var x s) /\
    mem_bytes_at (w2n b) (w2n n) u.vs_memory =
      mem_bytes_at (w2n a) (w2n n) s.vs_memory
Proof
  rpt gen_tac >> strip_tac >> asm_rewrite_tac[] >>
  rpt conj_tac
  >- (irule (cj 1 mcopy_operand_ghost_frame) >> simp[])
  >- (irule (cj 2 mcopy_operand_ghost_frame) >> simp[])
  >- (irule (cj 3 mcopy_operand_ghost_frame) >> simp[])
  >- (irule (cj 4 mcopy_operand_ghost_frame) >> simp[])
  >- simp[lookup_var_def, mcopy_def, write_memory_with_expansion_def] >>
  simp[mcopy_mem_bytes_at_same]
QED

Theorem assign_base_mcopy_exterior_bytes:
  !s b a n u i.
    u = mcopy (w2n b) (w2n a) (w2n n) s /\
    (i < w2n b \/ w2n b + w2n n <= i) ==>
    mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory
Proof
  rpt strip_tac >> asm_rewrite_tac[] >>
  irule mcopy_mem_bytes_at_disjoint >> decide_tac
QED
