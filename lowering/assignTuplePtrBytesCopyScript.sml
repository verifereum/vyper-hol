(* Bytestring copy: reuse the raw MCOPY singleton and normalize only at
   the compiler boundary. Overlapping source and destination are allowed. *)
Theory assignTuplePtrBytesCopy
Ancestors
  assignTuplePtrCopyLen assignTuplePtrLocalFixedCopy
  typedCopyPtr fragGasSeqPtr bodyPtrDefs ptrDiscipline
  context compileEnv emitHelper emitHelperProps exprLoweringProps
  exprSimBufferStore vfmConstants fragExec
  venomState venomExecSemantics venomInst finite_map list arithmetic words

Theorem emit_mcopy_normalized_ptr:
  emit_void MCOPY [Var dst; Var src; count_op] sa = ((),sb) /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~ctx_has_dalloca ctx /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  eval_operand count_op s = SOME n /\ op_taint tn count_op = {} /\
  ptr_covers G tn dst s (w2n n) /\ ptr_covers G tn src s (w2n n) ==>
  ?tn' t.
    run_inst_seq (emitted_insts sa sb) s =
      OK (t with vs_inst_idx := s.vs_inst_idx) /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_current_bb = s.vs_current_bb /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G tn' /\
    t = (mcopy (w2n b) (w2n a) (w2n n) s with
      vs_inst_idx := LENGTH sb.cs_current_insts) /\
    tn' = step_taint
      (mk_inst sa.cs_next_id MCOPY [Var dst; Var src; count_op] []) s
      (mcopy (w2n b) (w2n a) (w2n n) s) tn /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  qpat_assum `lookup_var src s = SOME a`
    (mp_then (Pat `lookup_var src s = SOME a`) mp_tac mcopy_operand_seq_ptr) >>
  disch_then drule_all >>
  disch_then (qspecl_then [`D`, `fn`, `PG`]
    (qspec_then `sa.cs_next_id` strip_assume_tac)) >>
  qexistsl_tac [`step_taint
      (mk_inst sa.cs_next_id MCOPY [Var dst; Var src; count_op] []) s
      (mcopy (w2n b) (w2n a) (w2n n) s) tn`,
    `mcopy (w2n b) (w2n a) (w2n n) s with
      vs_inst_idx := LENGTH sb.cs_current_insts`] >>
  `mcopy (w2n b) (w2n a) (w2n n) s with vs_inst_idx := s.vs_inst_idx =
   mcopy (w2n b) (w2n a) (w2n n) s` by
    simp[mcopy_def, write_memory_with_expansion_def, venom_state_component_equality] >>
  gs[mk_inst_def, is_terminator_def] >>
  simp[mcopy_def, write_memory_with_expansion_def]
QED

Theorem emit_mcopy_frames_normalized_ptr:
  emit_void MCOPY [Var dst; Var src; count_op] sa = ((),sb) /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~ctx_has_dalloca ctx /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  eval_operand count_op s = SOME (n2w n) /\ n < dimword (:256) /\
  op_taint tn count_op = {} /\
  ptr_covers G tn dst s n /\ ptr_covers G tn src s n ==>
  ?tn' t.
    run_inst_seq (emitted_insts sa sb) s =
      OK (t with vs_inst_idx := s.vs_inst_idx) /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_current_bb = s.vs_current_bb /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G tn' /\
    t.vs_memory = (mcopy (w2n b) (w2n a) n s).vs_memory /\
    (!p. lookup_var p t = lookup_var p s /\
      op_taint tn' (Var p) = op_taint tn (Var p)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!i. i < n ==> (w2n b + i IN tn'.t_mem <=> w2n a + i IN tn.t_mem)) /\
    (!i. ~(w2n b <= i /\ i < w2n b + n) ==>
      (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  strip_tac >>
  `w2n (n2w n : bytes32) = n` by simp[] >>
  `ptr_covers G tn dst s (w2n (n2w n : bytes32)) /\
   ptr_covers G tn src s (w2n (n2w n : bytes32))` by simp[] >>
  qpat_assum `emit_void _ _ sa = _`
    (mp_then Any mp_tac emit_mcopy_normalized_ptr) >>
  disch_then drule_all >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  `eval_operand (Var dst) s = SOME b /\
   eval_operand (Var src) s = SOME a` by simp[eval_operand_def] >>
  `tn'.t_var = tn.t_var /\ tn'.t_stor = tn.t_stor /\
   tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
   (!i. i < n ==> (w2n b + i IN tn'.t_mem <=> w2n a + i IN tn.t_mem)) /\
   (!i. ~(w2n b <= i /\ i < w2n b + n) ==>
     (i IN tn'.t_mem <=> i IN tn.t_mem))` by
    (irule mcopy_operand_taint_frames_ptr >>
     qexistsl_tac [`count_op`, `Var dst`, `sa.cs_next_id`, `n2w n`, `s`, `Var src`] >>
     simp[]) >>
  qpat_x_assum `tn' = step_taint _ _ _ _` kall_tac >>
  qexistsl_tac [`tn'`, `t`] >> simp[] >>
  simp[lookup_var_def, mcopy_def, write_memory_with_expansion_def, op_taint_def]
QED

Theorem compile_store_bytestring_normalized_ptr:
  compile_store_bytestring (Var src) (Var dst) sa = ((),sb) /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~ctx_has_dalloca ctx /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  n = 32 + 32 * ((len + 31) DIV 32) /\
  len + 31 < dimword (:256) /\ n < dimword (:256) /\
  mload (w2n a) s = n2w len /\
  ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
  ?Gf tnf t.
    run_inst_seq (emitted_insts sa sb) s =
      OK (t with vs_inst_idx := s.vs_inst_idx) /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_current_bb = s.vs_current_bb /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
    t.vs_memory = (mcopy (w2n b) (w2n a) n s).vs_memory /\
    (!i. ~(w2n b <= i /\ i < w2n b + n) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!i. i < n ==> (w2n b + i IN tnf.t_mem <=> w2n a + i IN tn.t_mem)) /\
    (!i. ~(w2n b <= i /\ i < w2n b + n) ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  strip_tac >>
  qpat_x_assum `compile_store_bytestring _ _ _ = _` mp_tac >>
  simp[compile_store_bytestring_def, comp_bind_def] >>
  pairarg_tac >> simp[LET_THM, pairTheory.pair_case_def] >> strip_tac >>
  rename1 `compile_bytestring_copy_len (Var src) sa = (count_op,sc)` >>
  `ptr_covers G tn src s 32` by
    (fs[ptr_covers_def] >> metis_tac[LESS_EQ_TRANS, LESS_EQ_ADD]) >>
  drule_all compile_bytestring_copy_len_normalized_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  rename1 `inst_seq_ptr D 0 ctx fn PG G tn _ s G1 tn1` >>
  rename1 `eval_operand count_op s1 = SOME _` >>
  `eval_operand count_op s1 = SOME (n2w n)` by
    (qspec_then `len` mp_tac buffer_round_size >> fs[word_size_def]) >>
  `lookup_var src s1 = SOME a /\ lookup_var dst s1 = SOME b /\
   ptr_covers G1 tn1 src s1 n /\ ptr_covers G1 tn1 dst s1 n` by
    (qpat_assum `!p. not_fresh_at sa p ==> _` (qspec_then `src` strip_assume_tac) >>
     qpat_assum `!p. not_fresh_at sa p ==> _` (qspec_then `dst` strip_assume_tac) >>
     gs[] >> conj_tac
     >- (irule ptr_covers_lookup_frame >>
         qexistsl_tac [`G`, `s`, `tn`] >> simp[]) >>
     irule ptr_covers_lookup_frame >>
     qexistsl_tac [`G`, `s`, `tn`] >> simp[]) >>
  drule_all emit_mcopy_frames_normalized_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  rename1 `inst_seq_ptr D 0 ctx fn PG G1 tn1 _ s1 G1 tn2` >>
  rename1 `t2.vs_memory = (mcopy _ _ _ s1).vs_memory` >>
  drule_all emitted_insts_join_normalized_ptr >> strip_tac >>
  qexistsl_tac [`G1`, `tn2`, `t2`] >>
  gs[] >>
  conj_tac >- simp[mcopy_def, write_memory_with_expansion_def] >>
  conj_tac
  >- (rpt strip_tac >>
      `mem_bytes_at i 1 (mcopy (w2n b) (w2n a) n s1).vs_memory =
       mem_bytes_at i 1 s1.vs_memory` by
        (irule buffer_mcopy_exterior >> decide_tac) >> gs[]) >>
  metis_tac[]
QED

Theorem compile_store_bytestring_run_frames_ptr:
  compile_store_bytestring (Var src) (Var dst) sa = ((),sb) /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~ctx_has_dalloca ctx /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  n = 32 + 32 * ((len + 31) DIV 32) /\
  len + 31 < dimword (:256) /\ n < dimword (:256) /\
  mload (w2n a) s = n2w len /\
  ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
  run_inst_seq (emitted_insts sa sb) s = OK u ==>
  ?Gf tnf.
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
    u.vs_memory = (mcopy (w2n b) (w2n a) n s).vs_memory /\
    (!i. ~(w2n b <= i /\ i < w2n b + n) ==>
      mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!i. i < n ==> (w2n b + i IN tnf.t_mem <=> w2n a + i IN tn.t_mem)) /\
    (!i. ~(w2n b <= i /\ i < w2n b + n) ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!p. not_fresh_at sa p ==>
      lookup_var p u = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all compile_store_bytestring_normalized_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`] >> gvs[lookup_var_def] >> metis_tac[]
QED
