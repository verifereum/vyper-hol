(* Destination-local facts on the concrete counted MCOPY witness. *)
Theory bodyPtrMakeArrayBulkFrame
Ancestors
  bodyPtrMakeArrayBulkStep typedCopyPtr valueEncodingProps
  venomState venomInst venomExecSemantics ptrDiscipline bodyPtrDefs pred_set

Theorem mcopy_cursor_state_frame:
  sf = ((mcopy dst src n s) with vs_inst_idx := idx) ==>
  (!p. lookup_var p sf = lookup_var p s) /\
  sf.vs_call_ctx = s.vs_call_ctx /\ sf.vs_accounts = s.vs_accounts /\
  sf.vs_transient = s.vs_transient /\
  (!i. ~(dst <= i /\ i < dst+n) ==>
    mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory)
Proof
  disch_then SUBST1_TAC >> conj_tac
  >- simp[lookup_var_def, mcopy_def, write_memory_with_expansion_def] >>
  conj_tac >- simp[mcopy_def, write_memory_with_expansion_def] >>
  conj_tac >- simp[mcopy_def, write_memory_with_expansion_def] >>
  conj_tac >- simp[mcopy_def, write_memory_with_expansion_def] >>
  rpt strip_tac >> simp[] >> irule mcopy_mem_bytes_at_disjoint >> decide_tac
QED

Theorem mcopy_operand_taint_frame:
  eval_operand (Var dst) s = SOME b /\
  eval_operand (Var src) s = SOME a /\ eval_operand count_op s = SOME n /\
  tnf = step_taint (mk_inst id MCOPY [Var dst; Var src; count_op] []) s
    (mcopy (w2n b) (w2n a) (w2n n) s) tn ==>
  (!p. op_taint tnf (Var p) = op_taint tn (Var p)) /\
  tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
  (!i. ~(w2n b <= i /\ i < w2n b + w2n n) ==>
    (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
  (!i. i < w2n n ==> (w2n b+i IN tnf.t_mem <=> w2n a+i IN tn.t_mem))
Proof
  strip_tac >>
  qpat_assum `eval_operand (Var dst) s = SOME b`
    (mp_then Any mp_tac mcopy_operand_ghost_frame) >>
  disch_then (fn th => qpat_assum `eval_operand (Var src) s = SOME a`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `eval_operand count_op s = SOME n`
    (mp_then Any mp_tac th)) >>
  disch_then (qspecl_then [`PG`, `G`, `tn`, `id`] strip_assume_tac) >>
  gvs[op_taint_def] >> conj_tac
  >- simp[step_taint_def, mk_inst_def, store_taint_def, adopt_reset_def,
          new_site_bytes_def, imm_taint_def] >>
  rpt strip_tac >> simp[] >> eq_tac >> strip_tac >> gvs[] >>
  metis_tac[arithmeticTheory.LE_ADD, arithmeticTheory.LESS_MONO_ADD]
QED

Theorem mcopy_operand_coverage_frame:
  eval_operand (Var dst) s = SOME b /\
  eval_operand (Var src) s = SOME a /\ eval_operand count_op s = SOME n /\
  tnf = step_taint (mk_inst id MCOPY [Var dst; Var src; count_op] []) s
    (mcopy (w2n b) (w2n a) (w2n n) s) tn /\
  sf = ((mcopy (w2n b) (w2n a) (w2n n) s) with vs_inst_idx := idx) ==>
  !p size. ptr_covers G tn p s size ==> ptr_covers G tnf p sf size
Proof
  strip_tac >> drule_all mcopy_operand_taint_frame >> strip_tac >>
  drule mcopy_cursor_state_frame >> strip_tac >>
  simp[ptr_covers_def]
QED

Theorem mcopy_operand_framed_ptr_path:
  eval_operand count_op s = SOME n /\ op_taint tn count_op = {} /\
  ptr_covers G tn dst s (w2n n) /\ ptr_covers G tn src s (w2n n) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id MCOPY [Var dst; Var src; count_op] []) /\
  lookup_var dst s = SOME b /\ lookup_var src s = SOME a ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\ Gf = G /\
    tnf = step_taint (mk_inst id MCOPY [Var dst; Var src; count_op] []) s
      (mcopy (w2n b) (w2n a) (w2n n) s) tn /\
    sf = ((mcopy (w2n b) (w2n a) (w2n n) s)
      with vs_inst_idx := SUC s.vs_inst_idx) /\
    (!p. lookup_var p sf = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    sf.vs_call_ctx = s.vs_call_ctx /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\
    (!p size. ptr_covers G tn p s size ==> ptr_covers Gf tnf p sf size) /\
    (!i. ~(w2n b <= i /\ i < w2n b+w2n n) ==>
      mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!i. i < w2n n ==> (w2n b+i IN tnf.t_mem <=> w2n a+i IN tn.t_mem))
Proof
  strip_tac >>
  qexistsl_tac [`G`,
    `step_taint (mk_inst id MCOPY [Var dst; Var src; count_op] []) s
       (mcopy (w2n b) (w2n a) (w2n n) s) tn`,
    `(mcopy (w2n b) (w2n a) (w2n n) s) with vs_inst_idx := SUC s.vs_inst_idx`] >>
  simp[] >> conj_tac >- (irule mcopy_operand_ptr_path >> simp[]) >>
  `eval_operand (Var dst) s = SOME b /\ eval_operand (Var src) s = SOME a` by
    simp[eval_operand_def] >>
  mp_tac (Q.INST [`tnf` |->
    `step_taint (mk_inst id MCOPY [Var dst; Var src; count_op] []) s
       (mcopy (w2n b) (w2n a) (w2n n) s) tn`] mcopy_operand_taint_frame) >>
  simp[] >> strip_tac >> simp[] >>
  conj_tac >- simp[lookup_var_def, mcopy_def, write_memory_with_expansion_def] >>
  conj_tac >- simp[mcopy_def, write_memory_with_expansion_def] >>
  conj_tac >- simp[mcopy_def, write_memory_with_expansion_def] >>
  conj_tac
  >- (rpt strip_tac >> gvs[ptr_covers_def, lookup_var_def] >>
      simp[mcopy_def, write_memory_with_expansion_def]) >>
  rpt strip_tac >> simp[] >> irule mcopy_mem_bytes_at_disjoint >> decide_tac
QED
