(* Finite bulk copies transport payload taint, including overlapping copies. *)
Theory forPtrBulk
Ancestors forPtrCopyInterface forPtrWord typedCopyPtr fragGasSeqPtr
  robustCopyTransportPtr bodyPtrDefs valueEncodingProps venomExecSemantics venomInst
  venomState arithmetic exprLoweringProps fragExecPtr ptrSafeRun ptrDiscipline finite_map pred_set
  context compileEnv emitHelperProps loweringSlice words valueEncoding

Theorem for_bulk_copy_checked_seq:
  ptr_covers G tn src s (w2n n) /\ ptr_covers G tn dst s (w2n n) /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  eval_operand count_op s = SOME n /\ op_taint tn count_op = {} /\
  ~ctx_has_dalloca ctx ==>
  inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst id MCOPY [Var dst; Var src; count_op] []] s G
    (step_taint (mk_inst id MCOPY [Var dst; Var src; count_op] []) s
       (mcopy (w2n b) (w2n a) (w2n n) s) tn)
Proof
  strip_tac >>
  `step_inst_base (mk_inst id MCOPY [Var dst; Var src; count_op] []) s =
    OK (mcopy (w2n b) (w2n a) (w2n n) s)` by
    (simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def]) >>
  `step_prov PG G (mk_inst id MCOPY [Var dst; Var src; count_op] [])
     (mcopy (w2n b) (w2n a) (w2n n) s) = G` by
    (irule (cj 1 mcopy_operand_ghost_frame) >> simp[eval_operand_def]) >>
  simp[inst_seq_ptr_def] >> irule ptr_inst_ok_mcopy_operand >>
  simp[eval_operand_def, op_taint_def]
QED

Theorem for_bulk_copy_robust:
  val_wf tv v /\ val_footprint tv v <= n /\
  tf = (tn DIFF {i | dst <= i /\ i < dst+n}) UNION
       {dst+i | i < n /\ src+i IN tn} /\
  (!m. mem_agree_outside tn s.vs_memory m ==> val_in_memory tv v src m) ==>
  !m. mem_agree_outside tf (mcopy dst src n s).vs_memory m ==>
    val_in_memory tv v dst m
Proof
  strip_tac >> rpt strip_tac >> irule robust_val_in_memory_copy_transport >> simp[] >>
  qexistsl [`s.vs_memory`, `(mcopy dst src n s).vs_memory`, `n`, `src`, `tn`, `tf`] >>
  simp[mcopy_mem_bytes_at_same] >> rpt strip_tac >> gvs[] >>
  eq_tac >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem for_bulk_copy_memory_frame:
  mem_agree_outside {i | dst <= i /\ i < dst+n}
    (mcopy dst src n s).vs_memory s.vs_memory
Proof
  simp[mem_agree_outside_def] >> rpt strip_tac >>
  irule mcopy_mem_bytes_at_disjoint >> decide_tac
QED

Theorem for_bulk_copy_robust_checked:
  ptr_covers G tn src s (w2n n) /\ ptr_covers G tn dst s (w2n n) /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  eval_operand count_op s = SOME n /\ op_taint tn count_op = {} /\
  ~ctx_has_dalloca ctx /\ val_wf tv v /\ val_footprint tv v <= w2n n /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v (w2n a) m) ==>
  ?tf sf.
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id MCOPY [Var dst; Var src; count_op] []] s G tf /\
    run_inst_seq [mk_inst id MCOPY [Var dst; Var src; count_op] []] s = OK sf /\
    mem_agree_outside {i | w2n b <= i /\ i < w2n b + w2n n}
      sf.vs_memory s.vs_memory /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!p. lookup_var p sf = lookup_var p s /\
         op_taint tf (Var p) = op_taint tn (Var p)) /\
    (!m. mem_agree_outside tf.t_mem sf.vs_memory m ==>
      val_in_memory tv v (w2n b) m)
Proof
  strip_tac >>
  qabbrev_tac `sf = mcopy (w2n b) (w2n a) (w2n n) s` >>
  qabbrev_tac `tf = step_taint
    (mk_inst id MCOPY [Var dst; Var src; count_op] []) s sf tn` >>
  `tf.t_var = tn.t_var /\ tf.t_stor = tn.t_stor /\
   tf.t_trans = tn.t_trans /\
   tf.t_mem = (tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+w2n n}) UNION
     {w2n b+i | i < w2n n /\ w2n a+i IN tn.t_mem}` by
    (simp_tac pure_ss [Abbr `tf`, Abbr `sf`] >>
     conj_tac
     >- (irule (cj 2 mcopy_operand_ghost_frame) >> simp[eval_operand_def]) >>
     conj_tac
     >- (irule (cj 3 mcopy_operand_ghost_frame) >> simp[eval_operand_def]) >>
     conj_tac
     >- (irule (cj 4 mcopy_operand_ghost_frame) >> simp[eval_operand_def]) >>
     irule (SRULE [] (cj 5 mcopy_operand_ghost_frame)) >> simp[eval_operand_def]) >>
  qexistsl [`tf`, `sf`] >> conj_tac
  >- (simp[Abbr `tf`, Abbr `sf`] >> irule for_bulk_copy_checked_seq >> simp[]) >>
  conj_tac
  >- (simp[run_inst_seq_def] >> simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def, Abbr `sf`]) >>
  conj_tac >- simp[Abbr `sf`, for_bulk_copy_memory_frame] >>
  simp[] >> conj_tac
  >- simp[Abbr `sf`, mcopy_def, write_memory_with_expansion_def,
          lookup_var_def, op_taint_def] >>
  rpt strip_tac >> simp[Abbr `sf`] >> irule for_bulk_copy_robust >>
  simp[] >> qexistsl [`w2n n`, `s`, `w2n a`, `tn.t_mem`] >> simp[]
QED

Theorem for_empty_bulk_robust:
  val_wf tv v /\ val_footprint tv v = 0 /\
  (!m. mem_agree_outside tn mem m ==> val_in_memory tv v src m) ==>
  !m. mem_agree_outside tn mem m ==> val_in_memory tv v dst m
Proof
  rpt strip_tac >> irule robust_val_in_memory_copy_transport >> simp[] >>
  qexistsl [`mem`, `mem`, `0`, `src`, `tn`, `tn`] >> simp[mem_bytes_at_def]
QED

Theorem for_compile_bulk_copy_code:
  compile_copy_memory dst src n sa = ((),sb) ==>
  emitted_insts sa sb =
    (if n = 0 then [] else
      [mk_inst sa.cs_next_id MCOPY [dst; src; Lit (n2w n)] []])
Proof
  Cases_on `n`
  >- simp[compile_copy_memory_def, comp_return_def, emitted_insts_def] >>
  simp[compile_copy_memory_def] >> strip_tac >>
  drule emitted_insts_emit_void >> simp[]
QED

Theorem for_compile_bulk_copy_checked:
  compile_copy_memory (Var dst) (Var src) n sa = ((),sb) /\
  n < dimword (:256) /\
  ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ~ctx_has_dalloca ctx /\ val_wf tv v /\ val_footprint tv v <= n /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v (w2n a) m) ==>
  ?tf sf.
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G tf /\
    run_inst_seq (emitted_insts sa sb) s = OK sf /\
    mem_agree_outside {i | w2n b <= i /\ i < w2n b + n}
      sf.vs_memory s.vs_memory /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!p. lookup_var p sf = lookup_var p s /\
         op_taint tf (Var p) = op_taint tn (Var p)) /\
    (!m. mem_agree_outside tf.t_mem sf.vs_memory m ==>
      val_in_memory tv v (w2n b) m)
Proof
  strip_tac >> drule for_compile_bulk_copy_code >> strip_tac >>
  Cases_on `n = 0`
  >- (qexistsl [`tn`, `s`] >> simp[inst_seq_ptr_def, run_inst_seq_def] >>
      conj_tac >- simp[mem_agree_outside_def] >>
      rpt strip_tac >> irule for_empty_bulk_robust >> simp[] >>
      qexistsl [`s.vs_memory`, `w2n a`, `tn.t_mem`] >> simp[]) >>
  gvs[] >>
  `w2n (n2w n:256 word) = n` by simp[] >>
  qspecl_then [`(n2w n:256 word)`, `sa.cs_next_id`] mp_tac
    (Q.GENL [`n`, `id`] (Q.INST [`count_op` |-> `Lit n`]
      for_bulk_copy_robust_checked)) >>
  simp[eval_operand_def, op_taint_def]
QED

Theorem for_iter_bulk_copy_checked:
  ~is_word_type ty /\ ~is_bytestring_type ty /\
  compile_iter_elem_copy cenv (Var src) (Var dst) stride LocMemory F ty ty
    sa = ((),sb) /\
  type_memory_bytes cenv ty = n /\ n < dimword (:256) /\
  ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ~ctx_has_dalloca ctx /\ val_wf tv v /\ val_footprint tv v <= n /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v (w2n a) m) ==>
  ?tf sf.
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G tf /\
    run_inst_seq (emitted_insts sa sb) s = OK sf /\
    mem_agree_outside {i | w2n b <= i /\ i < w2n b + n}
      sf.vs_memory s.vs_memory /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!p. lookup_var p sf = lookup_var p s /\
         op_taint tf (Var p) = op_taint tn (Var p)) /\
    (!m. mem_agree_outside tf.t_mem sf.vs_memory m ==>
      val_in_memory tv v (w2n b) m)
Proof
  strip_tac >>
  `compile_copy_memory (Var dst) (Var src) n sa = ((),sb)` by
    gvs[for_memory_element_copy_dispatch] >>
  irule for_compile_bulk_copy_checked >> simp[] >>
  qexistsl [`a`, `dst`, `src`] >> simp[]
QED

Theorem for_bulk_copy_checked_uniform:
  ptr_covers G tn src s (w2n n) /\ ptr_covers G tn dst s (w2n n) /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  eval_operand count_op s = SOME n /\ op_taint tn count_op = {} /\
  ~ctx_has_dalloca ctx ==>
  !k. inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst id MCOPY [Var dst; Var src; count_op] []]
    (s with vs_inst_idx := k) G
    (step_taint (mk_inst id MCOPY [Var dst; Var src; count_op] []) s
       (mcopy (w2n b) (w2n a) (w2n n) s) tn)
Proof
  strip_tac >> gen_tac >>
  `mcopy (w2n b) (w2n a) (w2n n) (s with vs_inst_idx := k) =
    (mcopy (w2n b) (w2n a) (w2n n) s) with vs_inst_idx := k` by
    simp[mcopy_def, write_memory_with_expansion_def] >>
  mp_tac (Q.INST [`s` |-> `s with vs_inst_idx := k`]
    for_bulk_copy_checked_seq) >> gvs[lookup_var_def]
QED
