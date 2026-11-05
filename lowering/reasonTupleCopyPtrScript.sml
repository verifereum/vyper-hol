(* Shared checked copy boundaries for the raise/assert Error(string) tuple. *)
Theory reasonTupleCopyPtr
Ancestors
  reasonPrefixPtr reasonResourcesPtr robustCopyTransportPtr typedCopyPtr
  valueEncodingProps valueEncodingProofs venomMemProofs ptrDiscipline
  venomExecSemantics venomState words list pred_set arithmetic fragExecPtr
  emitHelper bodyPtrDefs venomInst compileEnv fragExec

(* Actual MCOPY taint, including arbitrary tainted padding, transports the
   robust representation. No cleanliness assumption on payload bytes is used. *)
Theorem reason_mcopy_robust_representation:
  !tn s id dst src count_op a b n tv v.
    eval_operand dst s = SOME b /\ eval_operand src s = SOME a /\
    eval_operand count_op s = SOME n /\
    val_wf tv v /\ val_footprint tv v <= w2n n /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory tv v (w2n a) mem) ==>
    !mem. mem_agree_outside
      (step_taint (mk_inst id MCOPY [dst;src;count_op] []) s
        (mcopy (w2n b) (w2n a) (w2n n) s) tn).t_mem
      (mcopy (w2n b) (w2n a) (w2n n) s).vs_memory mem ==>
      val_in_memory tv v (w2n b) mem
Proof
  rpt gen_tac >> strip_tac >>
  ` (step_taint (mk_inst id MCOPY [dst;src;count_op] []) s
       (mcopy (w2n b) (w2n a) (w2n n) s) tn).t_mem =
      (tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + w2n n}) UNION
      {w2n b + i | i < w2n n /\ w2n a + i IN tn.t_mem}` by
    (irule (cj 5 mcopy_operand_ghost_frame) >> simp[]) >>
  rpt strip_tac >> irule robust_val_in_memory_copy_transport >>
  conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`,
    `(mcopy (w2n b) (w2n a) (w2n n) s).vs_memory`, `w2n n`,
    `w2n a`, `tn.t_mem`,
    `(step_taint (mk_inst id MCOPY [dst;src;count_op] []) s
      (mcopy (w2n b) (w2n a) (w2n n) s) tn).t_mem`] >>
  simp[mcopy_mem_bytes_at_same, IN_DIFF, IN_UNION, GSPECIFICATION]
QED

Theorem reason_mcopy_live_covers:
  !PG G tn s id dst src count_op a b n p k.
    eval_operand dst s = SOME b /\ eval_operand src s = SOME a /\
    eval_operand count_op s = SOME n /\ ptr_covers G tn p s k ==>
    ptr_covers
      (step_prov PG G (mk_inst id MCOPY [dst;src;count_op] [])
        (mcopy (w2n b) (w2n a) (w2n n) s))
      (step_taint (mk_inst id MCOPY [dst;src;count_op] []) s
        (mcopy (w2n b) (w2n a) (w2n n) s) tn)
      p (mcopy (w2n b) (w2n a) (w2n n) s) k
Proof
  rpt gen_tac >> strip_tac >>
  `step_prov PG G (mk_inst id MCOPY [dst;src;count_op] [])
      (mcopy (w2n b) (w2n a) (w2n n) s) = G` by
    (irule (cj 1 mcopy_operand_ghost_frame) >> simp[]) >>
  `(step_taint (mk_inst id MCOPY [dst;src;count_op] []) s
      (mcopy (w2n b) (w2n a) (w2n n) s) tn).t_var = tn.t_var` by
    (irule (cj 2 mcopy_operand_ghost_frame) >> simp[]) >>
  fs[ptr_covers_def, mcopy_def, write_memory_with_expansion_def,
     lookup_var_def, op_taint_def]
QED

Theorem reason_mcopy_path_ptr:
  emit_void MCOPY [Var dst;Var src;count_op] sa = ((),sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  eval_operand (Var dst) s = SOME b /\
  eval_operand (Var src) s = SOME a /\
  eval_operand count_op s = SOME n /\ op_taint tn count_op = {} /\
  ptr_covers G tn dst s (w2n n) /\ ptr_covers G tn src s (w2n n) ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;count_op] [])
      (mcopy (w2n b) (w2n a) (w2n n) s))
    (step_taint (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;count_op] []) s
      (mcopy (w2n b) (w2n a) (w2n n) s) tn)
    (OK (mcopy (w2n b) (w2n a) (w2n n) s with
      vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> irule reason_encoder_emit_path_ptr >>
  simp[GSYM emit_void_def, is_terminator_def] >> conj_tac
  >- (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
      gvs[mk_inst_def, eval_operand_def]) >>
  conj_tac
  >- (qexists_tac `sb` >> fs[emit_void_def, emit_inst_def]) >>
  irule ptr_inst_ok_mcopy_operand >> simp[] >> metis_tac[]
QED


Theorem reason_copy_binop_path_ptr:
  emit_inst opc [left;right] [out] sa = ((),sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  (opc = ADD /\ f = word_add \/ opc = AND /\ f = word_and) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id opc [left;right] [out])
      (update_var out (f a b) s))
    (step_taint (mk_inst sa.cs_next_id opc [left;right] [out]) s
      (update_var out (f a b) s) tn)
    (OK (update_var out (f a b) s with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> irule reason_encoder_emit_path_ptr >>
  simp[is_terminator_def] >> conj_tac >>
  all_tac
  >>~- ([`step_inst_base _ _ = _`],
    PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
    simp[mk_inst_def, exec_pure2_def]) >>
  irule typedCopyPtrTheory.ptr_inst_ok_copy_len_binop >> simp[]
QED
