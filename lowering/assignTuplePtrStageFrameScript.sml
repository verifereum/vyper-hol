(* Actual counted MCOPY and its separated staging frame. *)
Theory assignTuplePtrStageFrame
Ancestors
  assignTuplePtrPrefix robustCopyTransportPtr typedCopyPtr fragExecPtr
  venomMemProofs venomInst venomState venomExecSemantics bodyPtrDefs
  valueEncoding valueEncodingProofs compileEnv vyperInterpreter ptrDiscipline

Theorem emit_mcopy_zero_path_ptr:
  emit_inst MCOPY [Var dst; Var src; count_op] [] sa = ((),sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
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
  strip_tac >> irule emit_inst_zero_path_ptr >>
  simp[is_terminator_def] >> conj_tac
  >- (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
      simp[mk_inst_def, eval_operand_def]) >>
  irule ptr_inst_ok_mcopy_operand >> simp[]
QED

Theorem mcopy_exterior_ghost_inv:
  ghost_inv d cenv cx es G tn s /\
  eval_operand dst s = SOME b /\ eval_operand src s = SOME a /\
  eval_operand count_op s = SOME n /\
  (!name entry p sz w.
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w ==>
    val_wf entry.type entry.value /\
    (w2n w + val_footprint entry.type entry.value <= w2n b \/
     w2n b + w2n n <= w2n w)) ==>
  ghost_inv d cenv cx es
    (step_prov PG G (mk_inst id MCOPY [dst;src;count_op] [])
      (mcopy (w2n b) (w2n a) (w2n n) s))
    (step_taint (mk_inst id MCOPY [dst;src;count_op] []) s
      (mcopy (w2n b) (w2n a) (w2n n) s) tn)
    (mcopy (w2n b) (w2n a) (w2n n) s)
Proof
  strip_tac >>
  qpat_assum `eval_operand dst s = SOME b`
    (mp_then Any mp_tac mcopy_operand_ghost_frame) >>
  disch_then (fn th => qpat_assum `eval_operand src s = SOME a`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `eval_operand count_op s = SOME n`
    (mp_then Any mp_tac th)) >>
  disch_then (qspecl_then [`PG`, `G`, `tn`, `id`] strip_assume_tac) >>
  `(step_taint (mk_inst id MCOPY [dst;src;count_op] []) s
      (mcopy (w2n b) (w2n a) (w2n n) s) tn).t_imm = tn.t_imm` by
    simp[step_taint_def, imm_taint_def, mk_inst_def] >>
  qmatch_goalsub_abbrev_tac `ghost_inv d cenv cx es _ tf _` >>
  gvs[ghost_inv_def] >> reverse conj_tac
  >- (Cases_on `d`
      >- (gvs[return_buf_ptr_def, op_taint_def, stor_taint_ok_def,
              mcopy_def, write_memory_with_expansion_def] >> simp[]) >>
      rename1 `return_buf_ptr (SOME pair)` >> PairCases_on `pair` >>
      gvs[return_buf_ptr_def, ptr_covers_def, op_taint_def,
          stor_taint_ok_def, lookup_var_def, mcopy_def,
          write_memory_with_expansion_def] >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  conj_tac
  >- gvs[ptr_covers_def, op_taint_def, lookup_var_def,
         mcopy_def, write_memory_with_expansion_def] >>
  rpt gen_tac >> strip_tac >>
  `lookup_var p s = SOME w` by
    gvs[lookup_var_def, mcopy_def, write_memory_with_expansion_def] >>
  qpat_x_assum `!name entry p sz w. _`
    (drule_all_then (CONJUNCTS_THEN assume_tac)) >>
  irule robust_val_in_memory_exterior_frame >>
  conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`,
    `(mcopy (w2n b) (w2n a) (w2n n) s).vs_memory`,
    `tn.t_mem`, `tf.t_mem`, `{i | w2n b <= i /\ i < w2n b + w2n n}`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> eq_tac >> strip_tac >> gvs[] >>
      metis_tac[arithmeticTheory.LE_ADD, arithmeticTheory.LESS_MONO_ADD]) >>
  rpt strip_tac >> irule mcopy_mem_bytes_at_disjoint >> decide_tac
QED
