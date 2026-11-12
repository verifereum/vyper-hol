(* Counted flat data transport for widened dynamic arrays. *)
Theory widenedAssignPtrDynBulkData
Ancestors
  assignBasePtrBytesPost assignTuplePtrStageFrame bodyPtrPopLocalRootFrame
  typedCopyPtr typedMemoryCopy fragExecPtr ptrDiscipline venomState
  venomExecSemantics venomInst emitHelper emitHelperProps compileEnv context
  bodyPtrDefs ptrSafeRun memLocDefs codegenRel contextCodegenRel valueEncoding valueEncodingProps words finite_map pred_set

Theorem widened_assign_mcopy_empty_operand[local]:
  eval_operand dst s = SOME a /\ eval_operand src s = SOME b /\
  eval_operand count_op s = SOME 0w /\
  op_taint tn dst = {} /\ op_taint tn src = {} /\
  op_taint tn count_op = {} /\ ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn
    (mk_inst id MCOPY [dst;src;count_op] []) s
Proof
  strip_tac >>
  `step_inst fuel ctx (mk_inst id MCOPY [dst;src;count_op] []) s =
    OK (mcopy (w2n a) (w2n b) 0 s)` by
    (simp[step_inst_non_invoke] >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def]) >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, fixed_source_write_range_def,
       sized_source_write_range_def, mcopy_def,
       write_memory_with_expansion_def] >>
  gen_tac >> Cases_on `op = dst` >> gvs[] >>
  Cases_on `op = src` >> gvs[] >>
  Cases_on `op = count_op` >> gvs[]
QED

Theorem widened_assign_mcopy_conditional_path[local]:
  emit_inst MCOPY [Var dst;Var src;count_op] [] sa = ((),sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  eval_operand count_op s = SOME n /\ op_taint tn count_op = {} /\
  op_taint tn (Var dst) = {} /\ op_taint tn (Var src) = {} /\
  (0 < w2n n ==> ptr_covers G tn dst s (w2n n) /\
                      ptr_covers G tn src s (w2n n)) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;count_op] [])
      (mcopy (w2n b) (w2n a) (w2n n) s))
    (step_taint (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;count_op] []) s
      (mcopy (w2n b) (w2n a) (w2n n) s) tn)
    (OK (mcopy (w2n b) (w2n a) (w2n n) s with
      vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> Cases_on `0 < w2n n`
  >- (irule emit_mcopy_zero_path_ptr >> simp[]) >>
  `n = 0w` by (gvs[] >> metis_tac[w2n_eq_0]) >>
  qpat_x_assum `n = 0w` SUBST_ALL_TAC >>
  pure_rewrite_tac [word_0_n2w, w2n_n2w] >>
  irule assignTuplePtrPrefixTheory.emit_inst_zero_path_ptr >>
  simp[is_terminator_def] >> conj_tac
  >- simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def] >>
  irule widened_assign_mcopy_empty_operand >> simp[eval_operand_def]
QED

Theorem widened_assign_mcopy_robust_counted:
  emit_inst MCOPY [Var dst;Var src;count_op] [] sa = ((),sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  eval_operand count_op s = SOME n /\ op_taint tn count_op = {} /\
  op_taint tn (Var dst) = {} /\ op_taint tn (Var src) = {} /\
  (0 < w2n n ==> ptr_covers G tn dst s (w2n n) /\
                      ptr_covers G tn src s (w2n n)) /\
  val_wf tv v /\ val_footprint tv v <= w2n n /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v (w2n a) m) ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    t.vs_prev_bb = s.vs_prev_bb /\
    typed_copy_state_frame sa (w2n b) (w2n n) s t /\
    (!m. mem_agree_outside tn'.t_mem t.vs_memory m ==>
      val_in_memory tv v (w2n b) m) /\
    (!x. lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!i. i < w2n b \/ w2n b + w2n n <= i ==>
      (i IN tn'.t_mem <=> i IN tn.t_mem))
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts)` by
    gvs[emit_inst_def, fresh_id_def, emit_def, comp_bind_def,
        comp_ignore_bind_def, comp_return_def] >>
  drule_all widened_assign_mcopy_conditional_path >>
  disch_then (qspecl_then [`PG`, `D`] assume_tac) >>
  qabbrev_tac `u = mcopy (w2n b) (w2n a) (w2n n) s` >>
  qabbrev_tac `tf = step_taint
    (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;count_op] []) s u tn` >>
  `eval_operand (Var dst) s = SOME b /\ eval_operand (Var src) s = SOME a` by
    simp[eval_operand_def] >>
  `u = mcopy (w2n b) (w2n a) (w2n n) s /\
   tf = step_taint (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;count_op] []) s u tn /\
   (s with vs_vars := s.vs_vars) = s /\
   (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x s)` by
    simp[Abbr `u`, Abbr `tf`] >>
  drule_all (Q.SPECL [`Var dst`, `Var src`] assign_base_bytes_mcopy_post) >>
  disch_then (qspecl_then [`PG`, `G`, `SUC s.vs_inst_idx`] strip_assume_tac) >>
  `u.vs_current_bb = s.vs_current_bb /\ ~u.vs_halted /\
   u.vs_prev_bb = s.vs_prev_bb` by
    simp[Abbr `u`, mcopy_def, write_memory_with_expansion_def] >>
  qpat_x_assum `u = mcopy _ _ _ _` kall_tac >>
  qpat_x_assum `tf = step_taint _ _ _ _` kall_tac >>
  qexistsl_tac [`G`, `tf`, `u with vs_inst_idx := SUC s.vs_inst_idx`] >>
  simp[op_taint_def] >> metis_tac[]
QED
