Theory bodyPtrTypeBuiltinsCopyCounted
Ancestors
  context compileEnv emitHelper emitHelperProps exprLoweringProps
  typedCopyPtr fragExecPtr fragGasSeqPtr fragGasPathPtr
  venomExecSemantics venomState venomInst ptrDiscipline
  valueEncoding valueEncodingProps valueCopy finite_map list rich_list arithmetic words

Theorem copy_memory_emitted_shape:
  compile_copy_memory dst src n sa = ((),sb) ==>
  emitted_insts sa sb =
    (if n = 0 then [] else [mk_inst sa.cs_next_id MCOPY [dst;src;Lit (n2w n)] []])
Proof
  Cases_on `n` >>
  simp[compile_copy_memory_def, comp_return_def] >> strip_tac
  >- gvs[emitted_insts_def] >>
  drule emitted_insts_emit_void >> simp[]
QED

Theorem mcopy_singleton_counted_certificate:
  n < dimword(:256) /\ lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\ ~ctx_has_dalloca ctx /\
  run_inst_seq [mk_inst id MCOPY [Var dst;Var src;Lit (n2w n)] []] s = OK t ==>
  ?th.
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id MCOPY [Var dst;Var src;Lit (n2w n)] []] s G th /\
    t = mcopy (w2n b) (w2n a) n s /\
    th.t_var = tn.t_var /\ th.t_stor = tn.t_stor /\ th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
    th.t_mem = (tn.t_mem DIFF {j | w2n b <= j /\ j < w2n b+n}) UNION
      {w2n b+j | j < n /\ w2n a+j IN tn.t_mem}
Proof
  strip_tac >>
  `eval_operand (Var dst) s = SOME b /\ eval_operand (Var src) s = SOME a /\
   eval_operand (Lit (n2w n)) s = SOME (n2w n) /\
   op_taint tn (Lit (n2w n)) = {}` by simp[eval_operand_def, op_taint_def] >>
  `step_inst_base (mk_inst id MCOPY [Var dst;Var src;Lit (n2w n)] []) s =
     OK (mcopy (w2n b) (w2n a) n s)` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, eval_operand_def, w2n_n2w]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn
     (mk_inst id MCOPY [Var dst;Var src;Lit (n2w n)] []) s` by
    (irule ptr_inst_ok_mcopy_operand >> simp[w2n_n2w] >>
     goal_assum (drule_at Any) >> simp[]) >>
  qpat_assum `eval_operand (Var dst) s = _`
    (mp_then (Pos hd) mp_tac mcopy_operand_ghost_frame) >>
  disch_then (fn th => qpat_assum `eval_operand (Var src) s = _`
    (mp_then (Pos hd) mp_tac th)) >>
  disch_then (fn th => qpat_assum `eval_operand (Lit _) s = _`
    (mp_then (Pos hd) mp_tac th)) >>
  disch_then (qspecl_then [`PG`,`G`,`tn`,`id`] strip_assume_tac) >>
  qexists_tac `step_taint (mk_inst id MCOPY [Var dst;Var src;Lit (n2w n)] [])
     s (mcopy (w2n b) (w2n a) n s) tn` >>
  gvs[run_inst_seq_def, inst_seq_ptr_def, w2n_n2w] >>
  simp[step_taint_def, mk_inst_def, imm_taint_def]
QED

Theorem copy_memory_counted_certificate:
  compile_copy_memory (Var dst) (Var src) n sa = ((),sb) /\
  n < dimword(:256) /\ lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?th.
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G th /\
    (if n = 0 then t = s else t = mcopy (w2n b) (w2n a) n s) /\
    th.t_var = tn.t_var /\ th.t_stor = tn.t_stor /\ th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
    th.t_mem = (tn.t_mem DIFF {j | w2n b <= j /\ j < w2n b+n}) UNION
      {w2n b+j | j < n /\ w2n a+j IN tn.t_mem}
Proof
  strip_tac >> drule copy_memory_emitted_shape >> disch_tac >>
  Cases_on `n = 0` >> fs[]
  >- (gvs[run_inst_seq_def] >> qexists_tac `tn` >> simp[inst_seq_ptr_def]) >>
  drule_all mcopy_singleton_counted_certificate >> simp[]
QED

Theorem copy_memory_endpoint_frame:
  compile_copy_memory (Var dst) (Var src) n sa = ((),sb) /\
  n < dimword(:256) /\ lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  (!p. lookup_var p t = lookup_var p s) /\
  mem_bytes_at (w2n b) n t.vs_memory = mem_bytes_at (w2n a) n s.vs_memory /\
  (!p k. p+k <= w2n b \/ w2n b+n <= p ==>
    mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory)
Proof
  strip_tac >> drule_all copy_memory_counted_certificate >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  Cases_on `n = 0` >> gvs[] >- simp[mem_bytes_at_def] >>
  conj_tac >- simp[mcopy_def, write_memory_with_expansion_def, lookup_var_def] >>
  conj_tac >- simp[mcopy_mem_bytes_at_same] >>
  rpt strip_tac >> irule mcopy_mem_bytes_at_disjoint >> simp[]
QED

Theorem copy_memory_counted_path:
  compile_copy_memory (Var dst) (Var src) n sa = ((),sb) /\
  n < dimword(:256) /\ lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?th.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G th
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
    th.t_var = tn.t_var /\ th.t_stor = tn.t_stor /\ th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
    th.t_mem = (tn.t_mem DIFF {j | w2n b <= j /\ j < w2n b+n}) UNION
      {w2n b+j | j < n /\ w2n a+j IN tn.t_mem}
Proof
  strip_tac >> drule_all copy_memory_counted_certificate >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  drule copy_memory_emitted_shape >> disch_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (Cases_on `n = 0` >> simp[mk_inst_def, is_terminator_def]) >>
  drule_all run_inst_seq_gas_path_ptr >> simp[] >> disch_tac >>
  qexists_tac `th` >> simp[]
QED
