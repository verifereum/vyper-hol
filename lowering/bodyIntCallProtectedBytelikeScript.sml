Theory bodyIntCallProtectedBytelike
Ancestors
  bodyIntCallProtectedBuffer exprSimLiteralBuffer exprSimAlloc
  exprLowering exprLoweringProps context compileEnv emitHelperProps
  fragExec freshWrites intCallFrame valueEncodingProps finite_map
  rich_list list words venomState valueEncoding

Theorem protected_bytelike_literal_run:
  compile_bytelike_literal bs (LENGTH bs) sa = (buf,sb) /\
  fn_has_code sa sb func /\ stmt_state_rel ctx func ce cx es s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  32 + 32 * word_size (LENGTH bs) < dimword (:256) /\
  allocas_above lo s /\ (!a len. P a len ==> a + len <= lo) /\
  (!op x. reserved op /\ op = Var x ==> not_fresh_at sa x) ==>
  ?u w. run_inst_seq (emitted_insts sa sb) s = OK u /\
    stmt_state_rel ctx func ce cx es u /\
    eval_operand buf.buf_operand u = SOME w /\
    FLOOKUP u.vs_allocas sa.cs_next_id =
      SOME (w2n w,32 + 32 * word_size (LENGTH bs)) /\
    lo <= w2n w /\
    w2n w + (32 + 32 * word_size (LENGTH bs)) < dimword (:256) /\
    mem_word_at (w2n w) u.vs_memory = n2w (LENGTH bs) /\
    mem_bytes_at (w2n w + 32) (LENGTH bs) u.vs_memory = bs /\
    (!a len. P a len ==>
      mem_bytes_at a len u.vs_memory = mem_bytes_at a len s.vs_memory) /\
    (!op. reserved op ==> eval_operand op u = eval_operand op s) /\
    allocas_above lo u /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP u.vs_allocas aid = SOME entry)
Proof
  strip_tac >>
  qpat_x_assum `compile_bytelike_literal _ _ _ = _` mp_tac >>
  simp_tac (bool_ss ++ pairSimps.PAIR_ss)
    [compile_bytelike_literal_def, LET_THM, comp_bind_def,
     comp_ignore_bind_def, GSYM vfmConstantsTheory.word_size_def] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [comp_return_def] >>
  strip_tac >> gvs[] >>
  rename1 `compile_alloc_buffer _ sa = (buf,sm)` >>
  rename1 `emit_void MSTORE _ sm = (u,sh)` >> Cases_on `u` >>
  rename1 `compile_store_byte_chunks _ _ _ sh = (v,sb)` >> Cases_on `v` >>
  suspend "stages"
QED

Resume protected_bytelike_literal_run[stages]:
  `ci_mono sa sm` by
    (qspecl_then [`32 * word_size (LENGTH bs) + 32`, `sa`]
       mp_tac ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono sm sh` by
    (qspecl_then [`MSTORE`, `[buf.buf_operand; Lit (n2w (LENGTH bs))]`, `sm`]
       mp_tac ci_mono_emit_void >> simp[]) >>
  `ci_mono sh sb` by
    (qspecl_then [`buf.buf_operand`, `bs`, `32`, `sh`]
       mp_tac ci_mono_compile_store_byte_chunks >> simp[]) >>
  `cs_extends sm sb` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sa sm func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split]) >>
  `32 <= 32 * word_size (LENGTH bs) + 32` by simp[] >>
  `!op x. reserved op /\ op = Var x ==> not_fresh_at sa x` by simp[] >>
  drule_all protected_alloc_header_run >> strip_tac >>
  `local_ptrs_reserved ce sh` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     fs[ci_mono_def] >> decide_tac) >>
  `!x. buf.buf_operand = Var x ==> not_fresh_at sh x` by
    (fs[ci_mono_def] >> metis_tac[not_fresh_at_mono]) >>
  drule_all buffer_alloc_code >> strip_tac >>
  `w2n w < dimword (:256)` by simp[] >>
  `eval_operand buf.buf_operand u = SOME (n2w (w2n w))` by simp[] >>
  `w2n w + 32 + 32 * word_size (LENGTH bs) < dimword (:256)` by decide_tac >>
  `32 + 32 * word_size (LENGTH bs) <= 32 * word_size (LENGTH bs) + 32` by simp[] >>
  drule_at (Pat `MEM _ (fn_insts _)`) allocated_literal_chunks_run >>
  disch_then (drule_all o SRULE [venomInstTheory.mk_inst_def]) >> strip_tac >>
  suspend "resources"
QED

Resume protected_bytelike_literal_run[resources]:
  rename1 `run_inst_seq (emitted_insts sh sb) u = OK z` >>
  `sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm` by
    (qpat_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp_tac (bool_ss ++ pairSimps.PAIR_ss)
       [compile_alloc_buffer_def, comp_bind_def, comp_return_def, LET_THM] >>
     pairarg_tac >> simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >> strip_tac >>
     drule emit_op_extends >> gvs[]) >>
  drule emit_void_extends >> strip_tac >>
  `run_inst_seq (emitted_insts sa sb) s = OK z` by
    (irule run_emitted_compose3 >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `z.vs_allocas = u.vs_allocas /\ z.vs_alloca_next = u.vs_alloca_next /\
   z.vs_labels = u.vs_labels` by
    (qpat_x_assum `_ with <|vs_memory := _; vs_vars := _|> = _` mp_tac >>
     simp[venom_state_component_equality]) >>
  qexistsl_tac [`z`, `w`] >> simp[allocas_above_def] >>
  conj_tac
  >- (gvs[eval_operand_def] >>
      qpat_x_assum `!x. not_fresh_at sh x ==> _` (qspec_then `p` mp_tac) >>
      gvs[mstore_def, lookup_var_def]) >>
  conj_tac >- gvs[mstore_def] >>
  conj_tac
  >- (`mem_bytes_at (w2n w) 32 z.vs_memory =
       mem_bytes_at (w2n w) 32 u.vs_memory` by
        (first_x_assum irule >> simp[]) >>
      `mem_word_at (w2n w) z.vs_memory = mem_word_at (w2n w) u.vs_memory` by
        (fs[mem_word_at_def, mem_bytes_at_def]) >>
      gvs[mstore_mem_word_at_same]) >>
  conj_tac
  >- (rpt strip_tac >>
      `a + len <= w2n w + 32` by metis_tac[arithmeticTheory.LESS_EQ_TRANS,
        arithmeticTheory.LESS_EQ_ADD] >>
      metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `eval_operand op u = eval_operand op s` by metis_tac[] >>
      `eval_operand op z = eval_operand op u` suffices_by metis_tac[] >>
      Cases_on `op` >> simp[eval_operand_def]
      >- (rename1 `lookup_var x z = _` >>
          `not_fresh_at sh x` by
            (fs[ci_mono_def] >>
             `sa.cs_next_var <= sh.cs_next_var` by decide_tac >>
             irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
          qpat_x_assum `!x. not_fresh_at sh x ==> _` (qspec_then `x` mp_tac) >>
          gvs[eval_operand_def]) >>
      gvs[eval_operand_def]) >>
  gvs[allocas_above_def, mstore_def] >> metis_tac[]
QED

Finalise protected_bytelike_literal_run

Theorem protected_bytelike_literal_counted:
  compile_bytelike_literal bs (LENGTH bs) sa = (buf,sb) /\
  fn_has_code sa sb func /\ stmt_state_rel ctx func ce cx es s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  32 + 32 * word_size (LENGTH bs) < dimword (:256) /\
  allocas_above lo s /\ (!a len. P a len ==> a + len <= lo) /\
  (!op x. reserved op /\ op = Var x ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u w. run_inst_seq (emitted_insts sa sb) s = OK u /\
    stmt_state_rel ctx func ce cx es u /\
    eval_operand buf.buf_operand u = SOME w /\
    FLOOKUP u.vs_allocas sa.cs_next_id =
      SOME (w2n w,32 + 32 * word_size (LENGTH bs)) /\
    lo <= w2n w /\
    w2n w + (32 + 32 * word_size (LENGTH bs)) < dimword (:256) /\
    mem_word_at (w2n w) u.vs_memory = n2w (LENGTH bs) /\
    mem_bytes_at (w2n w + 32) (LENGTH bs) u.vs_memory = bs /\
    (!a len. P a len ==>
      mem_bytes_at a len u.vs_memory = mem_bytes_at a len s.vs_memory) /\
    (!op. reserved op ==> eval_operand op u = eval_operand op s) /\
    allocas_above lo u /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP u.vs_allocas aid = SOME entry) /\
    gas_path ctx func s 0 (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    u.vs_current_bb = sb.cs_current_bb
Proof
  strip_tac >> drule_all protected_bytelike_literal_run >> strip_tac >>
  drule_all literal_bytelike_gas_path >> strip_tac >>
  qexistsl_tac [`u`, `w`] >> simp[]
QED
