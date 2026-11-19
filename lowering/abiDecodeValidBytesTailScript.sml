(* Sequence certificates for the rounded padding store and bytes copy. *)
Theory abiDecodeValidBytesTail
Ancestors
  abiDecodePtrMemberFrame abiDecoderBytesRuntime abiDecoderRange loweringStateRelDefs
  bodyPtrBopScalarCompile bodyPtrBopScalarSeq bodyPtrBopScalarOutcome
  emitHelperProps exprLoweringProps compileEnv emitHelper freshWrites
  fragExecMem instMemFrontier memSafeRun logAbiPrefixPtr
  exprSimPtrTopLevelImmutableCopy ghostPcTransportPtr fragGasSeqPtr
  allocaFootprint dynCopyExec bodyPtrPrecompileBuiltinsStaging
  bodyPtrMakeArrayCopyStep abiDecodeStaticProps
  assignTuplePtrLocalBytesCopy assignTuplePtrLocalFixedCopy assignTuplePtrBytesCopy
  assignTuplePtrCopyLen reasonCopySourcePtr
  abiDecoderBytesPhases abiDecoderBytesMemory abiDecoderContract
  decoderGhostFramePtr bodyPtrDefs valueCopy
  venomState venomExecSemantics venomInst ptrDiscipline
  list pred_set finite_map words arithmetic

Theorem bytes_tail_round_code[local]:
  emit_op ADD [cnt;Lit 31w] sa = (up,c1) /\
  emit_op NOT [Lit 31w] c1 = (mask,c2) /\
  emit_op AND [up;mask] c2 = (rounded,sb) ==>
  bop_scalar_seq {x | not_fresh_at sa x} {cnt;Lit 31w} (emitted_insts sa sb)
    (rounded INSERT mask INSERT up INSERT {cnt;Lit 31w}) /\
  sb.cs_current_insts = sa.cs_current_insts ++ (emitted_insts sa sb) /\
  (!x. not_fresh_at sa x ==> not_fresh_at sb x) /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
  (!s. run_inst_seq_mem_ok (emitted_insts sa sb) s)
Proof
  strip_tac >> simp[] >>
  imp_res_tac inst_extends_emit_op >>
  `emitted_insts sa sb = emitted_insts sa c1 ++
     emitted_insts c1 c2 ++ emitted_insts c2 sb` by
    metis_tac[emitted_insts_append, inst_extends_def, inst_extends_trans] >>
  `!x. not_fresh_at sa x ==> not_fresh_at c1 x /\ not_fresh_at c2 x /\
                             not_fresh_at sb x` by
    (imp_res_tac emitted_insts_emit_op >> fs[not_fresh_at_def]) >>
  `bop_scalar_seq {x | not_fresh_at sa x} {cnt;Lit 31w}
     (emitted_insts sa c1) (up INSERT {cnt;Lit 31w})` by
    (irule bop_scalar_seq_emit_op >> simp[] >>
     qexistsl [`ADD`, `[cnt;Lit 31w]`] >> simp[]) >>
  `bop_scalar_seq {x | not_fresh_at sa x} (up INSERT {cnt;Lit 31w})
     (emitted_insts c1 c2) (mask INSERT up INSERT {cnt;Lit 31w})` by
    (irule bop_scalar_seq_emit_op >> simp[] >>
     qexistsl [`NOT`, `[Lit 31w]`] >> simp[]) >>
  `bop_scalar_seq {x | not_fresh_at sa x} (mask INSERT up INSERT {cnt;Lit 31w})
     (emitted_insts c2 sb) (rounded INSERT mask INSERT up INSERT {cnt;Lit 31w})` by
    (irule bop_scalar_seq_emit_op >> simp[] >>
     qexistsl [`AND`, `[up;mask]`] >> simp[]) >>
  conj_tac
  >- (simp[] >> irule bop_scalar_seq_append >>
      qexists `mask INSERT up INSERT {cnt;Lit 31w}` >> simp[] >>
      irule bop_scalar_seq_append >> qexists `up INSERT {cnt;Lit 31w}` >> simp[]) >>
  conj_tac >- metis_tac[inst_extends_trans, inst_extends_def] >>
  imp_res_tac emitted_insts_emit_op >> simp[mk_inst_def, is_terminator_def] >>
  gen_tac >> irule run_inst_seq_mem_ok_every >> simp[] >>
  rpt conj_tac >> gen_tac >>
  simp[below_frontier_no_ranges, inst_dload_in_section_def, mk_inst_def]
QED

Theorem bytes_tail_round_run[local]:
  emit_op ADD [cnt;Lit 31w] sa = (up,c1) /\
  emit_op NOT [Lit 31w] c1 = (mask,c2) /\
  emit_op AND [up;mask] c2 = (rounded,sb) /\
  eval_operand cnt s = SOME (n2w c) /\ c+31 < dimword(:256) /\
  fresh_vars_wrt sa s ==>
  ?r. run_inst_seq (emitted_insts sa sb) s = OK r /\
      eval_operand rounded r = SOME (n2w (32*((c+31) DIV 32))) /\
      fresh_vars_wrt sb r
Proof
  strip_tac >>
  `eval_operand (Lit 31w) s = SOME 31w` by simp[eval_operand_def] >>
  drule_all emit_op_ADD_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa c1) s = OK s1` >>
  `eval_operand (Lit 31w) s1 = SOME 31w` by simp[eval_operand_def] >>
  drule_all emit_op_NOT_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `eval_operand up s2 = SOME ((n2w c:bytes32)+31w)` by metis_tac[] >>
  drule_all emit_op_AND_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 sb) s2 = OK r` >>
  imp_res_tac inst_extends_emit_op >>
  qpat_assum `run_inst_seq (emitted_insts sa c1) _ = _`
    (mp_then (Pat `run_inst_seq (emitted_insts st st1) s = _`) mp_tac
      abi_decode_sequence_chain) >>
  disch_then drule_all >> strip_tac >>
  qpat_assum `run_inst_seq (emitted_insts sa c2) _ = _`
    (mp_then (Pat `run_inst_seq (emitted_insts st st1) s = _`) mp_tac
      abi_decode_sequence_chain) >>
  disch_then drule_all >> strip_tac >>
  qexists `r` >> simp[GSYM abi_decode_bytes_round_word]
QED

Theorem bytes_tail_round_certificate[local]:
  emit_op ADD [cnt;Lit 31w] sa = (up,c1) /\
  emit_op NOT [Lit 31w] c1 = (mask,c2) /\
  emit_op AND [up;mask] c2 = (rounded,sb) /\
  eval_operand cnt s = SOME (n2w c) /\
  c+31 < dimword(:256) /\ fresh_vars_wrt sa s /\
  op_prov G cnt = NONE /\ op_taint tn cnt = {} /\ ~ctx_has_dalloca ctx /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r Gr tr.
    run_inst_seq (emitted_insts sa sb) s = OK (r with vs_inst_idx := s.vs_inst_idx) /\
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gr tr /\
    eval_operand rounded r = SOME (n2w (contractABI$ceil32 c)) /\
    op_prov Gr rounded = NONE /\ op_taint tr rounded = {} /\
    r.vs_inst_idx = LENGTH sb.cs_current_insts /\
    r = s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|> /\
    tr.t_mem = tn.t_mem /\ tr.t_stor = tn.t_stor /\
    tr.t_trans = tn.t_trans /\ tr.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> not_fresh_at sb x /\
         lookup_var x r = lookup_var x s /\ FLOOKUP Gr x = FLOOKUP G x /\
         FLOOKUP tr.t_var x = FLOOKUP tn.t_var x) /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  strip_tac >> drule_all bytes_tail_round_run >> strip_tac >>
  drule_all bytes_tail_round_code >> simp[] >> strip_tac >>
  `!op. op IN {cnt;Lit 31w} ==> op_prov G op = NONE /\ op_taint tn op = {}` by
    (simp[] >> rpt strip_tac >> gvs[op_prov_def, op_taint_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by simp[] >>
  drule_all bop_scalar_seq_run >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  drule_all bop_scalar_seq_runtime_frame >> strip_tac >>
  `op_prov G' rounded = NONE /\ op_taint tn' rounded = {}` by
    (qpat_assum `!op. op IN rounded INSERT _ ==> _`
      (qspec_then `rounded` mp_tac) >> simp[]) >>
  `r.vs_inst_idx = s.vs_inst_idx` by
    (qpat_assum `r = s with vs_vars := _` (fn th => simp[Once th])) >>
  qexistsl [`r with vs_inst_idx := LENGTH sb.cs_current_insts`, `G'`, `tn'`] >>
  conj_tac >- simp[venom_state_component_equality] >>
  simp[lookup_var_def, contractABITheory.ceil32_def] >>
  qpat_assum `r = s with vs_vars := _` (fn th => simp[Once th])
QED

Theorem bytes_tail_offset_certificate[local]:
  emit_op ADD [Var dst;offset] sa = (Var last,sb) /\
  ptr_covers G tn dst s (q+32) /\ lookup_var dst s = SOME (n2w d) /\
  eval_operand offset s = SOME (n2w q) /\ op_taint tn offset = {} /\
  d+q < dimword(:256) /\ ~ctx_has_dalloca ctx /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gt tt.
    run_inst_seq (emitted_insts sa sb) s = OK (t with vs_inst_idx := s.vs_inst_idx) /\
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gt tt /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
    lookup_var last t = SOME (n2w (d+q)) /\ ptr_covers Gt tt last t 32 /\
    tt.t_mem = tn.t_mem /\ tt.t_stor = tn.t_stor /\
    tt.t_trans = tn.t_trans /\ tt.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> not_fresh_at sb x /\
         lookup_var x t = lookup_var x s /\ FLOOKUP Gt x = FLOOKUP G x /\
         op_taint tt (Var x) = op_taint tn (Var x)) /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  strip_tac >>
  `w2n (n2w d:bytes32) = d` by simp[wordsTheory.w2n_n2w] >>
  `w2n (n2w d:bytes32) + q < dimword(:256)` by asm_rewrite_tac[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by simp[] >>
  qpat_assum `emit_op ADD _ sa = _` (mp_then Any mp_tac emit_addr_add_seq_ptr) >>
  disch_then drule_all >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  `emitted_insts sa sb = [mk_inst sa.cs_next_id ADD [Var dst;offset] [last]] /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
   (!x. not_fresh_at sa x ==> not_fresh_at sb x)` by
    (drule emitted_insts_emit_op >> strip_tac >> fs[not_fresh_at_def]) >>
  qabbrev_tac `i = mk_inst sa.cs_next_id ADD [Var dst;offset] [last]` >>
  `step_inst_base i s = OK (update_var last (n2w (d+q)) s)` by
    simp[Abbr `i`, step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
         eval_operand_def, word_add_n2w] >>
  `sf = update_var last (n2w (d+q)) s /\ tnf.t_imm = tn.t_imm` by
    gvs[run_inst_seq_def, inst_seq_ptr_def, Abbr `i`, toplevel_immutable_add_ghost_frame] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule run_inst_seq_mem_ok_every >>
     simp[Abbr `i`, below_frontier_no_ranges, inst_dload_in_section_def, mk_inst_def]) >>
  qexistsl [`sf with vs_inst_idx := LENGTH sb.cs_current_insts`, `Gf`, `tnf`] >>
  simp[Abbr `i`, update_var_def, lookup_var_def, ptr_covers_inst_idx,
       word_add_n2w, mk_inst_def, is_terminator_def, venom_state_component_equality] >>
  rpt strip_tac >> res_tac >> gvs[lookup_var_def, word_add_n2w]
QED

Theorem bytes_tail_pad_certificate[local]:
  emit_void MSTORE [Var last;Lit 0w] sa = ((),sb) /\
  ptr_covers G tn last s 32 /\ lookup_var last s = SOME (n2w j) /\
  j < dimword(:256) /\ j+32 <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t tt.
    run_inst_seq (emitted_insts sa sb) s = OK (t with vs_inst_idx := s.vs_inst_idx) /\
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G tt /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t = (mstore j 0w s with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    tt.t_mem = tn.t_mem DIFF {i | j <= i /\ i < j+32} /\
    tt.t_stor = tn.t_stor /\ tt.t_trans = tn.t_trans /\ tt.t_imm = tn.t_imm /\
    tt.t_var = tn.t_var /\ (!x. lookup_var x t = lookup_var x s) /\
    (!x. not_fresh_at sa x ==> not_fresh_at sb x) /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  `w2n (n2w j:bytes32) = j` by simp[] >>
  `eval_operand (Var last) s = SOME (n2w j) /\ eval_operand (Lit 0w) s = SOME 0w /\
   op_taint tn (Lit 0w) = {}` by simp[eval_operand_def, op_taint_def] >>
  `w2n (n2w j:bytes32)+32 <= s.vs_alloca_next` by asm_rewrite_tac[] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule emit_mstore_mem_ok >> goal_assum $ drule_at Any >> metis_tac[]) >>
  qabbrev_tac `i = mk_inst sa.cs_next_id MSTORE [Var last;Lit 0w] []` >>
  qabbrev_tac `r = mstore j 0w s` >>
  `step_inst_base (mk_inst sa.cs_next_id MSTORE [Var last;Lit 0w] []) s =
     OK (mstore (w2n (n2w j:bytes32)) 0w s)` by (irule step_MSTORE >> simp[]) >>
  `step_inst_base i s = OK r` by simp[Abbr `i`, Abbr `r`] >>
  `inst_seq_ptr D 0 ctx fn PG G tn [i] s G (step_taint i s r tn)` by
    (`ctx_has_dalloca ctx ==> allocas_below_fmp s` by simp[] >>
     drule_all clean_word_store_checked_cursors >>
     disch_then (qspecl_then [`sa.cs_next_id`, `fn`, `PG`, `D`, `s.vs_inst_idx`] mp_tac) >>
     simp[Abbr `i`, Abbr `r`]) >>
  drule_all mstore_raw_ghost_frame >>
  disch_then (qspecl_then [`tn`, `sa.cs_next_id`, `PG`, `G`] strip_assume_tac) >>
  qexistsl [`r with vs_inst_idx := LENGTH sb.cs_current_insts`, `step_taint i s r tn`] >>
  gs[Abbr `r`, Abbr `i`, run_inst_seq_def, not_fresh_at_def, op_taint_def] >>
  simp[mk_inst_def, is_terminator_def, lookup_var_def, mstore_def,
       write_memory_with_expansion_def, venom_state_component_equality]
QED

Theorem bytes_tail_count_certificate[local]:
  emit_op ADD [Lit 32w;cnt] sa = (Var len,sb) /\
  eval_operand cnt s = SOME (n2w c) /\ op_taint tn cnt = {} /\
  ~ctx_has_dalloca ctx /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gt tt.
    run_inst_seq (emitted_insts sa sb) s = OK (t with vs_inst_idx := s.vs_inst_idx) /\
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gt tt /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
    eval_operand (Var len) t = SOME (n2w (32+c)) /\ op_taint tt (Var len) = {} /\
    tt.t_mem = tn.t_mem /\ tt.t_stor = tn.t_stor /\
    tt.t_trans = tn.t_trans /\ tt.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> not_fresh_at sb x /\
         lookup_var x t = lookup_var x s /\ FLOOKUP Gt x = FLOOKUP G x /\
         op_taint tt (Var x) = op_taint tn (Var x)) /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  strip_tac >>
  `eval_operand (Lit 32w) s = SOME 32w /\ op_taint tn (Lit 32w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by simp[] >>
  qpat_assum `emit_op ADD _ sa = _`
    (mp_then Any mp_tac (SRULE [] (Q.INST
       [`f` |-> `word_add:bytes32 -> bytes32 -> bytes32`, `opc` |-> `ADD`]
       (SPEC_ALL emit_copy_len_binop_normalized_ptr)))) >>
  disch_then drule_all >>
  disch_then (qspecl_then [`fn`, `PG`, `G`, `D`] strip_assume_tac) >>
  `emitted_insts sa sb = [mk_inst sa.cs_next_id ADD [Lit 32w;cnt] [len]] /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
   (!x. not_fresh_at sa x ==> not_fresh_at sb x)` by
    (drule emitted_insts_emit_op >> strip_tac >> fs[not_fresh_at_def]) >>
  qabbrev_tac `i = mk_inst sa.cs_next_id ADD [Lit 32w;cnt] [len]` >>
  `step_inst_base i s = OK (update_var len (n2w (32+c)) s)` by
    simp[Abbr `i`, step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
         word_add_n2w] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule run_inst_seq_mem_ok_every >>
     simp[Abbr `i`, below_frontier_no_ranges, inst_dload_in_section_def, mk_inst_def]) >>
  rename1 `run_inst_seq _ s = OK (t with vs_inst_idx := s.vs_inst_idx)` >>
  `t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|>` by
    fs[run_inst_seq_def, update_var_def, venom_state_component_equality] >>
  qexistsl [`t`, `G'`, `tn'`] >>
  gs[Abbr `i`, word_add_n2w, eval_operand_def, mk_inst_def, is_terminator_def] >>
  metis_tac[]
QED

Theorem bytes_tail_copy_certificate[local]:
  emit_void MCOPY [Var dst;Var ar;len] sa = ((),sb) /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~ctx_has_dalloca ctx /\
  lookup_var dst s = SOME (n2w d) /\ lookup_var ar s = SOME (n2w a) /\
  eval_operand len s = SOME (n2w n) /\ op_taint tn len = {} /\
  d < dimword(:256) /\ a < dimword(:256) /\ n < dimword(:256) /\
  d+n <= s.vs_alloca_next /\ a+n <= s.vs_alloca_next /\
  ptr_covers G tn dst s n /\ ptr_covers G tn ar s n ==>
  ?t tt.
    run_inst_seq (emitted_insts sa sb) s = OK (t with vs_inst_idx := s.vs_inst_idx) /\
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G tt /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t = (mcopy d a n s with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    tt.t_var = tn.t_var /\ tt.t_stor = tn.t_stor /\
    tt.t_trans = tn.t_trans /\ tt.t_imm = tn.t_imm /\
    (!x. lookup_var x t = lookup_var x s) /\
    (!i. i < n ==> (d+i IN tt.t_mem <=> a+i IN tn.t_mem)) /\
    (!i. ~(d <= i /\ i < d+n) ==> (i IN tt.t_mem <=> i IN tn.t_mem)) /\
    (!x. not_fresh_at sa x ==> not_fresh_at sb x) /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  strip_tac >>
  `w2n (n2w d:bytes32) = d /\ w2n (n2w a:bytes32) = a /\
   w2n (n2w n:bytes32) = n` by simp[] >>
  `eval_operand (Var dst) s = SOME (n2w d) /\
   eval_operand (Var ar) s = SOME (n2w a)` by simp[eval_operand_def] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (qpat_assum `emit_void MCOPY _ sa = _`
       (mp_then (Pat `emit_void MCOPY _ _ = _`) mp_tac emit_mcopy_mem_ok) >> simp[]) >>
  `ptr_covers G tn dst s (w2n (n2w n:bytes32)) /\
   ptr_covers G tn ar s (w2n (n2w n:bytes32))` by simp[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by simp[] >>
  qpat_assum `emit_void MCOPY _ sa = _` (mp_then Any mp_tac emit_mcopy_normalized_ptr) >>
  disch_then drule_all >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  `tn' = step_taint (mk_inst sa.cs_next_id MCOPY [Var dst;Var ar;len] []) s
                   (mcopy (w2n (n2w d:bytes32)) (w2n (n2w a:bytes32)) n s) tn` by simp[] >>
  drule_all mcopy_operand_taint_frames_ptr >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  qexistsl [`t`, `tn'`] >>
  gs[not_fresh_at_def, lookup_var_def, mcopy_def, write_memory_with_expansion_def] >>
  first_assum ACCEPT_TAC
QED

Theorem bytes_tail_append[local]:
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  sc.cs_current_insts = sb.cs_current_insts ++ emitted_insts sb sc /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sb sc) /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK (t with vs_inst_idx := s.vs_inst_idx) /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G1 tn1 /\
  run_inst_seq (emitted_insts sb sc) t = OK (u with vs_inst_idx := t.vs_inst_idx) /\
  u.vs_inst_idx = LENGTH sc.cs_current_insts /\
  inst_seq_ptr D 0 ctx fn PG G1 tn1 (emitted_insts sb sc) t G2 tn2 /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  run_inst_seq_mem_ok (emitted_insts sb sc) t ==>
  run_inst_seq (emitted_insts sa sc) s = OK (u with vs_inst_idx := s.vs_inst_idx) /\
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sc) s G2 tn2 /\
  sc.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sc /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sc) /\
  run_inst_seq_mem_ok (emitted_insts sa sc) s
Proof
  strip_tac >> drule_all emitted_insts_join_normalized_ptr >> strip_tac >> simp[] >>
  `emitted_insts sa sc = emitted_insts sa sb ++ emitted_insts sb sc` by
    metis_tac[emitted_insts_append] >>
  simp[] >> irule run_inst_seq_mem_ok_append >> simp[]
QED

Theorem bytes_tail_runtime_cuts[local]:
  abi_decode_bytes_runtime_tail (Var dst) (Var ar) cnt cm = ((),en) /\
  s.vs_inst_idx = LENGTH cm.cs_current_insts /\ fresh_vars_wrt cm s /\
  ~ctx_has_dalloca ctx /\ eval_operand cnt s = SOME (n2w c) /\
  op_prov G cnt = NONE /\ op_taint tn cnt = {} /\
  lookup_var dst s = SOME (n2w d) /\ lookup_var ar s = SOME (n2w a) /\
  ptr_covers G tn dst s cap /\ ptr_covers G tn ar s (32+c) /\
  c+31 < dimword(:256) /\ a < dimword(:256) /\
  d+cap < dimword(:256) /\ 32+c < dimword(:256) /\
  32+contractABI$ceil32 c <= cap /\
  d+cap <= s.vs_alloca_next /\ a+32+c <= s.vs_alloca_next ==>
  ?t Gf tf mid.
    run_inst_seq (emitted_insts cm en) s = OK (t with vs_inst_idx := s.vs_inst_idx) /\
    run_inst_seq_mem_ok (emitted_insts cm en) s /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts cm en) s Gf tf /\
    t.vs_inst_idx = LENGTH en.cs_current_insts /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_allocas = s.vs_allocas /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at cm x ==> not_fresh_at en x /\
         lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
         op_taint tf (Var x) = op_taint tn (Var x)) /\
    mid = tn.t_mem DIFF {i | d+contractABI$ceil32 c <= i /\ i < d+contractABI$ceil32 c+32} /\
    (!i. i < 32+c ==> (d+i IN tf.t_mem <=> a+i IN mid)) /\
    (!i. ~(d <= i /\ i < d+(32+c)) ==> (i IN tf.t_mem <=> i IN mid))
Proof
  strip_tac >>
  `not_fresh_at cm dst /\ not_fresh_at cm ar` by
    (fs[fresh_vars_wrt_def, not_fresh_at_def, lookup_var_def] >>
     metis_tac[optionTheory.NOT_SOME_NONE, GREATER_EQ, TO_FLOOKUP]) >>
  qpat_x_assum `abi_decode_bytes_runtime_tail _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [abi_decode_bytes_runtime_tail_def, comp_bind_def,
                    comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename [`emit_op ADD [cnt;Lit 31w] cm = (up,c1)`,
          `emit_op NOT [Lit 31w] c1 = (mask,c2)`,
          `emit_op AND [up;mask] c2 = (rounded,c3)`,
          `emit_op ADD [Var dst;rounded] c3 = (last,c4)`,
          `emit_void MSTORE [last;Lit 0w] c4 = ((),c5)`,
          `emit_op ADD [Lit 32w;cnt] c5 = (len,c6)`,
          `emit_void MCOPY [Var dst;Var ar;len] c6 = ((),en)`] >>
  `c <= contractABI$ceil32 c` by simp[contractABITheory.ceil32_def, abi_decode_bytes_round_bounds] >>
  `c+31 < dimword(:256)` by
    (qpat_assum `c <= _` mp_tac >> qpat_assum `contractABI$ceil32 c + 32 <= _` mp_tac >>
     qpat_assum `cap + d < _` mp_tac >> decide_tac) >>
  drule_all bytes_tail_round_certificate >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  `?lv. last = Var lv` by
    (qpat_assum `emit_op ADD [Var dst;rounded] c3 = _` mp_tac >>
     simp[NoAsms, loweringShapeRulesTheory.emit_op_eq] >> metis_tac[]) >>
  qpat_x_assum `last = Var _` SUBST_ALL_TAC >>
  `lookup_var dst r = SOME (n2w d) /\ ptr_covers Gr tr dst r cap` by
    (qpat_assum `!x. not_fresh_at cm x ==> not_fresh_at c3 x /\ _`
       (qspec_then `dst` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
     `op_taint tr (Var dst) = op_taint tn (Var dst)` by simp[op_taint_def] >>
     metis_tac[ptr_covers_lookup_frame]) >>
  `ptr_covers Gr tr dst r (contractABI$ceil32 c+32)` by (irule ptr_covers_mono >> metis_tac[]) >>
  `d+contractABI$ceil32 c < dimword(:256)` by
    (qpat_assum `contractABI$ceil32 c+32 <= _` mp_tac >> qpat_assum `cap+d < _` mp_tac >> decide_tac) >>
  drule_all bytes_tail_offset_certificate >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  rename [`run_inst_seq (emitted_insts c3 c4) r = OK (u4 with vs_inst_idx := _)`,
          `inst_seq_ptr D 0 ctx fn PG Gr tr (emitted_insts c3 c4) r G4 t4`] >>
  `u4.vs_alloca_next = s.vs_alloca_next /\ u4.vs_labels = s.vs_labels` by
    (conj_tac >> qpat_assum `u4 = _` (fn th => simp[Once th]) >>
     qpat_assum `r = _` (fn th => simp[Once th])) >>
  `d+contractABI$ceil32 c+32 <= u4.vs_alloca_next` by
    (qpat_assum `contractABI$ceil32 c+32 <= _` mp_tac >>
     qpat_assum `cap+d <= _` mp_tac >>
     asm_rewrite_tac[] >> decide_tac) >>
  drule_all bytes_tail_pad_certificate >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  rename [`run_inst_seq (emitted_insts c4 c5) u4 = OK (u5 with vs_inst_idx := _)`,
          `inst_seq_ptr D 0 ctx fn PG G4 t4 (emitted_insts c4 c5) u4 G4 t5`] >>
  `u5.vs_alloca_next = s.vs_alloca_next /\ u5.vs_labels = s.vs_labels` by
    (qpat_assum `u5 = _` (fn th => simp[th, mstore_def, write_memory_with_expansion_def])) >>
  `!x. not_fresh_at cm x ==>
     not_fresh_at c5 x /\ lookup_var x u5 = lookup_var x s /\
     FLOOKUP G4 x = FLOOKUP G x /\ op_taint t5 (Var x) = op_taint tn (Var x)` by
    (rpt gen_tac >> strip_tac >> res_tac >>
     fs[op_taint_def]) >>
  `eval_operand cnt u5 = SOME (n2w c) /\ op_taint t5 cnt = {}` by
    (Cases_on `cnt` >> fs[eval_operand_def, op_taint_def] >>
     rename1 `lookup_var x s = SOME (n2w c)` >>
     `not_fresh_at cm x` by
       (fs[fresh_vars_wrt_def, not_fresh_at_def, lookup_var_def] >>
        metis_tac[optionTheory.NOT_SOME_NONE, GREATER_EQ, TO_FLOOKUP]) >>
     res_tac >> fs[]) >>
  `?nv. len = Var nv` by
    (qpat_assum `emit_op ADD [Lit 32w;cnt] c5 = _` mp_tac >>
     simp[NoAsms, loweringShapeRulesTheory.emit_op_eq] >> metis_tac[]) >>
  qpat_x_assum `len = Var _` SUBST_ALL_TAC >>
  drule_all bytes_tail_count_certificate >>
  disch_then (qspecl_then [`fn`, `PG`, `G4`, `D`] strip_assume_tac) >>
  rename [`run_inst_seq (emitted_insts c5 c6) u5 = OK (u6 with vs_inst_idx := _)`,
          `inst_seq_ptr D 0 ctx fn PG G4 t5 (emitted_insts c5 c6) u5 G6 t6`] >>
  `u6.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `u6 = _` (fn th => simp[Once th])) >>
  `!x. not_fresh_at cm x ==>
     not_fresh_at c6 x /\ lookup_var x u6 = lookup_var x s /\
     FLOOKUP G6 x = FLOOKUP G x /\ op_taint t6 (Var x) = op_taint tn (Var x)` by
    (rpt gen_tac >> strip_tac >> res_tac >> fs[]) >>
  `lookup_var dst u6 = SOME (n2w d) /\ lookup_var ar u6 = SOME (n2w a) /\
   ptr_covers G6 t6 dst u6 cap /\ ptr_covers G6 t6 ar u6 (c+32)` by
    (qpat_assum `!x. not_fresh_at cm x ==> not_fresh_at c6 x /\ _`
       (fn th => map_every (fn q => qspec_then q mp_tac th) [`dst`, `ar`]) >>
     rpt (impl_tac >- simp[]) >> rpt strip_tac >> metis_tac[ptr_covers_lookup_frame]) >>
  `ptr_covers G6 t6 dst u6 (c+32)` by
    (irule ptr_covers_mono >> goal_assum $ drule_at Any >>
     qpat_assum `c <= contractABI$ceil32 c` mp_tac >> qpat_assum `contractABI$ceil32 c+32 <= _` mp_tac >> decide_tac) >>
  `eval_operand (Var nv) u6 = SOME (n2w (c+32))` by metis_tac[ADD_COMM] >>
  `d < dimword(:256) /\ d+(c+32) <= u6.vs_alloca_next /\ a+(c+32) <= u6.vs_alloca_next` by
    (qpat_assum `cap+d < _` mp_tac >> qpat_assum `cap+d <= _` mp_tac >>
     qpat_assum `a+(c+32) <= _` mp_tac >> qpat_assum `c <= contractABI$ceil32 c` mp_tac >>
     qpat_assum `contractABI$ceil32 c+32 <= _` mp_tac >> asm_rewrite_tac[] >> decide_tac) >>
  drule_all bytes_tail_copy_certificate >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  rename [`run_inst_seq (emitted_insts c6 en) u6 = OK (u with vs_inst_idx := _)`,
          `inst_seq_ptr D 0 ctx fn PG G6 t6 (emitted_insts c6 en) u6 G6 tu`] >>
  map_every (fn q => qpat_assum q
      (mp_then (Pat `run_inst_seq (emitted_insts sa sb) s = _`) mp_tac
        bytes_tail_append) >> disch_then drule_all >> strip_tac)
    [`run_inst_seq (emitted_insts cm c3) s = _`,
     `run_inst_seq (emitted_insts cm c4) s = _`,
     `run_inst_seq (emitted_insts cm c5) s = _`,
     `run_inst_seq (emitted_insts cm c6) s = _`] >>
  `u.vs_alloca_next = s.vs_alloca_next /\ u.vs_allocas = s.vs_allocas` by
    (conj_tac >>
     map_every (fn q => qpat_assum q (fn th => simp[Once th]))
       [`u = _`, `u6 = _`, `u5 = _`, `u4 = _`, `r = _`]) >>
  qexistsl [`u`, `G6`, `tu`] >>
  `t6.t_mem = tn.t_mem DIFF {i | d+contractABI$ceil32 c <= i /\ i < d+contractABI$ceil32 c+32}` by simp[] >>
  simp[DIFF_DEF] >> rpt strip_tac >> res_tac >> fs[op_taint_def]
QED

(* The copy and the padding word may overlap. Only the suffix of the
   rounded extent outside the copy depends on the zero store. *)
Theorem bytes_tail_taint_ranges[local]:
  c <= q /\ q <= c+32 /\
  (!i. a <= i /\ i < a+(32+c) ==> i NOTIN src) /\
  mid = src DIFF {i | d+q <= i /\ i < d+q+32} /\
  (!i. i < 32+c ==> (d+i IN out <=> a+i IN mid)) /\
  (!i. ~(d <= i /\ i < d+(32+c)) ==> (i IN out <=> i IN mid)) ==>
  (!i. d <= i /\ i < d+(32+q) ==> i NOTIN out) /\
  (!i. ~(d <= i /\ i < d+(32+q)) ==> (i IN out <=> i IN src))
Proof
  strip_tac >> conj_tac
  >- (rpt strip_tac >> Cases_on `i < d+(32+c)`
      >- (`i-d < 32+c /\ d+(i-d) = i /\ a <= a+(i-d) /\ a+(i-d) < a+(32+c)` by
            decide_tac >>
          `a+(i-d) NOTIN src` by (first_x_assum irule >> simp[]) >>
          qpat_assum `!j. j < 32+c ==> _` (qspec_then `i-d` mp_tac) >>
          metis_tac[IN_DIFF]) >>
      `d+q <= i /\ i < d+q+32` by decide_tac >>
      qpat_assum `!j. ~(d <= j /\ j < d+(32+c)) ==> _`
        (qspec_then `i` mp_tac) >> simp[IN_DIFF]) >>
  gen_tac >> disch_tac >>
  `~(d <= i /\ i < d+(32+c)) /\ ~(d+q <= i /\ i < d+q+32)` by decide_tac >>
  qpat_assum `!j. ~(d <= j /\ j < d+(32+c)) ==> _`
    (qspec_then `i` mp_tac) >> simp[IN_DIFF]
QED

Theorem abi_decode_valid_bytes_tail_certificate:
  abi_decode_bytes_runtime_tail (Var dst) (Var ar) cnt cm = ((),en) /\
  s.vs_inst_idx = LENGTH cm.cs_current_insts /\ fresh_vars_wrt cm s /\
  ~ctx_has_dalloca ctx /\ eval_operand cnt s = SOME (n2w c) /\
  op_prov G cnt = NONE /\ op_taint tn cnt = {} /\
  abi_decode_ptr_window G tn s srcvar (n2w B) L /\
  abi_decode_ptr_window G tn s ar (n2w (B+p)) (32+c) /\
  lookup_var dst s = SOME (n2w d) /\ ptr_covers G tn dst s cap /\
  p+32+c <= L /\ c+31 < dimword(:256) /\
  32+contractABI$ceil32 c <= cap /\
  B+L < dimword(:256) /\ d+cap < dimword(:256) /\
  B+L <= s.vs_alloca_next /\ d+cap <= s.vs_alloca_next /\
  regions_disjoint B L d cap ==>
  ?t Gf tf.
    run_inst_seq (emitted_insts cm en) s = OK (t with vs_inst_idx := s.vs_inst_idx) /\
    run_inst_seq_mem_ok (emitted_insts cm en) s /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts cm en) s Gf tf /\
    t.vs_inst_idx = LENGTH en.cs_current_insts /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_allocas = s.vs_allocas /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
    abi_decode_ptr_window Gf tf t srcvar (n2w B) L /\
    abi_decode_ptr_window Gf tf t ar (n2w (B+p)) (32+c) /\
    ptr_covers Gf tf dst t cap /\
    abi_decode_ptr_window Gf tf t dst (n2w d) (32+contractABI$ceil32 c) /\
    (!x. not_fresh_at cm x ==> not_fresh_at en x /\
         lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
         op_taint tf (Var x) = op_taint tn (Var x)) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    mem_agree_outside {i | d <= i /\ i < d+(32+contractABI$ceil32 c)}
      t.vs_memory s.vs_memory /\
    (!i. ~(d <= i /\ i < d+(32+contractABI$ceil32 c)) ==>
          (i IN tf.t_mem <=> i IN tn.t_mem))
Proof
  strip_tac >>
  qabbrev_tac `a = B+p` >>
  `B <= a /\ a+(32+c) <= B+L` by (unabbrev_all_tac >> decide_tac) >>
  `a < dimword(:256) /\ B < dimword(:256) /\ a+32+c <= s.vs_alloca_next` by
    (qpat_assum `a+(32+c) <= _` mp_tac >> qpat_assum `B+L < _` mp_tac >>
     qpat_assum `B+L <= _` mp_tac >> decide_tac) >>
  `c <= contractABI$ceil32 c /\ contractABI$ceil32 c < c+32` by
    simp[contractABITheory.ceil32_def, abi_decode_bytes_round_bounds] >>
  `32+c < dimword(:256) /\ d < dimword(:256) /\ d+contractABI$ceil32 c < dimword(:256)` by
    (qpat_assum `c <= contractABI$ceil32 c` mp_tac >> qpat_assum `32+contractABI$ceil32 c <= _` mp_tac >>
     qpat_assum `d+cap < _` mp_tac >> decide_tac) >>
  `lookup_var ar s = SOME (n2w a) /\ ptr_covers G tn ar s (32+c) /\
   (!i. a <= i /\ i < a+(32+c) ==> i NOTIN tn.t_mem)` by
    fs[abi_decode_ptr_window_def, w2n_n2w] >>
  drule_all bytes_tail_runtime_cuts >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  `contractABI$ceil32 c <= c+32` by (qpat_assum `contractABI$ceil32 c < c+32` mp_tac >> decide_tac) >>
  drule_all bytes_tail_taint_ranges >> strip_tac >>
  `eval_operand (Var dst) s = SOME (n2w d) /\
   eval_operand (Var ar) s = SOME (n2w a)` by simp[eval_operand_def] >>
  drule_all (REWRITE_RULE [GSYM contractABITheory.ceil32_def]
    abi_decode_bytes_runtime_tail_sequence) >>
  disch_then (qx_choose_then `raw` strip_assume_tac) >>
  `raw = t with vs_inst_idx := s.vs_inst_idx` by
    (qpat_assum `run_inst_seq _ _ = OK raw` mp_tac >>
     qpat_assum `run_inst_seq _ _ = OK (t with vs_inst_idx := _)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >> simp[]) >>
  `abi_decode_frame d (32+contractABI$ceil32 c) s
     (mcopy d a (32+c) (mstore (d+contractABI$ceil32 c) 0w s))` by
    (irule abi_decode_bytes_store_copy_frame >> simp[ADD_COMM]) >>
  `t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
   mem_agree_outside {i | d <= i /\ i < d+(32+contractABI$ceil32 c)}
     t.vs_memory s.vs_memory` by
    (qpat_assum `raw = _` SUBST_ALL_TAC >>
     gvs[abi_decode_frame_def, mem_agree_outside_def] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `lookup_var srcvar s = SOME (n2w B)` by fs[abi_decode_ptr_window_def] >>
  `not_fresh_at cm srcvar /\ not_fresh_at cm ar /\ not_fresh_at cm dst` by
    (fs[fresh_vars_wrt_def, not_fresh_at_def, lookup_var_def] >>
     metis_tac[optionTheory.NOT_SOME_NONE, GREATER_EQ, TO_FLOOKUP]) >>
  `!i. B <= i /\ i < B+L ==> ~(d <= i /\ i < d+(32+contractABI$ceil32 c))` by
    (qpat_assum `32+contractABI$ceil32 c <= cap` mp_tac >>
     qpat_assum `regions_disjoint B L d cap` mp_tac >>
     rewrite_tac[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `ptr_covers Gf tf dst t cap` by
    (qpat_assum `ptr_covers G tn dst s cap` (mp_then Any mp_tac ptr_covers_frame) >>
     disch_then irule >> simp[]) >>
  `ptr_covers Gf tf dst t (32+contractABI$ceil32 c)` by (irule ptr_covers_mono >> metis_tac[]) >>
  `!i. B <= i /\ i < B+L ==> (i IN tf.t_mem <=> i IN tn.t_mem)` by
    (rpt strip_tac >>
     qpat_assum `!j. ~(d <= j /\ j < d+(32+contractABI$ceil32 c)) ==> _`
       (qspec_then `i` mp_tac) >>
     qpat_assum `!j. B <= j /\ j < B+L ==> _` (qspec_then `i` mp_tac) >>
     simp[]) >>
  qexistsl [`t`,`Gf`,`tf`] >> asm_rewrite_tac[] >> rpt conj_tac
  >- (qpat_assum `abi_decode_ptr_window G tn s srcvar _ _`
        (mp_then Any mp_tac abi_decode_ptr_window_frame) >>
      disch_then irule >> simp[w2n_n2w])
  >- (qpat_assum `abi_decode_ptr_window G tn s ar _ _`
        (mp_then Any mp_tac abi_decode_ptr_window_frame) >>
      disch_then irule >> simp[w2n_n2w] >> rpt strip_tac >>
      first_x_assum irule >> decide_tac) >>
  simp[abi_decode_ptr_window_def, w2n_n2w]
QED
