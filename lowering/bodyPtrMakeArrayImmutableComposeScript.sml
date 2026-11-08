(* Assemble raw immutable-copy stages before lifting the installed path. *)
Theory bodyPtrMakeArrayImmutableCompose
Ancestors
  bodyPtrMakeArrayUniformStages bodyPtrMakeArraySeqCompose
  bodyPtrMakeArrayImmutableOne bodyPtrMakeArrayOffsetFrame
  bodyPtrMakeArrayImmutableStep exprSimCopy immutableCopyExecution immutableMemoryFrame
  freshWrites context compileEnv exprLoweringProps ptrDiscipline typedCopyPtr bodyPtrDefs
  venomState venomInst venomExecSemantics finite_map emitHelper emitHelperProps
  fragGasSeqPtr fragGasPathPtr

Theorem immutable_destination_address_no_wrap:
  ptr_covers G tn root s m /\ lookup_var root s = SOME b /\
  FLOOKUP G root = SOME (blo,cap) /\ blo + cap <= dimword(:256) /\
  off + 32 <= m ==>
  w2n (b+n2w off) = w2n b + off
Proof
  strip_tac >>
  `w2n b + off < dimword(:256)` by (gvs[ptr_covers_def] >> decide_tac) >>
  metis_tac[immutable_word_address_no_wrap, wordsTheory.n2w_w2n]
QED

Theorem immutable_runtime_one_exterior:
  u.vs_memory = (immutable_word_transfer F F a b off s).vs_memory /\
  tnf.t_mem = tn.t_mem DIFF {i | w2n (b+n2w off) <= i /\
                                   i < w2n (b+n2w off)+32} /\
  w2n (b+n2w off) = w2n b + off ==>
  !i. i < w2n b+off \/ w2n b+off+32 <= i ==>
    mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tnf.t_mem <=> i IN tn.t_mem)
Proof
  strip_tac >>
  `mem_agree_outside {i | w2n (b+n2w off) <= i /\
                         i < w2n (b+n2w off)+32}
     u.vs_memory s.vs_memory` by
    (qpat_x_assum `u.vs_memory = _` SUBST1_TAC >>
     pure_rewrite_tac[immutable_word_transfer_fields] >>
     irule mstore_memory_frame) >>
  fs[mem_agree_outside_def] >> rpt strip_tac >>
  `mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory` by
    (first_x_assum irule >> decide_tac) >> gvs[]
QED

Theorem immutable_runtime_source_pair:
  compile_lit_byte_offset src off sa = (op,sb) /\
  compile_imm_load_word F imm op sb = (value,sc) /\
  copy_old_operand sa src /\ eval_operand src s = SOME a /\
  op_taint tn src = {} /\ allocas_from 0 s /\ ~ctx_has_dalloca ctx ==>
  ?u Gf tnf.
    copy_runtime_frame sa s sc u /\
    (!j. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sc)
      (s with vs_inst_idx := j) Gf tnf) /\
    eval_operand value u = SOME (immutable_copy_read F (a+n2w off) s) /\
    copy_old_operand sc value /\ op_taint tnf value = {} /\
    u.vs_memory = s.vs_memory /\ u.vs_data_section = s.vs_data_section /\
    u.vs_immutables = s.vs_immutables /\
    u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_imm = tn.t_imm /\ u.vs_call_ctx = s.vs_call_ctx /\
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    (!p. not_fresh_at sa p ==>
      lookup_var p u = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all immutable_byte_offset_raw_frame >>
  disch_then (qspecl_then [`fn`, `PG`, `G`, `D`] strip_assume_tac) >>
  rename1 `copy_runtime_frame sa s sb u` >>
  `allocas_from 0 u` by fs[allocas_from_def] >>
  drule_all immutable_runtime_load_raw_frame >>
  disch_then (qspecl_then [`fn`, `PG`, `Gf`, `D`] strip_assume_tac) >>
  rename1 `copy_runtime_frame sb u sc v` >>
  `!j. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
     (s with vs_inst_idx := j) Gf tnf` by
    (drule_all immutable_offset_checks_uniform >> simp[]) >>
  `!j. inst_seq_ptr D 0 ctx fn PG Gf tnf (emitted_insts sb sc)
     (u with vs_inst_idx := j) Gf' tnf'` by
    (drule_all immutable_runtime_load_checks_uniform >> simp[]) >>
  drule immutable_byte_offset_opcodes >> strip_tac >>
  drule_all copy_runtime_checked_append_uniform >> strip_tac >>
  qexistsl_tac [`v`, `Gf'`, `tnf'`] >>
  simp[immutable_copy_read_def] >>
  rpt strip_tac >>
  `not_fresh_at sb p` by
    (irule not_fresh_at_mono >> qexists_tac `sa` >> fs[copy_runtime_frame_def]) >>
  metis_tac[]
QED

Theorem immutable_runtime_destination_pair:
  compile_lit_byte_offset (Var root) off sa = (dst,sb) /\
  emit_void MSTORE [dst;value] sb = ((),sc) /\
  copy_old_operand sa (Var root) /\ copy_old_operand sa value /\
  lookup_var root s = SOME b /\ eval_operand value s = SOME w /\
  op_taint tn value = {} /\ ptr_covers G tn root s m /\
  FLOOKUP G root = SOME (blo,cap) /\ blo + cap <= dimword(:256) /\
  off + 32 <= m /\ ~ctx_has_dalloca ctx ==>
  ?u Gf tnf.
    copy_runtime_frame sa s sc u /\
    (!j. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sc)
      (s with vs_inst_idx := j) Gf tnf) /\
    u.vs_memory = (mstore (w2n (b+n2w off)) w s).vs_memory /\
    u.vs_data_section = s.vs_data_section /\ u.vs_immutables = s.vs_immutables /\
    u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n (b+n2w off) <= i /\
                                      i < w2n (b+n2w off) + 32} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_imm = tn.t_imm /\ u.vs_call_ctx = s.vs_call_ctx /\
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    (!p. not_fresh_at sa p ==>
      lookup_var p u = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `eval_operand (Var root) s = SOME b /\ op_taint tn (Var root) = {}` by
    gvs[eval_operand_def, ptr_covers_def] >>
  drule_all immutable_byte_offset_raw_frame >>
  disch_then (qspecl_then [`fn`, `PG`, `G`, `D`] strip_assume_tac) >>
  rename1 `copy_runtime_frame sa s sb u` >>
  `copy_old_operand sb value /\ eval_operand value u = SOME w` by
    metis_tac[copy_old_operand_mono, copy_runtime_frame_operand, copy_runtime_frame_def] >>
  `op_taint tnf value = {}` by
    (Cases_on `value` >> fs[op_taint_def, copy_old_operand_def]) >>
  `?p. dst = Var p /\ ptr_covers Gf tnf p u 32` by
    (`off + 32 * SUC 0 <= m` by simp[] >>
     drule_all immutable_destination_raw_window >> simp[]) >>
  gvs[eval_operand_def] >>
  drule_all immutable_runtime_store_raw_frame >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  `!j. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
     (s with vs_inst_idx := j) Gf tnf` by
    (`eval_operand (Var root) s = SOME b` by simp[eval_operand_def] >>
     drule_all immutable_offset_checks_uniform >> simp[]) >>
  `!j. inst_seq_ptr D 0 ctx fn PG Gf tnf (emitted_insts sb sc)
     (u with vs_inst_idx := j) Gf' tnf'` by
    (drule_all immutable_runtime_store_checks_uniform >> simp[]) >>
  drule immutable_byte_offset_opcodes >> strip_tac >>
  drule_all copy_runtime_checked_append_uniform >> strip_tac >>
  qexistsl_tac [`u'`, `Gf'`, `tnf'`] >> simp[] >>
  conj_tac >- simp[mstore_def] >>
  rpt strip_tac >> fs[mstore_def, lookup_var_def, op_taint_def] >> metis_tac[]
QED

Theorem immutable_runtime_source_opcodes:
  compile_lit_byte_offset src off sa = (op,sb) /\
  compile_imm_load_word F imm op sb = (value,sc) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sc) /\
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sc) = []
Proof
  strip_tac >> drule immutable_byte_offset_extends >> strip_tac >>
  drule immutable_byte_offset_opcodes >> strip_tac >>
  gvs[compile_imm_load_word_def] >>
  drule emitted_insts_emit_op >> strip_tac >>
  `emitted_insts sa sc = emitted_insts sa sb ++ emitted_insts sb sc` by
    (irule emitted_insts_append >> simp[]) >>
  simp[mk_inst_def, is_terminator_def, listTheory.FILTER_APPEND_DISTRIB]
QED

Theorem immutable_runtime_one_checked:
  immutable_copy_one F imm src (Var root) off sa = ((),sb) /\
  copy_old_operand sa src /\ copy_old_operand sa (Var root) /\
  eval_operand src s = SOME a /\ lookup_var root s = SOME b /\
  op_taint tn src = {} /\ allocas_from 0 s /\ ptr_covers G tn root s m /\
  FLOOKUP G root = SOME (blo,cap) /\ blo + cap <= dimword(:256) /\
  off + 32 <= m /\ ~ctx_has_dalloca ctx ==>
  ?u Gf tnf.
    copy_runtime_frame sa s sb u /\
    (!j. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := j) Gf tnf) /\
    u.vs_memory = (immutable_word_transfer F F a b off s).vs_memory /\
    (!i. i < w2n b+off \/ w2n b+off+32 <= i ==>
      mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    u.vs_data_section = s.vs_data_section /\ u.vs_immutables = s.vs_immutables /\
    u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n (b+n2w off) <= i /\
                                      i < w2n (b+n2w off) + 32} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_imm = tn.t_imm /\ u.vs_call_ctx = s.vs_call_ctx /\
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    (!p. not_fresh_at sa p ==>
      lookup_var p u = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  qpat_x_assum `immutable_copy_one _ _ _ _ _ _ = _` mp_tac >>
  simp[immutable_copy_one_def, immutable_comp_bind_cases] >> strip_tac >>
  rename1 `compile_lit_byte_offset src off sa = (op,sc)` >>
  rename1 `compile_imm_load_word F imm op sc = (value,sd)` >>
  drule_all immutable_runtime_source_pair >>
  disch_then (qspecl_then [`fn`, `PG`, `G`, `D`] strip_assume_tac) >>
  rename1 `copy_runtime_frame sa s sd u` >>
  `not_fresh_at sa root` by fs[copy_old_operand_def] >>
  `copy_old_operand sd (Var root) /\ lookup_var root u = SOME b /\
   FLOOKUP Gf root = SOME (blo,cap) /\ ptr_covers Gf tnf root u m` by
    (conj_tac
     >- (irule copy_old_operand_mono >> qexists_tac `sa` >>
         fs[copy_runtime_frame_def]) >>
     gvs[ptr_covers_def]) >>
  drule_all immutable_runtime_destination_pair >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  rename1 `copy_runtime_frame sd u sb v` >>
  drule_all immutable_runtime_source_opcodes >> strip_tac >>
  drule_all copy_runtime_checked_append_uniform >> strip_tac >>
  `v.vs_memory = (immutable_word_transfer F F a b off s).vs_memory` by
    fs[immutable_word_transfer_def, immutable_copy_read_def, mstore_def] >>
  `w2n (b+n2w off) = w2n b+off` by
    (drule_all immutable_destination_address_no_wrap >> simp[]) >>
  `tnf'.t_mem = tn.t_mem DIFF {i | w2n (b+n2w off) <= i /\
                                      i < w2n (b+n2w off)+32}` by metis_tac[] >>
  `!i. i < w2n b+off \/ w2n b+off+32 <= i ==>
     mem_bytes_at i 1 v.vs_memory = mem_bytes_at i 1 s.vs_memory /\
     (i IN tnf'.t_mem <=> i IN tn.t_mem)` by
    metis_tac[immutable_runtime_one_exterior] >>
  qexistsl_tac [`v`, `Gf'`, `tnf'`] >> simp[] >>
  conj_tac >- (qpat_x_assum `!i. _ \/ _ ==> _ /\ _` mp_tac >> simp[]) >>
  rpt strip_tac >>
  `not_fresh_at sd p` by
    (irule not_fresh_at_mono >> qexists_tac `sa` >> fs[copy_runtime_frame_def]) >>
  metis_tac[]
QED

Theorem immutable_runtime_one_opcodes:
  immutable_copy_one F imm src dst off sa = ((),sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []
Proof
  simp[immutable_copy_one_def, immutable_comp_bind_cases] >> strip_tac >>
  rename1 `compile_lit_byte_offset src off sa = (op,sc)` >>
  rename1 `compile_imm_load_word F imm op sc = (value,sd)` >>
  rename1 `compile_lit_byte_offset dst off sd = (dst_op,se)` >>
  drule_all immutable_runtime_source_opcodes >> strip_tac >>
  drule_all immutable_byte_offset_extends >> strip_tac >>
  drule_at (Pat `compile_lit_byte_offset dst off sd = _`)
    immutable_byte_offset_opcodes >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `emitted_insts sd sb = emitted_insts sd se ++ emitted_insts se sb` by
    (irule emitted_insts_append >> simp[]) >>
  `sd.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sd` by
    (qpat_assum `compile_lit_byte_offset src off sa = _`
       (mp_then Any strip_assume_tac immutable_byte_offset_extends) >>
     gvs[compile_imm_load_word_def] >> drule emitted_insts_emit_op >> strip_tac >>
     `emitted_insts sa sd = emitted_insts sa sc ++ emitted_insts sc sd` by
       (irule emitted_insts_append >> simp[]) >> simp[]) >>
  `emitted_insts sa sb = emitted_insts sa sd ++ emitted_insts sd sb` by
    (irule emitted_insts_append >> simp[listTheory.APPEND_ASSOC]) >>
  simp[mk_inst_def, is_terminator_def, listTheory.FILTER_APPEND_DISTRIB]
QED

Theorem immutable_runtime_one_ptr_path:
  immutable_copy_one F imm src (Var root) off sa = ((),sb) /\
  copy_old_operand sa src /\ copy_old_operand sa (Var root) /\
  eval_operand src s = SOME a /\ lookup_var root s = SOME b /\
  op_taint tn src = {} /\ allocas_from 0 s /\ ptr_covers G tn root s m /\
  FLOOKUP G root = SOME (blo,cap) /\ blo + cap <= dimword(:256) /\
  off + 32 <= m /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?u Gf tnf.
    copy_runtime_frame sa s sb u /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf
      (OK (u with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
    u.vs_memory = (immutable_word_transfer F F a b off s).vs_memory /\
    (!i. i < w2n b+off \/ w2n b+off+32 <= i ==>
      mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    u.vs_data_section = s.vs_data_section /\ u.vs_immutables = s.vs_immutables /\
    u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n (b+n2w off) <= i /\
                                      i < w2n (b+n2w off) + 32} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_imm = tn.t_imm /\ u.vs_call_ctx = s.vs_call_ctx /\
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    (!p. not_fresh_at sa p ==>
      lookup_var p u = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (!p k. not_fresh_at sa p /\ ptr_covers G tn p s k ==>
      ptr_covers Gf tnf p u k)
Proof
  strip_tac >> drule_all immutable_runtime_one_checked >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  drule immutable_runtime_one_opcodes >> strip_tac >>
  `run_inst_seq (emitted_insts sa sb) s = OK u` by fs[copy_runtime_frame_def] >>
  `inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf` by
    (qpat_x_assum `!j. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
  drule_all run_inst_seq_gas_path_ptr >> strip_tac >>
  qexistsl_tac [`u`, `Gf`, `tnf`] >>
  conj_tac >- simp[] >>
  conj_tac
  >- (qpat_x_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >> simp[]) >>
  simp[] >>
  rpt strip_tac >> gvs[ptr_covers_def] >> metis_tac[]
QED
