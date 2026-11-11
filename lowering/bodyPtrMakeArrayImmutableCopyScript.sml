(* Runtime immutable copies compose with cursor-uniform pointer checks. *)
Theory bodyPtrMakeArrayImmutableCopy
Ancestors
  bodyPtrMakeArrayImmutableCompose bodyPtrMakeArraySeqCompose
  immutableCopyExecution exprSimCopy context compileEnv exprLoweringProps
  ptrDiscipline bodyPtrDefs fragGasSeqPtr venomState venomExecSemantics
  finite_map pred_set arithmetic freshWrites venomInst fragGasPathPtr
  bodyPtrMakeArrayImmutablePrefix

Theorem immutable_runtime_copy_checked:
  !n off sa sb s G tn.
  compile_imm_copy_to_memory F imm src (Var root) n off sa = ((),sb) /\
  copy_old_operand sa src /\ copy_old_operand sa (Var root) /\
  eval_operand src s = SOME a /\ lookup_var root s = SOME b /\
  op_taint tn src = {} /\ allocas_from 0 s /\ ptr_covers G tn root s m /\
  FLOOKUP G root = SOME (blo,cap) /\ blo + cap <= dimword(:256) /\
  off + 32*n <= m /\ ~ctx_has_dalloca ctx ==>
  ?u Gf tnf.
    copy_runtime_frame sa s sb u /\
    (!j. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := j) Gf tnf) /\
    u.vs_memory = (immutable_transfers F F a b n off s).vs_memory /\
    u.vs_data_section = s.vs_data_section /\ u.vs_immutables = s.vs_immutables /\
    u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp /\
    tnf.t_mem SUBSET tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_imm = tn.t_imm /\ u.vs_call_ctx = s.vs_call_ctx /\
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    (!i. i < w2n b+off \/ w2n b+off+32*n <= i ==>
      mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    ((!k. k < off ==> w2n b+k NOTIN tn.t_mem) ==>
      (!k. k < off+32*n ==> w2n b+k NOTIN tnf.t_mem)) /\
    (!p. not_fresh_at sa p ==>
      lookup_var p u = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  Induct
  >- (simp[compile_imm_copy_to_memory_def, comp_return_def] >>
      rpt strip_tac >> qexistsl_tac [`s`, `G`, `tn`] >>
      simp[copy_runtime_frame_refl, emitted_insts_def, inst_seq_ptr_def,
           immutable_transfers_def]) >>
  rpt gen_tac >>
  simp[immutable_copy_suc, comp_ignore_bind_def, immutable_comp_bind_cases] >>
  strip_tac >> rename1 `immutable_copy_one F imm src (Var root) off sa = ((),sc)` >>
  `off + 32 <= m` by decide_tac >>
  drule_all immutable_runtime_one_checked >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  `copy_old_operand sc src /\ copy_old_operand sc (Var root)` by
    metis_tac[copy_old_operand_mono, copy_runtime_frame_def] >>
  `eval_operand src u = SOME a` by metis_tac[copy_runtime_frame_operand] >>
  `lookup_var root u = SOME b /\ FLOOKUP Gf root = SOME (blo,cap) /\
   ptr_covers Gf tnf root u m` by
    (gvs[copy_old_operand_def, ptr_covers_def]) >>
  `op_taint tnf src = {}` by
    (Cases_on `src` >> fs[op_taint_def, copy_old_operand_def]) >>
  `allocas_from 0 u` by fs[allocas_from_def] >>
  `off + 32 + 32*n <= m` by decide_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule immutable_runtime_one_opcodes >> strip_tac >>
  drule_all copy_runtime_checked_append_uniform >> strip_tac >>
  qexistsl_tac [`u'`, `Gf'`, `tnf'`] >> simp[] >>
  conj_tac
  >- (simp[immutable_transfers_def] >>
      irule (cj 1 immutable_transfers_cong) >>
      simp[immutable_word_transfer_fields, immutable_transfer_data]) >>
  conj_tac >- (qpat_x_assum `_ SUBSET _` mp_tac >> simp[SUBSET_DEF]) >>
  conj_tac
  >- (rpt strip_tac >>
      ntac 2 (qpat_x_assum `!i. _ \/ _ ==> _ /\ _`
        (qspec_then `i` mp_tac) >> (impl_tac >- decide_tac) >> strip_tac) >>
      gvs[]) >>
  conj_tac
  >- (strip_tac >>
      `w2n (b+n2w off) = w2n b+off` by
        (irule immutable_destination_address_no_wrap >> metis_tac[]) >>
      `!k. k < off+32 ==> w2n b+k NOTIN tnf.t_mem` by
        (gen_tac >> strip_tac >> Cases_on `k < off` >>
         gvs[] >> simp[] >> decide_tac) >>
      `off + 32 * SUC n = (off+32)+32*n` by decide_tac >>
      asm_rewrite_tac[] >>
      qpat_x_assum `(_ ==> !k. _ ==> _ NOTIN tnf'.t_mem)` mp_tac >>
      simp[arithmeticTheory.ADD_COMM]) >>
  rpt strip_tac >>
  `not_fresh_at sc p` by
    (irule not_fresh_at_mono >> qexists_tac `sa` >> fs[copy_runtime_frame_def]) >>
  metis_tac[]
QED

Theorem immutable_runtime_copy_opcodes:
  compile_imm_copy_to_memory F imm src dst n off sa = ((),sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []
Proof
  strip_tac >> drule code_copy_insts >> strip_tac >>
  gvs[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
  fs[listTheory.EVERY_MEM] >>
  conj_tac >- (gen_tac >> strip_tac >>
    first_x_assum drule >> strip_tac >> gvs[is_terminator_def]) >>
  simp[listTheory.FILTER_EQ_NIL, listTheory.EVERY_MEM] >>
  gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >> gvs[]
QED

Theorem immutable_runtime_copy_ptr_path:
  compile_imm_copy_to_memory F imm src (Var root) n off sa = ((),sb) /\
  copy_old_operand sa src /\ copy_old_operand sa (Var root) /\
  eval_operand src s = SOME a /\ lookup_var root s = SOME b /\
  op_taint tn src = {} /\ allocas_from 0 s /\ ptr_covers G tn root s m /\
  FLOOKUP G root = SOME (blo,cap) /\ blo + cap <= dimword(:256) /\
  off + 32*n <= m /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?u Gf tnf.
    copy_runtime_frame sa s sb u /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf
      (OK (u with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
    u.vs_memory = (immutable_transfers F F a b n off s).vs_memory /\
    u.vs_data_section = s.vs_data_section /\ u.vs_immutables = s.vs_immutables /\
    u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp /\
    tnf.t_mem SUBSET tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_imm = tn.t_imm /\ u.vs_call_ctx = s.vs_call_ctx /\
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    (!i. i < w2n b+off \/ w2n b+off+32*n <= i ==>
      mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    ((!k. k < off ==> w2n b+k NOTIN tn.t_mem) ==>
      (!k. k < off+32*n ==> w2n b+k NOTIN tnf.t_mem)) /\
    (!p. not_fresh_at sa p ==>
      lookup_var p u = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (!p k. not_fresh_at sa p /\ ptr_covers G tn p s k ==>
      ptr_covers Gf tnf p u k)
Proof
  strip_tac >> drule_all immutable_runtime_copy_checked >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  drule immutable_runtime_copy_opcodes >> strip_tac >>
  `run_inst_seq (emitted_insts sa sb) s = OK u` by fs[copy_runtime_frame_def] >>
  `inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf` by
    (qpat_x_assum `!j. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
  drule_all run_inst_seq_gas_path_ptr >> strip_tac >>
  qexistsl_tac [`u`, `Gf`, `tnf`] >>
  conj_tac >- simp[] >>
  conj_tac
  >- (qpat_x_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >> simp[]) >>
  simp[] >> rpt strip_tac >> gvs[ptr_covers_def] >> metis_tac[]
QED
