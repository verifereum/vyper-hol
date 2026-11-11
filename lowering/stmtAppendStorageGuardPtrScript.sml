(* Opcode-specific application boundaries fix concrete runs before exposing
   the ghost parameters to the guard and suffix consumers. *)
Theory stmtAppendStorageGuardPtr
Ancestors stmtAppendStorageRunPtr instSeqComposePtr stmtSimAppendStorage
  exprLoweringProps emitHelperProps fragGasSeqPtr contextCodegenRel freshWrites
  stateFrame venomInst venomState ptrDiscipline finite_map list arithmetic compileEnv loweringStateRelDefs
  emittedSeqComposePtr abiDecoderArrayInit

Theorem emit_append_lt_uniform_ptr:
  !v cap st rop st' s t tn ctx.
  emit_op LT [Var v; Lit cap] st = (rop,st') /\
  run_inst_seq (emitted_insts st st') s = OK t /\
  op_taint tn (Var v) = {} /\
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp /\
  t.vs_requests = s.vs_requests /\ ~ctx_has_dalloca ctx ==>
  !D fn PG G. ?G' tn'.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st st')
            (s with vs_inst_idx := k) G' tn') /\
    op_taint tn' rop = {} /\ tn'.t_mem = tn.t_mem /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==>
         FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  rpt strip_tac >> irule emit_append_arith_uniform_ptr >> simp[] >>
  qexistsl_tac [`LT`, `[Var v; Lit cap]`] >>
  simp[] >> rpt strip_tac >> gvs[op_taint_def]
QED

Theorem append_storage_check_ptr:
  emit_op (if tr then TLOAD else SLOAD) [bop] st0 = (lop,st1) /\
  emit_op LT [lop; Lit cap] st1 = (valid,st2) /\
  run_inst_seq (emitted_insts st0 st1) s = OK s1 /\
  run_inst_seq (emitted_insts st1 st2) s1 = OK s2 /\
  state_frame s1 = state_frame s /\ state_frame s2 = state_frame s1 /\
  op_taint tn bop = {} /\ eval_operand bop s = SOME slot /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
  ~ctx_has_dalloca ctx ==>
  ?G2 tn2.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st0 st2)
           (s with vs_inst_idx := k) G2 tn2) /\
    op_taint tn2 valid = {} /\ op_taint tn2 lop = {} /\
    tn2.t_mem = tn.t_mem /\ tn2.t_stor = tn.t_stor /\
    tn2.t_trans = tn.t_trans /\ tn2.t_imm = tn.t_imm /\
    (!x. not_fresh_at st0 x ==>
         FLOOKUP G2 x = FLOOKUP G x /\
         op_taint tn2 (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `s1.vs_allocas = s.vs_allocas /\ s1.vs_fmp = s.vs_fmp /\
   s1.vs_requests = s.vs_requests /\
   s2.vs_allocas = s1.vs_allocas /\ s2.vs_fmp = s1.vs_fmp /\
   s2.vs_requests = s1.vs_requests` by
    metis_tac[state_frame_ptr_fields] >>
  qpat_x_assum `state_frame s1 = _` kall_tac >>
  qpat_x_assum `state_frame s2 = _` kall_tac >>
  drule_all emit_storage_load_uniform_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `G`, `D`] strip_assume_tac) >>
  `?v. lop = Var v` by metis_tac[emitted_insts_emit_op] >>
  qpat_x_assum `lop = Var v` SUBST_ALL_TAC >>
  drule_all emit_append_lt_uniform_ptr >>
  disch_then (qspecl_then [`D`, `fn`, `PG`, `G'`] strip_assume_tac) >>
  `st0.cs_next_var <= st1.cs_next_var /\ not_fresh_at st1 v` by
    (qpat_assum `emit_op (if tr then TLOAD else SLOAD) _ _ = _`
       (mp_then Any mp_tac emitted_insts_emit_op) >>
     simp[not_fresh_at_def]) >>
  imp_res_tac inst_extends_emit_op >>
  `~is_terminator (if tr then TLOAD else SLOAD)` by
    (Cases_on `tr` >> simp[is_terminator_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st0 st1)` by
    metis_tac[emitted_op_nonterminators] >>
  qexistsl_tac [`G''`, `tn''`] >> conj_tac
  >- (irule emitted_inst_seq_ptr_uniform_compose >> metis_tac[]) >>
  simp[] >> rpt strip_tac >>
  `not_fresh_at st1 x` by metis_tac[not_fresh_at_mono] >>
  metis_tac[]
QED

Theorem append_storage_guard_ptr:
  emit_op (if tr then TLOAD else SLOAD) [bop] st0 = (lop,st1) /\
  emit_op LT [lop; Lit cap] st1 = (valid,st2) /\
  emit_void ASSERT [valid] st2 = ((),st3) /\
  run_inst_seq (emitted_insts st0 st1) s = OK s1 /\
  run_inst_seq (emitted_insts st1 st2) s1 = OK s2 /\
  run_inst_seq (emitted_insts st2 st3) s2 = OK s3 /\
  state_frame s1 = state_frame s /\ state_frame s2 = state_frame s1 /\
  state_frame s3 = state_frame s2 /\
  op_taint tn bop = {} /\ eval_operand bop s = SOME slot /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
  ~ctx_has_dalloca ctx ==>
  ?G2 tn2.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st0 st3)
           (s with vs_inst_idx := k) G2 tn2) /\
    op_taint tn2 lop = {} /\
    tn2.t_mem = tn.t_mem /\ tn2.t_stor = tn.t_stor /\
    tn2.t_trans = tn.t_trans /\ tn2.t_imm = tn.t_imm /\
    (!x. not_fresh_at st0 x ==>
         FLOOKUP G2 x = FLOOKUP G x /\
         op_taint tn2 (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all append_storage_check_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `G`, `D`] strip_assume_tac) >>
  `s3.vs_allocas = s2.vs_allocas /\ s3.vs_fmp = s2.vs_fmp /\
   s3.vs_requests = s2.vs_requests` by
    metis_tac[state_frame_ptr_fields] >>
  qpat_x_assum `state_frame s3 = _` kall_tac >>
  `!k. inst_seq_ptr D 0 ctx fn PG G2 tn2 (emitted_insts st2 st3)
          (s2 with vs_inst_idx := k) G2 tn2` by
    (irule emit_append_assert_uniform_ptr >> simp[] >> metis_tac[]) >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends st0 st2` by metis_tac[inst_extends_trans] >>
  `~is_terminator (if tr then TLOAD else SLOAD) /\ ~is_terminator LT` by
    (Cases_on `tr` >> simp[is_terminator_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st0 st2)` by
    (irule abi_decoder_emitted_every_append >> qexists_tac `st1` >>
     metis_tac[emitted_op_nonterminators]) >>
  `run_inst_seq (emitted_insts st0 st2) s = OK s2` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`s1`, `st1`] >> simp[]) >>
  qexistsl_tac [`G2`, `tn2`] >> simp[] >>
  irule emitted_inst_seq_ptr_uniform_compose >> metis_tac[]
QED

Theorem append_storage_guard_abort_ptr:
  emit_op (if tr then TLOAD else SLOAD) [bop] st0 = (lop,st1) /\
  emit_op LT [lop; Lit cap] st1 = (valid,st2) /\
  emit_void ASSERT [valid] st2 = ((),st3) /\
  run_inst_seq (emitted_insts st0 st1) s = OK s1 /\
  run_inst_seq (emitted_insts st1 st2) s1 = OK s2 /\
  run_inst_seq (emitted_insts st2 st3) s2 = Abort ex s3 /\
  state_frame s1 = state_frame s /\ state_frame s2 = state_frame s1 /\
  op_taint tn bop = {} /\ eval_operand bop s = SOME slot /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
  ~ctx_has_dalloca ctx ==>
  ?G2 tn2.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st0 st3)
           (s with vs_inst_idx := k) G2 tn2) /\
    op_taint tn2 lop = {} /\
    tn2.t_mem = tn.t_mem /\ tn2.t_stor = tn.t_stor /\
    tn2.t_trans = tn.t_trans /\ tn2.t_imm = tn.t_imm /\
    (!x. not_fresh_at st0 x ==>
         FLOOKUP G2 x = FLOOKUP G x /\
         op_taint tn2 (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all append_storage_check_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `G`, `D`] strip_assume_tac) >>
  `!k. inst_seq_ptr D 0 ctx fn PG G2 tn2 (emitted_insts st2 st3)
          (s2 with vs_inst_idx := k) G2 tn2` by
    (irule emit_append_assert_abort_uniform_ptr >> simp[] >> metis_tac[]) >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends st0 st2` by metis_tac[inst_extends_trans] >>
  `~is_terminator (if tr then TLOAD else SLOAD) /\ ~is_terminator LT` by
    (Cases_on `tr` >> simp[is_terminator_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st0 st2)` by
    (irule abi_decoder_emitted_every_append >> qexists_tac `st1` >>
     metis_tac[emitted_op_nonterminators]) >>
  `run_inst_seq (emitted_insts st0 st2) s = OK s2` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`s1`, `st1`] >> simp[]) >>
  qexistsl_tac [`G2`, `tn2`] >> simp[] >>
  irule emitted_inst_seq_ptr_uniform_compose >> metis_tac[]
QED
