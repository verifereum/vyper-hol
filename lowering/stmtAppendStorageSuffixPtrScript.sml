(* Binary arithmetic boundary for the storage append suffix. *)
Theory stmtAppendStorageSuffixPtr
Ancestors stmtAppendStorageGuardPtr stmtAppendStorageRunPtr instSeqComposePtr
  exprLoweringProps emitHelperProps freshWrites stateFrame venomInst venomState
  ptrDiscipline finite_map list arithmetic compileEnv emittedSeqComposePtr
  abiDecoderArrayInit

Theorem emit_append_binary_uniform_ptr:
  !opc a b st rop st' s t tn ctx.
  emit_op opc [a;b] st = (rop,st') /\ (opc = ADD \/ opc = MUL) /\
  run_inst_seq (emitted_insts st st') s = OK t /\
  op_taint tn a = {} /\ op_taint tn b = {} /\
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
  qexistsl_tac [`opc`, `[a;b]`] >> simp[] >> rpt strip_tac >> gvs[]
QED

Theorem append_storage_address_ptr:
  emit_op ADD [bop; Lit 1w] st3 = (dop,st4) /\
  emit_op MUL [lop; Lit 1w] st4 = (off,st5) /\
  emit_op ADD [dop; off] st5 = (pop,st6) /\
  run_inst_seq (emitted_insts st3 st4) s3 = OK s4 /\
  run_inst_seq (emitted_insts st4 st5) s4 = OK s5 /\
  run_inst_seq (emitted_insts st5 st6) s5 = OK s6 /\
  state_frame s4 = state_frame s3 /\ state_frame s5 = state_frame s4 /\
  state_frame s6 = state_frame s5 /\
  op_taint tn bop = {} /\ op_taint tn lop = {} /\
  (!x. lop = Var x ==> not_fresh_at st3 x) /\ ~ctx_has_dalloca ctx ==>
  ?G6 tn6.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st3 st6)
           (s3 with vs_inst_idx := k) G6 tn6) /\
    op_taint tn6 pop = {} /\
    tn6.t_mem = tn.t_mem /\ tn6.t_stor = tn.t_stor /\
    tn6.t_trans = tn.t_trans /\ tn6.t_imm = tn.t_imm /\
    (!x. not_fresh_at st3 x ==>
         FLOOKUP G6 x = FLOOKUP G x /\
         op_taint tn6 (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `op_taint tn (Lit 1w) = {}` by simp[op_taint_def] >>
  `s4.vs_allocas = s3.vs_allocas /\ s4.vs_fmp = s3.vs_fmp /\
   s4.vs_requests = s3.vs_requests /\
   s5.vs_allocas = s4.vs_allocas /\ s5.vs_fmp = s4.vs_fmp /\
   s5.vs_requests = s4.vs_requests /\
   s6.vs_allocas = s5.vs_allocas /\ s6.vs_fmp = s5.vs_fmp /\
   s6.vs_requests = s5.vs_requests` by metis_tac[state_frame_ptr_fields] >>
  qpat_x_assum `state_frame s4 = _` kall_tac >>
  qpat_x_assum `state_frame s5 = _` kall_tac >>
  qpat_x_assum `state_frame s6 = _` kall_tac >>
  qpat_assum `emit_op ADD [bop; _] _ = _`
    (mp_then Any mp_tac (SRULE [] (Q.SPEC `ADD` emit_append_binary_uniform_ptr))) >>
  disch_then drule_all >>
  disch_then (qspecl_then [`D`, `fn`, `PG`, `G`] strip_assume_tac) >>
  `op_taint tn' lop = {}` by
    (`op_taint tn' lop = op_taint tn lop` by
       (irule old_operand_taint_frame >> metis_tac[]) >> simp[]) >>
  `op_taint tn' (Lit 1w) = {}` by simp[op_taint_def] >>
  qpat_assum `emit_op MUL _ _ = _`
    (mp_then Any mp_tac (SRULE [] (Q.SPEC `MUL` emit_append_binary_uniform_ptr))) >>
  disch_then drule_all >>
  disch_then (qspecl_then [`D`, `fn`, `PG`, `G'`] strip_assume_tac) >>
  `!x. dop = Var x ==> not_fresh_at st4 x` by
    (qpat_assum `emit_op ADD [bop; _] _ = _`
       (mp_then Any mp_tac emitted_insts_emit_op) >> simp[not_fresh_at_def]) >>
  `op_taint tn'' dop = {}` by
    (`op_taint tn'' dop = op_taint tn' dop` by
       (irule old_operand_taint_frame >> metis_tac[]) >> simp[]) >>
  qpat_assum `emit_op ADD [dop; off] _ = _`
    (mp_then Any mp_tac (SRULE [] (Q.SPEC `ADD` emit_append_binary_uniform_ptr))) >>
  disch_then drule_all >>
  disch_then (qspecl_then [`D`, `fn`, `PG`, `G''`] strip_assume_tac) >>
  rpt (qpat_x_assum `_.vs_allocas = _` kall_tac) >>
  rpt (qpat_x_assum `_.vs_fmp = _` kall_tac) >>
  rpt (qpat_x_assum `_.vs_requests = _` kall_tac) >>
  suspend "compose"
QED

Resume append_storage_address_ptr[compose]:
  rename1 `op_taint tn6 pop = {}` >>
  rename1 `!k. inst_seq_ptr D 0 ctx fn PG G'' tn'' (emitted_insts st5 st6)
                  (s5 with vs_inst_idx := k) Hfinal tn6` >>
  imp_res_tac inst_extends_emit_op >>
  `inst_extends st3 st5` by metis_tac[inst_extends_trans] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st3 st4) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st4 st5)` by
    metis_tac[emitted_op_nonterminators, is_terminator_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st3 st5)` by
    (irule abi_decoder_emitted_every_append >> metis_tac[]) >>
  `run_inst_seq (emitted_insts st3 st5) s3 = OK s5` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`s4`, `st4`] >> simp[]) >>
  `!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st3 st5)
          (s3 with vs_inst_idx := k) G'' tn''` by
    (irule emitted_inst_seq_ptr_uniform_compose >> metis_tac[]) >>
  `!x. not_fresh_at st3 x ==> not_fresh_at st4 x /\ not_fresh_at st5 x` by
    (imp_res_tac emitted_insts_emit_op >> metis_tac[not_fresh_at_mono, LESS_EQ_TRANS,
       DECIDE ``!n:num. n <= n + 1``]) >>
  qexistsl_tac [`Hfinal`, `tn6`] >> simp[] >>
  irule emitted_inst_seq_ptr_uniform_compose >> metis_tac[]
QED

Finalise append_storage_address_ptr
