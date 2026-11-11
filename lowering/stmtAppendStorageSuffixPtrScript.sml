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

Theorem append_storage_store_tail_ptr:
  emit_void (if tr then TSTORE else SSTORE) [pop;vop] st6 = ((),st7) /\
  emit_op ADD [lop; Lit 1w] st7 = (nop,st8) /\
  emit_void (if tr then TSTORE else SSTORE) [bop;nop] st8 = ((),st9) /\
  run_inst_seq (emitted_insts st6 st7) s6 = OK s7 /\
  run_inst_seq (emitted_insts st7 st8) s7 = OK s8 /\
  run_inst_seq (emitted_insts st8 st9) s8 = OK s9 /\
  s7.vs_allocas = s6.vs_allocas /\ s7.vs_fmp = s6.vs_fmp /\
  s7.vs_requests = s6.vs_requests /\
  s8.vs_allocas = s7.vs_allocas /\ s8.vs_fmp = s7.vs_fmp /\
  s8.vs_requests = s7.vs_requests /\
  s9.vs_allocas = s8.vs_allocas /\ s9.vs_fmp = s8.vs_fmp /\
  s9.vs_requests = s8.vs_requests /\
  eval_operand pop s6 = SOME addr /\ eval_operand bop s8 = SOME slot /\
  op_taint tn pop = {} /\ op_taint tn vop = {} /\
  op_taint tn lop = {} /\ op_taint tn bop = {} /\
  (!x. bop = Var x ==> not_fresh_at st7 x) /\ ~ctx_has_dalloca ctx ==>
  ?G9 tn9.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st6 st9)
           (s6 with vs_inst_idx := k) G9 tn9) /\
    tn9.t_mem = tn.t_mem /\ tn9.t_imm = tn.t_imm /\
    (if tr then
       tn9.t_trans = key_update (key_update tn.t_trans addr {}) slot {} /\
       tn9.t_stor = tn.t_stor
     else
       tn9.t_stor = key_update (key_update tn.t_stor addr {}) slot {} /\
       tn9.t_trans = tn.t_trans) /\
    (!x. not_fresh_at st6 x ==>
         FLOOKUP G9 x = FLOOKUP G x /\
         op_taint tn9 (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  qabbrev_tac `tn7 = if tr then tn with t_trans := key_update tn.t_trans addr {}
                    else tn with t_stor := key_update tn.t_stor addr {}` >>
  `!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st6 st7)
          (s6 with vs_inst_idx := k) G tn7` by
    (simp[Abbr `tn7`] >> irule emit_storage_store_uniform_ptr >> metis_tac[]) >>
  `op_taint tn7 lop = {} /\ op_taint tn7 bop = {} /\
   op_taint tn7 (Lit 1w) = {}` by
    (Cases_on `tr` >> gvs[Abbr `tn7`, op_taint_def]) >>
  qpat_assum `emit_op ADD _ _ = _`
    (mp_then Any mp_tac (SRULE [] (Q.SPEC `ADD` emit_append_binary_uniform_ptr))) >>
  disch_then drule_all >>
  disch_then (qspecl_then [`D`, `fn`, `PG`, `G`] strip_assume_tac) >>
  `op_taint tn' bop = {}` by
    (`op_taint tn' bop = op_taint tn7 bop` by
       (irule old_operand_taint_frame >> metis_tac[]) >> simp[]) >>
  qabbrev_tac `tn9 = if tr then tn' with t_trans := key_update tn'.t_trans slot {}
                    else tn' with t_stor := key_update tn'.t_stor slot {}` >>
  `!k. inst_seq_ptr D 0 ctx fn PG G' tn' (emitted_insts st8 st9)
          (s8 with vs_inst_idx := k) G' tn9` by
    (qunabbrev_tac `tn9` >> irule emit_storage_store_uniform_ptr >> metis_tac[]) >>
  rpt (qpat_x_assum `_.vs_allocas = _` kall_tac) >>
  rpt (qpat_x_assum `_.vs_fmp = _` kall_tac) >>
  rpt (qpat_x_assum `_.vs_requests = _` kall_tac) >>
  suspend "compose"
QED

Resume append_storage_store_tail_ptr[compose]:
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends st6 st8` by metis_tac[inst_extends_trans] >>
  `~is_terminator (if tr then TSTORE else SSTORE) /\ ~is_terminator ADD` by
    (Cases_on `tr` >> simp[is_terminator_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st6 st7) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st7 st8)` by
    metis_tac[emitted_void_nonterminators, emitted_op_nonterminators] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st6 st8)` by
    (irule abi_decoder_emitted_every_append >> metis_tac[]) >>
  `run_inst_seq (emitted_insts st6 st8) s6 = OK s8` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`s7`, `st7`] >> simp[]) >>
  `!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st6 st8)
          (s6 with vs_inst_idx := k) G' tn'` by
    (irule emitted_inst_seq_ptr_uniform_compose >> metis_tac[]) >>
  `!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st6 st9)
          (s6 with vs_inst_idx := k) G' tn9` by
    (irule emitted_inst_seq_ptr_uniform_compose >> metis_tac[]) >>
  `!x. not_fresh_at st6 x ==> not_fresh_at st7 x` by
    (imp_res_tac emitted_insts_emit_void >> metis_tac[not_fresh_at_mono, LESS_EQ_REFL]) >>
  qexistsl_tac [`G'`, `tn9`] >> simp[] >>
  Cases_on `tr` >> gvs[Abbr `tn7`, Abbr `tn9`, op_taint_def]
QED

Finalise append_storage_store_tail_ptr

Theorem append_storage_suffix_ptr:
  emit_op ADD [bop; Lit 1w] st3 = (dop,st4) /\
  emit_op MUL [lop; Lit 1w] st4 = (off,st5) /\
  emit_op ADD [dop; off] st5 = (pop,st6) /\
  emit_void (if tr then TSTORE else SSTORE) [pop;vop] st6 = ((),st7) /\
  emit_op ADD [lop; Lit 1w] st7 = (nop,st8) /\
  emit_void (if tr then TSTORE else SSTORE) [bop;nop] st8 = ((),st9) /\
  run_inst_seq (emitted_insts st3 st4) s3 = OK s4 /\
  run_inst_seq (emitted_insts st4 st5) s4 = OK s5 /\
  run_inst_seq (emitted_insts st5 st6) s5 = OK s6 /\
  run_inst_seq (emitted_insts st6 st7) s6 = OK s7 /\
  run_inst_seq (emitted_insts st7 st8) s7 = OK s8 /\
  run_inst_seq (emitted_insts st8 st9) s8 = OK s9 /\
  state_frame s4 = state_frame s3 /\ state_frame s5 = state_frame s4 /\
  state_frame s6 = state_frame s5 /\ state_frame s8 = state_frame s7 /\
  s7.vs_allocas = s6.vs_allocas /\ s7.vs_fmp = s6.vs_fmp /\
  s7.vs_requests = s6.vs_requests /\
  s9.vs_allocas = s8.vs_allocas /\ s9.vs_fmp = s8.vs_fmp /\
  s9.vs_requests = s8.vs_requests /\
  eval_operand pop s6 = SOME (slot+1w+len) /\
  eval_operand bop s8 = SOME slot /\
  op_taint tn bop = {} /\ op_taint tn lop = {} /\ op_taint tn vop = {} /\
  (!x. bop = Var x \/ lop = Var x \/ vop = Var x ==> not_fresh_at st3 x) /\
  ~ctx_has_dalloca ctx ==>
  ?G9 tn9.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st3 st9)
           (s3 with vs_inst_idx := k) G9 tn9) /\
    tn9.t_mem = tn.t_mem /\ tn9.t_imm = tn.t_imm /\
    (if tr then
       tn9.t_trans = key_update (key_update tn.t_trans (slot+1w+len) {}) slot {} /\
       tn9.t_stor = tn.t_stor
     else
       tn9.t_stor = key_update (key_update tn.t_stor (slot+1w+len) {}) slot {} /\
       tn9.t_trans = tn.t_trans) /\
    (!x. not_fresh_at st3 x ==>
         FLOOKUP G9 x = FLOOKUP G x /\
         op_taint tn9 (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `!x. lop = Var x ==> not_fresh_at st3 x` by metis_tac[] >>
  drule_all append_storage_address_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `G`, `D`] strip_assume_tac) >>
  `op_taint tn6 bop = {} /\ op_taint tn6 lop = {} /\ op_taint tn6 vop = {}` by
    (rpt conj_tac >>
     metis_tac[old_operand_taint_frame]) >>
  `!x. not_fresh_at st3 x ==> not_fresh_at st6 x /\ not_fresh_at st7 x` by
    (imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
     metis_tac[not_fresh_at_mono, LESS_EQ_TRANS, DECIDE ``!n:num. n <= n+1``]) >>
  `!x. bop = Var x ==> not_fresh_at st7 x` by metis_tac[] >>
  `s8.vs_allocas = s7.vs_allocas /\ s8.vs_fmp = s7.vs_fmp /\
   s8.vs_requests = s7.vs_requests` by metis_tac[state_frame_ptr_fields] >>
  qpat_x_assum `state_frame s8 = _` kall_tac >>
  drule_all append_storage_store_tail_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `G6`, `D`] strip_assume_tac) >>
  suspend "compose"
QED

Resume append_storage_suffix_ptr[compose]:
  rpt (qpat_x_assum `state_frame _ = _` kall_tac) >>
  rpt (qpat_x_assum `_.vs_allocas = _` kall_tac) >>
  rpt (qpat_x_assum `_.vs_fmp = _` kall_tac) >>
  rpt (qpat_x_assum `_.vs_requests = _` kall_tac) >>
  imp_res_tac inst_extends_emit_op >>
  imp_res_tac inst_extends_emit_void >>
  `inst_extends st3 st5 /\ inst_extends st3 st6 /\
   inst_extends st6 st9` by metis_tac[inst_extends_trans] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st3 st4) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st4 st5) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st5 st6)` by
    metis_tac[emitted_op_nonterminators, is_terminator_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st3 st5)` by
    (irule abi_decoder_emitted_every_append >> metis_tac[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st3 st6)` by
    (irule abi_decoder_emitted_every_append >> metis_tac[]) >>
  `run_inst_seq (emitted_insts st3 st5) s3 = OK s5` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`s4`, `st4`] >> simp[]) >>
  `run_inst_seq (emitted_insts st3 st6) s3 = OK s6` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`s5`, `st5`] >> simp[]) >>
  qexistsl_tac [`G9`, `tn9`] >> simp[] >>
  conj_tac
  >- (irule emitted_inst_seq_ptr_uniform_compose >> metis_tac[]) >>
  qpat_x_assum `if tr then _ else _` mp_tac >> simp[]
QED

Finalise append_storage_suffix_ptr
