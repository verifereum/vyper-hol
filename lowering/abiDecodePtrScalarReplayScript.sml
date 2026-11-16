(* Fixed-runtime scalar replay: the checked run and its gas path share ghosts. *)
Theory abiDecodePtrScalarReplay
Ancestors
  bodyPtrBopScalarOutcome bodyPtrBopScalarSeq fragGasSeqPtr fragExecPtr
  venomState venomExecSemantics list rich_list

Theorem scalar_seq_success_replay_ptr:
  bop_scalar_seq R A code B /\
  (!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  ~ctx_has_dalloca ctx /\ run_inst_seq code s = OK u /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?G' tn'. inst_seq_ptr D 0 ctx func PG G tn code s G' tn' /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G' tn'
      (OK (u with vs_inst_idx := s.vs_inst_idx + LENGTH code)) /\
    u = s with vs_vars := u.vs_vars /\
    (!op. op IN B ==> op_prov G' op = NONE /\ op_taint tn' op = {}) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. x IN R ==> lookup_var x u = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >> drule_all bop_scalar_seq_run >>
  disch_then (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
  drule_all bop_scalar_seq_runtime_frame >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
   EVERY (\i. i.inst_opcode <> GAS) code` by
    (drule bop_scalar_seq_opcodes >> simp[EVERY_CONJ]) >>
  `FILTER (\i. i.inst_opcode = GAS) code = []` by
    (fs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
  qexistsl_tac [`G'`, `tn'`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (drule_all run_inst_seq_gas_path_ptr >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac >- (rpt strip_tac >> fs[lookup_var_def] >> metis_tac[]) >>
  metis_tac[]
QED
