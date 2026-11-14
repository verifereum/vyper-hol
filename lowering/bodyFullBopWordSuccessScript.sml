Theory bodyFullBopWordSuccess
Ancestors
  bodyPtrBopScalarSeq bodyPtrBopScalarOutcome fragGasCopyLoop
  instMemFrontier fragExecMem memSafeRun fragGasSeqPtr list venomInst

Theorem bop_word_scalar_success_joint:
  bop_scalar_seq R A code B /\
  (!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  ~ctx_has_dalloca ctx /\ run_inst_seq code s = OK t /\
  ~s.vs_halted /\ allocas_from lo s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?G' tn'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code),G',tn')) /\
    (!op. op IN B ==> op_prov G' op = NONE /\ op_taint tn' op = {}) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. x IN R ==> FLOOKUP G' x = FLOOKUP G x /\
                       FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >>
  drule_all (Q.INST [`D` |-> `D0`] bop_scalar_seq_run) >>
  disch_then (qspecl_then [`fn`, `PG`, `D0`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`] >> simp[] >> gen_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
               i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) code` by
    (drule bop_scalar_seq_opcodes >>
     simp[EVERY_MEM] >> strip_tac >> gen_tac >> strip_tac >>
     drule_all bop_scalar_seq_outputs >> strip_tac >> gvs[]) >>
  `run_inst_seq_mem_ok code s` by
    (irule run_inst_seq_mem_ok_every >> simp[EVERY_MEM] >>
     rpt gen_tac >> strip_tac >> gen_tac >>
     drule_all bop_scalar_seq_outputs >> strip_tac >>
     conj_tac >- (irule below_frontier_no_ranges >> gvs[]) >>
     irule inst_dload_in_section_other >> gvs[]) >>
  `inst_seq_ptr D 0 ctx fn PG G tn code s G' tn'` by
    (drule_all bop_scalar_seq_run >>
     disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
     metis_tac[inst_seq_ptr_ghost_unique]) >>
  drule_all run_inst_seq_origin_ptr_lift >> simp[]
QED
