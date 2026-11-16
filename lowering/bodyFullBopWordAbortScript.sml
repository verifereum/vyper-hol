Theory bodyFullBopWordAbort
Ancestors
  bodyPtrBopScalarDynamic bodyPtrBopScalarSeq bodyPtrBopScalarCompile
  exprLoweringProps memSafeRun
  fragGasCopyLoop fragGasOriginPtrExec
  fragGasOriginPtrDead
  instMemFrontier fragExecMem fragGasSeqAbort fragGasMode
  venomInst venomState list rich_list pred_set

Theorem bop_word_scalar_memory_free[local]:
  !code R A B. bop_scalar_seq R A code B ==>
    EVERY (\i. i.inst_opcode <> ALLOCA /\
      !s. inst_mem_below_frontier i s /\ inst_dload_in_section i s) code
Proof
  Induct >> simp[Once bop_scalar_seq_def] >> rpt strip_tac >>
  gvs[mk_inst_def, MEM] >>
  simp[below_frontier_no_ranges, inst_dload_in_section_other] >>
  metis_tac[]
QED

Theorem bop_word_scalar_abort_joint:
  bop_scalar_seq R A code B /\
  (!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  ~ctx_has_dalloca ctx /\ run_inst_seq code s = Abort Revert_abort t /\
  ~s.vs_halted /\ allocas_from lo s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?j G' tn'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (Abort Revert_abort (t with vs_inst_idx := j),G',tn')) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. x IN R ==> FLOOKUP G' x = FLOOKUP G x /\
                      FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >> drule_all bop_scalar_seq_abort_prefix >> strip_tac >>
  `isPREFIX (prefix ++ [mk_inst id opc [op] []])
     (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]) >>
  drule bop_scalar_seq_assert_abort_checked >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then drule >>
  disch_then (drule_at (Pat `step_inst_base _ _ = _`)) >> simp[] >>
  disch_then (qspecl_then [`fn`, `PG`,
    `<| d_stor := K (K {}); d_trans := K (K {});
        d_imm := K {}; d_ret := K {} |>`] strip_assume_tac) >>
  `bop_scalar_seq R A (prefix ++ [mk_inst id opc [op] []]) C` by
    (irule bop_scalar_seq_append >> goal_assum (drule_at Any) >>
     irule bop_scalar_seq_assert >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
               i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS)
     (prefix ++ [mk_inst id opc [op] []])` by
    (drule_all bop_scalar_seq_opcodes >>
     drule_all bop_word_scalar_memory_free >> simp[EVERY_MEM]) >>
  `run_inst_seq_mem_ok (prefix ++ [mk_inst id opc [op] []]) s` by
    (irule run_inst_seq_mem_ok_every >>
     drule_all bop_word_scalar_memory_free >> simp[EVERY_MEM]) >>
  `run_inst_seq (prefix ++ [mk_inst id opc [op] []]) s =
     Abort Revert_abort t` by
    (drule run_inst_seq_append >>
     disch_then (qspec_then `[mk_inst id opc [op] []]` mp_tac) >>
     simp[run_inst_seq_def]) >>
  drule_all run_inst_seq_origin_ptr_abort_lift >>
  disch_then (qspecl_then [`explicit`, `ctx`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`j`, `G'`, `tn'`] >> simp[] >> gen_tac >>
  irule gas_origin_ptr_path_from_no_dead >>
  first_x_assum irule >> simp[]
QED
