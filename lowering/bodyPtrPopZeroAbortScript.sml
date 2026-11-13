Theory bodyPtrPopZeroAbort
Ancestors
  bodyPtrPopCountedTransfer stmtAppendStoragePathPtr fragGasSeqPtr fragGasSeqAbort
  fragExec venomExecSemantics venomInstProofs instIdxIndep
  exprLoweringProps list rich_list

(* The abort cursor of a GAS-free run is fixed by the run alone, so one j
   serves every dead mask D: each valid horizon reaches the same Abort. *)
Theorem run_inst_seq_abort_zero_path_ptr_uniform:
  !code s t a ctx fn bb.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
               ~is_terminator i.inst_opcode) code /\
    run_inst_seq code s = Abort a t ==>
    ?j. !D lo PG G tn G' tn'.
      inst_seq_ptr D lo ctx fn PG G tn code s G' tn' ==>
      gas_path_ptr D lo ctx fn PG G tn s 0 G' tn'
        (Abort a (t with vs_inst_idx := j))
Proof
  Induct >- simp[run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  Cases_on `step_inst_base h s` >>
  gvs[run_inst_seq_def]
  >~ [`step_inst_base h s = OK u`]
  >- (`step_inst 0 ctx h s = OK u` by simp[step_inst_non_invoke] >>
      `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
        metis_tac[step_preserves_halted, step_preserves_control_flow] >>
      first_x_assum (qspecl_then [`u with vs_inst_idx := SUC s.vs_inst_idx`,
        `t with vs_inst_idx := SUC s.vs_inst_idx`, `a`, `ctx`, `fn`, `bb`] mp_tac) >>
      simp[run_inst_seq_inst_idx, exec_result_map_def] >> strip_tac >>
      qexists_tac `j` >> rpt strip_tac >>
      qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ (_::_) _ _ _` mp_tac >>
      simp[inst_seq_ptr_def] >> strip_tac >>
      first_x_assum drule >> strip_tac >>
      drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`) gas_path_ptr_step >>
      simp[]) >>
  qexists_tac `t.vs_inst_idx` >> rpt strip_tac >>
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ (_::_) _ _ _` mp_tac >>
  simp[inst_seq_ptr_def] >> strip_tac >> gvs[] >>
  drule_all gas_path_ptr_abort >> simp[]
QED

(* The Pop compiler slice's abort, with its cursor chosen before the mask. *)
Theorem pop_root_abort_counted_zero:
  compile_dynarray_pop (Lit slot) 1 esz is_ctor imm
    (if tr then LocTransient else LocStorage) sa = (r,sb) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq (emitted_insts sa sb) s = Abort a t ==>
  ?j. !D lo PG G tn G' tn'.
    inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s G' tn' ==>
    gas_path_ptr D lo ctx fn PG G tn s 0 G' tn'
      (Abort a (t with vs_inst_idx := j))
Proof
  strip_tac >> drule pop_root_emitted_opcode_facts >> strip_tac >>
  irule run_inst_seq_abort_zero_path_ptr_uniform >> simp[] >>
  fs[EVERY_MEM, LENGTH_NIL, FILTER_EQ_NIL]
QED
