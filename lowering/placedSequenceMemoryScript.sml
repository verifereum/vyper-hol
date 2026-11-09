(* Reachable memory-safe endpoints for placed straight-line compiler output. *)
Theory placedSequenceMemory
Ancestors
  fragGasSeqMem entrySinkExtraction fragExec exprLoweringProps
  compileEnv venomState list rich_list

Theorem placed_sequence_path_mem:
  same_blocks sa sb /\ fn_has_code sa sb func /\
  isPREFIX sa.cs_current_insts sb.cs_current_insts /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = [] /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  gas_path_mem ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  ~(t with vs_inst_idx := LENGTH sb.cs_current_insts).vs_halted /\
  (t with vs_inst_idx := LENGTH sb.cs_current_insts).vs_current_bb =
    sb.cs_current_bb /\
  (t with vs_inst_idx := LENGTH sb.cs_current_insts).vs_inst_idx =
    LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND,
         emitted_insts_def] >> simp[DROP_APPEND]) >>
  `LENGTH sb.cs_current_insts = s.vs_inst_idx + LENGTH (emitted_insts sa sb)` by
    (gvs[IS_PREFIX_APPEND, emitted_insts_def] >> simp[]) >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  drule_all run_inst_seq_gas_path_mem >>
  gvs[same_blocks_def]
QED
