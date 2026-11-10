(* Control paths for the runtime-length memory-to-storage loop.
   Reuse typed_memory_array_condition_path_mem for LT/ISZERO/JNZ,
   and typed_memory_array_backedge_path_mem for increment/ASSIGN/JMP. *)
Theory assignPlaceDynStoragePaths
Ancestors
  assignPlaceDynStorageLayout placeTypedCopyPrimitiveMem bodyMemAssignTopCopyPaths
  fragExecMem fragExec memSafeRun instMemFrontier fragGasMode venomExecSemantics venomState
  venomInst emitHelperProps exprLoweringProps words arithmetic list rich_list

Theorem dyn_storage_entry_path_mem:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  DROP s.vs_inst_idx bb.bb_instructions =
    [mk_inst id1 MLOAD [src] [lv];
     mk_inst id2 ASSIGN [Lit 0w] [cv]; mk_inst id3 JMP [Label hdr] []] /\
  eval_operand src s = SOME b /\ w2n b + 32 <= s.vs_alloca_next ==>
  gas_path_mem ctx func s 0
    (OK (jump_to hdr
      ((update_var cv 0w (update_var lv (mload (w2n b) s) s)) with
        vs_inst_idx := s.vs_inst_idx + 2)))
Proof
  strip_tac >> irule typed_memory_prefix_jump_path_mem >> simp[] >>
  simp[mk_inst_def, is_terminator_def, run_inst_seq_def,
       step_inst_base_opcode_eqs, exec_read1_def, eval_operand_def,
       lookup_var_update_var, fragExecMemTheory.run_inst_seq_mem_ok_def,
       inst_dload_in_section_def, below_frontier_MLOAD] >>
  rpt conj_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem dyn_storage_length_store_path_mem:
  ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id (if tr then TSTORE else SSTORE) [dst;len] []]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  eval_operand dst s = SOME k /\ eval_operand len s = SOME n ==>
  gas_marked_path T ctx func s 0
    (OK (((if tr then tstore else sstore) k n s) with
           vs_inst_idx := s.vs_inst_idx + 1))
Proof
  strip_tac >>
  irule (SIMP_RULE (srw_ss()) []
    (Q.SPEC `[mk_inst id (if tr then TSTORE else SSTORE) [dst;len] []]`
      topcopy_seq_path)) >>
  conj_tac >- simp[] >>
  qexistsl_tac [`bb`, `dst`, `id`, `len`, `tr`] >> simp[] >>
  Cases_on `tr` >>
  simp[mk_inst_def, is_terminator_def, run_inst_seq_def,
       step_inst_base_opcode_eqs, exec_write2_def,
       run_inst_seq_mem_ok_last, below_frontier_no_ranges] >>
  gvs[mk_inst_def] >>
  Cases_on `DROP s.vs_inst_idx bb.bb_instructions` >> gvs[]
QED
