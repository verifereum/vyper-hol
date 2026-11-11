(* Operand-general memory checks for the nested local-pop suffix. *)
Theory popNestedLocalSuffixMemory
Ancestors
  exprSimPopNestedLocalRun bodyMemPopLocalPath
  fragGasSeqMem fragExecMem instMemFrontier storageCopyGasPath
  venomInstProofs venomExecSemantics venomState venomInst emitHelper
  exprLoweringProps allocaHistoryFragment venomMemProofs bodyUnopFragMemory
  compileEnv fragExec list rich_list

Theorem memory_pop_mem_checks[local]:
  EVERY (\x. hdr <> Var x) [x0;x1;x2;x3;x4;x5;x6] /\
  eval_operand hdr s = SOME w /\ w2n w + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok
    (memory_pop_insts hdr id esz x0 x1 x2 x3 x4 x5 x6) s
Proof
  strip_tac >>
  irule run_inst_seq_mem_ok_of_prefix_safe >>
  simp[memory_pop_insts_def, mk_inst_def] >>
  rpt gen_tac >> strip_tac >>
  `u.vs_alloca_next = s.vs_alloca_next` by
    (irule (SRULE [] (Q.ISPEC `\t:venom_state. t.vs_alloca_next` run_inst_seq_preserves_field)) >>
     qexists_tac `pre` >> simp[] >> rpt strip_tac >>
     irule step_inst_base_preserves_alloca_next >>
     qexists_tac `i'` >> simp[] >>
     qpat_x_assum `_ = pre ++ _ ++ _` (mp_tac o Q.AP_TERM `MEM i'`) >>
     simp[] >> rpt strip_tac >> gvs[]) >>
  `eval_operand hdr u = eval_operand hdr s` by
    (namedCases_on `hdr` ["c", "p", "lbl"] >>
     simp[eval_operand_def, NoAsms]
     >- (irule (Q.ISPEC `lookup_var p` run_inst_seq_preserves_field) >>
         qexists_tac `pre` >> simp[] >> rpt strip_tac >>
         irule step_preserves_non_output_vars >>
         qexistsl_tac [`ARB`, `0`, `i'`] >>
         qpat_x_assum `_ = pre ++ _ ++ _` (mp_tac o Q.AP_TERM `MEM i'`) >>
         simp[] >> rpt strip_tac >>
         gvs[step_inst_non_invoke, is_terminator_def]) >>
     `u.vs_labels = s.vs_labels` suffices_by simp[] >>
     irule (SRULE [] (Q.ISPEC `\t:venom_state. t.vs_labels` run_inst_seq_preserves_field)) >>
     qexists_tac `pre` >> simp[] >> rpt strip_tac >>
     irule step_preserves_labels >>
     qexistsl_tac [`ARB`, `0`, `i'`] >>
     qpat_x_assum `_ = pre ++ _ ++ _` (mp_tac o Q.AP_TERM `MEM i'`) >>
     simp[] >> rpt strip_tac >>
     gvs[step_inst_non_invoke, is_terminator_def]) >>
  qpat_x_assum `_ = pre ++ _ ++ _` (mp_tac o Q.AP_TERM `MEM i`) >>
  simp[] >> rpt strip_tac >> gvs[] >>
  rewrite_tac[GSYM mk_inst_def] >>
  simp[below_frontier_MLOAD, below_frontier_MSTORE,
       below_frontier_no_ranges, mk_inst_def, eval_operand_def]
QED

(* Lift the given run: no second existentially chosen execution. *)
Theorem memory_pop_run_path_mem:
  fn_has_code sa sb func /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_blocks = sa.cs_blocks /\
  sb.cs_current_insts = sa.cs_current_insts ++
    memory_pop_insts hdr id esz x0 x1 x2 x3 x4 x5 x6 /\
  EVERY (\x. hdr <> Var x) [x0;x1;x2;x3;x4;x5;x6] /\
  eval_operand hdr s = SOME w /\ w2n w + 32 <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (memory_pop_insts hdr id esz x0 x1 x2 x3 x4 x5 x6) s = OK t ==>
  gas_path_mem ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `same_blocks sa sb /\ isPREFIX sa.cs_current_insts sb.cs_current_insts` by
    simp[same_blocks_def, IS_PREFIX_APPEND] >>
  drule_all storage_copy_code_prefix >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `isPREFIX (memory_pop_insts hdr id esz x0 x1 x2 x3 x4 x5 x6)
     (DROP s.vs_inst_idx bb.bb_instructions)` by
    gvs[emitted_insts_def, DROP_LENGTH_APPEND] >>
  `run_inst_seq_mem_ok (memory_pop_insts hdr id esz x0 x1 x2 x3 x4 x5 x6) s`
    by (irule memory_pop_mem_checks >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (memory_pop_insts hdr id esz x0 x1 x2 x3 x4 x5 x6)` by
    simp[memory_pop_insts_def, mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_mem >>
  simp[memory_pop_insts_def, mk_inst_def]
QED

Theorem memory_pop_run_abort_path_mem:
  fn_has_code sa sb func /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_blocks = sa.cs_blocks /\
  sb.cs_current_insts = sa.cs_current_insts ++
    memory_pop_insts hdr id esz x0 x1 x2 x3 x4 x5 x6 /\
  EVERY (\x. hdr <> Var x) [x0;x1;x2;x3;x4;x5;x6] /\
  eval_operand hdr s = SOME w /\ w2n w + 32 <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (memory_pop_insts hdr id esz x0 x1 x2 x3 x4 x5 x6) s = Abort a t ==>
  ?j. gas_marked_path T ctx func s 0 (Abort a (t with vs_inst_idx := j))
Proof
  strip_tac >>
  `same_blocks sa sb /\ isPREFIX sa.cs_current_insts sb.cs_current_insts` by
    simp[same_blocks_def, IS_PREFIX_APPEND] >>
  drule_all storage_copy_code_prefix >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `isPREFIX (memory_pop_insts hdr id esz x0 x1 x2 x3 x4 x5 x6)
     (DROP s.vs_inst_idx bb.bb_instructions)` by
    gvs[emitted_insts_def, DROP_LENGTH_APPEND] >>
  `run_inst_seq_mem_ok (memory_pop_insts hdr id esz x0 x1 x2 x3 x4 x5 x6) s`
    by (irule memory_pop_mem_checks >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
       ~is_terminator i.inst_opcode)
     (memory_pop_insts hdr id esz x0 x1 x2 x3 x4 x5 x6)` by
    simp[memory_pop_insts_def, mk_inst_def, is_terminator_def] >>
  irule run_inst_seq_abort_zero_path_mem >> metis_tac[]
QED
