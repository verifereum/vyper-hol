Theory immutableDeployExecution
Ancestors
  immutableMemoryFrame immutableWordExecution moduleLowering
  exprLoweringProps venomInst venomExecSemantics venomState instIdxIndep fragExec
  vyperCompiler

(* MCOPY runs before CODECOPY in the actual epilogue. Its source is thus
   snapshotted before the runtime bytes are installed in the return buffer. *)
Theorem immutable_deploy_buffer_slice:
  TAKE (LENGTH runtime + LENGTH section)
    (DROP pos (write_memory_with_expansion pos runtime
      (write_memory_with_expansion (pos + LENGTH runtime) section s)).vs_memory) =
    runtime ++ section
Proof
  simp[LET_THM] >>
  qmatch_goalsub_abbrev_tac `DROP pos s2.vs_memory` >>
  qabbrev_tac `s1 = write_memory_with_expansion (pos + LENGTH runtime) section s` >>
  `TAKE (LENGTH runtime) (DROP pos s2.vs_memory) = runtime` by
    simp[Abbr `s2`, immutable_write_memory_slice] >>
  `pos + LENGTH runtime + LENGTH section <= LENGTH s1.vs_memory` by
    simp[Abbr `s1`, immutable_write_memory_capacity, arithmeticTheory.MAX_DEF] >>
  `TAKE (LENGTH section) (DROP (pos + LENGTH runtime) s2.vs_memory) = section` by
    (simp[Abbr `s2`, immutable_write_memory_disjoint] >>
     simp[Abbr `s1`, immutable_write_memory_slice]) >>
  simp[listTheory.TAKE_SUM, rich_listTheory.DROP_DROP_T, arithmeticTheory.ADD_COMM]
QED

Theorem immutable_deploy_eval_literal[local]:
  eval_operand (Lit w) s = SOME w
Proof
  simp[eval_operand_def]
QED

Theorem immutable_deploy_eval_label[local]:
  eval_operand (Label l) s = FLOOKUP s.vs_labels l
Proof
  simp[eval_operand_def]
QED

Theorem immutable_deploy_mcopy_step:
  eval_operand dst s = SOME d /\ eval_operand src s = SOME a /\
  eval_operand szop s = SOME n ==>
  step_inst_base (mk_inst id MCOPY [dst;src;szop] []) s =
    OK (mcopy (w2n d) (w2n a) (w2n n) s)
Proof
  simp[mk_inst_def, step_inst_base_def]
QED

Theorem immutable_deploy_codecopy_step:
  eval_operand dst s = SOME d /\ eval_operand src s = SOME a /\
  eval_operand szop s = SOME n ==>
  step_inst_base (mk_inst id CODECOPY [dst;src;szop] []) s =
    OK (write_memory_with_expansion (w2n d)
      (TAKE (w2n n) (DROP (w2n a) s.vs_code ++ REPLICATE (w2n n) 0w)) s)
Proof
  simp[mk_inst_def, step_inst_base_def]
QED

Theorem immutable_deploy_return_step:
  eval_operand dst s = SOME d /\ eval_operand szop s = SOME n ==>
  step_inst_base (mk_inst id RETURN [dst;szop] []) s =
    Halt (halt_state (set_returndata
      (TAKE (w2n n) (DROP (w2n d) s.vs_memory ++ REPLICATE (w2n n) 0w)) s))
Proof
  simp[mk_inst_def, step_inst_base_def]
QED

Theorem immutable_deploy_write_frame:
  eval_operand op (write_memory_with_expansion at bs s) = eval_operand op s /\
  (write_memory_with_expansion at bs s).vs_code = s.vs_code /\
  (write_memory_with_expansion at bs s).vs_labels = s.vs_labels
Proof
  Cases_on `op` >>
  simp[write_memory_with_expansion_def, eval_operand_def, lookup_var_def] >>
  IF_CASES_TAC >> simp[eval_operand_def, lookup_var_def]
QED

(* The four instructions after allocation, with arbitrary semantic state.
   The two output names are distinct; the base operand must survive ADD. *)
Theorem immutable_deploy_return_slice:
  eval_operand dst s = SOME (n2w pos) /\
  TAKE (LENGTH bytes) (DROP pos s.vs_memory) = bytes /\
  pos < dimword (:256) /\ LENGTH bytes < dimword (:256) ==>
  ?s'. run_inst_seq
    [mk_inst id RETURN [dst; Lit (n2w (LENGTH bytes))] []] s = Halt s' /\
    s'.vs_returndata = bytes /\ s'.vs_halted
Proof
  strip_tac >>
  `LENGTH bytes <= LENGTH (DROP pos s.vs_memory)` by
    (`LENGTH (TAKE (LENGTH bytes) (DROP pos s.vs_memory)) = LENGTH bytes` by simp[] >>
     fs[listTheory.LENGTH_TAKE_EQ] >> decide_tac) >>
  simp[run_inst_seq_def, mk_inst_def, step_inst_base_def,
       immutable_deploy_eval_literal, wordsTheory.w2n_n2w,
       listTheory.TAKE_APPEND1, halt_state_def, set_returndata_def]
QED

Theorem immutable_deploy_tail_execution:
  eval_operand (Var buf) s = SOME (n2w pos) /\ buf <> tmp /\
  eval_operand imm (update_var tmp (n2w (pos + LENGTH runtime)) s) = SOME 0w /\
  FLOOKUP s.vs_labels "runtime_begin" = SOME (n2w codepos) /\
  TAKE (LENGTH runtime)
    (DROP codepos s.vs_code ++ REPLICATE (LENGTH runtime) 0w) = runtime /\
  TAKE (LENGTH section) (s.vs_memory ++ REPLICATE (LENGTH section) 0w) = section /\
  pos + LENGTH runtime + LENGTH section < dimword (:256) /\
  codepos < dimword (:256) ==>
  ?s'. run_inst_seq
    [mk_inst id ADD [Var buf; Lit (n2w (LENGTH runtime))] [tmp];
     mk_inst (id + 1) MCOPY [Var tmp; imm; Lit (n2w (LENGTH section))] [];
     mk_inst (id + 2) CODECOPY
       [Var buf; Label "runtime_begin"; Lit (n2w (LENGTH runtime))] [];
     mk_inst (id + 3) RETURN
       [Var buf; Lit (n2w (LENGTH runtime + LENGTH section))] []] s = Halt s' /\
    s'.vs_returndata = runtime ++ section /\ s'.vs_halted
Proof
  strip_tac >>
  `pos < dimword (:256) /\ LENGTH runtime < dimword (:256) /\
   LENGTH section < dimword (:256) /\
   LENGTH runtime + LENGTH section < dimword (:256) /\
   pos + LENGTH runtime < dimword (:256)` by decide_tac >>
  qabbrev_tac `s1 = update_var tmp (n2w (pos + LENGTH runtime)) s` >>
  `step_inst_base (mk_inst id ADD [Var buf; Lit (n2w (LENGTH runtime))] [tmp]) s = OK s1` by
    simp[Abbr `s1`, mk_inst_def, step_inst_base_def, exec_pure2_def,
         eval_operand_def, wordsTheory.word_add_n2w] >>
  `s1.vs_memory = s.vs_memory /\ s1.vs_code = s.vs_code /\
   s1.vs_labels = s.vs_labels /\
   eval_operand (Var buf) s1 = SOME (n2w pos) /\
   eval_operand (Var tmp) s1 = SOME (n2w (pos + LENGTH runtime))` by
    (simp[Abbr `s1`, eval_operand_def, update_var_def, lookup_var_def,
          finite_mapTheory.FLOOKUP_UPDATE] >> fs[eval_operand_def, lookup_var_def]) >>
  `eval_operand imm s1 = SOME 0w` by fs[Abbr `s1`] >>
  qabbrev_tac `s2 = write_memory_with_expansion (pos + LENGTH runtime) section s1` >>
  `step_inst_base (mk_inst (id + 1) MCOPY
      [Var tmp; imm; Lit (n2w (LENGTH section))] []) s1 = OK s2` by
    (simp[mk_inst_def, step_inst_base_def, immutable_deploy_eval_literal,
          wordsTheory.w2n_n2w, mcopy_def, Abbr `s2`]) >>
  `eval_operand (Var buf) s2 = SOME (n2w pos) /\
   eval_operand (Label "runtime_begin") s2 = SOME (n2w codepos) /\
   s2.vs_code = s.vs_code` by
    simp[Abbr `s2`, immutable_deploy_write_frame, immutable_deploy_eval_label] >>
  qabbrev_tac `s3 = write_memory_with_expansion pos runtime s2` >>
  `step_inst_base (mk_inst (id + 2) CODECOPY
      [Var buf; Label "runtime_begin"; Lit (n2w (LENGTH runtime))] []) s2 = OK s3` by
    simp[mk_inst_def, step_inst_base_def, immutable_deploy_eval_literal,
         wordsTheory.w2n_n2w, Abbr `s3`] >>
  `eval_operand (Var buf) s3 = SOME (n2w pos)` by
    simp[Abbr `s3`, immutable_deploy_write_frame] >>
  `TAKE (LENGTH runtime + LENGTH section) (DROP pos s3.vs_memory) = runtime ++ section` by
    simp[Abbr `s3`, Abbr `s2`, immutable_deploy_buffer_slice] >>
  `LENGTH runtime + LENGTH section <= LENGTH (DROP pos s3.vs_memory)` by
    (`LENGTH (TAKE (LENGTH runtime + LENGTH section) (DROP pos s3.vs_memory)) =
        LENGTH runtime + LENGTH section` by simp[] >>
     fs[listTheory.LENGTH_TAKE_EQ] >> decide_tac) >>
  simp[Once run_inst_seq_def] >> simp[Once run_inst_seq_def] >>
  simp[Once run_inst_seq_def] >> simp[Once run_inst_seq_def] >>
  simp[mk_inst_def, step_inst_base_def, immutable_deploy_eval_literal,
       wordsTheory.w2n_n2w, listTheory.TAKE_APPEND1, halt_state_def, set_returndata_def]
QED

Theorem compile_constructor_epilogue_positive_insts:
  0 < cap /\ compile_constructor_epilogue rt cap imm st = ((),st') ==>
  emitted_insts st st' =
    [mk_inst st.cs_next_id ALLOCA [Lit (n2w (rt + cap))]
       ["%" ++ toString st.cs_next_var];
     mk_inst (st.cs_next_id + 1) ADD
       [Var ("%" ++ toString st.cs_next_var); Lit (n2w rt)]
       ["%" ++ toString (st.cs_next_var + 1)];
     mk_inst (st.cs_next_id + 2) MCOPY
       [Var ("%" ++ toString (st.cs_next_var + 1)); imm; Lit (n2w cap)] [];
     mk_inst (st.cs_next_id + 3) CODECOPY
       [Var ("%" ++ toString st.cs_next_var); Label "runtime_begin"; Lit (n2w rt)] [];
     mk_inst (st.cs_next_id + 4) RETURN
       [Var ("%" ++ toString st.cs_next_var); Lit (n2w (rt + cap))] []]
Proof
  strip_tac >>
  fs[moduleLoweringTheory.compile_constructor_epilogue_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       emitHelperTheory.emit_inst_def, compileEnvTheory.fresh_id_def,
       compileEnvTheory.fresh_var_def, compileEnvTheory.emit_def,
       compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.comp_return_def, arithmeticTheory.GREATER_DEF] >>
  gvs[compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
      compileEnvTheory.comp_return_def, compileEnvTheory.fresh_id_def,
      compileEnvTheory.fresh_var_def, compileEnvTheory.emit_def] >>
  simp[emitted_insts_def, listTheory.DROP_APPEND, listTheory.APPEND_ASSOC]
QED

(* Raw Venom execution with an already resolved allocation table entry.
   No assertion about post-ConcretizeMemLoc code is hidden in this premise. *)
Theorem compile_constructor_epilogue_allocated_execution:
  0 < LENGTH section /\
  compile_constructor_epilogue (LENGTH runtime) (LENGTH section) imm st = ((),st') /\
  FLOOKUP s.vs_allocas st.cs_next_id = SOME (pos,sz) /\
  eval_operand imm
    (update_var ("%" ++ toString (st.cs_next_var + 1))
      (n2w (pos + LENGTH runtime))
      (update_var ("%" ++ toString st.cs_next_var) (n2w pos) s)) = SOME 0w /\
  FLOOKUP s.vs_labels "runtime_begin" = SOME (n2w codepos) /\
  TAKE (LENGTH runtime)
    (DROP codepos s.vs_code ++ REPLICATE (LENGTH runtime) 0w) = runtime /\
  TAKE (LENGTH section) (s.vs_memory ++ REPLICATE (LENGTH section) 0w) = section /\
  pos + LENGTH runtime + LENGTH section < dimword (:256) /\
  codepos < dimword (:256) ==>
  ?s'. run_inst_seq (emitted_insts st st') s = Halt s' /\
    s'.vs_returndata = runtime ++ section /\ s'.vs_halted
Proof
  strip_tac >> drule_all compile_constructor_epilogue_positive_insts >>
  disch_then SUBST1_TAC >>
  simp[Once run_inst_seq_def] >>
  `step_inst_base (mk_inst st.cs_next_id ALLOCA
      [Lit (n2w (LENGTH runtime + LENGTH section))]
      ["%" ++ toString st.cs_next_var]) s =
     OK (update_var ("%" ++ toString st.cs_next_var) (n2w pos) s)` by
    simp[mk_inst_def, step_inst_base_def, exec_alloca_def, eval_operand_def] >>
  gvs[] >>
  `st.cs_next_id + 2 = (st.cs_next_id + 1) + 1 /\
   st.cs_next_id + 3 = (st.cs_next_id + 1) + 2 /\
   st.cs_next_id + 4 = (st.cs_next_id + 1) + 3` by decide_tac >>
  asm_rewrite_tac[] >> irule immutable_deploy_tail_execution >>
  gvs[update_var_def, ASCIInumbersTheory.toString_11] >>
  conj_tac >- (qexists_tac `codepos` >> simp[]) >>
  qexists_tac `pos` >>
  simp[eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem immutable_deploy_runtime_only_tail:
  eval_operand (Var buf) s = SOME (n2w pos) /\
  FLOOKUP s.vs_labels "runtime_begin" = SOME (n2w codepos) /\
  TAKE (LENGTH runtime)
    (DROP codepos s.vs_code ++ REPLICATE (LENGTH runtime) 0w) = runtime /\
  pos < dimword (:256) /\ LENGTH runtime < dimword (:256) /\
  codepos < dimword (:256) ==>
  ?s'. run_inst_seq
    [mk_inst id CODECOPY
       [Var buf; Label "runtime_begin"; Lit (n2w (LENGTH runtime))] [];
     mk_inst (id + 1) RETURN [Var buf; Lit (n2w (LENGTH runtime))] []] s = Halt s' /\
    s'.vs_returndata = runtime /\ s'.vs_halted
Proof
  strip_tac >> qabbrev_tac `s1 = write_memory_with_expansion pos runtime s` >>
  `step_inst_base (mk_inst id CODECOPY
    [Var buf; Label "runtime_begin"; Lit (n2w (LENGTH runtime))] []) s = OK s1` by
    simp[mk_inst_def, step_inst_base_def, immutable_deploy_eval_literal,
         immutable_deploy_eval_label, wordsTheory.w2n_n2w, Abbr `s1`] >>
  simp[Once run_inst_seq_def] >> irule immutable_deploy_return_slice >> simp[] >>
  qexists_tac `pos` >> simp[Abbr `s1`, immutable_deploy_write_frame,
                          immutable_write_memory_slice] >>
  fs[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``]
QED

Theorem compile_constructor_epilogue_zero_insts:
  compile_constructor_epilogue rt 0 imm st = ((),st') ==>
  emitted_insts st st' =
    [mk_inst st.cs_next_id ALLOCA [Lit (n2w rt)]
       ["%" ++ toString st.cs_next_var];
     mk_inst (st.cs_next_id + 1) CODECOPY
       [Var ("%" ++ toString st.cs_next_var); Label "runtime_begin"; Lit (n2w rt)] [];
     mk_inst (st.cs_next_id + 2) RETURN
       [Var ("%" ++ toString st.cs_next_var); Lit (n2w rt)] []]
Proof
  simp[moduleLoweringTheory.compile_constructor_epilogue_def,
       contextTheory.compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
       emitHelperTheory.emit_void_def, emitHelperTheory.emit_inst_def,
       compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.comp_return_def, compileEnvTheory.fresh_id_def,
       compileEnvTheory.fresh_var_def, compileEnvTheory.emit_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def, listTheory.DROP_APPEND, listTheory.APPEND_ASSOC]
QED

Theorem compile_constructor_epilogue_zero_allocated_execution:
  compile_constructor_epilogue (LENGTH runtime) 0 imm st = ((),st') /\
  FLOOKUP s.vs_allocas st.cs_next_id = SOME (pos,sz) /\
  FLOOKUP s.vs_labels "runtime_begin" = SOME (n2w codepos) /\
  TAKE (LENGTH runtime)
    (DROP codepos s.vs_code ++ REPLICATE (LENGTH runtime) 0w) = runtime /\
  pos < dimword (:256) /\ LENGTH runtime < dimword (:256) /\
  codepos < dimword (:256) ==>
  ?s'. run_inst_seq (emitted_insts st st') s = Halt s' /\
    s'.vs_returndata = runtime /\ s'.vs_halted
Proof
  strip_tac >> drule compile_constructor_epilogue_zero_insts >>
  disch_then SUBST1_TAC >> simp[Once run_inst_seq_def] >>
  `step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit (n2w (LENGTH runtime))]
      ["%" ++ toString st.cs_next_var]) s =
     OK (update_var ("%" ++ toString st.cs_next_var) (n2w pos) s)` by
    simp[mk_inst_def, step_inst_base_def, exec_alloca_def, eval_operand_def] >>
  gvs[] >>
  `st.cs_next_id + 2 = (st.cs_next_id + 1) + 1` by decide_tac >>
  asm_rewrite_tac[] >> irule immutable_deploy_runtime_only_tail >>
  gvs[update_var_def] >>
  conj_tac >- (qexists_tac `codepos` >> simp[]) >>
  qexists_tac `pos` >>
  simp[eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

(* A terminal boundary for real blocks: the prefix is straight-line and
   cannot itself halt. Non-OK execution is never silently discarded. *)
Theorem immutable_deploy_prefix_no_halt:
  !pre s final.
  EVERY (\i. !s final. step_inst_base i s <> Halt final) pre ==>
  run_inst_seq pre s <> Halt final
Proof
  Induct >> simp[run_inst_seq_def] >> rpt strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >> metis_tac[]
QED

Theorem immutable_deploy_return_index:
  step_inst_base (mk_inst id RETURN [dst;szop] []) (s with vs_inst_idx := n) =
  exec_result_map (\s'. s' with vs_inst_idx := n)
    (step_inst_base (mk_inst id RETURN [dst;szop] []) s)
Proof
  simp[mk_inst_def, step_inst_base_def, eval_op_inst_idx] >>
  Cases_on `eval_operand dst s` >> simp[exec_result_map_def] >>
  Cases_on `eval_operand szop s` >>
  simp[exec_result_map_def, halt_state_def, set_returndata_def]
QED

Theorem immutable_deploy_block_terminal_bridge:
  isPREFIX (pre ++ [mk_inst id RETURN [dst;szop] []])
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              !s final. step_inst_base i s <> Halt final) pre /\
  run_inst_seq (pre ++ [mk_inst id RETURN [dst;szop] []]) s = Halt final ==>
  ?final'. exec_block fuel ctx bb s = Halt final' /\
    final'.vs_returndata = final.vs_returndata /\
    final'.vs_halted = final.vs_halted
Proof
  strip_tac >>
  `EVERY (\i. !s final. step_inst_base i s <> Halt final) pre` by
    fs[listTheory.EVERY_MEM] >>
  `?mid. run_inst_seq pre s = OK mid` by
    (Cases_on `run_inst_seq pre s` >> gvs[] >>
     `!ss. run_inst_seq pre s <> OK ss` by simp[] >>
     drule run_inst_seq_append_err >>
     disch_then (qspec_then `[mk_inst id RETURN [dst;szop] []]` assume_tac) >>
     gvs[] >> drule immutable_deploy_prefix_no_halt >> metis_tac[]) >>
  `run_inst_seq [mk_inst id RETURN [dst;szop] []] mid = Halt final` by
    metis_tac[run_inst_seq_append] >>
  `isPREFIX pre (DROP s.vs_inst_idx bb.bb_instructions)` by
    metis_tac[rich_listTheory.IS_PREFIX_APPEND, listTheory.APPEND_ASSOC] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) pre` by
    fs[listTheory.EVERY_MEM] >>
  drule_all fragExecTheory.exec_block_run_inst_seq >>
  disch_then (qspecl_then [`fuel`,`ctx`] strip_assume_tac) >>
  qabbrev_tac `shifted = mid with vs_inst_idx := s.vs_inst_idx + LENGTH pre` >>
  `exec_block fuel ctx bb s = exec_block fuel ctx bb shifted` by metis_tac[] >>
  `?rest. DROP shifted.vs_inst_idx bb.bb_instructions =
     mk_inst id RETURN [dst;szop] [] :: rest` by
    (qpat_x_assum `isPREFIX (pre ++ _) _` mp_tac >>
     simp[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
     `DROP (LENGTH pre + s.vs_inst_idx) bb.bb_instructions =
        DROP (LENGTH pre) (DROP s.vs_inst_idx bb.bb_instructions)` by
       simp[rich_listTheory.DROP_DROP_T, arithmeticTheory.ADD_COMM] >>
     qexists_tac `l` >> simp[Abbr `shifted`, NoAsms] >>
     pure_once_asm_rewrite_tac[] >> pure_once_asm_rewrite_tac[] >>
     pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC,
                      rich_listTheory.DROP_LENGTH_APPEND] >> simp[NoAsms]) >>
  `shifted.vs_inst_idx < LENGTH bb.bb_instructions` by
    (`LENGTH (DROP shifted.vs_inst_idx bb.bb_instructions) = SUC (LENGTH rest)` by metis_tac[listTheory.LENGTH] >>
     fs[listTheory.LENGTH_DROP] >> decide_tac) >>
  `EL shifted.vs_inst_idx bb.bb_instructions = mk_inst id RETURN [dst;szop] []` by
    metis_tac[listTheory.HD_DROP, listTheory.HD] >>
  `step_inst_base (mk_inst id RETURN [dst;szop] []) mid = Halt final` by
    (fs[run_inst_seq_def] >> Cases_on `step_inst_base (mk_inst id RETURN [dst;szop] []) mid` >> gvs[]) >>
  `step_inst_base (mk_inst id RETURN [dst;szop] []) shifted =
     Halt (final with vs_inst_idx := s.vs_inst_idx + LENGTH pre)` by
    simp[Abbr `shifted`, immutable_deploy_return_index, exec_result_map_def] >>
  qexists_tac `final with vs_inst_idx := s.vs_inst_idx + LENGTH pre` >>
  simp[] >>
  simp[Once exec_block_def, get_instruction_def,
       step_inst_non_invoke, mk_inst_def] >>
  qpat_x_assum `step_inst_base _ shifted = _`
    (fn th => rewrite_tac[REWRITE_RULE [mk_inst_def] th]) >> simp[]
QED

Theorem immutable_deploy_prefix_opcodes:
  MEM i.inst_opcode [ALLOCA;ADD;MCOPY;CODECOPY] ==>
  i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
  !s final. step_inst_base i s <> Halt final
Proof
  simp[] >> strip_tac >> gvs[] >>
  simp[is_terminator_def] >> rpt gen_tac >>
  once_rewrite_tac[step_inst_base_def] >> simp[] >>
  simp[exec_pure2_def, exec_alloca_def, AllCaseEqs()]
QED

Theorem compile_constructor_epilogue_terminal_shape:
  compile_constructor_epilogue rt cap imm st = ((),st') ==>
  ?pre id dst szop.
    emitted_insts st st' = pre ++ [mk_inst id RETURN [dst;szop] []] /\
    EVERY (\i. MEM i.inst_opcode [ALLOCA;ADD;MCOPY;CODECOPY]) pre
Proof
  strip_tac >> Cases_on `cap = 0`
  >- (gvs[] >> drule compile_constructor_epilogue_zero_insts >> strip_tac >>
      qexistsl_tac [`TAKE 2 (emitted_insts st st')`, `st.cs_next_id + 2`,
        `Var ("%" ++ toString st.cs_next_var)`, `Lit (n2w rt)`] >>
      simp[mk_inst_def]) >>
  `0 < cap` by decide_tac >> drule_all compile_constructor_epilogue_positive_insts >>
  strip_tac >> qexistsl_tac [`TAKE 4 (emitted_insts st st')`, `st.cs_next_id + 4`,
    `Var ("%" ++ toString st.cs_next_var)`, `Lit (n2w (rt + cap))`] >>
  simp[mk_inst_def]
QED

Theorem compile_constructor_epilogue_block_bridge:
  compile_constructor_epilogue rt cap imm st = ((),st') /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq (emitted_insts st st') s = Halt final ==>
  ?final'. exec_block fuel ctx bb s = Halt final' /\
    final'.vs_returndata = final.vs_returndata /\
    final'.vs_halted = final.vs_halted
Proof
  strip_tac >> drule compile_constructor_epilogue_terminal_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              !s final. step_inst_base i s <> Halt final) pre` by
    (fs[listTheory.EVERY_MEM] >> gen_tac >> disch_tac >>
     irule immutable_deploy_prefix_opcodes >> simp[] >> metis_tac[]) >>
  gvs[] >> drule_all immutable_deploy_block_terminal_bridge >> metis_tac[]
QED

(* Public staging boundary: unlike the constructor relation this only needs
   the padded MCOPY source equation, not an allocated physical capacity. *)
Theorem compile_constructor_epilogue_staged_execution:
  compile_constructor_epilogue (LENGTH runtime)
    (LENGTH (immutables_section tops imms)) imm st = ((),st') /\
  FLOOKUP s.vs_allocas st.cs_next_id = SOME (pos,sz) /\
  eval_operand imm
    (update_var ("%" ++ toString (st.cs_next_var + 1))
      (n2w (pos + LENGTH runtime))
      (update_var ("%" ++ toString st.cs_next_var) (n2w pos) s)) = SOME 0w /\
  FLOOKUP s.vs_labels "runtime_begin" = SOME (n2w codepos) /\
  TAKE (LENGTH runtime)
    (DROP codepos s.vs_code ++ REPLICATE (LENGTH runtime) 0w) = runtime /\
  immutable_staging_exact tops imms s /\
  pos + LENGTH runtime + LENGTH (immutables_section tops imms) < dimword (:256) /\
  codepos < dimword (:256) ==>
  ?final. run_inst_seq (emitted_insts st st') s = Halt final /\
    final.vs_returndata = runtime ++ immutables_section tops imms /\ final.vs_halted
Proof
  strip_tac >> Cases_on `immutables_section tops imms = []`
  >- (`compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) tops = 0` by
        metis_tac[immutableSectionTheory.immutables_section_length, listTheory.LENGTH] >>
      `compile_constructor_epilogue (LENGTH runtime) 0 imm st = ((),st')` by fs[] >>
      `pos < dimword (:256) /\ LENGTH runtime < dimword (:256)` by (fs[] >> decide_tac) >>
      drule_all compile_constructor_epilogue_zero_allocated_execution >>
      strip_tac >> qexists_tac `s'` >> simp[]) >>
  `0 < LENGTH (immutables_section tops imms)` by
    metis_tac[listTheory.LENGTH_NIL, arithmeticTheory.NOT_ZERO_LT_ZERO] >>
  irule compile_constructor_epilogue_allocated_execution >>
  simp[Excl "immutables_section_length"] >>
  fs[immutableRelationTheory.immutable_staging_exact_def,
     Excl "immutables_section_length"] >>
  conj_tac >- (qexists_tac `codepos` >> simp[]) >>
  qexists_tac `imm` >> simp[]
QED

Theorem compile_constructor_epilogue_staged_block:
  compile_constructor_epilogue (LENGTH runtime)
    (LENGTH (immutables_section tops imms)) imm st = ((),st') /\
  FLOOKUP s.vs_allocas st.cs_next_id = SOME (pos,sz) /\
  eval_operand imm
    (update_var ("%" ++ toString (st.cs_next_var + 1))
      (n2w (pos + LENGTH runtime))
      (update_var ("%" ++ toString st.cs_next_var) (n2w pos) s)) = SOME 0w /\
  FLOOKUP s.vs_labels "runtime_begin" = SOME (n2w codepos) /\
  TAKE (LENGTH runtime)
    (DROP codepos s.vs_code ++ REPLICATE (LENGTH runtime) 0w) = runtime /\
  immutable_staging_exact tops imms s /\
  pos + LENGTH runtime + LENGTH (immutables_section tops imms) < dimword (:256) /\
  codepos < dimword (:256) /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?final. exec_block fuel ctx bb s = Halt final /\
    final.vs_returndata = runtime ++ immutables_section tops imms /\ final.vs_halted
Proof
  strip_tac >> drule_all compile_constructor_epilogue_staged_execution >> strip_tac >>
  drule_all compile_constructor_epilogue_block_bridge >> metis_tac[]
QED

Theorem immutable_deploy_early_stop:
  run_inst_seq (mk_inst id STOP [] [] :: later) s =
    Halt (halt_state (s with vs_returndata := []))
Proof
  simp[run_inst_seq_def, mk_inst_def, step_inst_base_def]
QED

(* Checked executions include the fresh bump-allocation path. They test
   empty and two-word suffixes; the general theorems above concern a resolved
   raw allocation entry, not a claim about placement after concretization. *)
Theorem immutable_deploy_two_word_execution_probe:
  let st = initial_compile_state "entry" in
  let st' = SND (compile_constructor_epilogue 2 64 (Lit 0w) st) in
  let section = [7w;8w] ++ REPLICATE 62 (0w:word8) in
  let s = (init_venom_state "entry") with
    <| vs_memory := section; vs_code := [0xaaw;0xbbw];
       vs_labels := FEMPTY |+ ("runtime_begin",0w); vs_alloca_next := 128 |> in
  case run_inst_seq (emitted_insts st st') s of
    Halt final => final.vs_returndata = [0xaaw;0xbbw] ++ section /\ final.vs_halted
  | _ => F
Proof
  EVAL_TAC >>
  simp[wordsTheory.word_add_n2w, wordsTheory.w2n_n2w, wordsTheory.dimword_def,
       fcpLib.INDEX_CONV ``dimindex(:256)``] >> EVAL_TAC
QED

Theorem immutable_deploy_empty_section_execution_probe:
  let st = initial_compile_state "entry" in
  let st' = SND (compile_constructor_epilogue 2 0 (Lit 0w) st) in
  let s = (init_venom_state "entry") with
    <| vs_memory := REPLICATE 64 (9w:word8); vs_code := [0xaaw;0xbbw];
       vs_labels := FEMPTY |+ ("runtime_begin",0w); vs_alloca_next := 128 |> in
  case run_inst_seq (emitted_insts st st') s of
    Halt final => final.vs_returndata = [0xaaw;0xbbw] /\ final.vs_halted
  | _ => F
Proof
  EVAL_TAC >>
  simp[wordsTheory.word_add_n2w, wordsTheory.w2n_n2w, wordsTheory.dimword_def,
       fcpLib.INDEX_CONV ``dimindex(:256)``] >> EVAL_TAC
QED


val _ = List.app (fn (name, th) => let
  val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") oracles then
       print ("IMMUTABLE_DEPLOY_KERNEL_CLOSED " ^ name ^ "\n")
     else raise Fail ("Unclosed immutable deploy theorem: " ^ name)
  end) (DB.thms "immutableDeployExecution");
