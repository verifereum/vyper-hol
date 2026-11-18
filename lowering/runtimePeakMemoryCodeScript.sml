(* Block-local allocation windows in the runtime compiler's emitted code. *)
Theory runtimePeakMemoryCode
Ancestors
  runtimePeakMemorySourceGate compileEnv context venomInst exprLoweringProps
  builtinSystem builtinCreate dallocaCalldata dallocaCreateGeometry
  emitHelper emitHelperProps exprSimRawCallCalldata loweringBudgetDallocaWindows
  loweringPackageInsts vyperCompiler
  list rich_list arithmetic

Definition dalloca_windows_def:
  dalloca_windows window insts <=>
    !j. j < LENGTH insts /\ (EL j insts).inst_opcode = DALLOCA ==>
      ?prefix chunk suffix k.
        insts = prefix ++ chunk ++ suffix /\
        j = LENGTH prefix + k /\ k < LENGTH chunk /\ window chunk k
End

Theorem dalloca_windows_empty[simp]:
  dalloca_windows window []
Proof
  simp[dalloca_windows_def]
QED

Theorem dalloca_windows_without_dalloca:
  EVERY (\i. i.inst_opcode <> DALLOCA) insts ==>
  dalloca_windows window insts
Proof
  simp[EVERY_EL, dalloca_windows_def] >> metis_tac[]
QED

Theorem dalloca_windows_append:
  dalloca_windows window xs /\ dalloca_windows window ys ==>
  dalloca_windows window (xs ++ ys)
Proof
  rewrite_tac[dalloca_windows_def] >> rpt strip_tac >>
  Cases_on `j < LENGTH xs` >> fs[EL_APPEND_EQN]
  >- (qpat_x_assum `!j. j < LENGTH xs /\ _ ==> _`
        (qspec_then `j` mp_tac) >> simp[] >> strip_tac >>
      qexistsl_tac [`prefix`, `chunk`, `suffix ++ ys`, `k`] >>
      fs[APPEND_ASSOC]) >>
  `j - LENGTH xs < LENGTH ys` by decide_tac >>
  qpat_x_assum `!j. j < LENGTH ys /\ _ ==> _`
    (qspec_then `j - LENGTH xs` mp_tac) >> simp[] >> strip_tac >>
  qexistsl_tac [`xs ++ prefix`, `chunk`, `suffix`, `k`] >>
  fs[APPEND_ASSOC] >> decide_tac
QED

Definition compiler_dalloca_windows_def:
  compiler_dalloca_windows window st <=>
    dalloca_windows window st.cs_current_insts /\
    EVERY (\bb. dalloca_windows window bb.bb_instructions) st.cs_blocks
End

Definition preserves_dalloca_windows_def:
  preserves_dalloca_windows window m <=>
    !st x st'. compiler_dalloca_windows window st /\ m st = (x,st') ==>
      compiler_dalloca_windows window st'
End

Theorem dalloca_windows_return:
  preserves_dalloca_windows window (comp_return x)
Proof
  simp[preserves_dalloca_windows_def, comp_return_def]
QED

Theorem dalloca_windows_bind:
  preserves_dalloca_windows window m /\
  (!x. preserves_dalloca_windows window (f x)) ==>
  preserves_dalloca_windows window (comp_bind m f)
Proof
  rw[preserves_dalloca_windows_def, comp_bind_def] >>
  pairarg_tac >> gvs[] >> metis_tac[]
QED

Theorem dalloca_windows_emit:
  i.inst_opcode <> DALLOCA ==> preserves_dalloca_windows window (emit i)
Proof
  simp[compiler_dalloca_windows_def, preserves_dalloca_windows_def, emit_def] >>
  rpt strip_tac >> irule dalloca_windows_append >>
  asm_rewrite_tac[] >> irule dalloca_windows_without_dalloca >> simp[]
QED

Theorem dalloca_windows_new_block:
  preserves_dalloca_windows window (new_block label)
Proof
  simp[preserves_dalloca_windows_def, new_block_def, compiler_dalloca_windows_def]
QED

Theorem dalloca_windows_fresh:
  preserves_dalloca_windows window fresh_var /\
  preserves_dalloca_windows window fresh_id /\
  preserves_dalloca_windows window (fresh_label suffix)
Proof
  simp[preserves_dalloca_windows_def, compiler_dalloca_windows_def,
       fresh_var_def, fresh_id_def, fresh_label_def]
QED

Theorem dalloca_windows_initial:
  compiler_dalloca_windows window (initial_compile_state label)
Proof
  simp[compiler_dalloca_windows_def, initial_compile_state_def]
QED

Definition raw_call_dalloca_chunk_def:
  raw_call_dalloca_chunk chunk k <=>
    k = 1 /\
    ?size_id alloc_id copy_id x y call gas addr value rbuf rsz.
      chunk = [mk_inst size_id CALLDATASIZE [] [x];
               mk_inst alloc_id DALLOCA [Var x] [y];
               mk_inst copy_id CALLDATACOPY [Var y;Lit 0w;Var x] [];
               call] /\
      x <> y /\
      ((call.inst_opcode = CALL /\
        call.inst_operands = [gas;addr;value;Var y;Var x;rbuf;rsz]) \/
       (MEM call.inst_opcode [STATICCALL;DELEGATECALL] /\
        call.inst_operands = [gas;addr;Var y;Var x;rbuf;rsz]))
End

Theorem raw_call_dalloca_chunk_windows:
  (!chunk. raw_call_dalloca_chunk chunk 1 ==> window chunk 1) /\
  raw_call_dalloca_chunk chunk 1 ==>
  dalloca_windows window chunk
Proof
  rewrite_tac[dalloca_windows_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  `j = 1` by
    (gvs[raw_call_dalloca_chunk_def] >>
     `j = 0 \/ j = 1 \/ j = 2 \/ j = 3` by decide_tac >>
     gvs[mk_inst_def]) >>
  qexistsl_tac [`[]`, `chunk`, `[]`, `1`] >> simp[]
QED

Theorem raw_call_dalloca_chunk_to_window:
  raw_call_dalloca_chunk chunk k /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ chunk ++ suffix /\
  s.vs_inst_idx = LENGTH prefix + k /\
  i = EL s.vs_inst_idx bb.bb_instructions ==>
  raw_call_dalloca_window fn i s
Proof
  rw[raw_call_dalloca_chunk_def] >>
  fs[raw_call_dalloca_window_def, EL_APPEND_EQN] >>
  qexistsl_tac [`LENGTH prefix`, `size_id`, `alloc_id`, `copy_id`,
                `x`, `y`, `call`, `gas`, `addr`, `value`, `rbuf`, `rsz`, `suffix`] >>
  PURE_REWRITE_TAC [GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> fs[ADD1]
QED

Theorem compile_raw_call_dalloca_chunk:
  (!chunk. raw_call_dalloca_chunk chunk 1 ==> window chunk 1) /\
  compiler_dalloca_windows window sa /\
  compile_msg_data_to_memory sa = ((dp,dl),sb) /\
  ((opc = CALL /\ ops = [gas;addr;value;dp;dl;rbuf;rsz]) \/
   (MEM opc [STATICCALL;DELEGATECALL] /\ ops = [gas;addr;dp;dl;rbuf;rsz])) /\
  emit_op opc ops sb = (result,sc) ==>
  compiler_dalloca_windows window sc
Proof
  disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  drule calldata_memory_insts >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
   sb.cs_blocks = sa.cs_blocks` by
    (qpat_x_assum `compile_msg_data_to_memory _ = _` mp_tac >>
     simp[compile_msg_data_to_memory_def, compile_alloc_dynamic_def,
          emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, fresh_id_def, fresh_var_def, emit_def,
          emitted_insts_def, DROP_LENGTH_APPEND] >>
     strip_tac >> gvs[]) >>
  `sc.cs_blocks = sb.cs_blocks` by metis_tac[emit_op_same_blocks, same_blocks_def] >>
  `raw_call_dalloca_chunk (emitted_insts sa sb ++ emitted_insts sb sc) 1` by
    (simp[raw_call_dalloca_chunk_def] >>
     fs[mk_inst_def, fresh_var_distinct] >> metis_tac[]) >>
  `dalloca_windows window (emitted_insts sa sb ++ emitted_insts sb sc)` by
    (irule raw_call_dalloca_chunk_windows >> asm_rewrite_tac[]) >>
  `dalloca_windows window
      (sa.cs_current_insts ++ (emitted_insts sa sb ++ emitted_insts sb sc))` by
    (irule dalloca_windows_append >> fs[compiler_dalloca_windows_def]) >>
  gvs[compiler_dalloca_windows_def] >>
  full_simp_tac pure_ss [GSYM APPEND_ASSOC, APPEND] >> first_assum ACCEPT_TAC
QED

Theorem extract_context_dalloca_windows:
  extract_context_with_internals label internals st = SOME (ctx,data) /\
  compiler_dalloca_windows window st /\
  MEM fn ctx.ctx_functions /\ MEM bb fn.fn_blocks ==>
  dalloca_windows window bb.bb_instructions
Proof
  simp[extract_context_with_internals_def, compiler_dalloca_windows_def,
       AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule package_internal_blocks_subset >> strip_tac >>
  gvs[mk_venom_context_def, mk_raw_function_def, EVERY_MEM] >>
  `MEM bb st.cs_blocks \/
    bb = <|bb_label := st.cs_current_bb; bb_instructions := st.cs_current_insts|>`
      by metis_tac[MEM_APPEND, MEM_REVERSE, MEM] >>
  gvs[] >> metis_tac[]
QED
