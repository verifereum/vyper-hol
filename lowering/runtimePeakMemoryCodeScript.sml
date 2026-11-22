(* Block-local allocation windows in the runtime compiler's emitted code. *)
Theory runtimePeakMemoryCode
Ancestors
  runtimePeakMemorySourceGate compileEnv context venomInst exprLoweringProps
  builtinSystem builtinCreate builtinSimple dallocaCalldata dallocaCreateCopy
  dallocaCreateGeometry loweringBudgetAccountCodes
  emitHelper emitHelperProps exprSimRawCallCalldata loweringBudgetDallocaWindows
  loweringPackageInsts vyperCompiler
  lowerDloadPtrRawReachable venomExecProofs
  venomExecSemantics venomState extCallOracle words list rich_list arithmetic

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

Definition create_copy_dalloca_chunk_def:
  create_copy_dalloca_chunk chunk k <=>
    k = 5 /\
    ?target value salt sa code a1 a2 shifted a3 preamble a4 size a5 alloc_ptr a6 a7
      code_dst a8 a9 buf a10 len sc created sd.
      emit_op EXTCODESIZE [target] sa = (code,a1) /\
      emit_void ASSERT [code] a1 = ((),a2) /\
      emit_op SHL [Lit 56w;code] a2 = (shifted,a3) /\
      emit_op OR [Lit 0x620000003d81600b3d39f3w;shifted] a3 =
        (preamble,a4) /\
      emit_op ADD [code;Lit 32w] a4 = (size,a5) /\
      compile_alloc_dynamic size a5 = (alloc_ptr,a6) /\
      emit_void MSTORE [alloc_ptr;preamble] a6 = ((),a7) /\
      emit_op ADD [alloc_ptr;Lit 32w] a7 = (code_dst,a8) /\
      emit_void EXTCODECOPY [target;code_dst;Lit 0w;code] a8 = ((),a9) /\
      emit_op ADD [alloc_ptr;Lit 21w] a9 = (buf,a10) /\
      emit_op ADD [code;Lit 11w] a10 = (len,sc) /\
      (case salt of NONE => emit_op CREATE [value;buf;len]
       | SOME salt_op => emit_op CREATE2 [value;buf;len;salt_op]) sc =
        (created,sd) /\
      chunk = emitted_insts sa sd
End

Theorem create_blueprint_dalloca_chunk_windows:
  (!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) /\
  create_blueprint_dalloca_chunk chunk 1 ==>
  dalloca_windows window chunk
Proof
  rewrite_tac[dalloca_windows_def] >> rpt strip_tac >>
  `window chunk 1` by
    (qpat_assum `!c. create_blueprint_dalloca_chunk c 1 ==> window c 1`
       (qspec_then `chunk` mp_tac) >> simp[]) >>
  drule create_blueprint_dalloca_chunk_parts >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> DALLOCA) (middle ++ [effect])` by
    (simp[EVERY_APPEND] >> conj_tac
     >- (fs[EVERY_MEM] >> metis_tac[])
     >> fs[]) >>
  `j = 1` by
    (qpat_x_assum `EVERY (\i. i.inst_opcode <> DALLOCA) _`
       (assume_tac o PURE_REWRITE_RULE[EVERY_EL]) >>
     Cases_on `j` >> fs[] >> rename1 `n = 0` >>
     Cases_on `n` >> fs[] >>
     qpat_x_assum `!k:num. k < _ ==> _` drule >> simp[]) >>
  qexistsl_tac [`[]`, `chunk`, `[]`, `1`] >> simp[]
QED

Theorem create_blueprint_dalloca_chunk_to_window:
  create_blueprint_dalloca_chunk chunk k /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ chunk ++ suffix /\
  s.vs_inst_idx = LENGTH prefix + k /\
  i = EL s.vs_inst_idx bb.bb_instructions ==>
  create_blueprint_dalloca_window fn i s
Proof
  strip_tac >> drule create_blueprint_dalloca_chunk_parts >> strip_tac >>
  simp[create_blueprint_dalloca_window_def] >>
  qexistsl_tac [`prefix`, `chunk`, `suffix`] >> gvs[EL_APPEND_EQN]
QED

Theorem create_copy_dalloca_chunk_opcodes:
  create_copy_dalloca_chunk chunk k ==>
  k = 5 /\
  ?effect.
    MEM effect [CREATE;CREATE2] /\
    MAP (\i. i.inst_opcode) chunk =
      [EXTCODESIZE; ASSERT; SHL; OR; ADD; DALLOCA; MSTORE; ADD; EXTCODECOPY;
       ADD; ADD; effect]
Proof
  rw[create_copy_dalloca_chunk_def] >>
  Cases_on `salt` >>
  gvs[compile_alloc_dynamic_def, emit_op_def, emit_void_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def] >>
  PURE_REWRITE_TAC [emitted_insts_def, GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[mk_inst_def, DROP_LENGTH_APPEND] >> metis_tac[]
QED

Theorem create_copy_dalloca_chunk_windows:
  (!chunk. create_copy_dalloca_chunk chunk 5 ==> window chunk 5) /\
  create_copy_dalloca_chunk chunk 5 ==>
  dalloca_windows window chunk
Proof
  rewrite_tac[dalloca_windows_def] >> strip_tac >> gen_tac >> strip_tac >>
  drule create_copy_dalloca_chunk_opcodes >> strip_tac >>
  `LENGTH chunk = 12` by
    (qpat_assum `MAP _ chunk = _`
       (mp_tac o AP_TERM ``LENGTH: opcode list -> num``) >> simp[]) >>
  `EL j (MAP (\i. i.inst_opcode) chunk) = DALLOCA` by simp[EL_MAP] >>
  `j = 5` by
    (`j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/
      j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/ j = 10 \/ j = 11` by decide_tac >>
     gvs[]) >>
  qexistsl_tac [`[]`, `chunk`, `[]`, `5`] >> simp[]
QED

Definition create_copy_dalloca_window_def:
  create_copy_dalloca_window fn i s <=>
    ?bb prefix chunk suffix.
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      bb.bb_instructions = prefix ++ chunk ++ suffix /\
      s.vs_inst_idx = LENGTH prefix + 5 /\
      i = EL 5 chunk /\
      create_copy_dalloca_chunk chunk 5
End

Theorem create_copy_dalloca_chunk_to_window:
  create_copy_dalloca_chunk chunk k /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ chunk ++ suffix /\
  s.vs_inst_idx = LENGTH prefix + k /\
  i = EL s.vs_inst_idx bb.bb_instructions ==>
  create_copy_dalloca_window fn i s
Proof
  strip_tac >> drule create_copy_dalloca_chunk_opcodes >> strip_tac >>
  `LENGTH chunk = 12` by
    (qpat_assum `MAP _ chunk = _`
       (mp_tac o AP_TERM ``LENGTH: opcode list -> num``) >> simp[]) >>
  simp[create_copy_dalloca_window_def] >>
  qexistsl_tac [`prefix`, `chunk`, `suffix`] >>
  gvs[EL_APPEND_EQN]
QED

Theorem create_copy_dalloca_chunk_parts:
  create_copy_dalloca_chunk chunk 5 ==>
  ?prologue alloc middle effect.
    chunk = prologue ++ alloc :: middle ++ [effect] /\
    LENGTH prologue = 5 /\ LENGTH middle = 5 /\
    alloc.inst_opcode = DALLOCA /\
    MEM effect.inst_opcode [CREATE; CREATE2] /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> PHI /\
               i.inst_opcode <> INVOKE) prologue /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
               ~MEM i.inst_opcode [DALLOCA; CALL; STATICCALL; DELEGATECALL;
                                   CREATE; CREATE2]) middle
Proof
  strip_tac >>
  qexistsl_tac [`TAKE 5 chunk`, `EL 5 chunk`, `TAKE 5 (DROP 6 chunk)`,
                `EL 11 chunk`] >>
  gvs[create_copy_dalloca_chunk_def] >> Cases_on `salt` >>
  gvs[compile_alloc_dynamic_def, emit_op_def, emit_void_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def] >>
  SIMP_TAC pure_ss [emitted_insts_def, GSYM APPEND_ASSOC, APPEND, DROP_LENGTH_APPEND] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def]
QED

Theorem create_copy_dalloca_chunk_size:
  create_copy_dalloca_chunk chunk 5 /\
  account_code_lengths_ok s.vs_accounts /\
  run_inst_seq (TAKE 5 chunk) s = OK t ==>
  ?op sz. (EL 5 chunk).inst_operands = [op] /\
           eval_operand op t = SOME sz /\ w2n sz < 2 ** 64
Proof
  strip_tac >> fs[create_copy_dalloca_chunk_def] >>
  `TAKE 5 chunk = emitted_insts sa a5 /\
   (EL 5 chunk).inst_operands = [size'] /\
   ?hd tl. TAKE 5 chunk = hd :: tl /\
          hd.inst_opcode = EXTCODESIZE /\ hd.inst_operands = [target]` by
    (Cases_on `salt` >>
     gvs[compile_alloc_dynamic_def, emit_op_def, emit_void_def,
         comp_bind_def, comp_ignore_bind_def, comp_return_def,
         fresh_id_def, fresh_var_def, emit_def] >>
     SIMP_TAC pure_ss [emitted_insts_def, GSYM APPEND_ASSOC, APPEND, DROP_LENGTH_APPEND] >>
     simp[mk_inst_def, DROP_LENGTH_APPEND]) >>
  `?addr. eval_operand target s = SOME addr` by
    (qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
     simp[run_inst_seq_def, step_inst_base_opcode_eqs, exec_read1_def,
          AllCaseEqs()] >> metis_tac[]) >>
  qexists_tac `size'` >> simp[] >>
  `LENGTH (lookup_account (w2w addr) s.vs_accounts).code <= 24576` by
    fs[account_code_lengths_ok_def] >>
  `run_inst_seq (emitted_insts sa a5) s = OK t` by metis_tac[] >>
  mp_tac (Q.SPECL [`target`, `sa`, `code`, `a1`, `a2`, `shifted`,
    `a3`, `preamble`, `a4`, `size'`, `a5`, `s`, `addr`, `t`] create_copy_prefix) >>
  simp[] >> metis_tac[]
QED

Theorem create_copy_dalloca_chunk_geometry:
  create_copy_dalloca_chunk chunk 5 /\
  run_inst_seq [EL 4 chunk] seed = OK pre /\
  run_inst_seq (TAKE 6 (DROP 5 chunk)) pre = OK ready /\
  eval_operands (EL 11 chunk).inst_operands ready = SOME ws /\
  (EL 5 chunk).inst_operands = [op] /\ eval_operand op pre = SOME sz ==>
  ?value len salt.
    (((EL 11 chunk).inst_opcode = CREATE /\
       ws = [value; pre.vs_fmp + 21w; len]) \/
     ((EL 11 chunk).inst_opcode = CREATE2 /\
       ws = [value; pre.vs_fmp + 21w; len; salt])) /\
    sz = len + 21w
Proof
  strip_tac >> fs[create_copy_dalloca_chunk_def] >>
  `[EL 4 chunk] = emitted_insts a4 a5 /\
   TAKE 6 (DROP 5 chunk) = emitted_insts a5 sc /\
   (EL 5 chunk).inst_operands = [size'] /\
   ((EL 11 chunk).inst_opcode = CREATE /\
     (EL 11 chunk).inst_operands = [value;buf;len]) \/
   ([EL 4 chunk] = emitted_insts a4 a5 /\
    TAKE 6 (DROP 5 chunk) = emitted_insts a5 sc /\
    (EL 5 chunk).inst_operands = [size'] /\
    (EL 11 chunk).inst_opcode = CREATE2 /\
    ?salt_op. (EL 11 chunk).inst_operands = [value;buf;len;salt_op])` by
    (Cases_on `salt` >>
     gvs[compile_alloc_dynamic_def, emit_op_def, emit_void_def,
         comp_bind_def, comp_ignore_bind_def, comp_return_def,
         fresh_id_def, fresh_var_def, emit_def] >>
     full_simp_tac pure_ss [emitted_insts_def, GSYM APPEND_ASSOC, APPEND, DROP_LENGTH_APPEND] >>
     gvs[mk_inst_def, DROP_APPEND, DROP_LENGTH_TOO_LONG]) >>
  `run_inst_seq (emitted_insts a4 a5) seed = OK pre /\
   run_inst_seq (emitted_insts a5 sc) pre = OK ready` by metis_tac[] >>
  mp_tac (Q.SPECL [`target`, `sa`, `code`, `a1`, `a2`, `shifted`,
    `a3`, `preamble`, `a4`, `size'`, `a5`, `alloc_ptr`, `a6`, `a7`,
    `code_dst`, `a8`, `a9`, `buf`, `a10`, `len`, `sc`, `seed`,
    `pre`, `ready`] create_copy_allocation_geometry) >>
  gvs[eval_operands_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem compile_create_copy_dalloca_chunk:
  compile_create_copy target value salt rof sa = (result,sb) ==>
  ?sd created chunk.
    create_copy_dalloca_chunk chunk 5 /\
    sd.cs_blocks = sa.cs_blocks /\
    sd.cs_current_bb = sa.cs_current_bb /\
    sd.cs_current_insts = sa.cs_current_insts ++ chunk /\
    compile_check_create_result created rof sd = (result,sb)
Proof
  strip_tac >> drule create_copy_create_prefix >> strip_tac >>
  qexistsl_tac [`sd`, `created`, `emitted_insts sa sd`] >>
  conj_tac
  >- (rewrite_tac[create_copy_dalloca_chunk_def] >> simp[] >>
      qexistsl_tac [`target`,`value`,`salt`,`sa`,`code`,`a1`,`a2`,`shifted`,
        `a3`,`preamble`,`a4`,`size'`,`a5`,`alloc_ptr`,`a6`,`a7`,`code_dst`,
        `a8`,`a9`,`buf`,`a10`,`len`,`sc`,`created`,`sd`] >>
      asm_rewrite_tac[]) >>
  Cases_on `salt` >>
  gvs[compile_alloc_dynamic_def, emit_op_def, emit_void_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def] >>
  PURE_REWRITE_TAC [emitted_insts_def, GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[DROP_LENGTH_APPEND]
QED

Theorem dalloca_windows_bind_result:
  preserves_dalloca_windows window m /\ (!st. P (FST (m st))) /\
  (!x. P x ==> preserves_dalloca_windows window (f x)) ==>
  preserves_dalloca_windows window (comp_bind m f)
Proof
  rw[preserves_dalloca_windows_def, comp_bind_def] >>
  pairarg_tac >> gvs[] >> metis_tac[pairTheory.FST]
QED

Theorem dalloca_windows_ignore_bind:
  preserves_dalloca_windows window m /\ preserves_dalloca_windows window n ==>
  preserves_dalloca_windows window (comp_ignore_bind m n)
Proof
  strip_tac >> rewrite_tac[comp_ignore_bind_def] >> irule dalloca_windows_bind >> simp[]
QED

Theorem dalloca_windows_emit_helpers:
  opc <> DALLOCA ==>
  preserves_dalloca_windows window (emit_op opc ops) /\
  preserves_dalloca_windows window (emit_void opc ops) /\
  preserves_dalloca_windows window (emit_inst opc ops outs)
Proof
  strip_tac >> simp[emit_op_def, emit_void_def, emit_inst_def] >>
  rpt conj_tac >>
  rpt (FIRST [
    CHANGED_TAC (simp[dalloca_windows_fresh, dalloca_windows_return,
      dalloca_windows_emit, mk_inst_def]),
    gen_tac, irule dalloca_windows_bind >> conj_tac,
    irule dalloca_windows_ignore_bind >> conj_tac])
QED

Theorem dalloca_windows_alloc_buffer:
  preserves_dalloca_windows window (compile_alloc_buffer nbytes)
Proof
  simp[compile_alloc_buffer_def] >> irule dalloca_windows_bind >>
  simp[dalloca_windows_emit_helpers, dalloca_windows_return]
QED

Theorem dalloca_windows_select:
  preserves_dalloca_windows window (compile_select c a b)
Proof
  simp[compile_select_def] >>
  rpt (FIRST [
    CHANGED_TAC (simp[dalloca_windows_emit_helpers]),
    gen_tac, irule dalloca_windows_bind >> conj_tac])
QED

fun windows_tac thms =
  rpt (FIRST [
    CHANGED_TAC (simp(thms @ [LET_THM, pairTheory.FORALL_PROD, pairTheory.UNCURRY_DEF,
      dalloca_windows_emit_helpers, dalloca_windows_new_block,
      dalloca_windows_fresh, dalloca_windows_return, dalloca_windows_select,
      dalloca_windows_alloc_buffer])),
    gen_tac, irule dalloca_windows_bind >> conj_tac,
    irule dalloca_windows_ignore_bind >> conj_tac,
    COND_CASES_TAC, BasicProvers.TOP_CASE_TAC]);

val windows_pure_tac = windows_tac [];

Theorem dalloca_windows_raw_call_outbuf:
  preserves_dalloca_windows window (compile_raw_call_outbuf max_outsize)
Proof
  rewrite_tac[compile_raw_call_outbuf_def] >> windows_pure_tac
QED

Theorem dalloca_windows_raw_call_finish:
  preserves_dalloca_windows window
    (compile_raw_call_finish addr dp dl gas value ty n rev out dest)
Proof
  Cases_on `ty` >> simp[compile_raw_call_finish_def] >> windows_pure_tac
QED

Theorem dalloca_windows_msg_data_followed_by_call:
  (!chunk. raw_call_dalloca_chunk chunk 1 ==> window chunk 1) ==>
  preserves_dalloca_windows window
    (comp_bind compile_msg_data_to_memory
      (\(ptr,len). compile_raw_call_finish addr ptr len gas value ty n rev out dest))
Proof
  strip_tac >> Cases_on `ty` >>
  simp[preserves_dalloca_windows_def, Once comp_bind_def] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> strip_tac >>
  Cases_on `a` >> gvs[] >>
  qpat_x_assum `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_raw_call_finish_def] >>
  once_rewrite_tac[comp_bind_def] >> simp[LET_THM] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `emit_op _ _ _ = (success,after_call)` >>
  `compiler_dalloca_windows window after_call` by
    (irule compile_raw_call_dalloca_chunk >> rpt (goal_assum drule) >>
     simp[] >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `tail after_call = _` >>
  `preserves_dalloca_windows window tail` by
    (qunabbrev_tac `tail` >> rpt (pop_assum kall_tac) >> windows_pure_tac) >>
  metis_tac[preserves_dalloca_windows_def]
QED

Theorem dalloca_windows_check_create_result[local]:
  preserves_dalloca_windows window (compile_check_create_result result rev)
Proof
  rewrite_tac[compile_check_create_result_def] >> windows_pure_tac
QED

Theorem dalloca_windows_create_copy:
  (!chunk. create_copy_dalloca_chunk chunk 5 ==> window chunk 5) ==>
  preserves_dalloca_windows window (compile_create_copy target value salt rev)
Proof
  rw[preserves_dalloca_windows_def] >>
  drule compile_create_copy_dalloca_chunk >> strip_tac >>
  `dalloca_windows window chunk` by metis_tac[create_copy_dalloca_chunk_windows] >>
  `compiler_dalloca_windows window sd` by
    gvs[compiler_dalloca_windows_def, dalloca_windows_append] >>
  metis_tac[dalloca_windows_check_create_result, preserves_dalloca_windows_def]
QED

Theorem dalloca_windows_create_blueprint_append:
  (!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
  preserves_dalloca_windows window
    (compile_create_blueprint_append target value salt offset code args_ptr args_len rev)
Proof
  rw[preserves_dalloca_windows_def] >>
  drule compile_create_blueprint_dalloca_chunk >> strip_tac >>
  `dalloca_windows window chunk` by metis_tac[create_blueprint_dalloca_chunk_windows] >>
  `compiler_dalloca_windows window sd` by
    gvs[compiler_dalloca_windows_def, dalloca_windows_append] >>
  metis_tac[dalloca_windows_check_create_result, preserves_dalloca_windows_def]
QED

Theorem active_inst_dalloca_windows_with_blueprint:
  ALL_DISTINCT (fn_labels fn) /\ active_inst fn i s /\ i.inst_opcode = DALLOCA /\
  (!bb. MEM bb fn.fn_blocks ==>
    dalloca_windows (\chunk k. raw_call_dalloca_chunk chunk k \/
       create_copy_dalloca_chunk chunk k \/ create_blueprint_dalloca_chunk chunk k)
      bb.bb_instructions) ==>
  raw_call_dalloca_window fn i s \/ create_copy_dalloca_window fn i s \/
  create_blueprint_dalloca_window fn i s
Proof
  strip_tac >> drule_all active_inst_block_lookup >> strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions /\
   i = EL s.vs_inst_idx bb.bb_instructions` by fs[get_instruction_def, AllCaseEqs()] >>
  qpat_x_assum `!bb. MEM bb fn.fn_blocks ==> _` drule >> simp[dalloca_windows_def] >>
  disch_then (qspec_then `s.vs_inst_idx` mp_tac) >>
  fs[] >> strip_tac >>
  metis_tac[raw_call_dalloca_chunk_to_window, create_copy_dalloca_chunk_to_window,
            create_blueprint_dalloca_chunk_to_window, ADD_COMM]
QED

Theorem active_inst_dalloca_windows:
  ALL_DISTINCT (fn_labels fn) /\ active_inst fn i s /\ i.inst_opcode = DALLOCA /\
  (!bb. MEM bb fn.fn_blocks ==>
    dalloca_windows (\chunk k. raw_call_dalloca_chunk chunk k \/
                              create_copy_dalloca_chunk chunk k) bb.bb_instructions) ==>
  raw_call_dalloca_window fn i s \/ create_copy_dalloca_window fn i s
Proof
  strip_tac >> drule_all active_inst_block_lookup >> strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions /\
   i = EL s.vs_inst_idx bb.bb_instructions` by fs[get_instruction_def, AllCaseEqs()] >>
  qpat_x_assum `!bb. MEM bb fn.fn_blocks ==> _` drule >> simp[dalloca_windows_def] >>
  disch_then (qspec_then `s.vs_inst_idx` mp_tac) >>
  fs[] >> strip_tac >>
  metis_tac[raw_call_dalloca_chunk_to_window, create_copy_dalloca_chunk_to_window, ADD_COMM]
QED
