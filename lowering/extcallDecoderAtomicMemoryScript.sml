(* Atomic memory-source decoder steps.  Each certificate concerns the same
   instruction and endpoint as the value execution, including rejected guards.
   Capacities bound physical word accesses, not just logical ABI lengths. *)
Theory extcallDecoderAtomicMemory
Ancestors
  abiDecoderContract abiDecoderBytesRuntime abiDecoderBytesPrefix
  abiDecoderBytesPhases compileEnv emitHelper rich_list
    exprLoweringProps fragExecMem allocaFootprint
  fragGasSeqMem fragGasSeqAbort fragGasMode fragGasPathMem
  allocaHistory instMemFrontier emitHelperProps stmtReasonMemory
  memSafeRun venomExecProofs venomInstProofs venomExecSemantics venomState
  venomInst venomMemProps words arithmetic list

Theorem extcall_decoder_read_edge:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id MLOAD [src] [out]) /\
  eval_operand src s = SOME p /\ w2n p + 32 <= s.vs_alloca_next ==>
  gas_path_mem_edge ctx func s 0
    (OK ((update_var out (abi_decode_load MLOAD p s) s)
      with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id MLOAD [src] [out]) s =
     OK (update_var out (abi_decode_load MLOAD p s) s)` by
    (irule abi_decode_read_step >> simp[abi_decode_source_opcode_def]) >>
  irule (SRULE [mk_inst_def, is_terminator_def]
    (Q.INST [`i` |-> `mk_inst id MLOAD [src] [out]`] straight_line_mem_edge)) >>
  simp[] >> qexistsl_tac [`id`, `out`, `src`] >>
  simp[GSYM mk_inst_def, below_frontier_MLOAD]
QED

Theorem extcall_decoder_store_edge:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id MSTORE [dst;value] []) /\
  eval_operand dst s = SOME d /\ eval_operand value s = SOME v /\
  w2n d + 32 <= s.vs_alloca_next ==>
  gas_path_mem_edge ctx func s 0
    (OK ((mstore (w2n d) v s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id MSTORE [dst;value] []) s =
     OK (mstore (w2n d) v s)` by (irule step_MSTORE >> simp[]) >>
  irule (SRULE [mk_inst_def, is_terminator_def]
    (Q.INST [`i` |-> `mk_inst id MSTORE [dst;value] []`] straight_line_mem_edge)) >>
  simp[] >> qexistsl_tac [`dst`, `id`, `value`] >>
  simp[GSYM mk_inst_def, below_frontier_MSTORE]
QED

Theorem extcall_decoder_copy_edge:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id MCOPY [dst;src;len] []) /\
  eval_operand dst s = SOME d /\ eval_operand src s = SOME a /\
  eval_operand len s = SOME n /\
  (w2n n = 0 \/ w2n a + w2n n <= s.vs_alloca_next) /\
  (w2n n = 0 \/ w2n d + w2n n <= s.vs_alloca_next) ==>
  gas_path_mem_edge ctx func s 0
    (OK ((mcopy (w2n d) (w2n a) (w2n n) s)
      with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id MCOPY [dst;src;len] []) s =
     OK (mcopy (w2n d) (w2n a) (w2n n) s)` by simp[step_mcopy_eq] >>
  irule (SRULE [mk_inst_def, is_terminator_def]
    (Q.INST [`i` |-> `mk_inst id MCOPY [dst;src;len] []`] straight_line_mem_edge)) >>
  simp[] >> qexistsl_tac [`dst`, `id`, `len`, `src`] >>
  simp[GSYM mk_inst_def, below_frontier_MCOPY] >> gvs[]
QED

Theorem extcall_decoder_guard_pass_edge:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ASSERT [guard] []) /\
  eval_operand guard s = SOME w /\ w <> 0w ==>
  gas_path_mem_edge ctx func s 0 (OK (s with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id ASSERT [guard] []) s = OK s` by
    (irule step_ASSERT_ok >> simp[]) >>
  irule (SRULE [mk_inst_def, is_terminator_def]
    (Q.INST [`i` |-> `mk_inst id ASSERT [guard] []`] straight_line_mem_edge)) >>
  simp[] >> qexistsl_tac [`guard`, `id`] >>
  simp[GSYM mk_inst_def, below_frontier_no_ranges]
QED

(* No range premise is needed on a rejected guard: no following load runs. *)
Theorem extcall_decoder_guard_reject_path:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ASSERT [guard] []) /\
  eval_operand guard s = SOME 0w ==>
  gas_path_mem ctx func s 0
    (Abort Revert_abort (revert_state (set_returndata [] s)))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id ASSERT [guard] []) s =
     Abort Revert_abort (revert_state (set_returndata [] s))` by
    (irule step_ASSERT_revert >> simp[]) >>
  irule (SRULE [gas_marked_path_def, mk_inst_def, is_terminator_def]
    (Q.INST [`memory` |-> `T`, `i` |-> `mk_inst id ASSERT [guard] []`]
       (SPEC_ALL gas_marked_path_abort))) >>
  simp[] >> qexistsl_tac [`guard`, `id`] >>
  simp[GSYM mk_inst_def, below_frontier_no_ranges]
QED

(* The actual runtime copy tail has an ADD between its padding store and
   MCOPY.  Prove checks on that sequence, rather than an adjacent surrogate. *)
Theorem extcall_decoder_bytes_copy_sequence_mem_ok:
  emit_void MSTORE [lastptr;Lit 0w] st = ((),c1) /\
  emit_op ADD [Lit 32w;cnt] c1 = (sz,c2) /\
  emit_void MCOPY [dst;addr;sz] c2 = ((),c3) /\
  eval_operand lastptr s = SOME (n2w (d+q)) /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand addr s = SOME (n2w a) /\
  eval_operand cnt s = SOME (n2w c) /\
  d+q < dimword (:256) /\ d < dimword (:256) /\ a < dimword (:256) /\
  32+c < dimword (:256) /\ d+q+32 <= s.vs_alloca_next /\
  d+32+c <= s.vs_alloca_next /\ a+32+c <= s.vs_alloca_next /\
  fresh_vars_wrt st s ==>
  run_inst_seq_mem_ok (emitted_insts st c3) s
Proof
  strip_tac >>
  `run_inst_seq (emitted_insts st c1) s = OK (mstore (d+q) 0w s)` by
    (qpat_assum `emit_void MSTORE _ _ = _`
       (mp_then Any mp_tac emitted_insts_emit_void) >> strip_tac >>
     simp[run_inst_seq_def, mk_inst_def, Once step_inst_base_def,
          exec_write2_def, eval_operand_def, w2n_n2w]) >>
  `fresh_vars_wrt c1 (mstore (d+q) 0w s)` by
    (drule_all fresh_vars_wrt_emit_void_ss >> simp[fresh_vars_wrt_mstore]) >>
  `eval_operand cnt (mstore (d+q) 0w s) = SOME (n2w c) /\
   eval_operand (Lit 32w) (mstore (d+q) 0w s) = SOME 32w` by
    simp[mstore_def, write_memory_with_expansion_def,
         eval_operand_with_memory, eval_operand_def] >>
  drule_all emit_op_ADD_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) _ = OK prepared` >>
  imp_res_tac emitted_insts_emit_void >>
  drule emitted_insts_emit_op >> strip_tac >>
  `emitted_insts st c3 = emitted_insts st c1 ++
      (emitted_insts c1 c2 ++ emitted_insts c2 c3)` by
    (asm_simp_tac bool_ss [emitted_insts_def, LENGTH_APPEND, LENGTH,
       DROP_APPEND, DROP_LENGTH_NIL, APPEND_ASSOC, APPEND] >>
     `!n k. n - (n+k) = 0` by decide_tac >> simp[]) >>
  qpat_x_assum `emitted_insts st c3 = _` SUBST1_TAC >>
  match_mp_tac run_inst_seq_mem_ok_append >>
  conj_tac >- simp[run_inst_seq_mem_ok_last, below_frontier_MSTORE,
                   eval_operand_def, w2n_n2w] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `run_inst_seq [_] _ = OK prepared` mp_tac >>
  simp[run_inst_seq_def, AllCaseEqs()] >> strip_tac >>
  simp[Once run_inst_seq_mem_ok_def, below_frontier_no_ranges] >>
  `prepared.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `step_inst_base _ _ = OK prepared` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     imp_res_tac step_inst_base_preserves_alloca_next >>
     gvs[mk_inst_def, mstore_def, write_memory_with_expansion_def]) >>
  `eval_operand dst prepared = SOME (n2w d) /\
   eval_operand addr prepared = SOME (n2w a)` by
    (conj_tac >> first_x_assum irule >> simp[eval_operand_with_memory,
       mstore_def, write_memory_with_expansion_def]) >>
  simp[run_inst_seq_mem_ok_last, below_frontier_MCOPY,
       word_add_n2w, w2n_n2w]
QED

Theorem extcall_decoder_bytes_copy_code[local]:
  emit_void MSTORE [lastptr;Lit 0w] st = ((),c1) /\
  emit_op ADD [Lit 32w;cnt] c1 = (sz,c2) /\
  emit_void MCOPY [dst;addr;sz] c2 = ((),c3) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st c3) /\
  LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st c3)) = 0
Proof
  strip_tac >> imp_res_tac emitted_insts_emit_void >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule_all emitted_insts_three >> strip_tac >>
  simp[mk_inst_def, is_terminator_def]
QED

Theorem extcall_decoder_bytes_copy_sequence_path:
  emit_void MSTORE [lastptr;Lit 0w] st = ((),c1) /\
  emit_op ADD [Lit 32w;cnt] c1 = (sz,c2) /\
  emit_void MCOPY [dst;addr;sz] c2 = ((),c3) /\
  eval_operand lastptr s = SOME (n2w (d+q)) /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand addr s = SOME (n2w a) /\
  eval_operand cnt s = SOME (n2w c) /\
  d+q < dimword (:256) /\ d < dimword (:256) /\ a < dimword (:256) /\
  32+c < dimword (:256) /\ d+q+32 <= s.vs_alloca_next /\
  d+32+c <= s.vs_alloca_next /\ a+32+c <= s.vs_alloca_next /\
  fresh_vars_wrt st s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st c3) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t. run_inst_seq (emitted_insts st c3) s = OK t /\
    gas_path_mem ctx func s 0
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st c3))) /\
    fresh_vars_wrt c3 t /\
    t.vs_memory = (mcopy d a (32+c) (mstore (d+q) 0w s)).vs_memory /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  strip_tac >>
  drule_all extcall_decoder_bytes_copy_sequence_mem_ok >> strip_tac >>
  drule_all abi_decode_bytes_runtime_copy_sequence >> strip_tac >>
  drule_all extcall_decoder_bytes_copy_code >> strip_tac >>
  drule_all run_inst_seq_gas_path_mem >> simp[] >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem extcall_decoder_bytes_pointer_code[local]:
  emit_op ADD [cnt;Lit 31w] st = (up,c1) /\
  emit_op NOT [Lit 31w] c1 = (mask,c2) /\
  emit_op AND [up;mask] c2 = (rounded,c3) /\
  emit_op ADD [dst;rounded] c3 = (lastptr,c4) ==>
  EVERY (\i. MEM i.inst_opcode [ADD;NOT;AND]) (emitted_insts st c4)
Proof
  strip_tac >> imp_res_tac emitted_insts_emit_op >>
  `!n k. n - (n+k) = 0` by decide_tac >>
  asm_simp_tac bool_ss [emitted_insts_def, APPEND_ASSOC, DROP_APPEND,
    LENGTH_APPEND, LENGTH, DROP_LENGTH_NIL, APPEND, mk_inst_def] >>
  simp[]
QED

Theorem extcall_decoder_bytes_runtime_tail_mem_ok[local]:
  abi_decode_bytes_runtime_tail dst addr cnt st = ((),st') /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand addr s = SOME (n2w a) /\
  eval_operand cnt s = SOME (n2w c) /\ c+31 < dimword (:256) /\
  d+32*((c+31) DIV 32) < dimword (:256) /\
  d < dimword (:256) /\ a < dimword (:256) /\ 32+c < dimword (:256) /\
  d+32*((c+31) DIV 32)+32 <= s.vs_alloca_next /\
  d+32+c <= s.vs_alloca_next /\ a+32+c <= s.vs_alloca_next /\
  fresh_vars_wrt st s ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_bytes_runtime_tail _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [abi_decode_bytes_runtime_tail_def, comp_bind_def,
    comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  `c+31 < dimword (:256) /\ d < dimword (:256)` by decide_tac >>
  drule_all abi_decode_bytes_runtime_pointer_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st ready) s = OK prepared` >>
  drule_all extcall_decoder_bytes_pointer_code >> strip_tac >>
  `prepared.vs_alloca_next = s.vs_alloca_next` by
    (irule (cj 2 abi_decode_nonallocating_sequence_frame) >>
     goal_assum (drule_at Any) >>
     qpat_x_assum `EVERY _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[EVERY_MEM] >>
     rpt strip_tac >> first_x_assum drule >>
     strip_tac >> gvs[is_terminator_def, is_alloca_op_def]) >>
  `eval_operand dst prepared = SOME (n2w d) /\
   eval_operand addr prepared = SOME (n2w a) /\
   eval_operand cnt prepared = SOME (n2w c)` by metis_tac[] >>
  `run_inst_seq_mem_ok (emitted_insts ready st') prepared` by
    (`32+c < dimword (:256) /\
      d+32*((c+31) DIV 32)+32 <= prepared.vs_alloca_next /\
      d+32+c <= prepared.vs_alloca_next /\
      a+32+c <= prepared.vs_alloca_next` by decide_tac >>
     drule_all extcall_decoder_bytes_copy_sequence_mem_ok >> simp[]) >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends st ready /\ inst_extends ready st'` by
    metis_tac[inst_extends_trans] >>
  `emitted_insts st st' = emitted_insts st ready ++ emitted_insts ready st'` by
    (irule emitted_insts_append >> gvs[inst_extends_def]) >>
  qpat_x_assum `emitted_insts st st' = _` SUBST1_TAC >>
  match_mp_tac run_inst_seq_mem_ok_append >> conj_tac
  >- (irule run_inst_seq_mem_ok_every >>
      gvs[EVERY_MEM] >> rpt strip_tac >>
      first_x_assum drule >>
      strip_tac >> simp[inst_dload_in_section_def] >>
      irule below_frontier_no_ranges >> simp[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem extcall_decoder_bytes_runtime_tail_no_gas[local]:
  abi_decode_bytes_runtime_tail dst addr cnt st = ((),st') ==>
  LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st st')) = 0
Proof
  simp[abi_decode_bytes_runtime_tail_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def,
       emit_def] >>
  rpt strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem extcall_decoder_bytes_runtime_tail_path:
  abi_decode_bytes_runtime_tail dst addr cnt st = ((),st') /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand addr s = SOME (n2w a) /\
  eval_operand cnt s = SOME (n2w c) /\ c <= n /\
  c+31 < dimword (:256) /\ a < dimword (:256) /\
  d+(32+32*((n+31) DIV 32)) < dimword (:256) /\
  a+32+c <= s.vs_alloca_next /\
  d+(32+32*((n+31) DIV 32)) <= s.vs_alloca_next /\
  fresh_vars_wrt st s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    gas_path_mem ctx func s 0
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st st'))) /\
    fresh_vars_wrt st' t /\
    t.vs_memory = (mcopy d a (32+c)
      (mstore (d+32*((c+31) DIV 32)) 0w s)).vs_memory /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  strip_tac >>
  qspec_then `c` strip_assume_tac (GEN_ALL abi_decode_bytes_round_bounds) >>
  qpat_assum `c <= n` (mp_then Any mp_tac abi_decode_bytes_round_capacity) >>
  strip_tac >>
  `d+32*((c+31) DIV 32) < dimword (:256) /\
   d < dimword (:256) /\ 32+c < dimword (:256) /\
   d+32*((c+31) DIV 32)+32 <= s.vs_alloca_next /\
   d+32+c <= s.vs_alloca_next` by decide_tac >>
  drule_all extcall_decoder_bytes_runtime_tail_mem_ok >> strip_tac >>
  drule_all abi_decode_bytes_runtime_tail_sequence >> strip_tac >>
  drule_all abi_decode_bytes_runtime_tail_shape >> strip_tac >>
  drule_all extcall_decoder_bytes_runtime_tail_no_gas >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  drule_all run_inst_seq_gas_path_mem >> simp[] >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED
