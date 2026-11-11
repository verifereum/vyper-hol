(* Memory execution of bounded ABI bytestring decoding. *)
Theory abiDecodeMemBytes
Ancestors
  abiDecodeMemRange abiDecoderBytesRuntime abiDecoderBytesPhases abiDecoderBytesEdges
  allocaFootprint entryDecodeProps freshWrites bodyUnopFragMemory
  codegenRel contextCodegenRel venomMemDefs memSafeRun fragExecMem fragGasSeqMem fragGasSeqAbort allocaHistoryFragment
  instMemFrontier loweringStateRelDefs abiEncoder emitHelperProps exprLoweringProps
  compileEnv emitHelper venomExecSemantics venomState venomInst words arithmetic list rich_list

Theorem abi_decode_bytes_pointer_straight[local]:
  straight_fresh
    (do up <- emit_op ADD [cnt;Lit 31w];
        mask <- emit_op NOT [Lit 31w];
        rounded <- emit_op AND [up;mask];
        emit_op ADD [dst;rounded]
     od)
Proof
  rpt (irule straight_fresh_bind >>
       (reverse conj_tac >- (irule straight_fresh_emit_op >> simp[fresh_write_op_def])) >>
       gen_tac >> BETA_TAC) >>
  irule straight_fresh_emit_op >> simp[fresh_write_op_def]
QED

Theorem abi_decode_bytes_copy_mem_ok[local]:
  emit_void MSTORE [lastptr;Lit 0w] st = ((),c1) /\
  emit_op ADD [Lit 32w;cnt] c1 = (sz,c2) /\
  emit_void MCOPY [dst;addr;sz] c2 = ((),c3) /\
  eval_operand lastptr s = SOME (n2w (d+q)) /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand addr s = SOME (n2w a) /\
  eval_operand cnt s = SOME (n2w c) /\ fresh_vars_wrt st s /\
  d+q < dimword (:256) /\ d < dimword (:256) /\ a < dimword (:256) /\
  32+c < dimword (:256) /\
  d+q+32 <= s.vs_alloca_next /\ d+32+c <= s.vs_alloca_next /\
  a+32+c <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts st c3) s
Proof
  strip_tac >>
  `run_inst_seq (emitted_insts st c1) s = OK (mstore (d+q) 0w s)` by
    (qpat_assum `emit_void MSTORE _ _ = _` (mp_then Any mp_tac emitted_insts_emit_void) >> strip_tac >>
     simp[run_inst_seq_def, Once step_inst_base_def, exec_write2_def,
          mk_inst_def, eval_operand_def, w2n_n2w]) >>
  `fresh_vars_wrt c1 (mstore (d+q) 0w s)` by
    (drule_all fresh_vars_wrt_emit_void_ss >> simp[fresh_vars_wrt_mstore]) >>
  `!op. eval_operand op (mstore (d+q) 0w s) = eval_operand op s` by
    (Cases >> simp[eval_operand_def, lookup_var_def, mstore_def,
                   write_memory_with_expansion_def]) >>
  `eval_operand cnt (mstore (d+q) 0w s) = SOME (n2w c) /\
   eval_operand (Lit 32w) (mstore (d+q) 0w s) = SOME 32w` by simp[eval_operand_def] >>
  drule_all emit_op_ADD_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) _ = OK prepared` >>
  suspend "finish"
QED

Resume abi_decode_bytes_copy_mem_ok[finish]:
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `emitted_insts st c3 = emitted_insts st c1 ++
     (emitted_insts c1 c2 ++ emitted_insts c2 c3)` by
    (`emitted_insts c1 c3 = emitted_insts c1 c2 ++ emitted_insts c2 c3` by
       (irule emitted_insts_append >> fs[inst_extends_def]) >>
     `emitted_insts st c3 = emitted_insts st c1 ++ emitted_insts c1 c3` by
       (irule emitted_insts_append >> fs[inst_extends_def] >> rfs[]) >> simp[]) >>
  qpat_x_assum `emitted_insts st c3 = _` (fn th => pure_once_rewrite_tac[th]) >>
  MATCH_MP_TAC run_inst_seq_mem_ok_append >> conj_tac
  >- (`w2n (n2w (d+q):bytes32) + 32 <= s.vs_alloca_next` by simp[] >>
      metis_tac[emit_mstore_mem_ok]) >>
  gen_tac >> strip_tac >> gvs[] >>
  MATCH_MP_TAC run_inst_seq_mem_ok_append >> conj_tac
  >- (drule emitted_insts_emit_op >> strip_tac >>
      simp[run_inst_seq_mem_ok_last, below_frontier_no_ranges,
           source_memory_read_ranges_def, source_memory_write_ranges_def,
           inst_dload_in_section_def, mk_inst_def, is_alloca_op_def]) >>
  gen_tac >> strip_tac >> gvs[] >>
  `eval_operand dst prepared = SOME (n2w d) /\
   eval_operand addr prepared = SOME (n2w a)` by metis_tac[] >>
  `prepared.vs_alloca_next = s.vs_alloca_next` by
    (drule emitted_insts_emit_op >> strip_tac >>
     qpat_x_assum `run_inst_seq (emitted_insts c1 c2) _ = _` mp_tac >>
     simp[run_inst_seq_def, Once step_inst_base_def, exec_pure2_def,
          mk_inst_def, eval_operand_def] >>
     strip_tac >> gvs[update_var_def, mstore_def, write_memory_with_expansion_def]) >>
  qpat_assum `emit_void MCOPY _ _ = _` (mp_then Any mp_tac emit_mcopy_mem_ok) >>
  disch_then irule >> simp[word_add_n2w, w2n_n2w]
QED
Finalise abi_decode_bytes_copy_mem_ok

Theorem abi_decode_bytes_runtime_tail_mem_ok:
  abi_decode_bytes_runtime_tail dst addr cnt st = ((),st') /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand addr s = SOME (n2w a) /\
  eval_operand cnt s = SOME (n2w c) /\ c <= n /\ c+31 < dimword (:256) /\
  a < dimword (:256) /\ d+32+32*((n+31) DIV 32) < dimword (:256) /\
  d+32+32*((n+31) DIV 32) <= s.vs_alloca_next /\
  a+32+c <= s.vs_alloca_next /\ fresh_vars_wrt st s ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_bytes_runtime_tail _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [abi_decode_bytes_runtime_tail_def, comp_bind_def,
                   comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_op ADD [dst;rounded] c3 = (lastptr,c4)` >>
  rename1 `emit_void MSTORE [lastptr;Lit 0w] c4 = ((),c5)` >>
  rename1 `emit_op ADD [Lit 32w;cnt] c5 = (copy_sz,c6)` >>
  `c <= 32*((c+31) DIV 32)` by simp[abi_decode_bytes_round_bounds] >>
  `32*((c+31) DIV 32)+32 <= 32+32*((n+31) DIV 32)` by
    (irule abi_decode_bytes_round_capacity >> simp[]) >>
  drule_all abi_decode_bytes_runtime_pointer_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c4) s = OK prepared` >>
  `straight_fresh
    (do up <- emit_op ADD [cnt;Lit 31w];
        mask <- emit_op NOT [Lit 31w];
        rounded <- emit_op AND [up;mask]; emit_op ADD [dst;rounded] od)` by
    metis_tac[abi_decode_bytes_pointer_straight] >>
  fs[straight_fresh_def, comp_bind_def] >>
  first_x_assum (qspecl_then [`st`, `lastptr`, `c4`] mp_tac) >>
  simp[LET_THM] >> strip_tac >>
  drule_all run_inst_seq_writes_fresh >> strip_tac >>
  suspend "tail"
QED

Resume abi_decode_bytes_runtime_tail_mem_ok[tail]:
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends c4 st'` by metis_tac[inst_extends_trans] >>
  `emitted_insts st st' = emitted_insts st c4 ++ emitted_insts c4 st'` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  qpat_x_assum `emitted_insts st st' = _` (fn th => pure_once_rewrite_tac[th]) >>
  MATCH_MP_TAC run_inst_seq_mem_ok_append >> conj_tac
  >- metis_tac[writes_fresh_mem_ok] >>
  gen_tac >> strip_tac >> gvs[] >>
  `prepared.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `prepared = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `eval_operand dst prepared = SOME (n2w d) /\
   eval_operand addr prepared = SOME (n2w a) /\
   eval_operand cnt prepared = SOME (n2w c)` by metis_tac[] >>
  `d+32*((c+31) DIV 32) < dimword (:256) /\ d < dimword (:256) /\
   32+c < dimword (:256) /\ d+32*((c+31) DIV 32)+32 <= prepared.vs_alloca_next /\
   d+32+c <= prepared.vs_alloca_next` by decide_tac >>
  qpat_assum `emit_void MSTORE _ _ = _`
    (mp_then Any mp_tac abi_decode_bytes_copy_mem_ok) >>
  disch_then drule >> disch_then drule >> disch_then irule >>
  reverse conj_tac >- simp[] >>
  qexistsl_tac [`a`, `c`, `d`, `32*((c+31) DIV 32)`] >> simp[]
QED
Finalise abi_decode_bytes_runtime_tail_mem_ok
