(* The memory raw-call continuation, starting at the counted call endpoint. *)
Theory bodyFullRawCallFinishJoint
Ancestors
  bodyFullRawCallCall bodyFullRawCallZero bodyFullRawCallBytes
  bodyFullRawCallTupleAllocFrame bodyFullRawCallTupleLength
  bodyFullRawCallTupleCopy bodyFullRawCallTupleWriteSeparation
  bodyFullRawCallTupleWriteFrame bodyFullRawCallRevertExit
  bodyFullAllocGeneric rawCallBufferPtr fragGasSeqPtr instSeqComposePtr
  stateRelProj valueEncodingProps bodyMemBiSha256Suffix
Libs
  monadsyntax

(* The CALL writes and clears taint on exactly the clipped payload, not on
   the entire reserved output row. The length store follows this cut. *)
Theorem raw_call_positive_payload_cut:
  u.vs_memory = (write_memory_with_expansion (w2n ro)
    (TAKE n data) s).vs_memory /\ u.vs_returndata = data /\
  tn'.t_mem = tn.t_mem DIFF
    {j | w2n ro <= j /\ j < w2n ro + LENGTH (TAKE n data)} /\
  w2n ro = b + 32 ==>
  mem_bytes_at (b + 32) (LENGTH (TAKE n u.vs_returndata)) u.vs_memory =
    TAKE n u.vs_returndata /\
  (!i. b + 32 <= i /\ i < b + 32 + LENGTH (TAKE n u.vs_returndata) ==>
    i NOTIN tn'.t_mem)
Proof
  strip_tac >> simp[write_memory_mem_bytes_at_same]
QED

Theorem raw_call_positive_suffix_mem_ok:
  (if n > 0 then
       do z <- emit_op RETURNDATASIZE [];
          cmp <- emit_op LT [z;Lit (n2w n)];
          cap <- compile_select cmp z (Lit (n2w n));
          emit_void MSTORE [ov;cap];
          buf <- compile_alloc_buffer (64 + ((n + 31) DIV 32) * 32);
          emit_void MSTORE [buf.buf_operand;ok];
          dst <- emit_op ADD [buf.buf_operand;Lit 32w];
          emit_void MCOPY [dst;ov;Lit (n2w (32 + ((n + 31) DIV 32) * 32))];
          return buf.buf_operand od
     else return ok) sa = (result,sb) /\ 0 < n /\
  stmt_state_rel H ctx func cenv cx es s /\ wb_frame cenv es0 es sf s0 s /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  MEM alloc (fn_insts func) /\ alloc.inst_opcode = ALLOCA /\
  alloc.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas alloc.inst_id = SOME (w2n w,32 + ((n + 31) DIV 32) * 32) /\
  local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sa /\
  sf.cs_next_var <= sa.cs_next_var /\ sf.cs_next_id <= alloc.inst_id /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  safe_operand sa ov /\ safe_operand sa ok /\
  eval_operand ov s = SOME w /\ eval_operand ok s = SOME flag /\
  s.vs_memory = (write_memory_with_expansion (w2n ro) (TAKE n data) pre).vs_memory /\
  s.vs_returndata = data /\
  tn'.t_mem = tn.t_mem DIFF {j | w2n ro <= j /\ j < w2n ro + LENGTH (TAKE n data)} /\
  w2n ro = w2n w + 32 /\ LENGTH data < dimword (:256) /\
  64 + ((n + 31) DIV 32) * 32 < dimword (:256) /\ n < dimword (:256) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >> drule_all exprSimRawCallTheory.raw_call_nonrevert_suffix_code >>
  strip_tac >> qpat_x_assum `(if _ then _ else _) _ = _` kall_tac >>
  drule_all raw_call_positive_payload_cut >> strip_tac >>
  `LENGTH s.vs_returndata < dimword (:256)` by simp[] >>
  `w2n w <= w2n w` by simp[] >>
  `w2n w + (32 + ((n + 31) DIV 32) * 32) <= s.vs_alloca_next` by
    (drule stmt_state_rel_local_ptrs_alloca >>
     rewrite_tac[venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def] >>
     strip_tac >> first_x_assum drule >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa s4) s` by
    (irule bodyMemRawCallFinishTheory.raw_call_success_mem_ok >>
     qexistsl_tac [`w`,`n`,`ov`,`ov`] >>
     simp[compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
          compileEnvTheory.comp_return_def,
          exprSafeOperandTheory.safe_operand_def] >>
     metis_tac[exprSafeOperandTheory.safe_operand_def]) >>
  `stmt_state_rel H ctx func cenv cx es (s with vs_fmp := s.vs_fmp)` by simp[] >>
  `w2n w + 32 <= w2n w + (32 + ((n + 31) DIV 32) * 32)` by decide_tac >>
  drule_all exprSimRawCallCalldataTheory.raw_call_output_prefix_ready >>
  strip_tac >> rename1 `run_inst_seq (emitted_insts sa s4) s = OK t` >>
  `local_ptrs_reserved cenv s4 /\ safe_operand s4 ov /\ safe_operand s4 ok` by
    (fs[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[exprSafeOperandTheory.safe_operand_mono,
               exprLoweringPropsTheory.local_ptrs_reserved_next_var]) >>
  `fn_has_code s4 sb func` by metis_tac[fragExecTheory.fn_has_code_split] >>
  drule_all exprSimHashTheory.hash_emitted_inst_mem >> strip_tac >>
  drule_all exprSimRawCallCalldataTheory.raw_call_alloc_buffer_run >>
  strip_tac >> rename1 `run_inst_seq (emitted_insts s4 s5) t = OK a` >>
  rename1 `eval_operand buf.buf_operand a = SOME tw` >>
  qabbrev_tac `cnt = 32 + ((n + 31) DIV 32) * 32` >>
  `FLOOKUP a.vs_allocas alloc.inst_id = SOME (w2n w,cnt)` by
    metis_tac[] >>
  suspend "after_alloca"
QED

Resume raw_call_positive_suffix_mem_ok[after_alloca]:
  `w2n w + cnt <= a.vs_alloca_next /\
   w2n tw + (64 + ((n + 31) DIV 32) * 32) <= a.vs_alloca_next` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _ (a with vs_fmp := _)`
       (mp_then Any mp_tac stmt_state_rel_local_ptrs_alloca) >>
     rewrite_tac[venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def] >>
     simp[venomStateTheory.venom_state_accfupds] >> strip_tac >>
     qpat_assum `!i b k. FLOOKUP a.vs_allocas i = SOME (b,k) ==> _`
       (qspecl_then [`alloc.inst_id`,`w2n w`,`cnt`] mp_tac) >>
     qpat_assum `!i b k. FLOOKUP a.vs_allocas i = SOME (b,k) ==> _`
       (qspecl_then [`s4.cs_next_id`,`w2n tw`,`64 + ((n + 31) DIV 32) * 32`] mp_tac) >>
     simp[]) >>
  `eval_operand ov a = SOME w /\ eval_operand ok a = SOME flag` by
    (`eval_operand ov t = SOME w /\ eval_operand ok t = SOME flag` by metis_tac[] >>
     conj_tac
     >- (Cases_on `ov` >>
         gvs[exprSafeOperandTheory.safe_operand_def, venomStateTheory.eval_operand_def])
     >> Cases_on `ok` >>
     gvs[exprSafeOperandTheory.safe_operand_def, venomStateTheory.eval_operand_def]) >>
  `w2n tw + 32 <= a.vs_alloca_next` by decide_tac >>
  drule_all sha256_mstore_mem >> strip_tac >>
  qabbrev_tac `b = mstore (w2n tw) flag a` >>
  qpat_assum `compile_alloc_buffer _ s4 = _`
    (strip_assume_tac o MATCH_MP abiBufferAllocationCodeTheory.compile_alloc_buffer_code) >>
  qpat_assum `emit_void MSTORE _ s5 = _`
    (strip_assume_tac o MATCH_MP emitHelperPropsTheory.emitted_insts_emit_void) >>
  drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
  qpat_assum `emit_void MCOPY _ s7 = _`
    (strip_assume_tac o MATCH_MP emitHelperPropsTheory.emitted_insts_emit_void) >>
  qabbrev_tac `out = STRING #"%" (toString s6.cs_next_var)` >>
  qabbrev_tac `c = update_var out (tw + 32w) b` >>
  `run_inst_seq (emitted_insts s6 s7) b = OK c` by
    (simp[Abbr `c`] >> irule emitHelperPropsTheory.run_inst_seq_sing_ok >>
     simp[Abbr `out`] >> irule emitHelperPropsTheory.step_ADD >>
     gvs[emitHelperPropsTheory.eval_operand_lit]) >>
  `eval_operand dst c = SOME (tw + 32w)` by
    simp[Abbr `c`, Abbr `out`, emitHelperPropsTheory.eval_operand_update_var] >>
  `eval_operand ov b = SOME w` by simp[] >>
  `eval_operand ov c = SOME w` by
    (Cases_on `ov` >>
     gvs[exprSafeOperandTheory.safe_operand_def, venomStateTheory.eval_operand_def, Abbr `c`] >>
     rename1 `not_fresh_at s4 src` >>
     qspecl_then [`s4`,`src`,`s4.cs_next_var + 1`,`tw + 32w`,`b`] mp_tac
       moduleLoweringPropsTheory.lookup_var_update_not_fresh >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts s6 s7) b` by
    (simp[fragExecMemTheory.run_inst_seq_mem_ok_last,
          memSafeRunTheory.inst_dload_in_section_def, venomInstTheory.mk_inst_def] >>
     irule instMemFrontierTheory.below_frontier_no_ranges >> simp[venomInstTheory.mk_inst_def]) >>
  `run_inst_seq_mem_ok (emitted_insts s4 s5) t` by
    (simp[fragExecMemTheory.run_inst_seq_mem_ok_last,
          memSafeRunTheory.inst_dload_in_section_def, venomInstTheory.mk_inst_def] >>
     irule instMemFrontierTheory.below_frontier_no_ranges >> simp[venomInstTheory.mk_inst_def]) >>
  suspend "copy_and_compose"
QED

Resume raw_call_positive_suffix_mem_ok[copy_and_compose]:
  `cnt < dimword (:256) /\ w2n tw + 32 < dimword (:256)` by
    (simp[Abbr `cnt`] >> decide_tac) >>
  `w2n (tw + 32w) = w2n tw + 32` by simp[abiDecodeStaticPropsTheory.w2n_add_n2w_lt] >>
  `w2n (n2w cnt : bytes32) = cnt` by simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  `c.vs_alloca_next = a.vs_alloca_next` by simp[Abbr `c`, allocaFootprintTheory.update_var_fields] >>
  `w2n (tw + 32w) + cnt <= c.vs_alloca_next` by (simp[Abbr `cnt`] >> decide_tac) >>
  `run_inst_seq_mem_ok (emitted_insts s7 sb) c` by
    (irule allocaFootprintTheory.emit_mcopy_mem_ok >>
     qexistsl_tac [`w`, `tw + 32w`, `dst`, `Lit (n2w cnt)`, `n2w cnt`, `ov`] >>
     simp[emitHelperPropsTheory.eval_operand_lit] >> decide_tac) >>
  `emitted_insts sa sb = emitted_insts sa s4 ++ emitted_insts s4 sb` by
    (irule exprLoweringPropsTheory.emitted_insts_append >>
     fs[emitHelperPropsTheory.inst_extends_def]) >>
  `emitted_insts s6 sb = emitted_insts s6 s7 ++ emitted_insts s7 sb` by
    (irule exprLoweringPropsTheory.emitted_insts_append >> simp[]) >>
  `emitted_insts s5 sb = emitted_insts s5 s6 ++ emitted_insts s6 sb` by
    (irule exprLoweringPropsTheory.emitted_insts_append >> simp[listTheory.APPEND_ASSOC]) >>
  `emitted_insts s4 sb = emitted_insts s4 s5 ++ emitted_insts s5 sb` by
    (irule exprLoweringPropsTheory.emitted_insts_append >> simp[listTheory.APPEND_ASSOC]) >>
  `run_inst_seq_mem_ok (emitted_insts s6 sb) b` by
    (qpat_assum `emitted_insts s6 sb = _` SUBST1_TAC >>
     irule bodyLiteralBufferMemoryTheory.run_inst_seq_mem_ok_append_run >>
     conj_tac >- simp[] >> qexists_tac `c` >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts s5 sb) a` by
    (qpat_assum `emitted_insts s5 sb = _` SUBST1_TAC >>
     irule bodyLiteralBufferMemoryTheory.run_inst_seq_mem_ok_append_run >>
     conj_tac >- simp[] >> qexists_tac `b` >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts s4 sb) t` by
    (qpat_assum `emitted_insts s4 sb = _` SUBST1_TAC >>
     irule bodyLiteralBufferMemoryTheory.run_inst_seq_mem_ok_append_run >>
     conj_tac >- simp[] >> qexists_tac `a` >> simp[]) >>
  qpat_assum `emitted_insts sa sb = _` SUBST1_TAC >>
  irule bodyLiteralBufferMemoryTheory.run_inst_seq_mem_ok_append_run >>
  conj_tac >- simp[] >> qexists_tac `t` >> simp[]
QED

Finalise raw_call_positive_suffix_mem_ok
