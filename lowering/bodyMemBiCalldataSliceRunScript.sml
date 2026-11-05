(* Execution boundaries reconstructed from inaccessible local lemmas of
   exprSimCalldataSliceScript.sml; reference proofs in alan-ref/base/. *)
Theory bodyMemBiCalldataSliceRun
Ancestors
  bodyMemBiCalldataSliceExecFacts bodyMemBiCalldataSliceSuffixMemory
  bodyMemBiCalldataSliceFacts exprSimCalldataSlice exprSimDefs
  freshWrites emitHelperProps exprLoweringProps emitHelper compileEnv
  fragExec venomExecSemantics venomState venomInst words list arithmetic
  exprSimVVFrame finite_map

(* Original: exprSimCalldataSlice.slice_calldata_after_alloc_run [local]. *)
Theorem slice_calldata_after_alloc_run:
  !buf_op op data_op len_op sa s1 s2 s3 s4 sb s w a n.
  emit_op ADD [buf_op; Lit 32w] sa = (data_op,s1) /\
  emit_op CALLDATASIZE [] s1 = (len_op,s2) /\
  compile_assert_slice_bounds op (Lit (n2w n)) len_op s2 = ((),s3) /\
  emit_void CALLDATACOPY [data_op; op; Lit (n2w n)] s3 = ((),s4) /\
  emit_void MSTORE [buf_op; Lit (n2w n)] s4 = ((),sb) /\
  eval_operand buf_op s = SOME w /\ eval_operand op s = SOME (n2w a) /\
  (!x. buf_op = Var x ==> not_fresh_at sa x) /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  0 < n /\ n < dimword (:256) /\ a < dimword (:256) /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  w2n w + 32 + 32 * word_size n < dimword (:256) ==>
  if dimword (:256) <= a+n \/ LENGTH s.vs_call_ctx.cc_calldata < a+n then
    ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t
  else ?t.
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    t.vs_memory = (mstore (w2n w) (n2w n)
      (write_memory_with_expansion (w2n w + 32)
        (TAKE n (DROP a s.vs_call_ctx.cc_calldata)) s)).vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    eval_operand buf_op t = SOME w
Proof
  rpt gen_tac >> strip_tac >>
  drule_all calldata_slice_address_size_mem >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa s2) s = OK u` >>
  `eval_operand op u = SOME (n2w a)` by
    (`eval_operand op u = eval_operand op s` suffices_by simp[] >>
     irule literal_operand_frame >> conj_tac
     >- (qexists_tac `sa` >> simp[]) >>
     qpat_x_assum `u = s with vs_vars := _` SUBST1_TAC >> simp[]) >>
  `!x. op = Var x ==> not_fresh_at s2 x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `eval_operand (Lit (n2w n)) u = SOME (n2w n)` by simp[eval_operand_def] >>
  `!x. Lit (n2w n) = Var x ==> not_fresh_at s2 x` by simp[] >>
  `emitted_insts sa sb = emitted_insts sa s2 ++
     emitted_insts s2 s3 ++ emitted_insts s3 sb` by
    (imp_res_tac inst_extends_emit_void >>
     drule calldata_slice_bounds_extends >> strip_tac >>
     `inst_extends s3 sb /\ inst_extends s2 sb` by
       metis_tac[inst_extends_trans] >>
     fs[inst_extends_def] >>
     `emitted_insts s2 sb = emitted_insts s2 s3 ++ emitted_insts s3 sb` by
       (irule emitted_insts_append >> simp[]) >>
     `emitted_insts sa sb = emitted_insts sa s2 ++ emitted_insts s2 sb` by
       (irule emitted_insts_append >> simp[]) >> simp[]) >>
  `(n2w a + n2w n <+ (n2w a:bytes32) \/
      n2w (LENGTH s.vs_call_ctx.cc_calldata) <+ (n2w a + n2w n:bytes32)) =
    (dimword (:256) <= a+n \/ LENGTH s.vs_call_ctx.cc_calldata < a+n)` by
    (mp_tac (Q.INST [`a` |-> `a`, `n` |-> `n`,
       `limit` |-> `LENGTH s.vs_call_ctx.cc_calldata`] slice_bounds_word) >>
     gvs[wordsTheory.dimword_def]) >>
  drule_all slice_bounds_run_frame >> simp[] >>
  Cases_on `dimword (:256) <= a+n \/ LENGTH s.vs_call_ctx.cc_calldata < a+n` >>
  simp[] >> strip_tac
  >- suspend "revert" >>
  suspend "success"
QED

Resume slice_calldata_after_alloc_run[revert]:
  qexists_tac `t` >> asm_rewrite_tac[] >>
  rewrite_tac[GSYM APPEND_ASSOC] >>
  qpat_assum `run_inst_seq _ s = OK u`
    (mp_then Any (qspec_then `emitted_insts s2 s3 ++ emitted_insts s3 sb`
       SUBST1_TAC) run_inst_seq_append) >>
  `!v. run_inst_seq (emitted_insts s2 s3) u <> OK v` by simp[] >>
  drule run_inst_seq_append_err >>
  disch_then (qspec_then `emitted_insts s3 sb` SUBST1_TAC) >> simp[]
QED

Resume slice_calldata_after_alloc_run[success]:
  qpat_x_assum `s2.cs_current_insts = _` kall_tac >>
  qpat_x_assum `same_blocks sa s2` kall_tac >>
  qpat_x_assum `s2.cs_next_id = _` kall_tac >>
  qpat_x_assum `_ <+ _ \/ _ <+ _ <=> _` kall_tac >>
  `!x. not_fresh_at s2 x ==> lookup_var x t = lookup_var x u` by
    simp[lookup_var_def] >>
  `eval_operand data_op t = SOME (w + 32w) /\
   eval_operand op t = SOME (n2w a)` by
    (conj_tac >>
     `!operand. (!x. operand = Var x ==> not_fresh_at s2 x) ==>
        eval_operand operand t = eval_operand operand u` by
       (rpt strip_tac >> irule literal_operand_frame >> conj_tac
        >- (qexists_tac `s2` >> simp[]) >>
        qpat_x_assum `t = u with vs_vars := _` SUBST1_TAC >> simp[]) >>
     simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at s2 x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s` by
    (rpt strip_tac >> metis_tac[]) >>
  `t = s with vs_vars := t.vs_vars` by
    (qpat_x_assum `t = u with vs_vars := _` SUBST1_TAC >>
     qpat_x_assum `u = s with vs_vars := _` SUBST1_TAC >> simp[]) >>
  `eval_operand buf_op t = SOME w` by
    (`eval_operand buf_op t = eval_operand buf_op s` suffices_by simp[] >>
     irule literal_operand_frame >> conj_tac
     >- (qexists_tac `sa` >> simp[]) >>
     qpat_x_assum `t = s with vs_vars := _` SUBST1_TAC >> simp[]) >>
  `w2n (n2w a:bytes32) + w2n (n2w n:bytes32) <=
     LENGTH t.vs_call_ctx.cc_calldata` by
    (qpat_x_assum `t = s with vs_vars := _` SUBST1_TAC >>
     gvs[wordsTheory.w2n_n2w]) >>
  `eval_operand (Lit (n2w n)) t = SOME (n2w n)` by simp[eval_operand_def] >>
  drule_all slice_calldata_copy_store_run >> disch_tac >>
  suspend "finish"
QED

Resume slice_calldata_after_alloc_run[finish]:
  qpat_x_assum `emit_op ADD _ _ = _` kall_tac >>
  qpat_x_assum `emit_op CALLDATASIZE _ _ = _` kall_tac >>
  qpat_x_assum `compile_assert_slice_bounds _ _ _ _ = _` kall_tac >>
  qpat_x_assum `emit_void CALLDATACOPY _ _ = _` kall_tac >>
  qpat_x_assum `emit_void MSTORE _ _ = _` kall_tac >>
  `w2n (w + 32w) = w2n w + 32` by
    (`w2n w + w2n (32w:bytes32) < dimword (:256)` by (simp[] >> decide_tac) >>
     drule wordsTheory.w2n_add_2 >> simp[]) >>
  qmatch_asmsub_abbrev_tac `run_inst_seq (emitted_insts s3 sb) t = OK result` >>
  qexists_tac `result` >> conj_tac
  >- (rewrite_tac[GSYM APPEND_ASSOC] >>
      qpat_assum `run_inst_seq _ s = OK u`
        (mp_then Any (qspec_then `emitted_insts s2 s3 ++ emitted_insts s3 sb`
          SUBST1_TAC) run_inst_seq_append) >>
      qpat_assum `run_inst_seq _ u = OK t`
        (mp_then Any (qspec_then `emitted_insts s3 sb` SUBST1_TAC)
          run_inst_seq_append) >> simp[]) >>
  `t.vs_memory = s.vs_memory /\
   t.vs_call_ctx = s.vs_call_ctx` by
    (qpat_x_assum `t = s with vs_vars := _` SUBST1_TAC >> simp[]) >>
  qmatch_goalsub_abbrev_tac `result.vs_memory = reference.vs_memory` >>
  suspend "frame"
QED

Resume slice_calldata_after_alloc_run[frame]:
  `result = t with vs_memory := reference.vs_memory` by
    (simp[Abbr `result`, Abbr `reference`, wordsTheory.w2n_n2w,
          IgnAsm `t = s with vs_vars := _`, IgnAsm `t = u with vs_vars := _`,
          IgnAsm `u = s with vs_vars := _`] >>
     drule write_memory_with_expansion_equal_memory >>
     disch_then (qspecl_then [`w2n w + 32`,
       `TAKE n (DROP a s.vs_call_ctx.cc_calldata)`] SUBST1_TAC) >>
     qmatch_goalsub_abbrev_tac `mstore _ _ (t with vs_memory := copied.vs_memory)` >>
     `(t with vs_memory := copied.vs_memory).vs_memory = copied.vs_memory` by simp[] >>
     drule mstore_equal_memory >>
     disch_then (qspecl_then [`w2n w`, `n2w n`] SUBST1_TAC) >>
     simp[NoAsms]) >>
  qpat_x_assum `result = t with vs_memory := _` SUBST1_TAC >>
  simp[IgnAsm `t = s with vs_vars := _`, IgnAsm `t = u with vs_vars := _`,
       IgnAsm `u = s with vs_vars := _`, lookup_var_def] >>
  conj_tac
  >- (qpat_x_assum `t = s with vs_vars := _` SUBST1_TAC >> simp[NoAsms]) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!x. not_fresh_at sa x ==> lookup_var x t = _` drule >>
      simp[lookup_var_def] >>
      qpat_x_assum `!x. not_fresh_at sa x ==> lookup_var x u = _` drule >>
      simp[lookup_var_def]) >>
  Cases_on `buf_op` >> gvs[eval_operand_def, lookup_var_def]
QED

Finalise slice_calldata_after_alloc_run
