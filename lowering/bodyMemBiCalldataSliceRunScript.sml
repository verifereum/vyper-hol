(* Execution boundaries reconstructed from inaccessible local lemmas of
   exprSimCalldataSliceScript.sml; reference proofs in alan-ref/base/. *)
Theory bodyMemBiCalldataSliceRun
Ancestors
  bodyMemBiCalldataSliceExecFacts bodyMemBiCalldataSliceSuffixMemory
  bodyMemBiCalldataSliceFacts exprSimCalldataSlice exprSimDefs
  freshWrites emitHelperProps exprLoweringProps emitHelper compileEnv
  fragExec venomExecSemantics venomState venomInst words list arithmetic
  exprSimVVFrame finite_map exprSimAlloc exprSimLiteralBuffer
  loweringPosts valueEncoding valueEncodingProps valueTypingMemoryProps
  vyperContext vyperState vyperValue vyperTypeSystem vyperAST
  exprSimProps context localPtrsProps immutableMemoryFrame builtinBytes
  vyperTypeInvariants

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

(* Original: exprSimCalldataSlice.calldata_slice_write_encoding [local]. *)
Theorem calldata_slice_write_encoding[local]:
  !a n bs p bound s. a + n <= LENGTH bs ==>
  val_in_memory (BaseTV (BytesT (Dynamic bound)))
    (BytesV (TAKE n (DROP a bs))) p
    (mstore p (n2w n)
      (write_memory_with_expansion (p + 32) (TAKE n (DROP a bs)) s)).vs_memory
Proof
  rpt strip_tac >>
  `LENGTH (TAKE n (DROP a bs)) = n` by simp[LENGTH_TAKE_EQ] >>
  metis_tac[bytes_buffer_write_encoding]
QED

(* Original: exprSimCalldataSlice.slice_calldata_run [local]. *)
Theorem slice_calldata_run:
  !op n sa ptr sb func cenv cx es s a ctx.
  compile_slice_calldata op (Lit (n2w n)) (32 + 32 * word_size n) sa = (ptr,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s /\
  context_well_typed cx /\ 0 < n /\ n < dimword (:256) /\ a < dimword (:256) /\
  32 + 32 * word_size n < 2 ** 64 /\
  eval_operand op s = SOME (n2w a) /\
  (!x. op = Var x ==> not_fresh_at sa x) ==>
  if dimword (:256) <= a+n \/ LENGTH cx.txn.calldata < a+n then
    ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t
  else ?t w. run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel ctx func cenv cx es t /\ eval_operand ptr t = SOME w /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,32 + 32 * word_size n) /\
    val_in_memory (BaseTV (BytesT (Dynamic n)))
      (BytesV (TAKE n (DROP a cx.txn.calldata))) (w2n w) t.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid b len. FLOOKUP s.vs_allocas aid = SOME (b,len) /\ aid < sa.cs_next_id ==>
       mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
    locals_kept cenv es s t /\
    (!nm lb len. local_region cenv es.scopes t nm lb len ==>
       regions_disjoint (w2n w) (32 + 32 * word_size n) lb len)
Proof
  rpt gen_tac >> strip_tac >>
  drule slice_calldata_shape >> strip_tac >>
  drule slice_calldata_parts >> strip_tac >> gvs[] >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w (32 + 32 * word_size n))]
       [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    (gvs[fn_has_code_def, same_blocks_def, rich_listTheory.IS_PREFIX_APPEND] >>
     irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
     simp[MEM_APPEND] >> metis_tac[MEM_APPEND]) >>
  `32 + 32 * word_size n < dimword (:256)` by
    (gvs[wordsTheory.dimword_def] >> decide_tac) >>
  gvs[] >> drule_all literal_alloc_buffer_run >> strip_tac >>
  suspend "allocated"
QED

Resume slice_calldata_run[allocated]:
  `(cenv.ce_is_ctor ==> !name tv v off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
       SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name =
       SOME (tv,v) ==>
     regions_disjoint off (type_memory_size tv) (w2n w)
       (32 * word_size n + 32))` by
    (rpt strip_tac >>
     qpat_assum `stmt_state_rel ctx func cenv cx es t` mp_tac >>
     pure_rewrite_tac[stmt_state_rel_def, immutable_alloca_sep_def] >> strip_tac >>
     qpat_x_assum `cenv.ce_is_ctor ==> _` drule >>
     disch_then drule_all >> strip_tac >>
     qpat_x_assum `!inst b sz. MEM inst _ /\ _ ==> _`
       (qspec_then `mk_inst sa.cs_next_id ALLOCA
         [Lit (n2w (32 * word_size n + 32))]
         [STRING #"%" (toString sa.cs_next_var)]` mp_tac) >>
     simp[mk_inst_def]) >>
  `t.vs_call_ctx.cc_calldata = cx.txn.calldata /\
   LENGTH t.vs_call_ctx.cc_calldata < dimword (:256)` by
    (gvs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def,
         context_well_typed_def, wordsTheory.dimword_def]) >>
  `t.vs_labels = s.vs_labels` by
    (drule_all hash_alloc_buffer_labels >> simp[]) >>
  `eval_operand op t = SOME (n2w a)` by
    (Cases_on `op` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[contextTheory.compile_alloc_buffer_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
     strip_tac >> gvs[]) >>
  `!x. op = Var x ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `!x. buf.buf_operand = Var x ==> not_fresh_at sm x` by simp[] >>
  `w2n w + 32 + 32 * word_size n < dimword (:256)` by decide_tac >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule calldata_slice_allocation_split >> metis_tac[]) >>
  drule_all slice_calldata_after_alloc_run >>
  suspend "run_cases"
QED

Resume slice_calldata_run[run_cases]:
  qpat_x_assum `compile_slice_calldata _ _ _ _ = _` kall_tac >>
  qpat_x_assum `fn_has_code _ _ _` kall_tac >>
  qpat_x_assum `fn_inst_ids_distinct _` kall_tac >>
  qpat_x_assum `EVERY _ _` kall_tac >>
  qpat_x_assum `same_blocks _ _` kall_tac >>
  qpat_x_assum `sb.cs_next_id = _` kall_tac >>
  qpat_x_assum `sb.cs_next_var = _` kall_tac >>
  qpat_x_assum `MEM _ (emitted_insts _ _)` kall_tac >>
  qpat_x_assum `MEM _ (fn_insts _)` kall_tac >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` kall_tac >>
  qpat_x_assum `emit_op ADD _ _ = _` kall_tac >>
  qpat_x_assum `emit_op CALLDATASIZE _ _ = _` kall_tac >>
  qpat_x_assum `compile_assert_slice_bounds _ _ _ _ = _` kall_tac >>
  qpat_x_assum `emit_void CALLDATACOPY _ _ = _` kall_tac >>
  qpat_x_assum `emit_void MSTORE _ _ = _` kall_tac >>
  simp[] >>
  Cases_on `dimword (:256) <= a+n \/ LENGTH cx.txn.calldata < a+n` >>
  simp[] >> strip_tac
  >- (rename1 `run_inst_seq (emitted_insts sm sb) t = Abort _ t_abort` >>
      qexists_tac `t_abort` >> asm_rewrite_tac[] >>
      qpat_assum `run_inst_seq _ s = OK t`
        (mp_then Any (qspec_then `emitted_insts sm sb` SUBST1_TAC)
          run_inst_seq_append) >> simp[]) >>
  rename1 `run_inst_seq (emitted_insts sm sb) t = OK u` >>
  `u.vs_allocas = t.vs_allocas` by
    (qpat_assum `_ with <|vs_memory := _; vs_vars := _|> = t`
       (mp_tac o AP_TERM ``\z. z.vs_allocas``) >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s` by
    (rpt strip_tac >>
     `not_fresh_at sm x` by
       (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
     qpat_x_assum `!x. not_fresh_at sm x ==> _` drule >>
     qpat_x_assum `!x. not_fresh_at sa x ==> _` drule >> simp[]) >>
  qexistsl_tac [`u`,`w`] >> conj_tac
  >- (asm_rewrite_tac[] >>
      qpat_assum `run_inst_seq _ s = OK t`
        (mp_then Any (qspec_then `emitted_insts sm sb` SUBST1_TAC)
          run_inst_seq_append) >> simp[]) >>
  suspend "success_frame"
QED

Resume slice_calldata_run[success_frame]:
  `LENGTH (TAKE n (DROP a cx.txn.calldata)) = n` by
    (simp[LENGTH_TAKE_EQ] >> decide_tac) >>
  `n <= 32 * word_size n` by simp[word_size_capacity] >>
  `!b len. b + len <= w2n w \/ w2n w + 32 + n <= b ==>
      mem_bytes_at b len u.vs_memory = mem_bytes_at b len t.vs_memory` by
    (rpt strip_tac >>
     qpat_assum `u.vs_memory = _` (fn th => once_rewrite_tac[th]) >>
     `n2w n = n2w (LENGTH (TAKE n (DROP a cx.txn.calldata))):bytes32` by simp[] >>
     pop_assum SUBST1_TAC >> irule bytes_buffer_write_frame >> simp[]) >>
  conj_tac >- suspend "state_rel" >>
  simp[] >> conj_tac
  >- (asm_rewrite_tac[] >> irule calldata_slice_write_encoding >> decide_tac) >>
  conj_tac
  >- (rpt strip_tac >>
      `b + len <= w2n w \/ w2n w + 32 + n <= b` by
        (qpat_x_assum `!aid b len. _ ==> regions_disjoint _ _ _ _` drule >>
         simp[regions_disjoint_def] >> decide_tac) >>
      metis_tac[]) >>
  reverse conj_tac
  >- (rpt strip_tac >>
      `local_region cenv es.scopes t nm lb len` by
        (irule exprSimPropsTheory.local_region_frame >> conj_tac
         >- (qexists_tac `func` >> gvs[stmt_state_rel_def, state_rel_def]) >>
         qexistsl [`sa`, `es.scopes`, `u`] >> simp[] >>
         rpt strip_tac >>
         qpat_x_assum `!x. not_fresh_at sa x ==> lookup_var x u = _` drule >>
         qpat_x_assum `!x. not_fresh_at sa x ==> lookup_var x t = _` drule >> simp[]) >>
      qpat_x_assum `!name b len. local_region _ _ t _ _ _ ==> _` drule >>
      pure_rewrite_tac[regions_disjoint_def] >> decide_tac) >>
  irule locals_kept_regions >> rpt strip_tac >>
  rename1 `local_region cenv es.scopes s nm b sz` >>
  `local_region cenv es.scopes t nm b sz` by
    (irule exprSimPropsTheory.local_region_frame_fwd >>
     qexistsl [`s`, `sa`, `es.scopes`] >> simp[]) >>
  `b + sz <= w2n w \/ w2n w + 32 + n <= b` by
    (qpat_x_assum `!name b len. local_region _ _ _ _ _ _ ==> _` drule >>
     simp[regions_disjoint_def] >> decide_tac) >>
  metis_tac[]
QED

Resume slice_calldata_run[state_rel]:
  irule literal_state_memory_frame >> qexists_tac `t` >>
  simp[IgnAsm `u.vs_memory = _`] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!b len. _ ==> mem_bytes_at _ _ u.vs_memory = _` mp_tac >>
      simp[IgnAsm `u.vs_memory = _`] >> disch_then irule >>
      qpat_x_assum `!name b len. local_region _ _ _ _ _ _ ==> _` drule >>
      simp[regions_disjoint_def] >> decide_tac) >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x t` by
    (rpt strip_tac >>
     `not_fresh_at sm x` by
       (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
     simp[]) >>
  rpt conj_tac
  >- (rpt strip_tac >>
      fs[local_ptrs_reserved_def] >>
      qpat_x_assum `!n1 n2 p sz1 sz2. _` drule >> strip_tac >> simp[])
  >- (rpt strip_tac >> drule_all local_ptrs_reserved_imm_base >> strip_tac >>
      qpat_x_assum `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x t` irule >>
      first_assum ACCEPT_TAC)
  >- (qpat_assum `u.vs_memory = _` (fn th => once_rewrite_tac[th]) >>
      simp[immutableMemoryFrameTheory.immutable_mstore_capacity,
           immutableMemoryFrameTheory.immutable_write_memory_capacity] >>
      decide_tac) >>
  rpt strip_tac >>
  `regions_disjoint off (type_memory_size tv) (w2n w)
     (32 * word_size n + 32)` by metis_tac[] >>
  qpat_assum `!b len. _ ==> mem_bytes_at _ _ u.vs_memory = _`
    (qspec_then `off` mp_tac) >>
  disch_then (qspec_then `type_memory_size tv` mp_tac) >>
  simp[regions_disjoint_def] >>
  impl_tac >- (fs[regions_disjoint_def] >> decide_tac) >> simp[]
QED

Finalise slice_calldata_run
