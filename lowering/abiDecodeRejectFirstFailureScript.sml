(* Allocation-backed decoder rejection at the first failed check. *)
Theory abiDecodeRejectFirstFailure
Ancestors
  abiMalformedRecursiveInterface exprSimAbiDecodePrimitiveOwned
  abiCanonicalHeadSize abiBoundedLeafReflection abiDecoderContract
  decoderNavigationPtr abiDecodePtrMemberFrame
  abiDecodePtrPrims[qualified,ignore_grammar]
  abiDecodeScalarRunSafety[qualified,ignore_grammar]
  abiDecodeRejectIndexedPass[qualified,ignore_grammar]
  abiMalformedEntryProps[qualified,ignore_grammar]
  calldataExactScalarJoint stmtReasonLitFragMemory abiDecoderClampOutcome
  abiDecoderAbortReentry abiDecoderReentry abiDecoderVarSequence
  stateRelProj emitHelperProps exprLoweringProps venomExecSemantics venomState
  venomInst fragGasOriginPtr ptrDiscipline allocasBelowFmpUpdatesProps arithmetic words list
  bodyPtrBopScalarCompile bodyPtrBopScalarSeq abiDecoderRange emitHelper
  loweringStateRelDefs bodyFullBopWordSuccess bodyPtrBopScalarDynamic
  abiBoundedBytesExecution decoderGhostFramePtr fragGasCopyLoop fragGasSeqPtr memSafeRun
  fragGasCopySeqLiftProps
  abiDecoderComplexHead abiDecoderComplexGuard exprSimAbiDecodeCompositePrefix
  exprSimAbiDecodeComplexOutcome
  abiDecodeRejectMemberTable abiDecodeRejectArrayPrefix abiDecodeRejectIndexedGuard
  calldataRecursiveProducers abiDecoderCoherence abiValidAllocatedContract
  exprLowering abiVyperAdmissible vyperABIValid valueEncodingTyping contractABI
  abiMalformedBoundedContract abiDecodeRejectArrayLayout abiDecodeRejectArrayCountLoad
  abiDecodeRejectArraySpan abiDecodeRejectFiniteArray[qualified,ignore_grammar]
  finite_map list rich_list

Theorem malformed_scalar_source_window[local]:
  abi_decoder_coherent ce env sf ty tv /\ assignable_type env ty /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  abi_malformed_allocated_window live B L xs s /\ p + 32 <= L /\
  bytes = (if is_dynamic (vyper_to_abi_type env ty) then DROP p xs
    else TAKE (static_length (vyper_to_abi_type env ty)) (DROP p xs)) ==>
  bytes = mem_bytes_at (B+p) 32 s.vs_memory /\ type_memory_bytes ce ty = 32
Proof
  strip_tac >> drule_all abi_decode_scalar_source_shape >> strip_tac >>
  fs[abi_malformed_allocated_window_def] >>
  qpat_x_assum `mem_bytes_at B L s.vs_memory = xs` (SUBST1_TAC o SYM) >>
  irule mem_bytes_at_window >> simp[]
QED

Theorem malformed_scalar_rejects_clamp[local]:
  abi_decoder_coherent ce env sf ty tv /\ assignable_type env ty /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  (?av. has_type (vyper_to_abi_type env ty) av) /\
  abi_malformed_allocated_window live B L xs s /\ p + 32 <= L /\
  bytes = (if is_dynamic (vyper_to_abi_type env ty) then DROP p xs
    else TAKE (static_length (vyper_to_abi_type env ty)) (DROP p xs)) /\
  ~(vyper_decode_valid_enc (vyper_to_abi_type env ty) bytes /\
    abi_vyper_admissible env ty (dec (vyper_to_abi_type env ty) bytes)) ==>
  ~abi_decoder_clamp_valid clamp (abi_decode_load MLOAD (n2w (B+p):bytes32) s)
Proof
  strip_tac >> drule_all malformed_scalar_source_window >> strip_tac >>
  `B+p < dimword(:256)` by (fs[abi_malformed_allocated_window_def] >> decide_tac) >>
  strip_tac >>
  `mem_bytes_at (B+p) 32 (abi_decode_source MLOAD s) = bytes` by
    simp[abi_decode_source_def] >>
  `vyper_decode_valid_enc (vyper_to_abi_type env ty) bytes /\
   abi_vyper_admissible env ty (dec (vyper_to_abi_type env ty) bytes)` by
    (irule abi_decoder_primitive_memory_reflect >> conj_tac
     >- (qexists `av` >> simp[])
     >- (qexistsl_tac [`ce`, `clamp`, `32`, `MLOAD`, `s`, `B+p`, `sf`, `tv`,
           `abi_decode_load MLOAD (n2w (B+p):bytes32) s`] >> simp[])) >>
  metis_tac[]
QED

(* The load's physical endpoint is the entry to the rejecting clamp. *)
Theorem malformed_scalar_load_prefix[local]:
  emit_op ADD [Var source;pos] st = (Var addr,sa) /\
  emit_op MLOAD [Var addr] sa = (value,sb) /\
  fn_has_code st sa func /\ fn_has_code sa sb func /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  eval_operand pos s = SOME (n2w p) /\
  op_prov G pos = NONE /\ op_taint tn pos = {} /\
  p+32 <= L /\ B+L < dimword(:256) /\ B+p+32 <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?loaded HG th.
    eval_operand value loaded = SOME (abi_decode_load MLOAD (n2w (B+p):bytes32) s) /\
    op_prov HG value = NONE /\ op_taint th value = {} /\
    allocas_from lo loaded /\ (ctx_has_dalloca ctx ==> allocas_below_fmp loaded) /\
      ~loaded.vs_halted /\
    loaded.vs_current_bb = sb.cs_current_bb /\
    loaded.vs_inst_idx = LENGTH sb.cs_current_insts /\
    loaded.vs_accounts = s.vs_accounts /\ loaded.vs_transient = s.vs_transient /\
    loaded.vs_call_ctx = s.vs_call_ctx /\ loaded.vs_immutables = s.vs_immutables /\
    loaded.vs_memory = s.vs_memory /\ loaded.vs_labels = s.vs_labels /\
    (!x. not_fresh_at st x ==> lookup_var x loaded = lookup_var x s /\
      FLOOKUP HG x = FLOOKUP G x /\ op_taint th (Var x) = op_taint tn (Var x)) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK loaded,HG,th))
Proof
  strip_tac >> fs[abi_decode_ptr_window_def] >>
  `B < dimword(:256) /\ B+p < dimword(:256)` by decide_tac >>
  `w2n (n2w B:bytes32) = B /\ w2n (n2w (B+p):bytes32) = B+p` by
    simp[w2n_n2w, LESS_MOD] >>
  `eval_operand (Var source) s = SOME (n2w B)` by simp[eval_operand_def] >>
  qabbrev_tac `raw = update_var addr (n2w (B+p)) s` >>
  `run_inst_seq (emitted_insts st sa) s = OK raw` by
    (qpat_assum `emit_op ADD _ _ = _`
       (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
     gvs[Abbr `raw`, run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
         exec_pure2_def, word_add_n2w]) >>
  `?G1 tn1. ptr_covers G1 tn1 addr
      (raw with vs_inst_idx := SUC s.vs_inst_idx) 32 /\
      tn1.t_mem = tn.t_mem /\
      (!x. not_fresh_at st x ==> lookup_var x raw = lookup_var x s /\
        FLOOKUP G1 x = FLOOKUP G x /\ op_taint tn1 (Var x) = op_taint tn (Var x)) /\
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK (raw with vs_inst_idx := LENGTH sa.cs_current_insts),G1,tn1))` by
    (`w2n (n2w B:bytes32) + p < dimword(:256)` by simp[] >>
     drule_all (Q.INST [`n` |-> `32`] (SPEC_ALL emit_ptr_offset_endpoint_ptr_origin_core)) >>
     strip_tac >> gvs[] >> metis_tac[]) >>
  `LENGTH sa.cs_current_insts = SUC s.vs_inst_idx` by
    (qpat_assum `emit_op ADD _ _ = _`
       (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >> simp[]) >>
  qabbrev_tac `mid = raw with vs_inst_idx := LENGTH sa.cs_current_insts` >>
  `sa.cs_current_bb = st.cs_current_bb /\ sb.cs_current_bb = sa.cs_current_bb` by
    metis_tac[emit_op_same_blocks,same_blocks_def] >>
  `ptr_covers G1 tn1 addr mid 32 /\ lookup_var addr mid = SOME (n2w (B+p)) /\
   allocas_from lo mid /\ ~mid.vs_halted /\
   mid.vs_current_bb = sa.cs_current_bb /\ mid.vs_inst_idx = LENGTH sa.cs_current_insts /\
   mid.vs_alloca_next = s.vs_alloca_next` by
    (conj_tac
     >- (qpat_x_assum `ptr_covers G1 tn1 addr _ 32` mp_tac >> simp[Abbr `mid`]) >>
     qpat_x_assum `allocas_from lo s` mp_tac >>
     simp[Abbr `mid`, Abbr `raw`, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
          allocas_from_def, update_var_def]) >>
  `!i. w2n (n2w (B+p):bytes32) <= i /\ i < w2n (n2w (B+p):bytes32)+32 ==>
       i NOTIN tn1.t_mem` by (simp[] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `eval_operand (Var addr) mid = SOME (n2w (B+p))` by simp[eval_operand_def] >>
  `?q rawload. value = Var q /\ rawload = update_var q (mload (B+p) mid) mid /\
    run_inst_seq (emitted_insts sa sb) mid = OK rawload` by
    (qpat_assum `emit_op MLOAD _ _ = _`
       (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
     gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def]) >>
  drule_all emit_mload_clean_endpoint_ptr_origin_core >>
  disch_then (qspecl_then [`H`, `cx`, `ctx`, `PG`, `R`] strip_assume_tac) >>
  rename1 `op_prov HG value = NONE` >> rename1 `op_taint th value = {}` >>
  `w2n (n2w (B+p):bytes32) + 32 <= mid.vs_alloca_next` by
    (simp[] >> decide_tac) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp mid` by
    (simp[Abbr `mid`, Abbr `raw`, allocas_below_fmp_updates] >>
     first_assum ACCEPT_TAC) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (mid,G1,tn1) [] (OK (rawload with vs_inst_idx := LENGTH sb.cs_current_insts),HG,th)` by
    (rpt gen_tac >>
     qpat_assum `!D lower explicit ctx' f. _ ==> gas_origin_ptr_path _ _ _ _`
       (qspecl_then [`D`, `lo`, `explicit`, `ctx`, `func`] mp_tac) >> simp[]) >>
  `ctx_has_dalloca ctx ==>
    allocas_below_fmp (rawload with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (qpat_assum `rawload = update_var _ _ mid` (fn th => rewrite_tac[th]) >>
     rewrite_tac[allocas_below_fmp_updates] >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`rawload with vs_inst_idx := LENGTH sb.cs_current_insts`, `HG`, `th`] >>
  `mid.vs_memory = s.vs_memory` by simp[Abbr `mid`, Abbr `raw`, update_var_def] >>
  `allocas_from lo (rawload with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (simp[allocas_from_def] >>
     qpat_assum `allocas_from lo mid` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  conj_tac
  >- simp[eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
           abi_decode_load_def, mload_def, update_var_def] >>
  simp[] >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK (rawload with vs_inst_idx := LENGTH sb.cs_current_insts),HG,th)` by
    (rpt gen_tac >>
     qpat_x_assum `!D explicit. gas_origin_ptr_path _ (mid,_,_) _ _`
       (qspecl_then [`D`, `explicit`] mp_tac) >>
     qpat_x_assum `!D explicit. gas_origin_ptr_path _ (s,_,_) _ _`
       (qspecl_then [`D`, `explicit`] mp_tac) >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[gas_origin_ptr_path_append, APPEND]) >>
  `st.cs_current_bb = sb.cs_current_bb` by fs[same_blocks_def] >>
  reverse (rpt conj_tac)
  >- (qpat_x_assum `!D explicit. gas_origin_ptr_path _ (s,_,_) _ (OK (rawload with vs_inst_idx := _),_,_)`
        mp_tac >> simp[update_var_def, Abbr `mid`])
  >- (rpt strip_tac >>
      `not_fresh_at sa x` by
        (qpat_assum `emit_op ADD _ st = _`
           (mp_then Any strip_assume_tac placeMemoryCodeLayoutTheory.emit_op_next_var) >>
         irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `st` >> simp[]) >>
      qpat_assum `!x. not_fresh_at sa x ==> _` (qspec_then `x` mp_tac) >>
      qpat_assum `!x. not_fresh_at st x ==> _` (qspec_then `x` mp_tac) >>
      `mid.vs_vars = raw.vs_vars` by simp[Abbr `mid`] >>
      `rawload.vs_vars = mid.vs_vars |+ (q, mload (B+p) mid)` by simp[update_var_def] >>
      qpat_assum `mid.vs_vars = raw.vs_vars` mp_tac >>
      qpat_assum `rawload.vs_vars = _` mp_tac >>
      qpat_assum `not_fresh_at sa x` mp_tac >>
      qpat_assum `not_fresh_at st x` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> simp[lookup_var_def] >> metis_tac[]) >>
  qpat_x_assum `Abbrev (mid = _)` mp_tac >>
  qpat_x_assum `Abbrev (raw = _)` mp_tac >>
  qpat_x_assum `s.vs_current_bb = st.cs_current_bb` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp[markerTheory.Abbrev_def, update_var_def] >>
  rpt strip_tac >> simp[update_var_def]
QED

(* Only the clamp's scalar temporaries and the revert bookkeeping change. *)
Theorem malformed_clamp_world_frame[local]:
  compile_abi_clamp_basetype value clamp sa = ((),sb) /\
  run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t ==>
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_immutables = s.vs_immutables
Proof
  strip_tac >> drule calldataClampPtrTheory.calldata_clamp_instructions >> strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  qpat_x_assum `emitted_insts _ _ = _` (fn th => pure_rewrite_tac[th])
  >- simp[run_inst_seq_def]
  >> qpat_x_assum `MEM _ _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp[MEM] >> strip_tac >> Cases_on `signed` >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure1_def, exec_pure2_def, AllCaseEqs(),
       update_var_def, revert_state_def, set_returndata_def] >>
  strip_tac >> gvs[]
QED

Theorem malformed_scalar_prefix_abort[local]:
  emit_op ADD [Var source;pos] st = (Var addr,sa) /\
  emit_op MLOAD [Var addr] sa = (value,sb) /\
  compile_abi_clamp_basetype value clamp sb = ((),sc) /\
  fn_has_code st sa func /\ fn_has_code sa sb func /\ fn_has_code sb sc func /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  eval_operand pos s = SOME (n2w p) /\
  op_prov G pos = NONE /\ op_taint tn pos = {} /\
  p+32 <= L /\ B+L < dimword(:256) /\ B+p+32 <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_decoder_clamp_wf clamp /\
  ~abi_decoder_clamp_valid clamp (abi_decode_load MLOAD (n2w (B+p):bytes32) s) ==>
  ?u G' tn'.
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (Abort Revert_abort u,G',tn'))
Proof
  strip_tac >>
  drule_all malformed_scalar_load_prefix >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `?stopped. run_inst_seq (emitted_insts sb sc) loaded = Abort Revert_abort stopped` by
    (irule abi_decoder_sequence_revert_reentry >>
     `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts sb sc)` by
       (drule calldataClampPtrTheory.calldata_clamp_instructions >> strip_tac >>
        gvs[mk_inst_def, abi_decoder_reentry_opcode_def, MEM] >>
        Cases_on `signed` >> simp[mk_inst_def, abi_decoder_reentry_opcode_def]) >>
     simp[] >>
     `abi_decoder_operand_live sb.cs_next_var value` by metis_tac[abi_decoder_operand_live_emit] >>
     CONV_TAC SWAP_EXISTS_CONV >> qexists `sb.cs_next_var` >>
     irule abi_decoder_clamp_revert >>
     simp[abi_decoder_prune_fresh] >>
     qexistsl_tac [`clamp`, `value`, `abi_decode_load MLOAD (n2w (B+p):bytes32) s`] >>
     simp[abi_decoder_prune_eval]) >>
  drule_all malformed_clamp_world_frame >> strip_tac >>
  `?bb. lookup_block loaded.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sb sc) (DROP loaded.vs_inst_idx bb.bb_instructions)` by
    (drule calldataClampPtrTheory.calldata_clamp_instructions >> strip_tac >>
     drule_all fn_has_code_code >> simp[] >> metis_tac[]) >>
  drule_all (Q.INST [`R` |-> `{} : string set`] (SPEC_ALL exact_scalar_clamp_abort_joint)
    |> SIMP_RULE (srw_ss()) []) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`stopped with vs_inst_idx := j`, `H`, `u`] >> simp[] >>
  rpt gen_tac >>
  qpat_x_assum `!D explicit. gas_origin_ptr_path _ (loaded,_,_) _ _`
    (qspecl_then [`D`, `explicit`] mp_tac) >>
  qpat_x_assum `!D explicit. gas_origin_ptr_path _ (s,_,_) _ _`
    (qspecl_then [`D`, `explicit`] mp_tac) >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[gas_origin_ptr_path_append, APPEND]
QED

(* The final store does not execute on rejection, but its compiler extension
   is needed to locate the preceding cuts in the enclosing function. *)
Theorem malformed_scalar_allocated_abort[local]:
  abi_decoder_coherent ce env sf ty tv /\ abi_decode_bytes_widths env ty /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  compile_abi_decode_to_buf (Var output) pos MLOAD (Var source) hi
    (type_to_abi_dec_info sf ce ty) st = ((),en) /\
  fn_has_code st en func /\
  (?av. has_type (vyper_to_abi_type env ty) av) /\ assignable_type env ty /\
  abi_malformed_entry H0 ctx func cenv cx es st
    (abi_malformed_scratch_sites st en func) dstid live
    (Var source) hi pos (Var output) B L xs p d (type_memory_bytes ce ty) s /\
  p+32 <= L /\ fresh_vars_wrt ceiling s /\ en.cs_next_var <= ceiling.cs_next_var /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  bytes = (if is_dynamic (vyper_to_abi_type env ty) then DROP p xs
    else TAKE (static_length (vyper_to_abi_type env ty)) (DROP p xs)) /\
  ~(vyper_decode_valid_enc (vyper_to_abi_type env ty) bytes /\
    abi_vyper_admissible env ty (dec (vyper_to_abi_type env ty) bytes)) /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  op_prov G pos = NONE /\ op_taint tn pos = {} /\ allocas_from lo s ==>
  ?u G' tn'.
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (Abort Revert_abort u,G',tn'))
Proof
  strip_tac >>
  `?addr sa value sb sc.
     emit_op ADD [Var source;pos] st = (Var addr,sa) /\
     emit_op MLOAD [Var addr] sa = (value,sb) /\
     compile_abi_clamp_basetype value clamp sb = ((),sc) /\
     fn_has_code st sa func /\ fn_has_code sa sb func /\ fn_has_code sb sc func` by
    (qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
     simp[abiEncoderTheory.compile_abi_decode_to_buf_def,
          abiEncoderTheory.compile_abi_dec_addr_def,
          abiEncoderTheory.compile_abi_decode_static_def,
          compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def, LET_THM] >>
     rpt (pairarg_tac >> simp[]) >> strip_tac >>
     drule (Q.SPEC `ADD` loweringShapeRulesTheory.emit_op_facts) >>
     disch_then (qx_choose_then `addr` strip_assume_tac) >>
     qpat_x_assum `src_addr = Var addr` SUBST_ALL_TAC >>
     rename1 `emit_op ADD _ st = (Var addr,sa)` >>
     rename1 `emit_op MLOAD _ sa = (value,sb)` >>
     rename1 `compile_abi_clamp_basetype value clamp sb = (unit_result,sc)` >>
     Cases_on `unit_result` >>
     `cs_extends st sa` by simp[compileEnvTheory.cs_extends_same_block, rich_listTheory.IS_PREFIX_APPEND] >>
     `cs_extends sa sb` by metis_tac[exprSimAccountsTheory.emit_op_extends_next_var] >>
     `cs_extends sb sc` by
       (drule entryDecodePropsTheory.compile_abi_clamp_structure >>
        simp[inst_extends_def, compileEnvTheory.cs_extends_same_block, rich_listTheory.IS_PREFIX_APPEND]) >>
     `cs_extends sc en` by
       (drule emit_void_extends >>
        simp[same_blocks_def, compileEnvTheory.cs_extends_same_block, rich_listTheory.IS_PREFIX_APPEND]) >>
     `cs_extends sb en /\ cs_extends sa en` by
       metis_tac[compileEnvTheory.cs_extends_trans] >>
     qexistsl_tac [`addr`, `value`, `sb`, `sc`] >>
     simp[] >> metis_tac[fragExecTheory.fn_has_code_split]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (drule abiMalformedEntryPropsTheory.abi_malformed_entry_allocas_below_fmp >>
     disch_then ACCEPT_TAC) >>
  fs[abi_malformed_entry_def] >>
  drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  `B+L < dimword(:256) /\ B+p+32 <= s.vs_alloca_next` by
    (fs[abi_malformed_allocated_window_def] >>
     drule_all allocaSiteResourceTheory.alloca_site_registered_below >> decide_tac) >>
  `~abi_decoder_clamp_valid clamp (abi_decode_load MLOAD (n2w (B+p):bytes32) s)` by
    (irule malformed_scalar_rejects_clamp >>
     metis_tac[]) >>
  drule_all abiDecoderScalarOutcomeTheory.abi_decoder_primitive_clamp_wf >> strip_tac >>
  irule malformed_scalar_prefix_abort >> metis_tac[]
QED

(* Every guard's temporaries are fresh relative to the selected live variables. *)
Theorem malformed_add_range_scalar_code[local]:
  emit_op ADD [src;delta] st = (e,sa) /\
  compile_abi_decode_range_check src e hi sa = ((),en) /\
  src IN A /\ delta IN A /\ hi IN A /\
  (!x. x IN R ==> not_fresh_at st x) ==>
  ?B. bop_scalar_seq R A (emitted_insts st en) B /\ e IN B
Proof
  strip_tac >>
  `!x. x IN R ==> not_fresh_at sa x` by
    (drule placeMemoryCodeLayoutTheory.emit_op_next_var >>
     metis_tac[freshWritesTheory.not_fresh_at_mono, arithmeticTheory.LESS_EQ_ADD]) >>
  `bop_scalar_seq R A (emitted_insts st sa) (e INSERT A)` by
    (drule bop_scalar_seq_emit_op >> simp[] >> disch_then irule >> simp[]) >>
  `?B. bop_scalar_seq R (e INSERT A) (emitted_insts sa en) B` by
    (drule abiDecodePtrPrimsTheory.abi_decode_range_scalar >> disch_then irule >> simp[]) >>
  `emitted_insts st en = emitted_insts st sa ++ emitted_insts sa en` by
    metis_tac[inst_extends_emit_op, inst_extends_def, emitted_insts_append,
              compile_abi_decode_range_check_shape] >>
  qexists `B` >> simp[] >> conj_tac
  >- (irule bop_scalar_seq_append >> metis_tac[]) >>
  drule bop_scalar_seq_available >> simp[pred_setTheory.SUBSET_DEF]
QED

Theorem malformed_head_scalar_code[local]:
  abi_decode_bytes_head pos hi st = (head,en) /\ hi <> Lit 0w /\
  (!x. x IN R ==> not_fresh_at st x) ==>
  ?B. bop_scalar_seq R {pos;Lit 32w;hi} (emitted_insts st en) B /\ head IN B
Proof
  strip_tac >> qpat_x_assum `abi_decode_bytes_head _ _ _ = _` mp_tac >>
  simp[abiDecoderBytesBoundTheory.abi_decode_bytes_head_def,
       compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  irule malformed_add_range_scalar_code >> simp[] >> metis_tac[]
QED

Theorem malformed_payload_scalar_code[local]:
  abi_decode_bytes_payload_guard head cnt hi st = ((),en) /\ hi <> Lit 0w /\
  (!x. x IN R ==> not_fresh_at st x) ==>
  ?B. bop_scalar_seq R {head;cnt;hi} (emitted_insts st en) B
Proof
  strip_tac >> qpat_x_assum `abi_decode_bytes_payload_guard _ _ _ _ = _` mp_tac >>
  simp[abiDecoderBytesBoundTheory.abi_decode_bytes_payload_guard_def,
       compileEnvTheory.comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule malformed_add_range_scalar_code >> disch_then drule >>
  disch_then (qspecl_then [`R`, `{head;cnt;hi}`] mp_tac) >> simp[] >> metis_tac[]
QED

(* Reflection already decides rejection before the decoder starts copying. *)
Theorem malformed_bytes_loaded_bounds[local]:
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecBytestring n /\
  abi_malformed_allocated_window live B L xs s /\
  cv = abi_decode_load MLOAD (n2w (B+p):bytes32) s /\
  bytes = (if is_dynamic (vyper_to_abi_type env ty) then DROP p xs
    else TAKE (static_length (vyper_to_abi_type env ty)) (DROP p xs)) /\
  ~(vyper_decode_valid_enc (vyper_to_abi_type env ty) bytes /\
    abi_vyper_admissible env ty (dec (vyper_to_abi_type env ty) bytes)) ==>
  w2n cv <= n ==> L < p+32+w2n cv
Proof
  disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >> disch_tac >> spose_not_then assume_tac >>
  `is_dynamic (vyper_to_abi_type env ty)` by
    (drule_all abiDecoderBytestringCasesTheory.abi_decoder_bytestring_cases >>
     strip_tac >> gvs[vyperABITheory.vyper_to_abi_type_def, contractABITheory.is_dynamic_def]) >>
  `mem_bytes_at (B+p) (L-p) (abi_decode_source MLOAD s) = DROP p xs` by
    (simp[abi_decode_source_def] >>
     irule abiMalformedBulkConstructorTheory.abi_malformed_source_suffix >>
     fs[abi_malformed_allocated_window_def]) >>
  `B+L < dimword(:256)` by fs[abi_malformed_allocated_window_def] >>
  `B+p < dimword(:256) /\ 32 + w2n cv <= L-p` by decide_tac >>
  qpat_x_assum `~(vyper_decode_valid_enc _ _ /\ _)` mp_tac >> rewrite_tac[NOT_IMP] >>
  simp[] >> irule abi_decoder_bytestring_memory_reflect >>
  qexistsl_tac [`w2n cv`,`ce`,`n`,`L-p`,`MLOAD`,`s`,`B+p`,`sf`,`tv`] >>
  simp[w2n_lt, n2w_w2n]
QED

Theorem malformed_bytes_prefix_fn_code[local]:
  compile_abi_decode_to_buf dst pos MLOAD (Var source) hi (DecBytestring n) st = ((),en) /\
  fn_has_code st en func ==>
  ?addr cnt mid.
    abi_decode_bytes_position_prefix pos MLOAD (Var source) hi n st = ((addr,cnt),mid) /\
    fn_has_code st mid func /\
    inst_extends st mid /\ mid.cs_current_bb = st.cs_current_bb /\
    EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode /\ ~is_terminator i.inst_opcode)
      (emitted_insts st mid)
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  `?addr cnt mid.
     abi_decode_bytes_position_prefix pos MLOAD (Var source) hi n st = ((addr,cnt),mid) /\
     abi_decode_bytes_runtime_tail dst addr cnt mid = ((),en)` by
    (Cases_on `abi_decode_bytes_position_prefix pos MLOAD (Var source) hi n st` >>
     PairCases_on `q` >>
     qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
     simp[abiDecoderBytesPrefixTheory.abi_decode_bytes_prefix_phases,
          compileEnvTheory.comp_bind_def] >>
     strip_tac >> metis_tac[]) >>
  drule_all abiDecoderBytesPrefixTheory.abi_decode_bytes_position_prefix_shape >> strip_tac >>
  drule abiDecoderBytesPhasesTheory.abi_decode_bytes_runtime_tail_shape >> strip_tac >>
  `cs_extends st mid /\ cs_extends mid en` by
    fs[inst_extends_def, compileEnvTheory.cs_extends_same_block] >>
  `fn_has_code st mid func` by metis_tac[fragExecTheory.fn_has_code_split] >>
  qexistsl_tac [`addr`, `cnt`, `mid`] >> simp[] >>
  drule_all abiDecoderBytesFrameTheory.abi_decoder_bytes_reentry_code >> strip_tac >>
  `emitted_insts st en = emitted_insts st mid ++ emitted_insts mid en` by
    metis_tac[emitted_insts_append, inst_extends_def] >>
  fs[EVERY_MEM] >> metis_tac[]
QED

(* Scalar guards can only revert at their first assertion that fails. *)
Theorem malformed_guard_abort_world[local]:
  bop_scalar_seq R A code B /\ run_inst_seq code s = Abort Revert_abort t ==>
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_immutables = s.vs_immutables
Proof
  strip_tac >> drule_all bop_scalar_seq_abort_prefix >> strip_tac >>
  drule_all bodyPtrBopScalarOutcomeTheory.bop_scalar_seq_runtime_frame >> strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  gvs[step_inst_base_opcode_eqs, mk_inst_def, AllCaseEqs(),
      revert_state_def, set_returndata_def] >> strip_tac >> gvs[] >>
  qpat_x_assum `u = s with vs_vars := _` SUBST1_TAC >> simp[]
QED

Theorem malformed_guard_abort_joint[local]:
  bop_scalar_seq R A code B /\
  (!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq code s = Abort Revert_abort t ==>
  ?u G' tn'.
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (Abort Revert_abort u,G',tn'))
Proof
  strip_tac >> drule_all malformed_guard_abort_world >> strip_tac >>
  drule_all bop_scalar_seq_abort_prefix >> strip_tac >>
  qabbrev_tac `cut = prefix ++ [mk_inst id opc [op] []]` >>
  `isPREFIX cut (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[Abbr `cut`, rich_listTheory.IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]) >>
  `run_inst_seq cut s = Abort Revert_abort t` by
    (unabbrev_all_tac >>
     qpat_assum `run_inst_seq prefix s = OK u`
       (fn th => rewrite_tac[MATCH_MP run_inst_seq_append th]) >>
     pure_once_rewrite_tac[run_inst_seq_def] >>
     qpat_assum `step_inst_base _ u = Abort Revert_abort t` (fn th => simp[th])) >>
  `bop_scalar_seq R A cut C` by
    (simp[Abbr `cut`] >> irule bop_scalar_seq_append >>
     goal_assum (drule_at Any) >> irule bop_scalar_seq_assert >> simp[]) >>
  qpat_assum `bop_scalar_seq _ _ cut _`
    (mp_then Any (qspec_then `s` strip_assume_tac) abiDecodeScalarRunSafetyTheory.abi_decode_scalar_run_safe) >>
  `(ctx_has_dalloca ctx ==> !pre i post u'.
      cut = pre ++ i::post /\ run_inst_seq pre s = OK u' ==>
      unitTransformDefs$dalloca_no_wrap i u')` by
    (rpt strip_tac >> `MEM i cut` by simp[] >>
     drule_all bodyPtrBopScalarOutcomeTheory.bop_scalar_seq_outputs >>
     disch_then (mp_tac o CONJUNCT1) >> simp[] >> strip_tac >> simp[]) >>
  `?j. !D lower explicit PG G tn H th.
     inst_seq_ptr D lower ctx func PG G tn cut s H th ==>
     gas_origin_ptr_path (D,lower,explicit,ctx,func,PG)
       (s,G,tn) [] (Abort Revert_abort (t with vs_inst_idx := j),H,th)` by
    (irule run_inst_seq_abort_origin_ptr_uniform >> fs[EVERY_MEM] >> metis_tac[]) >>
  `!D. ?H th. inst_seq_ptr D 0 ctx func PG G tn cut s H th` by
    (gen_tac >> qunabbrev_tac `cut` >>
     drule_at (Pat `run_inst_seq _ _ = OK _`) bop_scalar_seq_assert_abort_checked >>
     strip_tac >> metis_tac[]) >>
  qpat_assum `!D. ?H th. inst_seq_ptr D 0 _ _ _ _ _ _ _ H th`
    (qspec_then `ARB:dead` (qx_choose_then `G'` (qx_choose_then `tn'` assume_tac))) >>
  qexistsl_tac [`t with vs_inst_idx := j`, `G'`, `tn'`] >> simp[] >>
  rpt gen_tac >> first_x_assum irule >>
  first_x_assum (qspec_then `D` strip_assume_tac) >>
  `H = G' /\ th = tn'` by metis_tac[inst_seq_ptr_ghost_unique] >> gvs[] >>
  irule (Q.INST [`lo0` |-> `0`] inst_seq_ptr_lower_bound_transport) >>
  fs[EVERY_MEM]
QED

(* A successful scalar guard keeps the frame and advances the actual cursor. *)
Theorem malformed_guard_success_cut[local]:
  bop_scalar_seq R A (emitted_insts sa sb) B /\
  (!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ ~s.vs_halted /\
  fn_has_code sa sb func /\ inst_extends sa sb /\ sb.cs_current_bb = sa.cs_current_bb /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK raw ==>
  ?G' tn'.
    raw = s with vs_vars := raw.vs_vars /\
    (!x. x IN R ==> lookup_var x raw = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!op. op IN B ==> op_prov G' op = NONE /\ op_taint tn' op = {}) /\
    tn'.t_mem = tn.t_mem /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK (raw with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn'))
Proof
  strip_tac >>
  drule_all bodyPtrBopScalarOutcomeTheory.bop_scalar_seq_runtime_frame >> strip_tac >>
  drule_all bop_scalar_seq_run >>
  disch_then (qspecl_then [`func`, `PG`, `ARB:dead`] strip_assume_tac) >>
  drule abiDecodeScalarRunSafetyTheory.abi_decode_scalar_run_safe >> disch_then (qspec_then `s` strip_assume_tac) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `inst_extends sa sb` (assume_tac o REWRITE_RULE[inst_extends_def]) >>
     drule_all fn_has_code_code >> simp[] >> metis_tac[]) >>
  `LENGTH sb.cs_current_insts = s.vs_inst_idx + LENGTH (emitted_insts sa sb)` by
    fs[inst_extends_def] >>
  qexistsl_tac [`G'`, `tn'`] >> simp[] >> conj_tac
  >- (rpt strip_tac >> fs[lookup_var_def, op_taint_def]) >>
  rpt gen_tac >>
  `inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s G' tn'` by
    (drule_all bop_scalar_seq_run >>
     disch_then (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
     metis_tac[inst_seq_ptr_ghost_unique]) >>
  `(ctx_has_dalloca ctx ==> !pre i post u.
      emitted_insts sa sb = pre ++ i::post /\ run_inst_seq pre s = OK u ==>
      unitTransformDefs$dalloca_no_wrap i u)` by
    (rpt strip_tac >> `MEM i (emitted_insts sa sb)` by simp[] >>
     drule_all bodyPtrBopScalarOutcomeTheory.bop_scalar_seq_outputs >>
     disch_then (mp_tac o CONJUNCT1) >> simp[] >> strip_tac >> simp[]) >>
  drule_all run_inst_seq_origin_ptr_lift >> simp[]
QED

(* The bounded aggregate guard is an ADD followed by a scalar range check. *)
Theorem malformed_complex_head_guard_cut:
  abi_decode_complex_head_guard pos hi k st = ((),sh) /\ hi <> Lit 0w /\
  eval_operand pos s = SOME (n2w p) /\ eval_operand hi s = SOME (n2w L) /\
  p < dimword(:256) /\ k < dimword(:256) /\ L < dimword(:256) /\
  abi_decoder_operand_live st.cs_next_var pos /\ abi_decoder_operand_live st.cs_next_var hi /\
  op_prov G pos = NONE /\ op_taint tn pos = {} /\
  op_prov G hi = NONE /\ op_taint tn hi = {} /\
  sh.cs_next_var <= ceiling.cs_next_var /\ fresh_vars_wrt ceiling s /\
  fn_has_code st sh func /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  if p+k <= L then
    ?u H z.
      u = s with <|vs_vars := u.vs_vars; vs_inst_idx := LENGTH sh.cs_current_insts|> /\
      fresh_vars_wrt ceiling u /\
      (!x. not_fresh_at st x ==> lookup_var x u = lookup_var x s /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint z (Var x) = op_taint tn (Var x)) /\
      z.t_mem = tn.t_mem /\
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK u,H,z))
  else
    ?u H z.
      u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
      u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (Abort Revert_abort u,H,z))
Proof
  strip_tac >> drule abi_decode_complex_head_guard_prefix_shape >> strip_tac >>
  `?B. bop_scalar_seq {x | not_fresh_at st x} {pos; Lit (n2w k); hi}
      (emitted_insts st sh) B` by
    (Cases_on `emit_op ADD [pos; Lit (n2w k)] st` >>
     gvs[abi_decode_complex_head_guard_def, compileEnvTheory.comp_bind_def] >>
     drule malformed_add_range_scalar_code >> disch_then drule >>
     disch_then (qspecl_then [`{x | not_fresh_at st x}`, `{pos;Lit (n2w k);hi}`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  `!op. op IN {pos;Lit (n2w k);hi} ==> op_prov G op = NONE /\ op_taint tn op = {}` by
    (simp[] >> rpt strip_tac >> gvs[op_prov_def, op_taint_def]) >>
  Cases_on `p + k <= L` >> simp[]
  >- (drule abi_decoder_complex_guard_reentry >>
      disch_then (qspecl_then [`p`,`ceiling`,`s`] mp_tac) >>
      (impl_tac >- (simp[] >> qexists `L` >> simp[])) >>
      strip_tac >>
      drule_all malformed_guard_success_cut >>
      disch_then (qspec_then `PG` strip_assume_tac) >>
      qexistsl_tac [`actual with vs_inst_idx := LENGTH sh.cs_current_insts`, `G'`, `tn'`] >>
      simp[lookup_var_def, fresh_vars_wrt_def] >>
      qpat_assum `actual = s with vs_vars := _` (fn th => simp[Once th]) >>
      fs[lookup_var_def, fresh_vars_wrt_def]) >>
  `L < p+k` by decide_tac >>
  drule_all abi_decode_complex_head_guard_revert_reentry >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts st sh) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `inst_extends st sh` (assume_tac o REWRITE_RULE[inst_extends_def]) >>
     drule_all fn_has_code_code >> simp[] >> metis_tac[]) >>
  irule malformed_guard_abort_joint >> goal_assum (drule_at Any) >> metis_tac[]
QED

(* Split the first bounds guard before loading the count from the source. *)
Theorem malformed_bytes_head_cut[local]:
  abi_decode_bytes_head pos hi st = (head,sh) /\ hi <> Lit 0w /\
  fn_has_code st sh func /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st sh) /\
  eval_operand pos s = SOME (n2w p) /\ eval_operand hi s = SOME (n2w L) /\
  abi_decoder_operand_live st.cs_next_var pos /\ abi_decoder_operand_live st.cs_next_var hi /\
  p < dimword(:256) /\ L < dimword(:256) /\
  op_prov G pos = NONE /\ op_taint tn pos = {} /\
  op_prov G hi = NONE /\ op_taint tn hi = {} /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (?u G' tn'.
     u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
     u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
     (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (Abort Revert_abort u,G',tn'))) \/
  (p+32 <= L /\ ?u G' tn'.
     u = s with <| vs_vars := u.vs_vars; vs_inst_idx := LENGTH sh.cs_current_insts |> /\
     (!x. not_fresh_at st x ==> lookup_var x u = lookup_var x s /\
        FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
     (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
        eval_operand op u = SOME w /\ op_prov G' op = op_prov G op /\ op_taint tn' op = op_taint tn op) /\
     eval_operand head u = SOME (n2w (p+32)) /\
     abi_decoder_operand_live sh.cs_next_var head /\
     op_prov G' head = NONE /\ op_taint tn' head = {} /\ tn'.t_mem = tn.t_mem /\
     (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK u,G',tn')))
Proof
  strip_tac >>
  drule abiDecoderBytesBoundTheory.abi_decode_bytes_head_fragment_shape >> strip_tac >>
  drule malformed_head_scalar_code >>
  disch_then (qspec_then `{x | not_fresh_at st x}` mp_tac) >> simp[] >> strip_tac >>
  `!op. op IN {pos; Lit 32w; hi} ==> op_prov G op = NONE /\ op_taint tn op = {}` by
    (simp[] >> rpt strip_tac >> gvs[op_prov_def, op_taint_def]) >>
  qabbrev_tac `clean = abi_decoder_prune_vars st.cs_next_var s` >>
  `eval_operand pos clean = SOME (n2w p) /\ eval_operand hi clean = SOME (n2w L) /\
   fresh_vars_wrt st clean` by simp[Abbr `clean`, abi_decoder_prune_eval, abi_decoder_prune_fresh] >>
  drule_all abi_decode_bytes_head_total >>
  simp[w2n_n2w, LESS_MOD] >> strip_tac
  >- (disj1_tac >>
      `?t. run_inst_seq (emitted_insts st sh) s = Abort Revert_abort t` by
        (qunabbrev_tac `clean` >> metis_tac[abi_decoder_sequence_revert_reentry]) >>
      `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts st sh) (DROP s.vs_inst_idx bb.bb_instructions)` by
        (qpat_assum `inst_extends st sh` (assume_tac o REWRITE_RULE[inst_extends_def]) >>
         drule_all fn_has_code_code >> simp[] >> metis_tac[]) >>
      irule malformed_guard_abort_joint >> simp[] >> metis_tac[]) >>
  disj2_tac >> simp[] >>
  `abi_decoder_operand_live sh.cs_next_var head` by
    metis_tac[abi_decoder_operand_live_fresh] >>
  `abi_decoder_vars_extend s.vs_vars clean s` by simp[Abbr `clean`, abi_decoder_prune_extension] >>
  drule_all abi_decoder_sequence_vars_extend >> strip_tac >>
  drule_all malformed_guard_success_cut >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `eval_operand head v = SOME (n2w (p+32))` by metis_tac[abiDecoderVarExtendTheory.abi_decoder_vars_extend_eval] >>
  qexistsl_tac [`v with vs_inst_idx := LENGTH sh.cs_current_insts`, `G'`, `tn'`] >>
  simp[] >> rpt conj_tac
  >- (qpat_x_assum `v = s with vs_vars := _` SUBST1_TAC >> simp[])
  >- (rpt strip_tac >> fs[lookup_var_def])
  >- (rpt gen_tac >> Cases_on `op` >>
      simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
           GSYM not_fresh_at_def, eval_operand_def, lookup_var_def, op_prov_def, op_taint_def] >>
      TRY (qpat_assum `v = s with vs_vars := _` (fn th => simp[Once th])) >>
      rpt strip_tac >>
      qpat_assum `!x. x IN {x | _} ==> _` drule >> simp[lookup_var_def, op_taint_def]) >>
  (Cases_on `head` >> fs[eval_operand_def, lookup_var_def])
QED

(* The count load is followed by an ordinary scalar <= guard. *)
Theorem malformed_count_guard_split[local]:
  abi_decode_count_guard MLOAD (Var addr) n sa = (cnt,sc) ==>
  ?sb. emit_op MLOAD [Var addr] sa = (cnt,sb) /\
       abi_decode_le_guard cnt (Lit (n2w n)) sb = ((),sc) /\
       cs_extends sa sb /\ cs_extends sb sc /\
       sc.cs_current_bb = sb.cs_current_bb /\ sb.cs_next_var <= sc.cs_next_var /\
       EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts sb sc) /\
       (!R. (!x. x IN R ==> not_fresh_at sb x) ==>
         ?A. bop_scalar_seq R {cnt; Lit (n2w n)} (emitted_insts sb sc) A)
Proof
  simp[abiDecoderGuardsTheory.abi_decode_count_guard_def, compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  conj_tac
  >- simp[abiDecoderGuardTheory.abi_decode_le_guard_def, compileEnvTheory.comp_bind_def] >>
  conj_tac >- metis_tac[exprSimAccountsTheory.emit_op_extends_next_var] >>
  gvs[emit_op_def, emit_void_def, compileEnvTheory.fresh_var_def,
      compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def,
      compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
      compileEnvTheory.comp_return_def,
      compileEnvTheory.cs_extends_same_block, rich_listTheory.IS_PREFIX_APPEND,
      emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[listTheory.DROP_APPEND2, abi_decoder_reentry_opcode_def,
       bop_scalar_seq_def, mk_inst_def] >>
  fs[not_fresh_at_def] >> rpt strip_tac >> first_x_assum drule >> simp[]
QED

(* Run the count comparison at the actual load endpoint.  Pruning is used
   only to select the outcome; the witnesses are on the unpruned run. *)
Theorem malformed_count_compare_cut[local]:
  abi_decode_le_guard cnt (Lit (n2w n)) sa = ((),sb) /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts sa sb) /\
  bop_scalar_seq {x | not_fresh_at sa x} {cnt;Lit (n2w n)} (emitted_insts sa sb) A /\
  fn_has_code sa sb func /\ sb.cs_current_bb = sa.cs_current_bb /\
  eval_operand cnt s = SOME cv /\ abi_decoder_operand_live sa.cs_next_var cnt /\
  n < dimword(:256) /\ op_prov G cnt = NONE /\ op_taint tn cnt = {} /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  if w2n cv <= n then
    ?u G' tn'.
      u = s with <|vs_vars := u.vs_vars; vs_inst_idx := LENGTH sb.cs_current_insts|> /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
        FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
      tn'.t_mem = tn.t_mem /\
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK u,G',tn'))
  else
    ?u G' tn'.
      u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
      u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (Abort Revert_abort u,G',tn'))
Proof
  strip_tac >> drule abiDecoderGuardTheory.abi_decode_le_guard_shape >> strip_tac >>
  `!op. op IN {cnt;Lit (n2w n)} ==> op_prov G op = NONE /\ op_taint tn op = {}` by
    (simp[] >> rpt strip_tac >> gvs[op_prov_def, op_taint_def]) >>
  qabbrev_tac `clean = abi_decoder_prune_vars sa.cs_next_var s` >>
  `eval_operand cnt clean = SOME cv /\ eval_operand (Lit (n2w n)) clean = SOME (n2w n) /\
   fresh_vars_wrt sa clean` by
    simp[Abbr `clean`, abi_decoder_prune_eval, abi_decoder_prune_fresh, eval_operand_def] >>
  `w2n (n2w n:bytes32) = n` by simp[w2n_n2w, LESS_MOD] >>
  Cases_on `w2n cv <= n` >> simp[]
  >- (`?raw. run_inst_seq (emitted_insts sa sb) clean = OK raw` by
        metis_tac[abiDecoderGuardTheory.abi_decode_le_guard_sequence] >>
      `abi_decoder_vars_extend s.vs_vars clean s` by simp[Abbr `clean`, abi_decoder_prune_extension] >>
      drule_all abi_decoder_sequence_vars_extend >> strip_tac >>
      drule_all malformed_guard_success_cut >>
      disch_then (qspec_then `PG` strip_assume_tac) >>
      qexistsl_tac [`v with vs_inst_idx := LENGTH sb.cs_current_insts`, `G'`, `tn'`] >>
      simp[] >> conj_tac
      >- (qpat_x_assum `v = s with vs_vars := _` SUBST1_TAC >> simp[]) >>
      rpt strip_tac >> fs[lookup_var_def]) >>
  `?t. run_inst_seq (emitted_insts sa sb) clean = Abort Revert_abort t` by
    (drule abi_decode_le_guard_reverts >>
     disch_then (qspecl_then [`n2w n`,`cv`,`clean`] mp_tac) >> simp[]) >>
  `?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t` by
    (qunabbrev_tac `clean` >> metis_tac[abi_decoder_sequence_revert_reentry]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `inst_extends sa sb` (assume_tac o REWRITE_RULE[inst_extends_def]) >>
     drule_all fn_has_code_code >> simp[] >> metis_tac[]) >>
  irule malformed_guard_abort_joint >> simp[] >> metis_tac[]
QED

Theorem malformed_bytes_payload_abort[local]:
  abi_decode_bytes_payload_guard head cnt hi sa = ((),sb) /\ hi <> Lit 0w /\
  fn_has_code sa sb func /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts sa sb) /\
  eval_operand head s = SOME (n2w q) /\ eval_operand cnt s = SOME (n2w c) /\
  eval_operand hi s = SOME (n2w L) /\ q < dimword(:256) /\ c < dimword(:256) /\
  L < dimword(:256) /\ L < q+c /\
  EVERY (abi_decoder_operand_live sa.cs_next_var) [head;cnt;hi] /\
  (!op. op IN {head;cnt;hi} ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u G' tn'.
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (Abort Revert_abort u,G',tn'))
Proof
  strip_tac >> drule abiDecoderBytesBoundTheory.abi_decode_bytes_payload_guard_fragment_shape >> strip_tac >>
  drule malformed_payload_scalar_code >> simp[] >>
  disch_then (qspec_then `{x | not_fresh_at sa x}` mp_tac) >> simp[] >> strip_tac >>
  fs[EVERY_DEF] >>
  qabbrev_tac `clean = abi_decoder_prune_vars sa.cs_next_var s` >>
  `eval_operand head clean = SOME (n2w q) /\ eval_operand cnt clean = SOME (n2w c) /\
   eval_operand hi clean = SOME (n2w L) /\ fresh_vars_wrt sa clean` by
    simp[Abbr `clean`, abi_decoder_prune_eval, abi_decoder_prune_fresh] >>
  `?t. run_inst_seq (emitted_insts sa sb) clean = Abort Revert_abort t` by
    (irule abiDecoderBytestringOutcomeTheory.abi_decode_bytes_payload_guard_revert >>
     simp[] >> qexistsl_tac [`c`, `L`, `q`, `head`, `hi`, `cnt`] >> simp[]) >>
  `?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t` by
    (qunabbrev_tac `clean` >> metis_tac[abi_decoder_sequence_revert_reentry]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `inst_extends sa sb` (assume_tac o REWRITE_RULE[inst_extends_def]) >>
     drule_all fn_has_code_code >> simp[] >> metis_tac[]) >>
  irule malformed_guard_abort_joint >> simp[] >>
  qexistsl_tac [`{head;cnt;hi}`,`B`,`{x | not_fresh_at sa x}`,`emitted_insts sa sb`,`t'`] >>
  conj_tac
  >- (qpat_assum `!op. _ ==> op_prov G op = NONE /\ _` mp_tac >> simp[]) >>
  qpat_assum `s.vs_inst_idx = _` (once_rewrite_tac o single o SYM) >> simp[]
QED

(* The position and count are already loaded.  A failed count check takes
   precedence over a failed payload check. *)
Theorem malformed_bytes_compare_abort[local]:
  abi_decode_le_guard cnt (Lit (n2w n)) sa = ((),sb) /\
  abi_decode_bytes_payload_guard head cnt hi sb = ((),sc) /\ hi <> Lit 0w /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts sa sb) /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts sb sc) /\
  bop_scalar_seq {x | not_fresh_at sa x} {cnt;Lit (n2w n)} (emitted_insts sa sb) A /\
  fn_has_code sa sb func /\ fn_has_code sb sc func /\
  sb.cs_current_bb = sa.cs_current_bb /\ sa.cs_next_var <= sb.cs_next_var /\
  eval_operand head s = SOME (n2w q) /\ eval_operand cnt s = SOME cv /\
  eval_operand hi s = SOME (n2w L) /\ q < dimword(:256) /\ L < dimword(:256) /\
  n < dimword(:256) /\ (w2n cv <= n ==> L < q + w2n cv) /\
  EVERY (abi_decoder_operand_live sa.cs_next_var) [head;cnt;hi] /\
  (!op. op IN {head;cnt;hi} ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u G' tn'.
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (Abort Revert_abort u,G',tn'))
Proof
  strip_tac >> fs[EVERY_DEF] >>
  `op_prov G cnt = NONE /\ op_taint tn cnt = {}` by metis_tac[] >>
  drule_all malformed_count_compare_cut >> disch_then (qspec_then `PG` mp_tac) >>
  Cases_on `w2n cv <= n` >> simp[] >> strip_tac >>
  rename1 `r = s with <|vs_vars := r.vs_vars; vs_inst_idx := _|>` >>
  `r.vs_labels = s.vs_labels` by
    (qpat_assum `r = s with <|vs_vars := _; vs_inst_idx := _|>` (fn th => ONCE_REWRITE_TAC[th]) >> simp[]) >>
  `!op. abi_decoder_operand_live sa.cs_next_var op ==>
    eval_operand op r = eval_operand op s /\
    op_prov G' op = op_prov G op /\ op_taint tn' op = op_taint tn op` by
    (rpt strip_tac >> drule_all abiDecodeRejectIndexedPassTheory.indexed_pass_operand_frame >> simp[]) >>
  `EVERY (abi_decoder_operand_live sb.cs_next_var) [head;cnt;hi]` by
    (simp[EVERY_DEF] >> metis_tac[abi_decoder_operand_live_mono]) >>
  `!op. op IN {head;cnt;hi} ==> op_prov G' op = NONE /\ op_taint tn' op = {}` by
    (simp[] >> rpt strip_tac >> gvs[]) >>
  `eval_operand head r = SOME (n2w q) /\ eval_operand cnt r = SOME (n2w (w2n cv)) /\
   eval_operand hi r = SOME (n2w L)` by metis_tac[n2w_w2n] >>
  `L < q + w2n cv /\ w2n cv < dimword(:256)` by (simp[w2n_lt] >> decide_tac) >>
  `~r.vs_halted /\ r.vs_allocas = s.vs_allocas /\ r.vs_current_bb = sb.cs_current_bb /\
    r.vs_inst_idx = LENGTH sb.cs_current_insts /\
    r.vs_accounts = s.vs_accounts /\ r.vs_transient = s.vs_transient /\
    r.vs_call_ctx = s.vs_call_ctx /\ r.vs_immutables = s.vs_immutables` by
    (qpat_assum `r = s with <|vs_vars := _; vs_inst_idx := _|>` (fn th => ONCE_REWRITE_TAC[th]) >>
     simp[]) >>
  `allocas_from lo r` by
    (qpat_assum `r.vs_allocas = s.vs_allocas`
       (fn th => PURE_REWRITE_TAC[allocas_from_def,th]) >>
     qpat_assum `allocas_from lo s` (ACCEPT_TAC o PURE_REWRITE_RULE[allocas_from_def])) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp r` by
    (qpat_assum `r = s with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => once_rewrite_tac[th]) >>
     rewrite_tac[allocas_below_fmp_updates] >> first_assum ACCEPT_TAC) >>
  drule_all malformed_bytes_payload_abort >>
  disch_then (qspec_then `PG` (qx_choose_then `u` (qx_choose_then `H` (qx_choose_then `th` strip_assume_tac)))) >>
  qexistsl_tac [`u`,`H`,`th`] >> simp[] >>
  rpt gen_tac >> metis_tac[gas_origin_ptr_path_append, APPEND_NIL]
QED

(* Account for each cut in the real function, including the separate count load. *)
Theorem malformed_bytes_cut_layout[local]:
  abi_decode_bytes_position_prefix pos MLOAD (Var source) hi n st = ((addr,cnt),en) /\
  fn_has_code st en func /\ hi <> Lit 0w /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode /\ ~is_terminator i.inst_opcode)
    (emitted_insts st en) ==>
  ?head sh sa sb sc A ar.
    addr = Var ar /\
    abi_decode_bytes_head pos hi st = (head,sh) /\
    emit_op ADD [Var source;pos] sh = (Var ar,sa) /\
    emit_op MLOAD [Var ar] sa = (cnt,sb) /\
    abi_decode_le_guard cnt (Lit (n2w n)) sb = ((),sc) /\
    abi_decode_bytes_payload_guard head cnt hi sc = ((),en) /\
    fn_has_code st sh func /\ fn_has_code sh sa func /\ fn_has_code sa sb func /\
    fn_has_code sb sc func /\ fn_has_code sc en func /\
    EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st sh) /\
    EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts sb sc) /\
    EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts sc en) /\
    bop_scalar_seq {x | not_fresh_at sb x} {cnt;Lit (n2w n)} (emitted_insts sb sc) A /\
    sh.cs_current_bb = st.cs_current_bb /\ sc.cs_current_bb = sb.cs_current_bb /\
    st.cs_next_var <= sh.cs_next_var /\ sh.cs_next_var <= sb.cs_next_var /\
    sb.cs_next_var <= sc.cs_next_var /\ abi_decoder_operand_live sb.cs_next_var cnt
Proof
  strip_tac >>
  fs[abiDecoderBytesPrefixTheory.abi_decode_bytes_position_prefix_trace,
     abiEncoderTheory.compile_abi_dec_addr_def] >>
  drule (Q.SPEC `ADD` loweringShapeRulesTheory.emit_op_facts) >> strip_tac >> gvs[] >>
  drule malformed_count_guard_split >> strip_tac >>
  drule abiDecoderBytesBoundTheory.abi_decode_bytes_head_fragment_shape >> strip_tac >>
  drule abiDecoderBytesBoundTheory.abi_decode_bytes_payload_guard_fragment_shape >> strip_tac >>
  rename1 `abi_decode_bytes_head pos hi st = (head,sh)` >>
  rename1 `emit_op ADD [Var source;pos] sh = (Var ar,sa)` >>
  rename1 `emit_op MLOAD [Var ar] sa = (cnt,sb)` >>
  rename1 `abi_decode_le_guard cnt _ sb = ((),sc)` >>
  `cs_extends st sh /\ cs_extends sh sa /\ cs_extends sc en /\
    sh.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sb.cs_next_var` by
    (fs[inst_extends_def, compileEnvTheory.cs_extends_same_block,
        rich_listTheory.IS_PREFIX_APPEND] >> metis_tac[exprSimAccountsTheory.emit_op_extends_next_var]) >>
  `st.cs_next_var <= sh.cs_next_var` by
    (qpat_x_assum `abi_decode_bytes_head _ _ _ = _` mp_tac >>
     simp[abiDecoderBytesBoundTheory.abi_decode_bytes_head_def,
          abiEncoderTheory.compile_abi_decode_range_check_def,
          compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
          compileEnvTheory.comp_return_def, emit_op_def, emit_void_def,
          compileEnvTheory.fresh_var_def, compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def] >>
     strip_tac >> gvs[]) >>
  `inst_extends sh sa /\ inst_extends sa sb /\ inst_extends sb sc` by
    metis_tac[inst_extends_emit_op, abiDecoderGuardTheory.abi_decode_le_guard_shape] >>
  `emitted_insts st en = emitted_insts st sh ++ emitted_insts sh sa ++
      emitted_insts sa sb ++ emitted_insts sb sc ++ emitted_insts sc en` by
    (fs[inst_extends_def] >> metis_tac[emitted_insts_append, APPEND_ASSOC]) >>
  `fn_has_code st sh func /\ fn_has_code sh sa func /\ fn_has_code sa sb func /\
    fn_has_code sb sc func /\ fn_has_code sc en func` by
    metis_tac[fragExecTheory.fn_has_code_split, compileEnvTheory.cs_extends_trans] >>
  qexistsl_tac [`sb`,`sc`] >> fs[EVERY_APPEND] >>
  qpat_x_assum `!R. _ ==> ?A. _` (qspec_then `{x | not_fresh_at sb x}` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >> qexists_tac `A` >> simp[] >>
  conj_tac >- (fs[EVERY_MEM] >> metis_tac[]) >>
  conj_tac >- (fs[EVERY_MEM] >> metis_tac[]) >>
  drule abi_decoder_operand_live_emit >> simp[]
QED

(* Count and payload checks run after the head check and bounded count load. *)
Theorem malformed_bytes_allocated_abort[local]:
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecBytestring n /\
  compile_abi_decode_to_buf (Var output) pos MLOAD (Var source) hi
    (type_to_abi_dec_info sf ce ty) st = ((),en) /\
  fn_has_code st en func /\
  abi_malformed_entry H0 ctx func cenv cx es st
    (abi_malformed_scratch_sites st en func) dstid live
    (Var source) hi pos (Var output) B L xs p d (type_memory_bytes ce ty) s /\
  fresh_vars_wrt ceiling s /\ en.cs_next_var <= ceiling.cs_next_var /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  bytes = (if is_dynamic (vyper_to_abi_type env ty) then DROP p xs
    else TAKE (static_length (vyper_to_abi_type env ty)) (DROP p xs)) /\
  ~(vyper_decode_valid_enc (vyper_to_abi_type env ty) bytes /\
    abi_vyper_admissible env ty (dec (vyper_to_abi_type env ty) bytes)) /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  op_prov G pos = NONE /\ op_taint tn pos = {} /\
  op_prov G hi = NONE /\ op_taint tn hi = {} /\ allocas_from lo s ==>
  ?u G' tn'.
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (Abort Revert_abort u,G',tn'))
Proof
  disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  `compile_abi_decode_to_buf (Var output) pos MLOAD (Var source) hi
      (DecBytestring n) st = ((),en)` by metis_tac[] >>
  drule_all malformed_bytes_prefix_fn_code >> strip_tac >>
  `hi <> Lit 0w /\ p < dimword(:256) /\
   d+type_memory_bytes ce ty < dimword(:256) /\
   eval_operand (Var source) s = SOME (n2w B) /\
   eval_operand hi s = SOME (n2w L) /\ eval_operand pos s = SOME (n2w p) /\
   abi_malformed_allocated_window live B L xs s /\
   stmt_state_rel H0 ctx func cenv cx es s` by fs[abi_malformed_entry_def] >>
  drule_all malformed_bytes_cut_layout >> strip_tac >>
  `B+L < dimword(:256) /\ L < dimword(:256)` by
    (fs[abi_malformed_allocated_window_def] >> decide_tac) >>
  `n+32 < dimword(:256)` by
    (`type_memory_bytes ce ty <= type_memory_bytes ce ty` by simp[] >>
     drule_all abiMalformedBulkConstructorTheory.abi_malformed_bytestring_capacity >> simp[]) >>
  `n < dimword(:256)` by decide_tac >>
  `abi_decoder_operand_live st.cs_next_var pos /\ abi_decoder_operand_live st.cs_next_var hi /\
   not_fresh_at st source` by
    fs[abi_malformed_entry_def, abi_decoder_operand_live_def,
       abi_decoder_older_vars_def, not_fresh_at_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (drule abiMalformedEntryPropsTheory.abi_malformed_entry_allocas_below_fmp >>
     disch_then ACCEPT_TAC) >>
  drule_all malformed_bytes_head_cut >> disch_then (qspec_then `PG` strip_assume_tac)
  >- metis_tac[] >>
  rename1 `r = s with <|vs_vars := r.vs_vars; vs_inst_idx := _|>` >>
  `r.vs_labels = s.vs_labels /\ r.vs_memory = s.vs_memory /\
   r.vs_allocas = s.vs_allocas /\ r.vs_alloca_next = s.vs_alloca_next /\
   ~r.vs_halted /\ r.vs_current_bb = sh.cs_current_bb /\
   r.vs_inst_idx = LENGTH sh.cs_current_insts /\
   r.vs_accounts = s.vs_accounts /\ r.vs_transient = s.vs_transient /\
   r.vs_call_ctx = s.vs_call_ctx /\ r.vs_immutables = s.vs_immutables` by
    (qpat_assum `r = s with <|vs_vars := _; vs_inst_idx := _|>` (fn th => ONCE_REWRITE_TAC[th]) >> simp[]) >>
  `abi_decode_ptr_window G' tn' r source (n2w B) L` by
    (irule abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_frame >> metis_tac[]) >>
  `allocas_from lo r` by
    (simp[allocas_from_def] >>
     qpat_assum `allocas_from lo s` (ACCEPT_TAC o REWRITE_RULE[allocas_from_def])) >>
  `B+p+32 <= r.vs_alloca_next` by
    (drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
     fs[abi_malformed_allocated_window_def] >>
     drule_all allocaSiteResourceTheory.alloca_site_registered_below >> decide_tac) >>
  `eval_operand pos r = SOME (n2w p) /\ op_prov G' pos = NONE /\ op_taint tn' pos = {}` by metis_tac[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp r` by
    (qpat_assum `r = s with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => once_rewrite_tac[th]) >>
     rewrite_tac[allocas_below_fmp_updates] >> first_assum ACCEPT_TAC) >>
  drule_all malformed_scalar_load_prefix >> disch_then (qspec_then `PG` strip_assume_tac) >>
  `abi_decoder_operand_live sh.cs_next_var hi` by metis_tac[abi_decoder_operand_live_mono] >>
  `eval_operand hi r = SOME (n2w L) /\ op_prov G' hi = NONE /\ op_taint tn' hi = {}` by metis_tac[] >>
  `!op. abi_decoder_operand_live sh.cs_next_var op ==>
    eval_operand op loaded = eval_operand op r /\
    op_prov HG op = op_prov G' op /\ op_taint th op = op_taint tn' op` by
    (rpt strip_tac >> drule_all abiDecodeRejectIndexedPassTheory.indexed_pass_operand_frame >> simp[]) >>
  `EVERY (abi_decoder_operand_live sb.cs_next_var) [head;cnt;hi]` by
    (simp[] >> metis_tac[abi_decoder_operand_live_mono]) >>
  `!op. op IN {head;cnt;hi} ==> op_prov HG op = NONE /\ op_taint th op = {}` by
    (simp[] >> rpt strip_tac >> gvs[]) >>
  `eval_operand head loaded = SOME (n2w (p+32)) /\ eval_operand hi loaded = SOME (n2w L)` by metis_tac[] >>
  `p+32 < dimword(:256)` by decide_tac >>
  qabbrev_tac `cv = abi_decode_load MLOAD (n2w (B+p):bytes32) r` >>
  `eval_operand cnt loaded = SOME cv` by simp[Abbr `cv`] >>
  `(w2n cv <= n ==> L < (p+32)+w2n cv)` by
    (`abi_malformed_allocated_window live B L xs r` by fs[abi_malformed_allocated_window_def] >>
     disch_tac >> irule malformed_bytes_loaded_bounds >> simp[Abbr `cv`] >> metis_tac[]) >>
  drule_all malformed_bytes_compare_abort >>
  disch_then (qspec_then `PG` (qx_choose_then `u` (qx_choose_then `H` (qx_choose_then `Tn` strip_assume_tac)))) >>
  qexistsl_tac [`u`,`H`,`Tn`] >> simp[] >> rpt gen_tac >>
  metis_tac[gas_origin_ptr_path_append, APPEND_NIL]
QED

(* HOL notation for the independently closed success and rejection contracts. *)
val table_inputs = #1 (boolSyntax.dest_imp (concl malformed_table_first_failure_joint));
val (ordinary_success, table_tail) = boolSyntax.dest_conj table_inputs;
val (table_head, table_after_head) = boolSyntax.dest_conj table_tail;
val table_scalar_abort = #1 (boolSyntax.dest_conj table_after_head);
val scalar_lift = #1 (boolSyntax.dest_conj
  (#1 (boolSyntax.dest_imp (concl malformed_indexed_guard_revert_joint))));

val coherent_reject = ``\ce env sf ty tv.
  !H0 output b_op source hi st en func ctx cenv cx es
   dstid live B L xs b d s ceiling bytes G tn lo PG.
    abi_decoder_coherent ce env sf ty tv /\ abi_decode_bytes_widths env ty /\
    compile_abi_decode_to_buf (Var output) b_op MLOAD (Var source) hi
      (type_to_abi_dec_info sf ce ty) st = ((),en) /\
    fn_has_code st en func /\ fn_inst_ids_distinct func /\
    (?av. has_type (vyper_to_abi_type env ty) av) /\
    assignable_type env ty /\ type_memory_size tv < dimword(:256) /\
    abi_size_bound sf ty < dimword(:256) /\
    abi_malformed_entry H0 ctx func cenv cx es st
      (abi_malformed_scratch_sites st en func) dstid live
      (Var source) hi b_op (Var output) B L xs b d (type_memory_bytes ce ty) s /\
    (case type_to_abi_dec_info sf ce ty of DecPrimWord clamp => b+32 <= L | _ => T) /\
    fresh_vars_wrt ceiling s /\ en.cs_next_var <= ceiling.cs_next_var /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    bytes = (if is_dynamic (vyper_to_abi_type env ty) then DROP b xs
             else TAKE (static_length (vyper_to_abi_type env ty)) (DROP b xs)) /\
    ~(vyper_decode_valid_enc (vyper_to_abi_type env ty) bytes /\
      abi_vyper_admissible env ty (dec (vyper_to_abi_type env ty) bytes)) /\
    abi_decode_ptr_window G tn s source (n2w B) L /\
    ptr_covers G tn output s (type_memory_bytes ce ty) /\
    op_prov G b_op = NONE /\ op_prov G hi = NONE /\
    op_taint tn b_op = {} /\ op_taint tn hi = {} /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\ alloca_history func s ==>
    ?u G' tn'.
      u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
      u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (Abort Revert_abort u,G',tn'))``;

(* The residual is the passing branch of the checked prefix, with its count
   opened. Keep the original parent inputs, since the prefix does not give an
   execution entry for the finite loop. *)
val (prefix_inputs, prefix_result) =
  boolSyntax.strip_imp (concl malformed_dynarray_prefix_or_bulk_joint);
val [layout_cut, bytes_head_cut, scalar_load_cut, count_compare_cut, guard_abort_cut] =
  List.take (prefix_inputs, 5);
val (_, prefix_pass) = boolSyntax.dest_disj prefix_result;
val (prefix_nonbulk, prefix_tail) = boolSyntax.dest_conj prefix_pass;
val (prefix_head, prefix_count) = boolSyntax.dest_conj prefix_tail;
val (count_var, count_body) = boolSyntax.dest_exists prefix_count;
val passed_count = subst [count_var |-> ``n:num``] count_body;
val (_, array_reject_body) = boolSyntax.strip_forall (rhs (concl (DEPTH_CONV BETA_CONV
  ``(^coherent_reject) ce env sf (ArrayT ty (Dynamic cap)) (ArrayTV tv (Dynamic cap))``)));
val (array_reject_input, array_reject_post) = boolSyntax.dest_imp array_reject_body;
val finite_arm = ``!ce env sf ty tv cap ei stride mem_sz elem_dyn n
  H0 output b_op source hi st en func ctx cenv cx es
  dstid live B L xs b d s ceiling bytes G tn lo PG.
    ^ordinary_success /\ ^scalar_lift /\ abi_decoder_coherent ce env sf ty tv /\
    (^coherent_reject) ce env sf ty tv /\ ^array_reject_input /\
    type_to_abi_dec_info sf ce (ArrayT ty (Dynamic cap)) =
      DecDynArray ei stride mem_sz elem_dyn cap /\
    (\p. ^prefix_nonbulk /\ ^prefix_head /\ ^passed_count) b ==>
    ^array_reject_post``;
val _ = if null (free_vars finite_arm) andalso null (free_vars ordinary_success)
        then () else raise Fail "Unclosed rejection contract";

Theorem abi_malformed_allocated_joint_from_finite_arm:
  ^finite_arm ==> ^ordinary_success ==>
  !ce env sf ty tv. (^coherent_reject) ce env sf ty tv
Proof
  disch_then (mk_asm "finite") >> disch_then (mk_asm "valid") >>
  `!ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
     (^coherent_reject) ce env sf ty tv` suffices_by
   (BETA_TAC >> disch_then (mk_asm "coherent") >>
    rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
    asm "coherent" drule_all >> simp[]) >>
  asm "valid" assume_tac >>
  `^table_head` by
    (BETA_TAC >> rpt gen_tac >> MATCH_ACCEPT_TAC malformed_complex_head_guard_cut) >>
  `^scalar_lift` by
    (BETA_TAC >> rpt gen_tac >> MATCH_ACCEPT_TAC malformed_guard_abort_joint) >>
  `^table_scalar_abort` by
    (BETA_TAC >> rpt gen_tac >> strip_tac >>
     irule malformed_guard_abort_joint >> simp[] >>
     qexistsl_tac [`A`,`C`,`R`,`code`,`t`] >> simp[]) >>
  BETA_TAC >>
  MATCH_MP_TAC
    (BETA_RULE (Q.INST [`P` |-> `^coherent_reject`] calldata_coherent_induction)) >>
  rpt conj_tac >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS)
  >- (`(?clamp. type_to_abi_dec_info sf ce (BaseT bt) = DecPrimWord clamp) \/
       (?n. type_to_abi_dec_info sf ce (BaseT bt) = DecBytestring n)` by
        (Cases_on `bt` >> simp[type_to_abi_dec_info_def] >>
         rename1 `BytesT bd` >> Cases_on `bd` >> simp[type_to_abi_dec_info_def])
      >- (rename1 `type_to_abi_dec_info sf ce (BaseT bt) = DecPrimWord cl` >>
          `b+32 <= L` by fs[] >>
          mp_tac (Q.INST [`ty` |-> `BaseT bt`, `tv` |-> `BaseTV bt`,
                           `clamp` |-> `cl`, `p` |-> `b`, `pos` |-> `b_op`]
            malformed_scalar_allocated_abort) >>
          (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
          disch_then ACCEPT_TAC) >>
      rename1 `type_to_abi_dec_info sf ce (BaseT bt) = DecBytestring len` >>
      mp_tac (Q.INST [`ty` |-> `BaseT bt`, `tv` |-> `BaseTV bt`,
                       `n` |-> `len`, `p` |-> `b`, `pos` |-> `b_op`]
        malformed_bytes_allocated_abort) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then ACCEPT_TAC)
  >- (`?clamp. type_to_abi_dec_info sf ce (FlagT nsid) = DecPrimWord clamp` by
        simp[type_to_abi_dec_info_def] >>
      rename1 `type_to_abi_dec_info sf ce (FlagT nsid) = DecPrimWord cl` >>
      `b+32 <= L` by fs[] >>
      mp_tac (Q.INST [`ty` |-> `FlagT nsid`, `tv` |-> `FlagTV n`,
                       `clamp` |-> `cl`, `p` |-> `b`, `pos` |-> `b_op`]
        malformed_scalar_allocated_abort) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then ACCEPT_TAC)
  >- (namedCases_on `bound` ["n", "cap"]
      >- (qpat_x_assum `bytes = _` SUBST_ALL_TAC >>
          mp_tac (Q.INST [`par` |-> `ArrayT ty (Fixed n)`, `tv` |-> `ArrayTV tv (Fixed n)`]
            malformed_table_first_failure_joint) >>
          rule_assum_tac (SIMP_RULE bool_ss [GSYM CONJ_ASSOC]) >>
          simp_tac bool_ss [GSYM CONJ_ASSOC] >>
          (impl_tac >-
            (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
             ntac 2 disj2_tac >> qexistsl_tac [`ty`, `n`, `tv`] >>
             simp_tac bool_ss [] >> first_assum ACCEPT_TAC)) >>
          disch_then ACCEPT_TAC) >>
      `?ei stride mem_sz elem_dyn.
        type_to_abi_dec_info sf ce (ArrayT ty (Dynamic cap)) =
          DecDynArray ei stride mem_sz elem_dyn cap` by
        simp[type_to_abi_dec_info_def] >>
      `bytes = DROP b xs` by
        (qpat_assum `bytes = _` SUBST1_TAC >>
         simp[vyperABITheory.vyper_to_abi_type_def, is_dynamic_def]) >>
      `^layout_cut` by (rpt gen_tac >> MATCH_ACCEPT_TAC malformed_count_guard_split) >>
      `^bytes_head_cut` by (rpt gen_tac >> MATCH_ACCEPT_TAC malformed_bytes_head_cut) >>
      `^scalar_load_cut` by (rpt gen_tac >> MATCH_ACCEPT_TAC malformed_scalar_load_prefix) >>
      `^count_compare_cut` by (rpt gen_tac >> MATCH_ACCEPT_TAC malformed_count_compare_cut) >>
      `^guard_abort_cut` by (rpt gen_tac >> MATCH_ACCEPT_TAC malformed_guard_abort_joint) >>
      `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
        (qhdtm_assum `abi_malformed_entry`
           (ACCEPT_TAC o MATCH_MP abiMalformedEntryPropsTheory.abi_malformed_entry_allocas_below_fmp)) >>
      mp_tac (Q.INST [`p` |-> `b`, `pos` |-> `b_op`]
        malformed_dynarray_prefix_or_bulk_joint) >>
      ntac 5 (impl_tac >- first_assum ACCEPT_TAC) >>
      BETA_TAC >>
      (impl_tac >-
        (rpt conj_tac >> FIRST
          [first_assum ACCEPT_TAC,
           qpat_assum `type_to_abi_dec_info _ _ (ArrayT _ (Dynamic _)) = _`
            (fn desc => qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`
              (ACCEPT_TAC o PURE_REWRITE_RULE [desc])),
           qpat_assum `bytes = DROP b xs`
            (fn view => qpat_assum `~(vyper_decode_valid_enc _ bytes /\ _)`
              (ACCEPT_TAC o PURE_REWRITE_RULE [view]))])) >>
      disch_then (DISJ_CASES_THEN2 ACCEPT_TAC
        (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
          (qx_choose_then `n` (MAP_EVERY assume_tac o CONJUNCTS))))) >>
      asm "finite" (mp_tac o BETA_RULE o SPEC_ALL) >>
      rule_assum_tac BETA_RULE >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then ACCEPT_TAC)
  >- (qpat_x_assum `bytes = _` SUBST_ALL_TAC >>
      qpat_x_assum `LIST_REL _ tys tvs`
        (strip_assume_tac o SIMP_RULE (srw_ss()) [LIST_REL_CONJ, SF ETA_ss]) >>
      qpat_assum `LIST_REL (\t v. !H0. _) _ _`
        (strip_assume_tac o REWRITE_RULE [EVERY2_EVERY]) >>
      mp_tac (Q.INST [`par` |-> `TupleT tys`, `tv` |-> `TupleTV tvs`]
        malformed_table_first_failure_joint) >>
      rule_assum_tac (SIMP_RULE bool_ss [GSYM CONJ_ASSOC]) >>
      simp_tac bool_ss [GSYM CONJ_ASSOC] >>
      (impl_tac >-
        (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         disj1_tac >> qexistsl_tac [`tys`, `tvs`] >>
         simp_tac bool_ss [] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then ACCEPT_TAC) >>
  qpat_x_assum `bytes = _` SUBST_ALL_TAC >>
  qpat_x_assum `LIST_REL _ (MAP SND args) tvs`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [LIST_REL_CONJ, SF ETA_ss]) >>
  qpat_assum `LIST_REL (\t v. !H0. _) _ _`
    (strip_assume_tac o REWRITE_RULE [EVERY2_EVERY]) >>
  mp_tac (Q.INST [`par` |-> `StructT nsid`, `tv` |-> `StructTV (ZIP (MAP FST (args:(string # type) list),tvs))`]
    malformed_table_first_failure_joint) >>
  rule_assum_tac (SIMP_RULE bool_ss [GSYM CONJ_ASSOC]) >>
  simp_tac bool_ss [GSYM CONJ_ASSOC] >>
  (impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> disj2_tac >> disj1_tac >>
     qexistsl_tac [`nsid`, `args`, `tvs`] >> simp_tac bool_ss [] >>
     rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED

Theorem abi_malformed_allocated_joint_from_success:
  (!H0 ce env sf ty tv v ctx func cenv cx es st en source hi pos output
    B L xs p d dstid live ceiling s G tn lo PG.
    abi_valid_allocated_entry H0 ce env sf ty tv v ctx func cenv cx es
      st en (Var source) hi pos (Var output) B L xs p d dstid live ceiling s /\
    abi_decode_ptr_window G tn s source (n2w B) L /\
    ptr_covers G tn output s (type_memory_bytes ce ty) /\
    op_prov G pos = NONE /\ op_prov G hi = NONE /\
    op_taint tn pos = {} /\ op_taint tn hi = {} /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\ alloca_history func s ==>
    ?u G' tn'.
      abi_valid_allocated_post tv v ctx func cenv cx es st en ceiling dstid
        d (type_memory_bytes ce ty) s u /\
      u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
      u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK u,G',tn')) /\
      ptr_covers G' tn' output u (type_memory_bytes ce ty) /\
      abi_decode_ptr_window G' tn' u source (n2w B) L /\
      (!mem. mem_agree_outside tn'.t_mem u.vs_memory mem ==>
         val_in_memory tv v d mem) /\
      (!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
         FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)) /\
      tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
      (!a. ~(d <= a /\ a < d+type_memory_bytes ce ty) /\
           ~abi_malformed_site_range
              (abi_malformed_scratch_sites st en func) s u a 1 ==>
           (a IN tn'.t_mem <=> a IN tn.t_mem)) /\
      alloca_history func u /\ allocas_from lo u /\ lo <= u.vs_alloca_next) ==>
  (!H0 ce env sf ty tv ctx func cenv cx es st en source hi pos output
    B L xs p d dstid live ceiling s G tn lo PG bytes.
    abi_decoder_coherent ce env sf ty tv /\
    abi_decode_bytes_widths env ty /\
    compile_abi_decode_to_buf (Var output) pos MLOAD (Var source) hi
      (type_to_abi_dec_info sf ce ty) st = ((),en) /\
    fn_has_code st en func /\ fn_inst_ids_distinct func /\
    (?av. has_type (vyper_to_abi_type env ty) av) /\
    assignable_type env ty /\ type_memory_size tv < dimword (:256) /\
    abi_size_bound sf ty < dimword (:256) /\
    abi_malformed_entry H0 ctx func cenv cx es st
      (abi_malformed_scratch_sites st en func) dstid live
      (Var source) hi pos (Var output) B L xs p d (type_memory_bytes ce ty) s /\
    (case type_to_abi_dec_info sf ce ty of DecPrimWord clamp => p+32 <= L | _ => T) /\
    fresh_vars_wrt ceiling s /\ en.cs_next_var <= ceiling.cs_next_var /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    bytes = (if is_dynamic (vyper_to_abi_type env ty) then DROP p xs
      else TAKE (static_length (vyper_to_abi_type env ty)) (DROP p xs)) /\
    ~(vyper_decode_valid_enc (vyper_to_abi_type env ty) bytes /\
      abi_vyper_admissible env ty (dec (vyper_to_abi_type env ty) bytes)) /\
    abi_decode_ptr_window G tn s source (n2w B) L /\
    ptr_covers G tn output s (type_memory_bytes ce ty) /\
    op_prov G pos = NONE /\ op_prov G hi = NONE /\
    op_taint tn pos = {} /\ op_taint tn hi = {} /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\ alloca_history func s ==>
    ?u G' tn'.
      u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
      u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (Abort Revert_abort u,G',tn')))
Proof
  mp_tac abi_malformed_allocated_joint_from_finite_arm >>
  (impl_tac >-
    (BETA_TAC >> rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
     mp_tac (BETA_RULE (Q.INST [`maxn` |-> `cap`, `di` |-> `ei`, `memsz` |-> `mem_sz`,
       `dyn` |-> `elem_dyn`, `pos` |-> `b_op`, `p` |-> `b`]
       abiDecodeRejectFiniteArrayTheory.malformed_finite_array_first_failure_joint)) >>
     rule_assum_tac (PURE_REWRITE_RULE [GSYM CONJ_ASSOC]) >>
     PURE_REWRITE_TAC [GSYM CONJ_ASSOC] >>
     (impl_tac >-
       (rpt conj_tac >> FIRST
         [first_assum ACCEPT_TAC,
          MATCH_ACCEPT_TAC malformed_guard_abort_joint,
          qpat_assum `type_to_abi_dec_info _ _ (ArrayT _ (Dynamic _)) = _`
            (fn desc => qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`
              (ACCEPT_TAC o PURE_REWRITE_RULE [desc])),
          qpat_assum `bytes = _`
            (fn th => let val view = SIMP_RULE bool_ss
                [vyperABITheory.vyper_to_abi_type_def, is_dynamic_def, optionTheory.IS_NONE_DEF] th
              in qpat_assum `~(vyper_decode_valid_enc _ bytes /\ _)`
                (ACCEPT_TAC o PURE_REWRITE_RULE [view]) end)])) >>
     disch_then ACCEPT_TAC)) >>
  disch_then (mk_asm "induct") >> disch_tac >>
  asm "induct" (mp_tac o BETA_RULE) >>
  (impl_tac >-
    (rule_assum_tac (PURE_REWRITE_RULE [GSYM CONJ_ASSOC]) >>
     PURE_REWRITE_TAC [GSYM CONJ_ASSOC] >> first_assum ACCEPT_TAC)) >>
  disch_then (mk_asm "reject") >> rpt gen_tac >> disch_tac >>
  asm "reject" (qspecl_then [`ce`,`env`,`sf`,`ty`,`tv`] mp_tac) >>
  disch_then (fn th => first_assum (ACCEPT_TAC o MATCH_MP (SPEC_ALL th)))
QED
