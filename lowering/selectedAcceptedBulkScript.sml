(* Accepted bulk decoding on the actual calldata, with its installed endpoint. *)
Theory selectedAcceptedBulk
Ancestors decoderNavigationPtr[qualified,ignore_grammar] exprSimPtrProps[qualified,ignore_grammar] entryDispatchPtr[qualified,ignore_grammar] fragGasOriginPtr[qualified,ignore_grammar] gasEvents[qualified,ignore_grammar] contextCodegenRel[qualified,ignore_grammar] ptrSafeRun[qualified,ignore_grammar] fragExec[qualified,ignore_grammar] venomInst[qualified,ignore_grammar] ptrDiscipline[qualified,ignore_grammar] memSafeRun[qualified,ignore_grammar]
  selectedAcceptedInterfaces calldataBulkSourceOutcome calldataBulkOperationalCertificate
  calldataStaticSourceExact calldataBulkSourceExact calldataReconstruction
  logStoreDataOriginPtr calldataBulkUniformPtr abiStaticAggregateProps vyperValue
  abiEncoder compileEnv emitHelper loweringStateRelDefs rich_list
  abiDecoderBulk abiDecoderContract
  abiDecoderRecursiveArray[qualified,ignore_grammar]
  abiDecoderCoherence[qualified,ignore_grammar] abiCallerAllocation[qualified,ignore_grammar]
  abiDecoderFrameCompose[qualified,ignore_grammar] calldataDynOwned[qualified,ignore_grammar]
  calldataSourceCorrespondence[qualified,ignore_grammar]
  ctorDeployLoweringEntryRegistration[qualified,ignore_grammar] instIdxIndep[qualified,ignore_grammar]
  arithmetic words list

Theorem bulk_clean_value[local]:
  abi_decoder_coherent ce env sf ety etv /\
  ~tv_abi_dynamic etv /\ ~tv_needs_clamp etv /\
  n = w2n (cd_word cd (w2n (p:bytes32))) /\ n <= maxn /\
  cd_decode F cd (ArrayTV etv (Dynamic maxn)) (w2n p) = SOME x /\
  mem_word_at d orig = n2w n /\
  mem_bytes_at (d+32) (n * type_memory_size etv) orig =
    mem_bytes_at (w2n (p+32w)) (n * type_memory_size etv) cd /\
  (!i. d <= i /\ i < d+32+n*type_memory_size etv ==> i NOTIN dirty) /\
  mem_agree_outside dirty orig mem ==>
  val_in_memory (ArrayTV etv (Dynamic maxn)) x d mem
Proof
  strip_tac >>
  `mem_word_at d mem = n2w n` by
    (simp[mem_word_at_bytes] >>
     `mem_bytes_at d 32 orig = mem_bytes_at d 32 mem` by
       (irule mem_agree_outside_window >> qexists_tac `dirty` >>
        simp[] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
     fs[mem_word_at_bytes]) >>
  `mem_bytes_at (d+32) (n * type_memory_size etv) orig =
    mem_bytes_at (d+32) (n * type_memory_size etv) mem` by
    (irule mem_agree_outside_window >> qexists_tac `dirty` >>
     simp[] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `?vs. cd_decode_elems T cd etv (w2n (p+32w)) 0 n = SOME vs /\
        LENGTH vs = n /\ EVERY (value_has_type etv) vs /\
        elems_in_memory vs (d+32) etv mem` by
    (qpat_x_assum `n = _` kall_tac >> irule calldata_static_elems_source_exact >>
     conj_tac >- metis_tac[MULT_COMM] >> metis_tac[]) >>
  `x = ArrayV (DynArrayV vs)` by
    (`~(maxn < w2n (cd_word cd (w2n p)))` by decide_tac >>
     `cd_decode_elems T cd etv (w2n (p+32w)) 0 (w2n (cd_word cd (w2n p))) = SOME vs`
       by metis_tac[] >>
     mp_tac (Q.INST [`cd` |-> `cd`, `p` |-> `p`, `maxn` |-> `maxn`,
       `etv` |-> `etv`] (SPEC_ALL calldata_bulk_source_decode)) >>
     asm_simp_tac bool_ss [optionTheory.OPTION_MAP_DEF, combinTheory.o_THM] >>
     simp[]) >>
  qpat_x_assum `x = _` SUBST1_TAC >>
  irule (cj 3 (REWRITE_RULE [make_array_value_def] calldata_dynamic_values_typed_memory)) >>
  asm_rewrite_tac[] >> decide_tac
QED

(* The successor of a successful ordinary instruction is independent of
   the surrounding function. Keep the ghost update on that same edge. *)
Theorem bulk_origin_edge_step[local]:
  gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (s,G,tn) ms (OK t,H,u) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode ==>
  ?fuel z. ~s.vs_halted /\ ~z.vs_halted /\
    step_inst fuel ctx i s = OK z /\
    ms = MAP (\key. key IN explicit) (gas_events_step fuel ctx fn.fn_name i s) /\
    (revert_forward_at bb s.vs_inst_idx \/ mem_safe_step fuel ctx i s) /\
    ptr_safe_step D lo fuel ctx fn PG G tn i s /\
    t = z with vs_inst_idx := SUC s.vs_inst_idx /\
    t.vs_current_bb = s.vs_current_bb /\
    (H,u) = ghost_step fuel ctx PG G tn i s /\
    H = step_prov PG G i z /\ u = step_taint i s z tn
Proof
  strip_tac >> drule fragGasOriginPtrTheory.gas_origin_ptr_edge_common_fuel >>
  simp[] >> strip_tac >>
  gvs[] >>
  TRY (qpat_x_assum `exit_result _` mp_tac >>
       qpat_x_assum `OK _ = step_inst _ _ _ _` (SUBST1_TAC o SYM) >>
       simp[fragExecTheory.exit_result_def] >> NO_TAC) >>
  drule_all (cj 1 venomInstPropsTheory.step_preserves_control_flow) >> strip_tac >>
  drule_all ptrSafeRunTheory.ghost_step_non_invoke >> strip_tac >>
  qexistsl_tac [`fuel`,`t'`] >> gvs[]
QED

Theorem bulk_origin_path_ok_cases[local]:
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,H,u) ==>
  ((s,G,tn) = (t,H,u) /\ ~s.vs_halted) \/
  ?s1 G1 tn1.
    gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK s1,G1,tn1) /\
    gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s1,G1,tn1) [] (OK t,H,u)
Proof
  simp[Once fragGasOriginPtrTheory.gas_origin_ptr_path_cases, fragExecTheory.exit_result_def] >> metis_tac[]
QED

Theorem bulk_not_revert_forward[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> REVERT ==>
  ~revert_forward_at bb s.vs_inst_idx /\ ~in_revert_forward fn s
Proof
  strip_tac >> simp[contextCodegenRelTheory.in_revert_forward_def] >>
  metis_tac[memSafeRunTheory.revert_forward_at_opcode]
QED

Theorem bulk_origin_edge_install[local]:
  gas_origin_ptr_edge (D,lo,explicit,ctx,clip,PG) (s,G,tn) ms (OK t,H,u) /\
  clip.fn_name = fn.fn_name /\
  lookup_block s.vs_current_bb clip.fn_blocks = SOME bc /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bc s.vs_inst_idx = SOME i /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
  i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> REVERT ==>
  gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (s,G,tn) ms (OK t,H,u)
Proof
  strip_tac >> drule_all bulk_origin_edge_step >> strip_tac >>
  `~in_revert_forward fn s` by
    (irule (cj 2 bulk_not_revert_forward) >> metis_tac[]) >>
  `~revert_forward_at bc s.vs_inst_idx /\ ~in_revert_forward clip s` by
    (irule bulk_not_revert_forward >> metis_tac[]) >>
  `ptr_safe_step D lo fuel ctx fn PG G tn i s =
   ptr_safe_step D lo fuel ctx clip PG G tn i s` by
    (qpat_x_assum `ptr_safe_step _ _ _ _ clip _ _ _ _ _` kall_tac >>
     asm_rewrite_tac[ptrSafeRunTheory.ptr_safe_step_def,
       ptrSafeRunTheory.ptr_inst_ok_def, ptrDisciplineTheory.access_ok_def,
       ptrDisciplineTheory.taint_ok_def, ptrDisciplineTheory.about_to_revert_def]) >>
  `ptr_safe_step D lo fuel ctx fn PG G tn i s` by metis_tac[] >>
  `mem_safe_step fuel ctx i s` by fs[] >>
  PURE_REWRITE_TAC[fragGasOriginPtrTheory.gas_origin_ptr_edge_def] >> conj_tac
  >- (PURE_REWRITE_TAC[fragGasOriginTheory.gas_origin_edge_def] >>
      conj_tac >- simp[] >>
      qexistsl_tac [`fuel`, `bb`, `i`, `OK z`] >> simp[]) >>
  PURE_REWRITE_TAC[fragGasPathPtrTheory.gas_path_ptr_edge_def] >>
  conj_tac >- simp[] >>
  qexistsl_tac [`fuel`, `bb`, `i`, `OK z`] >>
  simp[gasEventsTheory.gas_events_length]
QED

(* Replay the exact clipped suffix, not an unrestricted path that may
   return to the continuation after visiting another block. *)
Theorem bulk_clipped_suffix[local]:
  !code pre post s G tn.
    gas_origin_ptr_path (D,lo,explicit,ctx,clip,PG) (s,G,tn) [] (OK t,H,u) /\
    clip.fn_name = fn.fn_name /\
    lookup_block s.vs_current_bb clip.fn_blocks = SOME bc /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    bc.bb_instructions = pre ++ code /\
    bb.bb_instructions = pre ++ code ++ post /\
    s.vs_inst_idx = LENGTH pre /\ t.vs_inst_idx = LENGTH (pre ++ code) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> REVERT) code ==>
    gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,H,u) /\
    (!x. EVERY (\i. ~MEM x i.inst_outputs) code ==>
      FLOOKUP H x = FLOOKUP G x /\ FLOOKUP u.t_var x = FLOOKUP tn.t_var x)
Proof
  Induct >-
    (simp[] >> rpt gen_tac >> strip_tac >> drule bulk_origin_path_ok_cases >> strip_tac
     >- gvs[fragGasOriginPtrTheory.gas_origin_ptr_path_rules] >>
     drule fragGasOriginPtrTheory.gas_origin_ptr_edge_common_fuel >>
     gvs[venomInstTheory.get_instruction_def]) >>
  rpt gen_tac >> strip_tac >> rename1 `bc.bb_instructions = pre ++ i::code` >>
  qpat_x_assum `EVERY _ (i::code)` (strip_assume_tac o SRULE [EVERY_DEF]) >>
  `get_instruction bc s.vs_inst_idx = SOME i /\
   get_instruction bb s.vs_inst_idx = SOME i` by
    simp[venomInstTheory.get_instruction_def, rich_listTheory.APPEND_ASSOC_CONS,
      rich_listTheory.EL_APPEND2] >>
  drule bulk_origin_path_ok_cases >> strip_tac
  >- (gvs[] >> decide_tac) >>
  rename1 `gas_origin_ptr_edge _ (s,G,tn) [] (OK s1,G1,tn1)` >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK s1,G1,tn1)` by
    (irule bulk_origin_edge_install >> gvs[] >> metis_tac[]) >>
  `s1.vs_current_bb = s.vs_current_bb /\ s1.vs_inst_idx = SUC s.vs_inst_idx /\
   (!x. ~MEM x i.inst_outputs ==>
      FLOOKUP G1 x = FLOOKUP G x /\ FLOOKUP tn1.t_var x = FLOOKUP tn.t_var x)` by
    (qpat_x_assum `gas_origin_ptr_edge (_,_,_,_,fn,_) _ _ _` kall_tac >>
     drule_all bulk_origin_edge_step >>
     strip_tac >> gvs[decoderGhostFramePtrTheory.step_prov_other_output,
       ptrDisciplineTheory.step_taint_def,ptrTaintCleanTheory.set_var_taint_lookup]) >>
  first_x_assum (qspecl_then [`pre ++ [i]`,`post`,`s1`,`G1`,`tn1`] mp_tac) >>
  (impl_tac >- gvs[APPEND_ASSOC, ADD1]) >> strip_tac >>
  conj_tac >- metis_tac[cj 2 fragGasOriginPtrTheory.gas_origin_ptr_path_rules, APPEND] >>
  simp[] >> metis_tac[]
QED

Theorem bulk_old_outputs[local]:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),last) /\
  ~dec_info_needs_clamp ei /\ not_fresh_at st x ==>
  EVERY (\i. ~MEM x i.inst_outputs) (emitted_insts st last)
Proof
  strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_abi_decode_to_buf_def, compile_abi_dec_addr_def,
    compile_abi_decode_range_check_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
    fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[exprLoweringPropsTheory.emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  fs[DROP_LENGTH_APPEND, venomInstTheory.mk_inst_def, not_fresh_at_def] >>
  rpt conj_tac >> first_x_assum irule >> decide_tac
QED

Theorem bulk_origin_exact_frame[local]:
  compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),last) /\
  ~dec_info_needs_clamp ei /\ lookup_var root s = SOME (n2w d) /\
  eval_operand src s = SOME p /\ abi_decode_load CALLDATALOAD p s = n2w n /\
  not_fresh_at st root /\ (!x. src = Var x ==> not_fresh_at st x) /\
  ptr_covers G tn root s cap /\ op_taint tn src = {} /\ op_prov G src = NONE /\
  32+n*mem_sz <= cap /\ d+32 < dimword (:256) /\ n*mem_sz < dimword (:256) /\
  run_inst_seq (emitted_insts st last) s = OK t /\ ~s.vs_halted /\
  fn_has_code st last fn /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
  d+32+n*mem_sz <= s.vs_alloca_next ==>
  ?H u.
    ptr_covers H u root t cap /\ u.t_mem SUBSET tn.t_mem /\
    (!i. d <= i /\ i < d+32+n*mem_sz ==> i NOTIN u.t_mem) /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==> FLOOKUP H x = FLOOKUP G x /\
      FLOOKUP u.t_var x = FLOOKUP tn.t_var x) /\
    (!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := LENGTH last.cs_current_insts),H,u))
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bulk_shape >> strip_tac >>
  drule_all abiDecoderBulkExecuteTheory.abi_decoder_bulk_allocation_shape >> strip_tac >>
  `last.cs_current_insts = st.cs_current_insts ++ emitted_insts st last` by
    fs[exprLoweringPropsTheory.emitted_insts_def, rich_listTheory.IS_PREFIX_APPEND,
      DROP_LENGTH_APPEND] >>
  `?bb post. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    bb.bb_instructions = last.cs_current_insts ++ post` by
    fs[fragExecTheory.fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
  qabbrev_tac `bc = <|bb_label := s.vs_current_bb;
    bb_instructions := last.cs_current_insts|>` >>
  qabbrev_tac `clip = fn with fn_blocks := [bc]` >>
  `clip.fn_name = fn.fn_name /\
   lookup_block s.vs_current_bb clip.fn_blocks = SOME bc /\
   bc.bb_instructions = last.cs_current_insts /\ fn_has_code st last clip` by
    simp[Abbr`clip`, Abbr`bc`, fragExecTheory.fn_has_code_def,
      fragExecTheory.emitted_blocks_def, venomInstTheory.lookup_block_def, FIND_thm] >>
  drule_all (Q.INST [`func` |-> `clip`] calldata_bulk_decoder_endpoint_ptr_uniform_origin) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl [`H`,`u`] >> simp[] >>
  `!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := LENGTH last.cs_current_insts),H,u) /\
    !x. not_fresh_at st x ==> FLOOKUP H x = FLOOKUP G x /\
             FLOOKUP u.t_var x = FLOOKUP tn.t_var x` by
    (rpt gen_tac >>
     `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
        i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> REVERT)
        (emitted_insts st last)` by
       (gvs[EVERY_MEM, abiDecoderVarSequenceTheory.abi_decoder_reentry_opcode_def] >>
        rpt strip_tac >> res_tac >> gvs[]) >>
     `gas_origin_ptr_path (D,lower,explicit,ctx,clip,PG) (s,G,tn) []
       (OK (t with vs_inst_idx := LENGTH last.cs_current_insts),H,u)` by simp[] >>
     mp_tac (Q.INST [`lo` |-> `lower`,
       `t` |-> `t with vs_inst_idx := LENGTH last.cs_current_insts`]
       (Q.SPECL [`emitted_insts st last`,`st.cs_current_insts`,
         `post`,`s`,`G`,`tn`] bulk_clipped_suffix)) >>
     (impl_tac >- asm_simp_tac bool_ss [venomStateTheory.venom_state_accfupds, combinTheory.K_THM]) >>
     strip_tac >> simp[] >> rpt strip_tac >>
     drule_all bulk_old_outputs >> metis_tac[]) >>
  qpat_x_assum `!D explicit. gas_origin_ptr_path (_,_,_,_,fn,_) _ [] _ /\ _` mp_tac >>
  simp[] >> metis_tac[]
QED

Theorem selected_bulk_accepts:
  type_to_abi_dec_info sf ce (ArrayT ety (Dynamic maxn)) =
    DecDynArray ei abi_sz mem_sz F maxn /\ ~dec_info_needs_clamp ei ==>
  selected_decoder_accepts ce env sf (ArrayT ety (Dynamic maxn)) tv
Proof
  strip_tac >> pure_asm_rewrite_tac[selected_decoder_accepts_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `maxn < dimword (:256)` by
    (drule (iffLR abiDecoderCoherenceTheory.abi_decoder_coherent_array_iff) >>
     strip_tac >> qpat_x_assum `tv = _` SUBST_ALL_TAC >>
     drule_then ACCEPT_TAC abiDecoderRecursiveArrayTheory.abi_decoder_coherent_array_capacity) >>
  drule_all calldata_bulk_source_outcome >> strip_tac >>
  qpat_x_assum `if _ then _ else _` mp_tac >>
  reverse (Q.ASM_CASES_TAC `n <= maxn`) >-
    (asm_rewrite_tac[optionTheory.NOT_SOME_NONE]) >>
  qpat_assum `n <= maxn` (fn th => rewrite_tac[th]) >> strip_tac >>
  `v = x` by (qpat_x_assum `cd_decode _ _ _ _ = SOME v` mp_tac >>
              asm_rewrite_tac[optionTheory.SOME_11] >> metis_tac[]) >>
  qpat_x_assum `v = x` SUBST_ALL_TAC >>
  `d + (32+maxn*mem_sz) <= initial.vs_alloca_next` by
    (irule abiCallerAllocationTheory.abi_caller_allocation_end >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`cap`,`oid`,`base_addr`] >>
     qpat_assum `type_memory_size tv = _` (fn th => rewrite_tac[GSYM th]) >>
     asm_rewrite_tac[]) >>
  `d + (32+maxn*mem_sz) < dimword (:256)` by
    (qpat_assum `type_memory_size tv = _` (fn th => rewrite_tac[GSYM th]) >>
     asm_rewrite_tac[]) >>
  drule_all_then (qspec_then `ctx` strip_assume_tac) calldata_bulk_accepted_operational >>
  `lookup_var child initial = SOME (n2w d)` by
    (qpat_x_assum `eval_operand (Var child) _ = _` mp_tac >>
     rewrite_tac[venomStateTheory.eval_operand_def]) >>
  `not_fresh_at st child /\ !y. src = Var y ==> not_fresh_at st y` by
    (conj_tac >- asm_rewrite_tac[GSYM calldataDynOwnedTheory.calldata_operand_live_not_fresh] >>
     rpt strip_tac >> qpat_x_assum `src = _` SUBST_ALL_TAC >>
     asm_rewrite_tac[GSYM calldataDynOwnedTheory.calldata_operand_live_not_fresh]) >>
  `abi_decode_load CALLDATALOAD p initial = n2w n` by asm_rewrite_tac[n2w_w2n] >>
  `d+32+n*mem_sz <= initial.vs_alloca_next` by
    (rewrite_tac[GSYM ADD_ASSOC] >> decide_tac) >>
  drule_all_then (qspec_then `PG` strip_assume_tac) bulk_origin_exact_frame >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abiDecoderBulkExecuteTheory.abi_decoder_bulk_allocation_shape >> strip_tac >>
  drule_all (cj 2 ctorDeployLoweringEntryRegistrationTheory.deploy_ctor_decoder_sequence_observations) >>
  strip_tac >>
  `!mem. mem_agree_outside u.t_mem t.vs_memory mem ==> val_in_memory tv x d mem` by
    (`n = w2n (cd_word initial.vs_call_ctx.cc_calldata (w2n p))` by
       (qpat_assum `n = w2n (abi_decode_load _ _ _)` mp_tac >>
        rewrite_tac[calldataSourceCorrespondenceTheory.calldata_decode_load_word]) >>
     qpat_x_assum `tv = _` SUBST_ALL_TAC >> qpat_x_assum `mem_sz = _` SUBST_ALL_TAC >>
     rpt strip_tac >> drule_all_then ACCEPT_TAC bulk_clean_value) >>
  qexistsl [`t with vs_inst_idx := LENGTH last.cs_current_insts`, `[]`,`H`,`u`] >>
  qpat_x_assum `abi_decode_load _ _ _ = n2w n` kall_tac >>
  qpat_x_assum `n = w2n (abi_decode_load _ _ _)` kall_tac >>
  rpt conj_tac >>
  (first_assum ACCEPT_TAC ORELSE
   (rewrite_tac [venomStateTheory.venom_state_accfupds, combinTheory.K_THM,
      instIdxIndepTheory.eval_op_inst_idx, MEM, LESS_EQ_REFL,
      ghostPcTransportPtrTheory.ptr_covers_inst_idx] >>
    TRY (first_assum ACCEPT_TAC))) >>
  TRY (qmatch_goalsub_rename_tac `(t with vs_inst_idx := idx)` >>
    FIRST [irule calldataFiniteTransportTheory.calldata_alloca_inv_fields,
           irule calldataFiniteTransportTheory.calldata_alloca_frontier_inv_fields] >>
    qexists_tac `initial` >>
    asm_rewrite_tac[venomStateTheory.venom_state_accfupds, combinTheory.K_THM] >> NO_TAC) >>
  asm_rewrite_tac[]
  >- (qpat_assum `allocas_from lower initial` mp_tac >>
      rewrite_tac[ptrDisciplineTheory.allocas_from_def,
        venomStateTheory.venom_state_accfupds, combinTheory.K_THM] >>
      qpat_assum `t.vs_allocas = initial.vs_allocas` (fn th => rewrite_tac[th]))
  >- simp[]
  >> `abi_decode_frame d (type_memory_size tv) initial t` by
     (irule abiDecoderFrameComposeTheory.abi_decode_frame_widen >>
      qexistsl [`d`,`32+n*mem_sz`] >>
      qpat_assum `abi_decode_frame d (32+n*mem_sz) initial t`
        (fn th => rewrite_tac[th, LESS_EQ_REFL, LE_ADD_LCANCEL]) >>
      first_assum ACCEPT_TAC)
  >> qpat_assum `abi_decode_frame d (type_memory_size tv) initial t` mp_tac
  >> qpat_assum `type_memory_size tv = _` (fn th => rewrite_tac[th])
  >> qpat_assum `mem_sz = _` (fn th => rewrite_tac[th])
  >> rewrite_tac[GSYM abiDecoderFrameComposeTheory.abi_decode_frame_footprint,
       abi_decode_frame_def, venomStateTheory.venom_state_accfupds, combinTheory.K_THM]
QED
