(* The allocation-free leaves of the owned source decoder contract: primitive
   words and bytestrings, and dynamic arrays of static elements without clamp
   (copied in bulk).  Neither allocates scratch. *)
Theory sourceOwnedLeafPtr
Ancestors
  fragGasOriginPtr fragGasSeqPtr fragGasSeqMem venomExecSemantics
  emitHelper emitHelperProps compileEnv finite_map pred_set valueEncodingProps
  ptrSafetyTransport fragExecPtr entryDispatchPtr
  calldataClampPtr decoderNavigationPtr venomInstProps abiEncoder abiDecoderContract
  calldataWordPtr instSeqComposePtr calldataOverwritePtr
  venomInst list unitTransformDefs ptrSafeRun contextCodegenRel memSafeRun codegenRel
  fragExec loweringStateRelDefs decoderGhostFramePtr exprLoweringProps
  ghostPcTransportPtr instIdxIndep
  abiDecoderArrayHeader compileEnv exprLoweringProps emitHelperProps fragExec
  decoderNavigationPtr instIdxIndep venomInst venomExecSemantics
  fragExecPtr decoderArraySetupPtr decoderSetupStepPtr wordLoadStorePtr fragGasOriginPtr fragGasSeqPtr fragGasSeqMem
  memSafeRun ghostPcTransportPtr fragGasOrigin instMemFrontier ptrSafetyTransport decoderGhostFramePtr words finite_map pred_set
  ptrSafeRun ptrDiscipline codegenRel contextCodegenRel
  sourcePrimitiveGasMem sourceBulkGasMem
  sourcePrimitiveGasMem sourceBulkGasMem abiDecoderGuards decoderArraySetupPtr
  fragGasOriginPtr fragGasSeqPtr fragGasSeqMem codegenRel venomExecSemantics
  venomExecProofs decoderArrayInitPtr decoderNavigationPtr decoderGuardClampCorePtr
  emitHelperProps emitHelper compileEnv ptrSafeRun ptrDiscipline venomInstProofs
  instMemFrontier memSafeRun instIdxIndep fragExec finite_map pred_set words
  exprLoweringProps loweringStateRelDefs venomInst unitTransformDefs
  contextCodegenRel calldataClampPtr decoderGhostFramePtr list
  sourceOwnedArrayLoopPtr sourcePrimitiveReentryPtr abiDecoderSequenceReach
  decoderPrimitiveObservations decoderWorldFramePtr
  sourceBulkArrayLayout calldataBulkReentry calldataBulkUniformPtr
  abiDecoderBulkExecute abiStaticDynarrayLayout calldataTypedRobustPtr dynarrayLiveRobustPtr
  abiDecoderClampedWord abiDecoderBytesTyped abiValueEncoding
  abiDecoderCoherence sourceBytesRepresentation calldataDecodePtr abiDecoderReentry
  venomState abiDecoderBytes calldataDynOwned abiDecoderFrameCompose
  allocaFrontierBound allocaBudgetProps venomMemDefs ptrDiscipline bodyPtrDefs arithmetic

(* Canonical ghost step used inside the allocation-free word certificate. *)
Theorem owned_word_instruction_origin[local]:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
  ~is_terminator i.inst_opcode /\
  inst_mem_below_frontier i s /\ inst_dload_in_section i s /\
  ptr_inst_ok D lo 0 ctx fn G tn i s /\
  step_inst_base i s = OK t ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G i t, step_taint i s t tn)
Proof
  strip_tac >>
  `gas_path_mem_edge ctx fn s 0
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx))` by
    metis_tac[fragGasSeqMemTheory.straight_line_mem_edge] >>
  `gas_path_ptr_edge D lo ctx fn PG G tn s 0
    (step_prov PG G i t) (step_taint i s t tn)
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx))` by
    metis_tac[fragGasSeqPtrTheory.straight_line_ptr_edge] >>
  `step_inst 0 ctx i s = OK t` by simp[step_inst_non_invoke] >>
  `~t.vs_halted` by metis_tac[step_preserves_halted] >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G i t, step_taint i s t tn)` by
    (simp[gas_origin_ptr_edge_def] >>
     metis_tac[fragGasOriginTheory.gas_path_mem_edge_zero_origin]) >>
  drule (cj 2 gas_origin_ptr_path_rules) >>
  disch_then (qspec_then `[]` mp_tac) >>
  simp[cj 1 gas_origin_ptr_path_rules]
QED

Theorem owned_word_scalar_origin[local]:
  MEM opc [SIGNEXTEND; SHR; SHL; EQ; ISZERO; ASSERT] /\
  EVERY (\op. op_taint tn op = {} /\ op_prov G op = NONE) ops /\
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc ops outs) /\
  step_inst_base (mk_inst id opc ops outs) s = OK t /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G (mk_inst id opc ops outs) t,
     step_taint (mk_inst id opc ops outs) s t tn)
Proof
  strip_tac >>
  `?vars. t = s with vs_vars := vars` by
    metis_tac[clamp_scalar_state_frame] >>
  `step_inst 0 ctx (mk_inst id opc ops outs) s = OK t` by
    (`(mk_inst id opc ops outs).inst_opcode <> INVOKE` by
       (fs[MEM] >> simp[mk_inst_def]) >>
     simp[step_inst_non_invoke]) >>
  `ptr_safe_step D lo 0 ctx fn PG G tn (mk_inst id opc ops outs) s` by
    (irule clamp_scalar_step_safe >> simp[] >>
     metis_tac[venom_state_accfupds]) >>
  irule owned_word_instruction_origin >>
  simp[] >>
  `?b. lookup_block s.vs_current_bb fn.fn_blocks = SOME b /\
    get_instruction b s.vs_inst_idx = SOME (mk_inst id opc ops outs)` by
    metis_tac[] >>
  fs[ptr_safe_step_def, MEM] >>
  simp[mk_inst_def, is_terminator_def, inst_mem_below_frontier_def,
    source_memory_read_ranges_def, source_memory_write_ranges_def,
    inst_dload_in_section_def]
QED

Theorem owned_word_scalar_indexed_origin[local]:
  MEM opc [SIGNEXTEND; SHR; SHL; EQ; ISZERO; ASSERT] /\
  EVERY (\op. op_taint tn op = {} /\ op_prov G op = NONE) ops /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb n = SOME (mk_inst id opc ops outs) /\
  step_inst_base (mk_inst id opc ops outs) s = OK t /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s with vs_inst_idx := n,G,tn) []
    (OK (t with vs_inst_idx := SUC n),
     step_prov PG G (mk_inst id opc ops outs) t,
     step_taint (mk_inst id opc ops outs) s t tn)
Proof
  strip_tac >>
  `~is_terminator (mk_inst id opc ops outs).inst_opcode` by
    (fs[MEM] >> simp[mk_inst_def, is_terminator_def]) >>
  `step_inst_base (mk_inst id opc ops outs) (s with vs_inst_idx := n) =
    OK (t with vs_inst_idx := n)` by
    simp[step_inst_inst_idx_indep, exec_result_map_def] >>
  mp_tac (Q.INST [`s` |-> `s with vs_inst_idx := n`,
    `t` |-> `t with vs_inst_idx := n`] owned_word_scalar_origin) >>
  simp[allocas_from_def]
QED

Theorem owned_word_clamp_origin[local]:
  compile_abi_clamp_basetype op clamp sa = ((),sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  op_taint tn op = {} /\ op_prov G op = NONE /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?H u.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),H,u)) /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint u (Var x) = op_taint tn (Var x)) /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u
      (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> drule calldata_clamp_instructions >> strip_tac
  >- (gvs[run_inst_seq_def] >> qexistsl [`G`,`tn`] >>
      `s with vs_inst_idx := LENGTH sa.cs_current_insts = s` by
        simp[venom_state_component_equality] >>
      simp[cj 1 gas_origin_ptr_path_rules]) >>
  qabbrev_tac `v0 = "%" ++ toString sa.cs_next_var` >>
  qabbrev_tac `v1 = "%" ++ toString (sa.cs_next_var + 1)` >>
  qabbrev_tac `i0 = mk_inst sa.cs_next_id opc [Lit shift;op] [v0]` >>
  qabbrev_tac `i1 = mk_inst (sa.cs_next_id + 1) (if signed then EQ else ISZERO)
    (if signed then [op;Var v0] else [Var v0]) [v1]` >>
  qabbrev_tac `i2 = mk_inst (sa.cs_next_id + 2) ASSERT [Var v1] []` >>
  `emitted_insts sa sb = [i0;i1;i2]` by
    simp[Abbr `i0`, Abbr `i1`, Abbr `i2`, Abbr `v0`, Abbr `v1`] >>
  `?s1 s2. step_inst_base i0 s = OK s1 /\
    step_inst_base i1 s1 = OK s2 /\ step_inst_base i2 s2 = OK t` by
    (qpat_x_assum `run_inst_seq _ s = OK t` mp_tac >>
     simp[run_inst_seq_def, AllCaseEqs()] >> metis_tac[]) >>
  `?vars0. s1 = s with vs_vars := vars0` by
    (irule clamp_scalar_state_frame >>
     qexistsl [`sa.cs_next_id`,`opc`,`[Lit shift;op]`,`[v0]`] >>
     simp[Abbr `i0`] >> fs[MEM]) >>
  `?vars1. s2 = s1 with vs_vars := vars1` by
    (irule clamp_scalar_state_frame >>
     qexistsl [`sa.cs_next_id + 1`,`if signed then EQ else ISZERO`,
       `if signed then [op;Var v0] else [Var v0]`,`[v1]`] >>
     simp[Abbr `i1`] >> Cases_on `signed` >> simp[]) >>
  `?vars2. t = s2 with vs_vars := vars2` by
    (irule clamp_scalar_state_frame >>
     qexistsl [`sa.cs_next_id + 2`,`ASSERT`,`[Var v1]`,`[]:string list`] >>
     simp[Abbr `i2`]) >>
  `op <> Var v0` by
    (strip_tac >> qpat_x_assum `!x. op = Var x ==> _` drule >>
     simp[not_fresh_at_def, Abbr `v0`]) >>
  qabbrev_tac `G1 = step_prov PG G i0 s1` >>
  qabbrev_tac `tn1 = step_taint i0 s s1 tn` >>
  qabbrev_tac `G2 = step_prov PG G1 i1 s2` >>
  qabbrev_tac `tn2 = step_taint i1 s1 s2 tn1` >>
  qabbrev_tac `G3 = step_prov PG G2 i2 t` >>
  qabbrev_tac `tn3 = step_taint i2 s2 t tn2` >>
  `op_taint tn1 op = {} /\ op_prov G1 op = NONE` by
    (Cases_on `op` >>
     gvs[Abbr `tn1`, Abbr `G1`, Abbr `i0`, op_prov_def, op_taint_def,
       step_prov_other_output, step_taint_other_output, mk_inst_def]) >>
  `op_prov G1 (Var v0) = NONE /\ op_taint tn1 (Var v0) = {}` by
    (simp[Abbr `tn1`, Abbr `G1`, Abbr `i0`] >>
     irule clamp_scalar_output_ghost >> simp[op_taint_def] >> fs[MEM]) >>
  `op_prov G2 (Var v1) = NONE /\ op_taint tn2 (Var v1) = {}` by
    (simp_tac (srw_ss()) [Abbr `tn2`, Abbr `G2`, Abbr `i1`] >>
     irule clamp_scalar_output_ghost >> Cases_on `signed` >> simp[]) >>
  `tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
    tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm` by
    (simp_tac (srw_ss()) [Abbr `tn1`, Abbr `i0`] >>
     irule clamp_scalar_taint_frame >> fs[MEM]) >>
  `tn2.t_mem = tn1.t_mem /\ tn2.t_stor = tn1.t_stor /\
    tn2.t_trans = tn1.t_trans /\ tn2.t_imm = tn1.t_imm` by
    (simp_tac (srw_ss()) [Abbr `tn2`, Abbr `i1`] >>
     irule clamp_scalar_taint_frame >> Cases_on `signed` >> fs[]) >>
  `tn3.t_mem = tn2.t_mem /\ tn3.t_stor = tn2.t_stor /\
    tn3.t_trans = tn2.t_trans /\ tn3.t_imm = tn2.t_imm` by
    (simp_tac (srw_ss()) [Abbr `tn3`, Abbr `i2`] >>
     irule clamp_scalar_taint_frame >> fs[]) >>
  `!x. not_fresh_at sa x ==> x <> v0 /\ x <> v1` by
    (simp[not_fresh_at_def, Abbr `v0`, Abbr `v1`] >>
     metis_tac[LESS_EQ_REFL, arithmeticTheory.LESS_EQ_ADD]) >>
  `!x. not_fresh_at sa x ==> FLOOKUP G3 x = FLOOKUP G x /\
    op_taint tn3 (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> simp[Abbr `G3`, Abbr `G2`, Abbr `G1`,
       Abbr `tn3`, Abbr `tn2`, Abbr `tn1`, Abbr `i0`, Abbr `i1`, Abbr `i2`,
       mk_inst_def, step_prov_other_output, step_taint_other_output]) >>
  `?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sa.cs_current_insts) = SOME i0 /\
    get_instruction bb (LENGTH sa.cs_current_insts + 1) = SOME i1 /\
    get_instruction bb (LENGTH sa.cs_current_insts + 2) = SOME i2` by
    (drule_all fn_has_code_same_block >> strip_tac >>
     qexists `bb` >> simp[] >>
     first_x_assum (fn th => map_every (fn n => mp_tac (Q.SPEC n th))
       [`0`,`1`,`2`]) >> simp[]) >>
  qexistsl [`G3`,`tn3`] >> simp[] >> conj_tac
  >- suspend "path" >> suspend "backward"
QED

Resume owned_word_clamp_origin[path]:
  rpt gen_tac >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s with vs_inst_idx := LENGTH sa.cs_current_insts,G,tn) []
    (OK (s1 with vs_inst_idx := SUC (LENGTH sa.cs_current_insts)),G1,tn1)` by
    (simp_tac (srw_ss()) [Abbr `G1`, Abbr `tn1`, Abbr `i0`] >>
     irule owned_word_scalar_indexed_origin >>
     simp[op_taint_def, op_prov_def] >> fs[MEM] >> metis_tac[]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s1 with vs_inst_idx := LENGTH sa.cs_current_insts + 1,G1,tn1) []
    (OK (s2 with vs_inst_idx := SUC (LENGTH sa.cs_current_insts + 1)),G2,tn2)` by
    (simp_tac (srw_ss()) [Abbr `G2`, Abbr `tn2`, Abbr `i1`] >>
     irule owned_word_scalar_indexed_origin >>
     simp[] >> conj_tac >- (Cases_on `signed` >> simp[]) >>
     conj_tac >- (Cases_on `signed` >> simp[]) >>
     simp[allocas_from_def] >> metis_tac[allocas_from_def]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s2 with vs_inst_idx := LENGTH sa.cs_current_insts + 2,G2,tn2) []
    (OK (t with vs_inst_idx := SUC (LENGTH sa.cs_current_insts + 2)),G3,tn3)` by
    (simp_tac (srw_ss()) [Abbr `G3`, Abbr `tn3`, Abbr `i2`] >>
     irule owned_word_scalar_indexed_origin >>
     simp[allocas_from_def] >> metis_tac[allocas_from_def]) >>
  qpat_x_assum `s.vs_inst_idx = _` (fn th => assume_tac th) >>
  `s with vs_inst_idx := LENGTH sa.cs_current_insts = s` by
    simp[venom_state_component_equality] >>
  ntac 3 (qpat_x_assum `gas_origin_ptr_path _ _ _ _` mp_tac) >>
  asm_rewrite_tac[arithmeticTheory.ADD1] >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[venom_state_accfupds, arithmeticTheory.ADD_ASSOC] >>
  metis_tac[gas_origin_ptr_path_append, APPEND_NIL]
QED

Resume owned_word_clamp_origin[backward]:
  gen_tac >> strip_tac >>
  `!fuel. ptr_safe_run D lo fuel ctx fn PG G2 tn2
     (s2 with vs_inst_idx := LENGTH sa.cs_current_insts + 2)` by
    (qunabbrev_tac `i2` >>
     irule clamp_scalar_indexed_continuation >>
     conj_tac >- asm_rewrite_tac[] >>
     reverse conj_tac >-
       (qpat_x_assum `allocas_from lo s` mp_tac >> simp[allocas_from_def]) >>
     goal_assum $ drule_at (Pat `get_instruction`) >>
     qexists `t` >>
     simp[Abbr `G3`, Abbr `tn3`, allocas_from_def] >>
     qpat_x_assum `!fuel. ptr_safe_run _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[arithmeticTheory.ADD1]) >>
  `!fuel. ptr_safe_run D lo fuel ctx fn PG G1 tn1
     (s1 with vs_inst_idx := LENGTH sa.cs_current_insts + 1)` by
    (qunabbrev_tac `i1` >>
     irule clamp_scalar_indexed_continuation >>
     conj_tac >- asm_rewrite_tac[] >>
     reverse conj_tac >-
       (qpat_x_assum `allocas_from lo s` mp_tac >> simp[allocas_from_def]) >>
     goal_assum $ drule_at (Pat `get_instruction`) >>
     qexists `s2` >>
     simp[Abbr `G2`, Abbr `tn2`] >>
     conj_tac
     >- (qpat_x_assum `!fuel. ptr_safe_run _ _ _ _ _ _ G2 tn2 _` mp_tac >>
         simp[arithmeticTheory.ADD1]) >>
     Cases_on `signed` >> simp[]) >>
  `!fuel. ptr_safe_run D lo fuel ctx fn PG G tn
     (s with vs_inst_idx := LENGTH sa.cs_current_insts)` by
    (qunabbrev_tac `i0` >>
     irule clamp_scalar_indexed_continuation >>
     conj_tac >- asm_rewrite_tac[] >>
     reverse conj_tac >- asm_rewrite_tac[] >>
     goal_assum $ drule_at (Pat `get_instruction`) >>
     qexists `s1` >>
     simp[Abbr `G1`, Abbr `tn1`, op_taint_def, op_prov_def] >>
     conj_tac
     >- (qpat_x_assum `!fuel. ptr_safe_run _ _ _ _ _ _ G1 tn1 _` mp_tac >>
         simp[arithmeticTheory.ADD1]) >>
     fs[MEM]) >>
  qpat_x_assum `!fuel. ptr_safe_run _ _ _ _ _ _ G tn (s with vs_inst_idx := _)` mp_tac >>
  qpat_x_assum `s.vs_inst_idx = _` (fn th => rewrite_tac[GSYM th]) >>
  simp[]
QED

Finalise owned_word_clamp_origin

Theorem owned_word_mstore_origin[local]:
  emit_void MSTORE [Var p;v] sa = ((),sb) /\
  eval_operand (Var p) s = SOME dw /\ eval_operand v s = SOME w /\
  ptr_covers G tn p s 32 /\ op_taint tn v = {} /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\ allocas_from lo s /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  w2n dw + 32 <= s.vs_alloca_next /\ w2n dw + 32 < dimword (:256) ==>
  ?H u.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (OK ((mstore (w2n dw) w s) with vs_inst_idx := LENGTH sb.cs_current_insts),H,u)) /\
    ptr_covers H u p ((mstore (w2n dw) w s) with vs_inst_idx := LENGTH sb.cs_current_insts) 32 /\
    (!j. w2n dw <= j /\ j < w2n dw + 32 ==> j NOTIN u.t_mem) /\
    (!x. FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u
      ((mstore (w2n dw) w s) with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_same_blocks >> strip_tac >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id MSTORE [Var p;v] []` >>
  qabbrev_tac `t = mstore (w2n dw) w s` >>
  `step_inst_base inst s = OK t` by
    (simp[Abbr `inst`, Abbr `t`] >> irule step_MSTORE >> simp[]) >>
  `emitted_insts sa sb = [inst]` by simp[Abbr `inst`] >>
  qabbrev_tac `H = step_prov PG G inst t` >>
  qabbrev_tac `u = step_taint inst s t tn` >>
  `!x. FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)` by
    simp[Abbr `H`, Abbr `u`, Abbr `inst`, mk_inst_def,
      step_prov_other_output, step_taint_other_output] >>
  `ptr_covers H u p t 32` by
    (simp[Abbr `H`, Abbr `u`] >> irule ptr_covers_step_frame >>
     simp[Abbr `inst`, mk_inst_def, Abbr `t`, mstore_def, lookup_var_def]) >>
  `!j. w2n dw <= j /\ j < w2n dw + 32 ==> j NOTIN u.t_mem` by
    (gen_tac >> strip_tac >> simp[Abbr `u`, Abbr `inst`] >>
     irule mstore_word_clean >> fs[eval_operand_def, lookup_var_def] >> metis_tac[]) >>
  `u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm` by
    simp[Abbr `u`, Abbr `inst`, step_taint_nonmemory_frame, mk_inst_def] >>
  `new_site_bytes s t = {}` by
    (simp[Abbr `t`, mstore_def, new_site_bytes_def, EXTENSION, FLOOKUP_DEF] >>
     metis_tac[]) >>
  `written_taint tn inst s = {}` by
    simp[Abbr `inst`, written_taint_def, mk_inst_def] >>
  `u.t_mem SUBSET tn.t_mem` by
    (simp_tac (srw_ss()) [Abbr `u`] >>
     irule (SRULE [] (Q.INST [`R` |-> `{}:num set`] step_taint_memory_bound)) >>
     simp[]) >>
  `?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sa.cs_current_insts) = SOME inst` by
    (`sb.cs_current_bb = sa.cs_current_bb /\ sb.cs_blocks = sa.cs_blocks` by
       fs[same_blocks_def] >>
     drule_all fn_has_code_same_block >> strip_tac >>
     qexists `bb` >> simp[] >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `LENGTH sb.cs_current_insts = SUC s.vs_inst_idx` by
    (fs[same_blocks_def, emit_void_def, emit_inst_def, fresh_id_def,
      emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >> gvs[]) >>
  qexistsl [`H`,`u`] >>
  qunabbrev_tac `t` >>
  conj_tac >- suspend "path" >>
  conj_tac >- simp[ptr_covers_def, lookup_var_def] >>
  simp[] >> suspend "backward"
QED

Resume owned_word_mstore_origin[path]:
  rpt gen_tac >> simp_tac (srw_ss()) [Abbr `H`, Abbr `u`] >>
  qpat_x_assum `LENGTH sb.cs_current_insts = _` (fn th => rewrite_tac[th]) >>
  irule owned_word_instruction_origin >>
  simp[Abbr `inst`, mk_inst_def, is_terminator_def] >>
  conj_tac >-
    simp[inst_mem_below_frontier_def, source_memory_read_ranges_def,
      source_memory_write_ranges_def, eval_operands_def, fixed_source_write_range_def] >>
  irule ptr_inst_ok_lower_bound_transport >>
  conj_tac >- simp[] >> qexists `0` >> simp[] >>
  irule (SRULE [mk_inst_def] ptr_inst_ok_mstore) >>
  fs[eval_operand_def, lookup_var_def]
QED

Resume owned_word_mstore_origin[backward]:
  gen_tac >> strip_tac >> gen_tac >>
  irule ptr_safe_run_scalar_continuation >>
  qexistsl [`bb`,`inst`,`mstore (w2n dw) w s`] >>
  simp[Abbr `inst`, mk_inst_def, is_terminator_def, mstore_def,
    step_inst_non_invoke] >>
  conj_tac
  >- (qpat_x_assum `!fuel. ptr_safe_run _ _ _ _ _ _ H u _` mp_tac >>
      simp[Abbr `H`, Abbr `u`, mk_inst_def, ADD1, mstore_def]) >>
  simp_tac (srw_ss()) [ptr_safe_defs] >>
  irule ptr_inst_ok_lower_bound_transport >>
  conj_tac >- simp[] >> qexists `0` >> simp[] >>
  irule (SRULE [mk_inst_def] ptr_inst_ok_mstore) >>
  fs[eval_operand_def, lookup_var_def]
QED

Finalise owned_word_mstore_origin

Theorem owned_word_run_origin_certificate[local]:
  compile_abi_decode_to_buf (Var p) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecPrimWord clamp) sa = ((),sb) /\
  eval_operand (Var p) s = SOME dw /\ eval_operand src s = SOME sw /\
  not_fresh_at sa p /\ (!x. src = Var x ==> not_fresh_at sa x) /\
  run_inst_seq (emitted_insts sa sb) s = OK actual /\
  ptr_covers G tn p s 32 /\ op_taint tn src = {} /\ op_prov G src = NONE /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  w2n dw + 32 <= s.vs_alloca_next /\ w2n dw + 32 < dimword (:256) ==>
  ?H u.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (OK (actual with vs_inst_idx := LENGTH sb.cs_current_insts),H,u)) /\
    ptr_covers H u p (actual with vs_inst_idx := LENGTH sb.cs_current_insts) 32 /\
    (!j. w2n dw <= j /\ j < w2n dw+32 ==> j NOTIN u.t_mem) /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint u (Var x) = op_taint tn (Var x)) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u
      (actual with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_x_assum `run_inst_seq _ _ = OK actual` (mk_asm "actual_run") >>
  simp_tac (srw_ss()) [compile_abi_decode_to_buf_def, compile_abi_dec_addr_def, comp_return_def,
    compile_abi_decode_static_def, comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op CALLDATALOAD [src] sa = (value,c1)` >>
  rename1 `compile_abi_clamp_basetype value clamp c1 = ((),c2)` >>
  `inst_extends sa c1 /\ inst_extends c2 sb` by
    metis_tac[inst_extends_emit_op, inst_extends_emit_void] >>
  `same_blocks sa c1 /\ same_blocks c2 sb` by
    metis_tac[emit_op_same_blocks, emit_void_same_blocks] >>
  `cs_extends sa c1 /\ cs_extends c2 sb` by
    (fs[inst_extends_def, same_blocks_def, cs_extends_def] >>
     conj_tac >> qexists `[]` >> simp[]) >>
  `cs_extends c1 c2` by
    (drule calldata_clamp_instructions >> strip_tac >>
     simp[cs_extends_def] >> qexists `[]` >> simp[]) >>
  `cs_extends c1 sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa c1 fn /\ fn_has_code c1 sb fn` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code c1 c2 fn /\ fn_has_code c2 sb fn` by
    metis_tac[fn_has_code_split] >>
  `c1.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa c1 /\
   c2.cs_current_insts = c1.cs_current_insts ++ emitted_insts c1 c2 /\
   sb.cs_current_insts = c2.cs_current_insts ++ emitted_insts c2 sb` by
    (drule calldata_clamp_instructions >> fs[inst_extends_def]) >>
  `sb.cs_current_insts = c1.cs_current_insts ++ emitted_insts c1 sb` by
    metis_tac[emitted_insts_append, APPEND_ASSOC] >>
  `emitted_insts sa sb = emitted_insts sa c1 ++ emitted_insts c1 sb /\
   emitted_insts c1 sb = emitted_insts c1 c2 ++ emitted_insts c2 sb` by
    metis_tac[emitted_insts_append] >>
  `?raw1 raw2. run_inst_seq (emitted_insts sa c1) s = OK raw1 /\
     run_inst_seq (emitted_insts c1 c2) raw1 = OK raw2 /\
     run_inst_seq (emitted_insts c2 sb) raw2 = OK actual` by
    (asm "actual_run" mp_tac >> asm_rewrite_tac[] >>
     metis_tac[run_inst_seq_append_ok_split]) >>
  drule_all calldata_load_overwrite_prefix_uniform >>
  disch_then (qspecl_then [`PG`,`G`] strip_assume_tac) >>
  rename1 `eval_operand value s1 = SOME _` >>
  `!x. not_fresh_at sa x ==> not_fresh_at c1 x` by
    (qpat_x_assum `emit_op CALLDATALOAD _ _ = _` mp_tac >>
     simp[emit_op_def, emit_inst_def, fresh_var_def, fresh_id_def,
       emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >> strip_tac >>
     gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS, DECIDE ``n <= n + 1``]) >>
  `!x. value = Var x ==> not_fresh_at c1 x` by
    (qpat_x_assum `emit_op CALLDATALOAD _ _ = _` mp_tac >>
     simp[emit_op_def, emit_inst_def, fresh_var_def, fresh_id_def,
       emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       not_fresh_at_def] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[] >>
     metis_tac[LESS_EQ_ANTISYM, DECIDE ``~(n + 1 <= n)``]) >>
  `raw1 = s1 with vs_inst_idx := s.vs_inst_idx` by metis_tac[exec_result_11] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c1 c2)` by
    (drule calldata_clamp_instructions >> strip_tac >>
     simp[mk_inst_def, is_terminator_def] >> fs[MEM] >>
     Cases_on `signed` >> simp[mk_inst_def, is_terminator_def]) >>
  `?mid. run_inst_seq (emitted_insts c1 c2) s1 = OK mid` by
    (qpat_x_assum `run_inst_seq (emitted_insts c1 c2) raw1 = _` mp_tac >>
     simp[run_inst_seq_inst_idx] >>
     Cases_on `run_inst_seq (emitted_insts c1 c2) s1` >>
     simp[exec_result_map_def]) >>
  drule_all emit_calldata_load_endpoint_ptr_origin_core >>
  disch_then (qspecl_then [`G`,`ARB`,`ctx`,`PG`,`\g r. T`] strip_assume_tac) >>
  rename1 `op_prov H1 value = NONE` >>
  `raw1 with vs_inst_idx := LENGTH c1.cs_current_insts = s1` by
    simp[venom_state_component_equality] >>
  `allocas_from lo s1` by
    (qpat_x_assum `allocas_from lo s` mp_tac >> simp[allocas_from_def]) >>
  drule_all calldata_clamp_overwrite_prefix_uniform >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  rename1 `s2 = mid with vs_inst_idx := _` >>
  drule_all (Q.INST [`G` |-> `H1`, `tn` |-> `u'`] owned_word_clamp_origin) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  rename1 `gas_origin_ptr_path _ (s1,H1,u') [] (OK _,H2,u2)` >>
  `eval_operand (Var p) s1 = SOME dw` by
    (first_x_assum irule >> simp[]) >>
  `eval_operand (Var p) s2 = SOME dw /\
   eval_operand value s2 = SOME (abi_decode_load CALLDATALOAD sw s)` by
    (conj_tac >> qpat_assum `!a v. _ ==> eval_operand a s2 = SOME v` irule >> simp[]) >>
  `ptr_covers H1 u' p s1 32` by
    (irule ptr_covers_frame >> goal_assum $ drule_at Any >>
     fs[eval_operand_def, lookup_var_def]) >>
  `ptr_covers H2 u2 p s2 32` by
    (irule ptr_covers_frame >> goal_assum $ drule_at Any >>
     simp[] >> fs[eval_operand_def, lookup_var_def] >> gvs[]) >>
  `op_taint u2 value = {}` by
    (Cases_on `value` >> fs[op_taint_def] >> metis_tac[]) >>
  `allocas_from lo s2` by
    (qpat_x_assum `allocas_from lo s1` mp_tac >> simp[allocas_from_def]) >>
  `w2n dw + 32 <= s2.vs_alloca_next` by simp[] >>
  drule_all (Q.INST [`G` |-> `H2`, `tn` |-> `u2`] owned_word_mstore_origin) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `raw2 = s2 with vs_inst_idx := s.vs_inst_idx` by
    (qpat_x_assum `run_inst_seq (emitted_insts c1 c2) raw1 = _` mp_tac >>
     simp[run_inst_seq_inst_idx, exec_result_map_def, venom_state_accfupds]) >>
  `actual with vs_inst_idx := LENGTH sb.cs_current_insts =
    (mstore (w2n dw) (abi_decode_load CALLDATALOAD sw s) s2)
      with vs_inst_idx := LENGTH sb.cs_current_insts` by
    (qpat_x_assum `run_inst_seq (emitted_insts c2 sb) raw2 = _` mp_tac >>
     drule emitted_insts_emit_void >> strip_tac >>
     `step_inst_base (mk_inst c2.cs_next_id MSTORE [Var p;value] []) raw2 =
       OK (mstore (w2n dw) (abi_decode_load CALLDATALOAD sw s) raw2)` by
       (irule step_MSTORE >> gvs[]) >>
     simp[run_inst_seq_def] >> strip_tac >>
     gvs[venom_state_accfupds, mstore_def]) >>
  qexistsl_tac [`H'`,`u''`] >>
  qpat_assum `actual with vs_inst_idx := _ = _` (fn th => rewrite_tac[th]) >>
  conj_tac >- suspend "word_path" >>
  conj_tac >- (
    `ptr_covers H' u'' p (actual with vs_inst_idx := LENGTH sb.cs_current_insts) 32`
      suffices_by (POP_ASSUM_LIST (K all_tac) >> simp[]) >>
    qpat_assum `actual with vs_inst_idx := _ = _`
      (fn th => pure_once_rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "word_frame" >>
  conj_tac >- (gvs[]) >>
  conj_tac >- (gvs[]) >>
  conj_tac >- (gvs[]) >>
  conj_tac >- (gvs[]) >>
  suspend "word_backward"
QED

Resume owned_word_run_origin_certificate[word_path]:
  gvs[venom_state_accfupds] >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
     (s,G,tn) [] (OK s1,H1,u')` by
    (rpt gen_tac >> first_x_assum irule >> simp[]) >>
  qpat_x_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) _ _` mp_tac >>
  qpat_x_assum `!D explicit. gas_origin_ptr_path _ (s1,H1,u') _ _` mp_tac >>
  qpat_x_assum `!D explicit. gas_origin_ptr_path _ (_,H2,u2) _ _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  metis_tac[gas_origin_ptr_path_append, APPEND_NIL]
QED

Resume owned_word_run_origin_certificate[word_frame]:
  gen_tac >> strip_tac >>
  `not_fresh_at c1 x` by metis_tac[] >>
  qpat_x_assum `!x. FLOOKUP H' x = _ /\ _` (qspec_then `x` strip_assume_tac) >>
  qpat_x_assum `!x. not_fresh_at c1 x ==> FLOOKUP H2 x = _ /\ _`
    (qspec_then `x` mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `!q. not_fresh_at sa q ==> _ /\ FLOOKUP H1 q = _ /\ _`
    (qspec_then `x` mp_tac) >> simp[]
QED

Resume owned_word_run_origin_certificate[word_backward]:
  gvs[venom_state_accfupds] >>
  `!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H1 u' s1) ==>
        !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s` by
    (gen_tac >> first_x_assum irule >> simp[]) >>
  qpat_x_assum `!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H1 u' s1) ==> _` mp_tac >>
  qpat_x_assum `!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H2 u2 _) ==> _` mp_tac >>
  qpat_x_assum `!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H' u'' _) ==> _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  metis_tac[]
QED

Finalise owned_word_run_origin_certificate
Theorem source_bulk_header_origin[local]:
  abi_decode_array_header (Var root) src CALLDATALOAD sa = (cnt,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\ ~s.vs_halted /\
  lookup_var root s = SOME (n2w d) /\ d < dimword (:256) /\
  ptr_covers G tn root s capacity /\ 32 <= capacity /\ not_fresh_at sa root /\
  eval_operand src s = SOME a /\ op_taint tn src = {} ==>
  ?H u.
    ptr_covers H u root t capacity /\ op_taint u cnt = {} /\ op_prov H cnt = NONE /\
    eval_operand cnt t = SOME (abi_decode_load CALLDATALOAD a s) /\
    (!op. abi_decoder_operand_live sa.cs_next_var op ==> eval_operand op t = eval_operand op s) /\
    u.t_mem = tn.t_mem DIFF {x | d <= x /\ x < d+32} /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_halted = s.vs_halted /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    (!D lower ctx func.
      fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
      s.vs_current_bb = sa.cs_current_bb /\
      (!fuel. ptr_safe_run D lower fuel ctx func PG H u
        (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
      !fuel. ptr_safe_run D lower fuel ctx func PG G tn
        (s with vs_inst_idx := LENGTH sa.cs_current_insts)) /\
    (!D lower explicit ctx func.
      fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
      s.vs_current_bb = sa.cs_current_bb /\ d + 32 <= s.vs_alloca_next ==>
      gas_origin_ptr_path (D,lower,explicit,ctx,func,PG)
        (s with vs_inst_idx := LENGTH sa.cs_current_insts,G,tn) []
        (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),H,u))
Proof
  strip_tac >>
  `eval_operand (Var root) s = SOME (n2w d) /\
   abi_decoder_operand_live sa.cs_next_var (Var root)` by
    simp[eval_operand_def, calldata_operand_live_not_fresh] >>
  drule_all calldata_array_header_repeat_sequence >> strip_tac >>
  qpat_x_assum `abi_decode_array_header _ _ _ _ = _` mp_tac >>
  simp[abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def] >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  rename1 `emit_op CALLDATALOAD [src] sa = (cnt,sm)` >>
  rename1 `emit_void MSTORE [Var root; cnt] sm = ((),sb)` >>
  `inst_extends sa sm /\ inst_extends sm sb` by
    metis_tac[inst_extends_emit_op, inst_extends_emit_void] >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (fs[inst_extends_def] >> metis_tac[emitted_insts_append]) >>
  qpat_x_assum `run_inst_seq _ s = OK t` mp_tac >>
  pure_asm_rewrite_tac [] >>
  disch_then (mp_then Any strip_assume_tac run_inst_seq_append_ok) >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK s1` >>
  `run_inst_seq (emitted_insts sa sm)
    (s with vs_inst_idx := LENGTH sa.cs_current_insts) =
    OK (s1 with vs_inst_idx := LENGTH sa.cs_current_insts)` by
    (drule emit_op_run_pc >> simp[is_terminator_def] >>
     disch_then (qspecl_then [`s`,`LENGTH sa.cs_current_insts`] mp_tac) >>
     simp[exec_result_map_def]) >>
  `eval_operand src (s with vs_inst_idx := LENGTH sa.cs_current_insts) = SOME a` by simp[] >>
  drule_all (Q.INST [`s` |-> `s with vs_inst_idx := LENGTH sa.cs_current_insts`,
    `t` |-> `s1 with vs_inst_idx := LENGTH sa.cs_current_insts`]
    (SPEC_ALL emit_calldata_load_endpoint_ptr_origin_core)) >>
  disch_then (qspecl_then [`ARB`,`ARB`,`ARB`,`PG`,`G`] strip_assume_tac) >>
  gvs[lookup_var_def] >>
  suspend "finish"
QED

Resume source_bulk_header_origin[finish]:
  rpt (qpat_x_assum `frag_exec_ptr _ _ _ _ _ _ _ _` kall_tac) >>
  `lookup_var root s1 = SOME (n2w d) /\ ptr_covers H u root s1 capacity` by
    (conj_tac >- metis_tac[lookup_var_def] >>
     irule ptr_covers_frame >> metis_tac[lookup_var_def]) >>
  `ptr_covers H u root s1 32` by
    (fs[ptr_covers_def] >> metis_tac[LESS_EQ_TRANS]) >>
  drule emitted_insts_emit_void >> strip_tac >>
  `?w. eval_operand cnt s1 = SOME w` by
    (qpat_x_assum `run_inst_seq (emitted_insts sm sb) _ = _` mp_tac >>
     simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_write2_def, eval_operand_def, AllCaseEqs()] >> metis_tac[]) >>
  `t = mstore d w s1` by
    (qpat_x_assum `run_inst_seq (emitted_insts sm sb) _ = _` mp_tac >>
     simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_write2_def, eval_operand_def, w2n_n2w] >>
     Cases_on `cnt` >> fs[eval_operand_def]) >>
  `w2n (n2w d : bytes32) = d` by simp[] >>
  drule_all mstore_ghost_frame >> disch_then (qspecl_then [`PG`,`H`] strip_assume_tac) >>
  qabbrev_tac `u2 = step_taint (mk_inst sm.cs_next_id MSTORE [Var root;cnt] []) s1 t u` >>
  `u2.t_var = u.t_var /\ u2.t_stor = tn.t_stor /\ u2.t_trans = tn.t_trans /\
    u2.t_mem = tn.t_mem DIFF {x | d <= x /\ x < d+32}` by
    (simp[Abbr `u2`] >> metis_tac[]) >>
  `step_prov PG H (mk_inst sm.cs_next_id MSTORE [Var root;cnt] []) t = H` by metis_tac[] >>
  qpat_x_assum `!id. _` kall_tac >>
  `u2.t_imm = tn.t_imm` by
    simp[Abbr `u2`, step_taint_def, mk_inst_def, set_var_taint_def, imm_taint_def] >>
  `!op. op_taint u2 op = op_taint u op` by (Cases >> simp[op_taint_def]) >>
  `!x. lookup_var x t = lookup_var x s1` by
    simp[mstore_def, write_memory_with_expansion_def, lookup_var_def] >>
  `ptr_covers H u2 root t capacity` by (irule ptr_covers_frame >> metis_tac[]) >>
  qexistsl_tac [`H`,`u2`] >> simp[] >>
  `t.vs_current_bb = s.vs_current_bb` by
    (drule emitted_insts_emit_op >> strip_tac >>
     qpat_x_assum `run_inst_seq (emitted_insts sa sm) s = OK s1` mp_tac >>
     simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_read1_def, AllCaseEqs()] >> strip_tac >>
     gvs[update_var_def, mstore_def, write_memory_with_expansion_def]) >>
  simp[] >>
  conj_tac >- metis_tac[lookup_var_def] >>
  conj_tac >- suspend "backward" >>
  suspend "joint"
QED

Resume source_bulk_header_origin[backward]:
  rpt gen_tac >> strip_tac >>
  `same_blocks sa sm /\ same_blocks sm sb` by
    metis_tac[emit_op_same_blocks, emit_void_same_blocks] >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    (conj_tac >> irule cs_extends_same_block >> fs[inst_extends_def, same_blocks_def] >> metis_tac[]) >>
  drule_all fn_has_code_split >> strip_tac >>
  `sm.cs_current_bb = sa.cs_current_bb /\ sb.cs_current_bb = sm.cs_current_bb` by fs[same_blocks_def] >>
  `s1.vs_current_bb = s.vs_current_bb /\ s1.vs_halted = s.vs_halted /\
    s1.vs_alloca_next = s.vs_alloca_next` by
    gvs[mstore_def, write_memory_with_expansion_def] >>
  `!fuel. ptr_safe_run D lower fuel ctx func PG H u
     (s1 with vs_inst_idx := LENGTH sm.cs_current_insts)` suffices_by
    (strip_tac >> first_x_assum (qspecl_then [`D`,`lower`,`ctx`,`func`] mp_tac) >> simp[]) >>
  `!fuel. ptr_inst_ok D lower fuel ctx func H u
    (mk_inst sm.cs_next_id MSTORE [Var root;cnt] [])
    (s1 with vs_inst_idx := LENGTH sm.cs_current_insts)` by
    (gen_tac >> irule ptr_inst_ok_lower_bound_transport >>
     conj_tac >- (gvs[allocas_from_def] >> metis_tac[]) >>
     qexists_tac `0` >> simp[] >> irule ptr_inst_ok_mstore >> simp[] >>
     gvs[ptr_covers_def, lookup_var_def]) >>
  irule setup_instruction_continuation >>
  qexistsl_tac [`H`, `mk_inst sm.cs_next_id MSTORE [Var root;cnt] []`,
    `sm`, `sb`, `t with vs_inst_idx := LENGTH sm.cs_current_insts`, `u2`] >>
  simp[mk_inst_def, is_terminator_def, same_blocks_def] >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def,
    eval_operand_def, mstore_def, write_memory_with_expansion_def] >>
  Cases_on `cnt` >> gvs[eval_operand_def, lookup_var_def, mstore_def,
    write_memory_with_expansion_def, w2n_n2w, Abbr `u2`]
QED

Resume source_bulk_header_origin[joint]:
  rpt gen_tac >> strip_tac >>
  `same_blocks sa sm /\ same_blocks sm sb` by
    metis_tac[emit_op_same_blocks, emit_void_same_blocks] >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    (conj_tac >> irule cs_extends_same_block >> fs[inst_extends_def, same_blocks_def] >> metis_tac[]) >>
  drule_all fn_has_code_split >> strip_tac >>
  `sm.cs_current_bb = sa.cs_current_bb /\ sb.cs_current_bb = sm.cs_current_bb` by fs[same_blocks_def] >>
  `s1.vs_current_bb = s.vs_current_bb /\ s1.vs_halted = s.vs_halted /\
    s1.vs_alloca_next = s.vs_alloca_next` by
    gvs[mstore_def, write_memory_with_expansion_def] >>
  `ptr_inst_ok D lower 0 ctx func H u
    (mk_inst sm.cs_next_id MSTORE [Var root;cnt] [])
    (s1 with vs_inst_idx := LENGTH sm.cs_current_insts)` by
    (irule ptr_inst_ok_lower_bound_transport >>
     conj_tac >- (gvs[allocas_from_def] >> metis_tac[]) >>
     qexists_tac `0` >> simp[] >> irule ptr_inst_ok_mstore >> simp[] >>
     gvs[ptr_covers_def, lookup_var_def]) >>
  `?bb. lookup_block s1.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sm.cs_current_insts) =
      SOME (mk_inst sm.cs_next_id MSTORE [Var root;cnt] [])` by
    (`?bb. lookup_block sm.cs_current_bb func.fn_blocks = SOME bb /\
      !k. k < LENGTH [mk_inst sm.cs_next_id MSTORE [Var root;cnt] []] ==>
      get_instruction bb (LENGTH sm.cs_current_insts + k) =
        SOME (EL k [mk_inst sm.cs_next_id MSTORE [Var root;cnt] []])` by
       (irule fn_has_code_same_block >> qexists_tac `sb` >> simp[]) >>
     qexists_tac `bb` >> gvs[] >> first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst_base (mk_inst sm.cs_next_id MSTORE [Var root;cnt] [])
    (s1 with vs_inst_idx := LENGTH sm.cs_current_insts) =
    OK (t with vs_inst_idx := LENGTH sm.cs_current_insts)` by
    (simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def,
      eval_operand_def, lookup_var_def, w2n_n2w] >>
     Cases_on `cnt` >> gvs[eval_operand_def, lookup_var_def,
      mstore_def, write_memory_with_expansion_def]) >>
  `inst_mem_below_frontier (mk_inst sm.cs_next_id MSTORE [Var root;cnt] [])
    (s1 with vs_inst_idx := LENGTH sm.cs_current_insts)` by
    (simp[below_frontier_MSTORE, eval_operand_def, lookup_var_def] >>
     gvs[lookup_var_def]) >>
  suspend "edges"
QED

Resume source_bulk_header_origin[edges]:
  `gas_path_mem_edge ctx func
    (s1 with vs_inst_idx := LENGTH sm.cs_current_insts) 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (mp_tac (Q.INST [`s` |-> `s1 with vs_inst_idx := LENGTH sm.cs_current_insts`,
      `u` |-> `t with vs_inst_idx := LENGTH sm.cs_current_insts`,
      `i` |-> `mk_inst sm.cs_next_id MSTORE [Var root;cnt] []`]
      straight_line_mem_edge) >>
     simp[mk_inst_def, is_terminator_def, inst_dload_in_section_def] >> gvs[ADD1]) >>
  `gas_path_ptr_edge D lower ctx func PG H u
    (s1 with vs_inst_idx := LENGTH sm.cs_current_insts) 0 H u2
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (mp_tac (Q.INST [`lo` |-> `lower`, `fn` |-> `func`, `G` |-> `H`, `tn` |-> `u`]
      (Q.INST [`s` |-> `s1 with vs_inst_idx := LENGTH sm.cs_current_insts`,
        `u` |-> `t with vs_inst_idx := LENGTH sm.cs_current_insts`,
        `i` |-> `mk_inst sm.cs_next_id MSTORE [Var root;cnt] []`]
        straight_line_ptr_edge)) >>
     simp[mk_inst_def, is_terminator_def, Abbr `u2`] >> gvs[ADD1]) >>
  `gas_origin_ptr_edge (D,lower,explicit,ctx,func,PG)
    (s1 with vs_inst_idx := LENGTH sm.cs_current_insts,H,u) []
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),H,u2)` by
    (simp[gas_origin_ptr_edge_def] >> gvs[gas_path_mem_edge_zero_origin]) >>
  `gas_origin_ptr_path (D,lower,explicit,ctx,func,PG)
    (s1 with vs_inst_idx := LENGTH sm.cs_current_insts,H,u) []
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),H,u2)` by
    (irule (SRULE [] (Q.INST [`left` |-> `[]`, `right` |-> `[]`]
       (SPEC_ALL (cj 2 gas_origin_ptr_path_rules)))) >>
     qexistsl_tac [`H`,`t with vs_inst_idx := LENGTH sb.cs_current_insts`,`u2`] >>
     simp[] >> irule (cj 1 gas_origin_ptr_path_rules) >> simp[]) >>
  qpat_x_assum `!D lower explicit ctx' func. _` (qspecl_then
    [`D`,`lower`,`explicit`,`ctx`,`func`] mp_tac) >> simp[] >>
  disch_then (mp_then Any mp_tac gas_origin_ptr_path_append) >>
  disch_then (qspecl_then [`s1 with vs_inst_idx := LENGTH sm.cs_current_insts`,
    `H`,`u`,`[]`,`OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)`,`H`,`u2`] mp_tac) >>
  simp[]
QED

Finalise source_bulk_header_origin
(* A single emitted scalar instruction, with its canonical ghost update. *)
Theorem source_bulk_instruction_origin[local]:
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ [i] /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
  ~is_terminator i.inst_opcode /\
  inst_mem_below_frontier i s /\ inst_dload_in_section i s /\
  ptr_inst_ok D lower 0 ctx func G tn i s /\
  step_inst_base i s = OK t ==>
  gas_origin_ptr_path (D,lower,explicit,ctx,func,PG) (s,G,tn) []
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G i t, step_taint i s t tn)
Proof
  strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME i` by
    (drule_all fn_has_code_same_block >> strip_tac >>
     qexists_tac `bb` >> simp[] >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `gas_path_mem_edge ctx func s 0
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx))` by
    metis_tac[fragGasSeqMemTheory.straight_line_mem_edge] >>
  `gas_path_ptr_edge D lower ctx func PG G tn s 0
    (step_prov PG G i t) (step_taint i s t tn)
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx))` by
    metis_tac[fragGasSeqPtrTheory.straight_line_ptr_edge] >>
  `step_inst 0 ctx i s = OK t` by simp[step_inst_non_invoke] >>
  `~t.vs_halted` by metis_tac[step_preserves_halted] >>
  `gas_origin_ptr_edge (D,lower,explicit,ctx,func,PG) (s,G,tn) []
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G i t, step_taint i s t tn)` by
    (simp[gas_origin_ptr_edge_def] >>
     metis_tac[fragGasOriginTheory.gas_path_mem_edge_zero_origin]) >>
  drule (cj 2 gas_origin_ptr_path_rules) >>
  disch_then (qspec_then `[]` mp_tac) >>
  simp[cj 1 gas_origin_ptr_path_rules]
QED

Theorem source_bulk_compare_origin[local]:
  emit_op GT [src; Lit bound] sa = (out,sb) /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H u. op_taint u out = {} /\ op_prov H out = NONE /\
    (?vars. t = s with vs_vars := vars) /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    (!D lower explicit ctx func.
      fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
      ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_origin_ptr_path (D,lower,explicit,ctx,func,PG) (s,G,tn) []
        (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),H,u))
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (drule emit_op_same_blocks >> simp[same_blocks_def]) >>
  qabbrev_tac `out = "%" ++ toString sa.cs_next_var` >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id GT [src; Lit bound] [out]` >>
  `step_inst_base inst s =
    OK (update_var out (bool_to_word (w2n a > w2n bound)) s)` by
    (simp[Abbr `inst`] >> irule step_GT >> simp[eval_operand_def]) >>
  `t = update_var out (bool_to_word (w2n a > w2n bound)) s` by
    (qpat_x_assum `run_inst_seq _ s = OK t` mp_tac >>
     qpat_x_assum `step_inst_base inst s = _` mp_tac >>
     simp[Abbr `inst`, Abbr `out`, run_inst_seq_def] >> metis_tac[]) >>
  `step_inst_base inst s = OK t` by metis_tac[] >>
  `!x. not_fresh_at sa x ==> x <> out` by
    (simp[not_fresh_at_def, Abbr `out`] >> metis_tac[LESS_EQ_REFL]) >>
  qabbrev_tac `H = step_prov PG G inst t` >>
  qabbrev_tac `u = step_taint inst s t tn` >>
  `!D lower explicit ctx func.
      fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
      ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_origin_ptr_path (D,lower,explicit,ctx,func,PG) (s,G,tn) []
        (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),H,u)` by
    (rpt gen_tac >> strip_tac >>
     `ptr_inst_ok D lower 0 ctx func G tn inst s` by
       (`op_taint tn (Lit bound) = {}` by simp[op_taint_def] >>
        qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
        simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
          Abbr `inst`, mk_inst_def, step_inst_non_invoke,
          source_memory_write_ranges_def, source_memory_read_ranges_def,
          update_var_def] >> metis_tac[]) >>
     `LENGTH sb.cs_current_insts = SUC s.vs_inst_idx` by simp[] >>
     simp[NoAsms, Abbr `H`, Abbr `u`] >>
     qpat_assum `LENGTH sb.cs_current_insts = _` (fn th => rewrite_tac [th]) >>
     irule source_bulk_instruction_origin >>
     goal_assum (drule_at Any) >>
     simp[Abbr `inst`, Abbr `out`, mk_inst_def, is_terminator_def,
       inst_mem_below_frontier_def, inst_dload_in_section_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def] >>
     qexistsl_tac [`sa`,`sb`] >> simp[mk_inst_def]) >>
  qpat_x_assum `!D lower explicit ctx func. _` (assume_tac o SRULE []) >>
  qexistsl_tac [`H`,`u`] >> simp[] >>
  simp[Abbr `H`, Abbr `u`, Abbr `inst`, Abbr `out`,
    lookup_var_def, op_prov_def, step_prov_def, out_prov_def, set_prov_def,
    op_taint_def, step_taint_def, out_taint_def, set_var_taint_def,
    FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, mk_inst_def,
    mem_taint_def, new_site_bytes_def, step_writes_def,
    written_taint_def, store_taint_def, imm_taint_def, adopt_reset_def,
    update_var_def, source_memory_write_ranges_def, range_bytes_def,
    pred_setTheory.EXTENSION, FDOM_DRESTRICT, SF CONJ_ss] >>
  simp[FLOOKUP_DEF, SF CONJ_ss] >>
  conj_tac >- (qexists_tac `t.vs_vars` >> simp[update_var_def]) >>
  reverse conj_tac >-
    (qpat_x_assum `!D lower explicit ctx func. _` mp_tac >>
     simp[update_var_def, step_prov_def, out_prov_def, set_prov_def,
       step_taint_def, out_taint_def, set_var_taint_def, mk_inst_def,
       mem_taint_def, new_site_bytes_def, step_writes_def, written_taint_def,
       store_taint_def, imm_taint_def, adopt_reset_def,
       source_memory_write_ranges_def, range_bytes_def,
       pred_setTheory.EXTENSION, FDOM_DRESTRICT, FLOOKUP_DEF, SF CONJ_ss]) >>
  qpat_x_assum `!x. not_fresh_at sa x ==> _` (assume_tac o SRULE []) >>
  gen_tac >> disch_tac >>
  `x <> STRING #"%" (toString sa.cs_next_var)` by metis_tac[] >>
  simp[FLOOKUP_DEF, SF CONJ_ss]
QED

Theorem source_bulk_iszero_origin[local]:
  emit_op ISZERO [op] sa = (out,sb) /\
  op_taint tn op = {} /\ op_prov G op = NONE /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H u.
    (!D lower explicit ctx func.
      fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
      ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_origin_ptr_path (D,lower,explicit,ctx,func,PG) (s,G,tn) []
        (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),H,u)) /\
    op_taint u out = {} /\ op_prov H out = NONE /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (?vars. t = s with vs_vars := vars) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (drule emit_op_same_blocks >> simp[same_blocks_def]) >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id ISZERO [op]
    ["%" ++ toString sa.cs_next_var]` >>
  `step_inst_base inst s = OK t` by
    gvs[Abbr `inst`, run_inst_seq_def, AllCaseEqs()] >>
  `MEM ISZERO [SIGNEXTEND; SHR; SHL; EQ; ISZERO; ASSERT] /\
   EVERY (\op. op_taint tn op = {} /\ op_prov G op = NONE) [op]` by simp[] >>
  `?vars. t = s with vs_vars := vars` by
    (qpat_assum `step_inst_base inst s = OK t` mp_tac >>
     simp[Abbr `inst`] >> metis_tac[clamp_scalar_state_frame, MEM]) >>
  qexistsl_tac [`step_prov PG G inst t`, `step_taint inst s t tn`] >>
  conj_tac >-
    (rpt gen_tac >> strip_tac >>
     `ptr_inst_ok D lower 0 ctx func G tn inst s` by
       (simp[Abbr `inst`] >>
        irule (cj 1 (SRULE [ptr_safe_step_def] clamp_scalar_step_safe)) >>
        simp[step_inst_non_invoke, mk_inst_def] >>
        qexists_tac `t` >> gvs[step_inst_non_invoke, mk_inst_def] >>
        simp[]) >>
     `LENGTH sb.cs_current_insts = SUC s.vs_inst_idx` by simp[] >>
     qpat_assum `LENGTH sb.cs_current_insts = _` (fn th => rewrite_tac [th]) >>
     irule source_bulk_instruction_origin >> goal_assum (drule_at Any) >>
     simp[Abbr `inst`, mk_inst_def, is_terminator_def,
       inst_mem_below_frontier_def, inst_dload_in_section_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def] >>
     qexistsl_tac [`sa`,`sb`] >> simp[mk_inst_def]) >>
  `EVERY (\op. op_taint tn op = {}) [op]` by simp[] >>
  conj_tac >- (simp[Abbr `inst`] >> metis_tac[clamp_scalar_output_ghost]) >>
  conj_tac >- (simp[Abbr `inst`] >> metis_tac[clamp_scalar_output_ghost]) >>
  `!x. not_fresh_at sa x ==> x <> "%" ++ toString sa.cs_next_var` by
    (simp[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  simp[Abbr `inst`] >>
  qpat_x_assum `step_inst_base _ _ = _` (assume_tac o SRULE []) >>
  qpat_x_assum `!x. not_fresh_at sa x ==> _` (assume_tac o SRULE []) >>
  drule_all clamp_scalar_taint_frame >>
  disch_then (qspec_then `tn` strip_assume_tac) >>
  gvs[] >>
  conj_tac >- (qexists_tac `vars` >> simp[]) >>
  gen_tac >> disch_tac >>
  `x <> "%" ++ toString sa.cs_next_var` by (simp[] >> metis_tac[]) >>
  qpat_x_assum `x <> _` (assume_tac o SRULE []) >>
  conj_tac >-
    (irule clamp_scalar_lookup_frame >> goal_assum (drule_at Any) >> simp[]) >>
  simp[mk_inst_def, step_prov_other_output, step_taint_other_output]
QED
Theorem source_bulk_assert_origin[local]:
  emit_void ASSERT [op] sa = ((),sb) /\
  op_taint tn op = {} /\ op_prov G op = NONE /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  t = s /\
  (!D lower explicit ctx func.
    fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_origin_ptr_path (D,lower,explicit,ctx,func,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),G,tn))
Proof
  strip_tac >>
  `t = s` by (drule_all emit_assert_endpoint_ptr_core >> metis_tac[]) >>
  drule emitted_insts_emit_void >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (drule emit_void_same_blocks >> simp[same_blocks_def]) >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id ASSERT [op] []` >>
  `step_inst_base inst s = OK s` by
    gvs[Abbr `inst`, run_inst_seq_def, AllCaseEqs()] >>
  simp[NoAsms] >> conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  `ptr_inst_ok D lower 0 ctx func G tn inst s` by
    (simp[Abbr `inst`] >>
     irule (cj 1 (SRULE [ptr_safe_step_def] clamp_scalar_step_safe)) >>
     simp[step_inst_non_invoke, mk_inst_def] >> qexists_tac `s` >>
     gvs[step_inst_non_invoke, mk_inst_def]) >>
  `step_prov PG G inst s = G /\ step_taint inst s s tn = tn` by
    simp[Abbr `inst`, mk_inst_def, step_prov_def, set_prov_def,
      step_taint_def, set_var_taint_def, mem_taint_def, new_site_bytes_def,
      step_writes_def, written_taint_def, store_taint_def, imm_taint_def,
      adopt_reset_def, source_memory_write_ranges_def, range_bytes_def,
      DRESTRICT_UNIV, FLOOKUP_DEF, taint_component_equality,
      pred_setTheory.EXTENSION, SF CONJ_ss] >>
  `LENGTH sb.cs_current_insts = SUC s.vs_inst_idx` by simp[] >>
  qpat_assum `LENGTH sb.cs_current_insts = _` (fn th => rewrite_tac [th]) >>
  qpat_x_assum `t = s` SUBST_ALL_TAC >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\
   ~is_terminator inst.inst_opcode /\ inst_mem_below_frontier inst s /\
   inst_dload_in_section inst s` by
    simp[Abbr `inst`, mk_inst_def, is_terminator_def,
      inst_mem_below_frontier_def, inst_dload_in_section_def,
      source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  drule_all source_bulk_instruction_origin >>
  disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >> simp[]
QED


Theorem source_bulk_count_guard_origin[local]:
  abi_decode_count_guard CALLDATALOAD src maxn sa = (cnt,sb) /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H u. op_taint u cnt = {} /\ op_prov H cnt = NONE /\
    (?vars. t = s with vs_vars := vars) /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    (!D lower explicit ctx func.
      fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
      ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_origin_ptr_path (D,lower,explicit,ctx,func,PG) (s,G,tn) []
        (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),H,u))
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_count_guard _ _ _ _ = _` mp_tac >>
  simp[abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[comp_return_def] >> strip_tac >> gvs[] >>
  rename1 `emit_op CALLDATALOAD [src] sa = (cnt,c1)` >>
  rename1 `emit_op GT [cnt; Lit (n2w maxn)] c1 = (cmp,c2)` >>
  rename1 `emit_op ISZERO [cmp] c2 = (ok,c3)` >>
  rename1 `emit_void ASSERT [ok] c3 = ((),sb)` >>
  `inst_extends sa c1 /\ inst_extends c1 c2 /\
    inst_extends c2 c3 /\ inst_extends c3 sb` by
    metis_tac[inst_extends_emit_op, inst_extends_emit_void] >>
  `emitted_insts sa sb = emitted_insts sa c1 ++
    (emitted_insts c1 c2 ++ (emitted_insts c2 c3 ++ emitted_insts c3 sb))` by
    (fs[inst_extends_def] >> metis_tac[emitted_insts_append, APPEND_ASSOC]) >>
  qpat_x_assum `run_inst_seq _ s = OK t` mp_tac >> pure_asm_rewrite_tac [] >>
  disch_then (mp_then Any strip_assume_tac run_inst_seq_append_ok) >>
  rename1 `run_inst_seq (emitted_insts sa c1) s = OK s1` >>
  qpat_x_assum `run_inst_seq (_ ++ _) _ = OK t`
    (mp_then Any strip_assume_tac run_inst_seq_append_ok) >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  qpat_x_assum `run_inst_seq (_ ++ _) _ = OK t`
    (mp_then Any strip_assume_tac run_inst_seq_append_ok) >>
  rename1 `run_inst_seq (emitted_insts c2 c3) s2 = OK s3` >>
  `s2.vs_inst_idx = s.vs_inst_idx /\ s3.vs_inst_idx = s.vs_inst_idx /\
    t.vs_inst_idx = s.vs_inst_idx` by
    (imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
     gvs[run_inst_seq_def, AllCaseEqs()] >>
     imp_res_tac step_inst_base_preserves_inst_idx >>
     gvs[mk_inst_def, is_terminator_def]) >>
  drule_all emit_calldata_load_endpoint_ptr_origin_core >>
  disch_then (qspecl_then [`G`,`ARB`,`ARB`,`PG`,`ARB`] mp_tac) >>
  strip_tac >>
  suspend "segments"
QED

Resume source_bulk_count_guard_origin[segments]:
  rename1 `op_taint u1 cnt = {}` >> rename1 `op_prov H1 cnt = NONE` >>
  `?vars1. s1 = s with vs_vars := vars1` by
    (qpat_assum `emit_op CALLDATALOAD _ _ = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     qpat_x_assum `run_inst_seq (emitted_insts sa c1) s = _` mp_tac >>
     simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_read1_def, AllCaseEqs(), update_var_def] >> metis_tac[]) >>
  `?b. eval_operand cnt s1 = SOME b` by
    (qpat_assum `emit_op GT _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     qpat_x_assum `run_inst_seq (emitted_insts c1 c2) s1 = _` mp_tac >>
     simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure2_def, AllCaseEqs()] >> metis_tac[]) >>
  `run_inst_seq (emitted_insts c1 c2)
    (s1 with vs_inst_idx := LENGTH c1.cs_current_insts) =
    OK (s2 with vs_inst_idx := LENGTH c1.cs_current_insts)` by
    (qpat_assum `emit_op GT _ _ = _` (mp_then Any mp_tac emit_op_run_pc) >>
     simp[is_terminator_def, exec_result_map_def]) >>
  `eval_operand cnt (s1 with vs_inst_idx := LENGTH c1.cs_current_insts) = SOME b` by
    (Cases_on `cnt` >> gvs[eval_operand_def, lookup_var_def]) >>
  qpat_x_assum `run_inst_seq (emitted_insts c1 c2) s1 = _` kall_tac >>
  drule_all source_bulk_compare_origin >>
  disch_then (qspecl_then [`PG`,`H1`] mp_tac) >> strip_tac >>
  rename1 `op_taint u2 cmp = {}` >> rename1 `op_prov H2 cmp = NONE` >>
  `run_inst_seq (emitted_insts c2 c3)
    (s2 with vs_inst_idx := LENGTH c2.cs_current_insts) =
    OK (s3 with vs_inst_idx := LENGTH c2.cs_current_insts)` by
    (qpat_assum `emit_op ISZERO _ _ = _` (mp_then Any mp_tac emit_op_run_pc) >>
     simp[is_terminator_def, exec_result_map_def]) >>
  qpat_x_assum `run_inst_seq (emitted_insts c2 c3) s2 = _` kall_tac >>
  drule_all source_bulk_iszero_origin >>
  disch_then (qspec_then `PG` mp_tac) >> strip_tac >>
  rename1 `op_taint u3 ok = {}` >> rename1 `op_prov H3 ok = NONE` >>
  `run_inst_seq (emitted_insts c3 sb)
    (s3 with vs_inst_idx := LENGTH c3.cs_current_insts) =
    OK (t with vs_inst_idx := LENGTH c3.cs_current_insts)` by
    (qpat_assum `emit_void ASSERT _ _ = _`
      (mp_then Any strip_assume_tac emitted_insts_emit_void) >>
     simp[run_inst_seq_inst_idx, mk_inst_def, is_terminator_def, exec_result_map_def]) >>
  qpat_x_assum `run_inst_seq (emitted_insts c3 sb) s3 = _` kall_tac >>
  drule_all source_bulk_assert_origin >> disch_then (qspec_then `PG` mp_tac) >>
  strip_tac >> suspend "frames"
QED

Resume source_bulk_count_guard_origin[frames]:
  `s2 = s1 with vs_vars := vars /\ s3 = s2 with vs_vars := vars' /\ t = s3` by
    (qpat_x_assum `s2 with vs_inst_idx := _ = _` mp_tac >>
     qpat_x_assum `s3 with vs_inst_idx := _ = _` mp_tac >>
     qpat_x_assum `t with vs_inst_idx := _ = _` mp_tac >>
     simp[venom_state_component_equality]) >>
  `sa.cs_next_var <= c1.cs_next_var /\ c1.cs_next_var <= c2.cs_next_var` by
    metis_tac[ci_mono_emit_op, ci_mono_def, pairTheory.SND] >>
  `!x. not_fresh_at sa x ==> not_fresh_at c1 x /\ not_fresh_at c2 x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `!x. cnt = Var x ==> not_fresh_at c1 x` by
    (qpat_assum `emit_op CALLDATALOAD _ sa = _`
      (mp_then Any mp_tac abi_decoder_operand_live_emit) >>
     Cases_on `cnt` >> simp[calldata_operand_live_not_fresh]) >>
  `!x. cnt = Var x ==> not_fresh_at c2 x` by
    (rpt strip_tac >> `not_fresh_at c1 x` by metis_tac[] >>
     gvs[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  qexistsl_tac [`H3`,`u3`] >>
  conj_tac >- (Cases_on `cnt` >> gvs[op_taint_def] >> metis_tac[]) >>
  conj_tac >- (Cases_on `cnt` >> gvs[op_prov_def] >> metis_tac[]) >>
  conj_tac >- (qexists_tac `vars'` >> simp[]) >>
  simp[] >>
  conj_tac >- (fs[lookup_var_def] >> rpt strip_tac >> metis_tac[]) >>
  suspend "joint"
QED

Resume source_bulk_count_guard_origin[joint]:
  rpt (qpat_x_assum `frag_exec_ptr _ _ _ _ _ _ _ _` kall_tac) >>
  rpt (qpat_x_assum `!x. not_fresh_at _ x ==> _` kall_tac) >>
  `cs_extends sa c1 /\ cs_extends c1 c2 /\ cs_extends c2 c3 /\ cs_extends c3 sb` by
    (rpt conj_tac >> irule cs_extends_same_block >> fs[inst_extends_def] >>
     metis_tac[emit_op_same_blocks, emit_void_same_blocks, same_blocks_def]) >>
  `c1.cs_current_bb = sa.cs_current_bb /\
   c2.cs_current_bb = sa.cs_current_bb /\ c3.cs_current_bb = sa.cs_current_bb` by
    (imp_res_tac emit_op_same_blocks >> gvs[same_blocks_def]) >>
  rpt gen_tac >> strip_tac >>
  `fn_has_code sa c1 func /\ fn_has_code c1 c2 func /\
   fn_has_code c2 c3 func /\ fn_has_code c3 sb func` by
    (`cs_extends c2 sb` by metis_tac[cs_extends_trans] >>
     `cs_extends c1 sb` by metis_tac[cs_extends_trans] >>
     drule_all (Q.SPECL [`sa`,`c1`,`sb`,`func`] fn_has_code_split) >> strip_tac >>
     drule_all (Q.SPECL [`c1`,`c2`,`sb`,`func`] fn_has_code_split) >> strip_tac >>
     drule_all (Q.SPECL [`c2`,`c3`,`sb`,`func`] fn_has_code_split) >> simp[]) >>
  gvs[] >>
  rpt (qpat_x_assum `run_inst_seq _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `emit_op _ _ _ = _` kall_tac) >>
  qpat_x_assum `emit_void _ _ _ = _` kall_tac >>
  `allocas_from lower (s with vs_vars := vars1) /\
   allocas_from lower (s with vs_vars := vars) /\
   allocas_from lower (s with vs_vars := vars')` by (fs[allocas_from_def] >> metis_tac[]) >>
  qpat_x_assum `!D lower explicit ctx func. fn_has_code sa c1 func /\ _ ==> _`
    (drule_all_then (qspecl_then [`D`,`explicit`] assume_tac)) >>
  qpat_x_assum `!D lower explicit ctx func. fn_has_code c1 c2 func /\ _ ==> _`
    (drule_all_then (qspecl_then [`D`,`explicit`] assume_tac)) >>
  qpat_x_assum `!D lower explicit ctx func. fn_has_code c2 c3 func /\ _ ==> _`
    (drule_all_then (qspecl_then [`D`,`explicit`] assume_tac)) >>
  qpat_x_assum `!D lower explicit ctx func. fn_has_code c3 sb func /\ _ ==> _`
    (drule_all_then (qspecl_then [`D`,`explicit`] assume_tac)) >>
  qpat_assum `gas_origin_ptr_path _ (s,G,tn) [] _`
    (mp_then Any mp_tac gas_origin_ptr_path_append) >> simp[NoAsms] >>
  disch_then drule >> simp[NoAsms] >>
  disch_then (mp_then Any mp_tac gas_origin_ptr_path_append) >> simp[NoAsms] >>
  disch_then drule >> simp[NoAsms] >>
  disch_then (mp_then Any mp_tac gas_origin_ptr_path_append) >> simp[NoAsms] >>
  disch_then drule >> simp[]
QED

Finalise source_bulk_count_guard_origin

Theorem source_owned_primitive_decoder_ptr:
  abi_decoder_coherent ce env sf ty tv /\
  ((?clamp. type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\ is_word_type ty) \/
   (?m. type_to_abi_dec_info sf ce ty = DecBytestring m)) /\
  compile_abi_decode_to_buf (Var child) childsrc CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
  value_has_type tv v /\
  vyper_to_abi env ty v = SOME av /\
  mem_bytes_at srcpos (LENGTH (enc (vyper_to_abi_type env ty) av))
    r.vs_call_ctx.cc_calldata = enc (vyper_to_abi_type env ty) av /\
  srcpos + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
  eval_operand childsrc r = SOME (n2w srcpos) /\
  lookup_var child r = SOME (n2w e) /\ lookup_var root r = SOME (n2w d) /\
  abi_decoder_operand_live middle.cs_next_var childsrc /\
  abi_decoder_operand_live middle.cs_next_var (Var child) /\
  abi_decoder_operand_live middle.cs_next_var (Var root) /\
  ptr_covers G tn child r (type_memory_size tv) /\
  ptr_covers G tn root r outsz /\ op_taint tn childsrc = {} /\ op_prov G childsrc = NONE /\
  alloca_inv r /\ alloca_frontier_inv ctx fn site r /\
  unit_alloca_budget ctx < dimword (:256) /\
  FLOOKUP r.vs_allocas oid = SOME (base_addr,owner_cap) /\
  (oid < middle.cs_next_id \/ end_st.cs_next_id <= oid) /\
  base_addr <= e /\ e + type_memory_size tv <= base_addr + owner_cap /\
  e + type_memory_size tv < dimword (:256) /\
  (!id p k. middle.cs_next_id <= id /\ id < end_st.cs_next_id /\
    FLOOKUP r.vs_allocas id = SOME (p,k) ==>
    k = 32 /\ p < dimword (:256) /\ p+32 <= r.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  fn_has_code middle end_st fn /\ fn_inst_ids_distinct fn /\
  (middle.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  end_st.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit r /\
  allocas_from lower r /\ lower <= r.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~r.vs_halted /\ r.vs_current_bb = middle.cs_current_bb /\
  r.vs_inst_idx = LENGTH middle.cs_current_insts ==>
  ?t H u.
    abi_decode_sim ctx fn r t /\
    gas_path_mem ctx fn r 0 (OK t) /\
    (!D explicit. gas_origin_ptr_path (D, lower, explicit, ctx, fn, PG) (r, G, tn) [] (OK t, H, u)) /\
    ~t.vs_halted /\ t.vs_current_bb = end_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH end_st.cs_current_insts /\ fresh_vars_wrt limit t /\
    val_in_memory tv v e t.vs_memory /\
    (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
      val_in_memory tv v e mem) /\
    abi_decode_footprint_frame [(e,type_memory_size tv)] r t /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\ allocas_from lower t /\
    r.vs_alloca_next <= t.vs_alloca_next /\
    FLOOKUP t.vs_allocas oid = SOME (base_addr,owner_cap) /\
    (!id p k. FLOOKUP r.vs_allocas id = SOME (p,k) ==>
      FLOOKUP t.vs_allocas id = SOME (p,k)) /\
    (!id. id < middle.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP r.vs_allocas id) /\
    (!id p k. middle.cs_next_id <= id /\ id < end_st.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (p,k) ==>
      k = 32 /\ p < dimword (:256) /\ p+32 <= t.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    ptr_covers H u child t (type_memory_size tv) /\ ptr_covers H u root t outsz /\
    (!op. abi_decoder_operand_live middle.cs_next_var op ==>
      eval_operand op t = eval_operand op r) /\
    (!x. not_fresh_at middle x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint u (Var x) = op_taint tn (Var x)) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!D. (!fuel. ptr_safe_run D lower fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lower fuel ctx fn PG G tn r) /\
    t.vs_accounts = r.vs_accounts /\ t.vs_transient = r.vs_transient /\
    t.vs_logs = r.vs_logs /\ t.vs_outcomes = r.vs_outcomes /\
    t.vs_requests = r.vs_requests /\
    t.vs_pending_deletions = r.vs_pending_deletions /\ t.vs_tx_ctx = r.vs_tx_ctx /\
    t.vs_block_ctx = r.vs_block_ctx /\ t.vs_fmp = r.vs_fmp /\
    t.vs_gas_readings = r.vs_gas_readings
Proof
  disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  `evaluate_type env ty = SOME tv /\
   type_memory_size tv = type_memory_bytes ce ty` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  `((?clamp. type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
       is_word_type ty /\ type_memory_size tv = 32) \/
    (?m. type_to_abi_dec_info sf ce ty = DecBytestring m /\
       type_memory_size tv = abi_decode_bytes_copy_size m /\ m < dimword (:256)))` by
    (qpat_x_assum `(?clamp. _ /\ is_word_type ty) \/ _` strip_assume_tac
     >- metis_tac[abi_word_type_size] >>
     drule_all coherent_source_bytes_representation >> strip_tac >>
     disj2_tac >> qexists `m` >>
     `m < dimword (:256)` by
       (mp_tac (Q.INST [`n` |-> `m`] abi_decoder_bytes_copy_size) >> decide_tac) >>
     metis_tac[]) >> (
  `type_memory_size tv < dimword (:256) /\ e < dimword (:256) /\
    srcpos < dimword (:256)` by decide_tac >>
  `not_fresh_at middle child /\ not_fresh_at middle root /\
   (!x. childsrc = Var x ==> not_fresh_at middle x)` by
    (conj_tac >- metis_tac[calldata_operand_live_not_fresh] >>
     conj_tac >- metis_tac[calldata_operand_live_not_fresh] >>
     rpt strip_tac >>
     metis_tac[calldata_operand_live_not_fresh]) >>
  `eval_operand (Var child) r = SOME (n2w e)` by simp[eval_operand_def] >>
  `?t H u.
    run_inst_seq (emitted_insts middle end_st) r = OK (t with vs_inst_idx := r.vs_inst_idx) /\
    ~t.vs_halted /\ t.vs_current_bb = end_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ptr_covers H u child t (type_memory_size tv) /\
    val_in_memory tv v e t.vs_memory /\
    (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==> val_in_memory tv v e mem) /\
    abi_decode_frame e (type_memory_size tv) r t /\ fresh_vars_wrt limit t /\
    t.vs_allocas = r.vs_allocas /\ t.vs_alloca_next = r.vs_alloca_next /\
    (!op w. (!x. op = Var x ==> not_fresh_at middle x) /\ eval_operand op r = SOME w ==>
      eval_operand op t = SOME w) /\
    (!x. not_fresh_at middle x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint u (Var x) = op_taint tn (Var x)) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!D. (!fuel. ptr_safe_run D lower fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lower fuel ctx fn PG G tn r)` by
    (irule source_primitive_decoder_reentry_ptr >>
     metis_tac[]) >>
  `base_addr + owner_cap <= r.vs_alloca_next` by
    metis_tac[alloca_inv_def, alloca_next_valid_def] >>
  `e + type_memory_size tv <= r.vs_alloca_next` by decide_tac >>
  `gas_path_mem ctx fn r 0
     (OK ((t with vs_inst_idx := r.vs_inst_idx) with
       vs_inst_idx := LENGTH end_st.cs_current_insts))` by
    (irule source_primitive_run_gas_path_mem >>
     conj_tac >- simp[] >>
     qexistsl [`child`, `type_to_abi_dec_info sf ce ty`, `e`, `middle`,
       `childsrc`, `type_memory_size tv`] >> metis_tac[]) >>
  `gas_path_mem ctx fn r 0 (OK t)` by
    (qpat_x_assum `gas_path_mem _ _ _ _ _` mp_tac >>
     qpat_x_assum `t.vs_inst_idx = _` (fn th => simp[GSYM th])) >>
  drule decoder_primitive_code_shape >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  `abi_decode_sim ctx fn r t` by
    (drule_all abi_decoder_run_sequence_reach >>
     qpat_x_assum `t.vs_inst_idx = _` (fn th => simp[GSYM th])) >>
  `!op. abi_decoder_operand_live middle.cs_next_var op ==>
    eval_operand op t = eval_operand op r` by
    (rpt strip_tac >>
     drule decoder_primitive_old_operand >>
     disch_then (qspecl_then [`t with vs_inst_idx := r.vs_inst_idx`,`r`,`op`] mp_tac) >>
     (impl_tac >- metis_tac[]) >>
     simp[eval_operand_def, lookup_var_def]) >>
  drule_all decoder_run_world_frame >>
  simp_tac (srw_ss()) [] >> strip_tac >>
  qexistsl [`t`,`H`,`u`] >>
  pure_asm_rewrite_tac [] >>
  simp_tac bool_ss [] >>
  conj_tac >- metis_tac[abi_decode_frame_footprint] >>
  conj_tac >-
    (qpat_x_assum `alloca_inv r` mp_tac >>
     pure_asm_rewrite_tac [alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
     simp_tac bool_ss []) >>
  conj_tac >-
    (qpat_x_assum `alloca_frontier_inv ctx fn site r` mp_tac >>
     pure_asm_rewrite_tac [alloca_frontier_inv_def, remaining_alloca_budget_def] >>
     simp_tac bool_ss []) >>
  conj_tac >-
    (qpat_x_assum `allocas_from lower r` mp_tac >>
     pure_asm_rewrite_tac [allocas_from_def] >> simp_tac bool_ss []) >>
  simp_tac bool_ss [LESS_EQ_REFL] >>
  `lookup_var root t = lookup_var root r` by
    (qpat_x_assum `!op. abi_decoder_operand_live _ op ==> _` (qspec_then `Var root` mp_tac) >>
     simp[eval_operand_def]) >>
  qpat_x_assum `ptr_covers G tn root r outsz` mp_tac >>
  pure_rewrite_tac[ptr_covers_def] >>
  `FLOOKUP H root = FLOOKUP G root /\ op_taint u (Var root) = op_taint tn (Var root)` by
    metis_tac[] >>
  pure_asm_rewrite_tac[] >> simp_tac bool_ss [])
QED

Theorem source_owned_bulk_array_ptr:
  abi_decoder_coherent ce env sf (ArrayT ety (Dynamic maxn)) tv /\
  ~is_abi_dynamic ce.ce_struct_fields ety /\
  ~dec_info_needs_clamp (type_to_abi_dec_info sf ce ety) /\
  compile_abi_decode_to_buf (Var child) childsrc CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce (ArrayT ety (Dynamic maxn))) middle = ((),end_st) /\
  value_has_type tv v /\
  vyper_to_abi env (ArrayT ety (Dynamic maxn)) v = SOME av /\
  mem_bytes_at srcpos (LENGTH (enc (vyper_to_abi_type env (ArrayT ety (Dynamic maxn))) av))
    r.vs_call_ctx.cc_calldata = enc (vyper_to_abi_type env (ArrayT ety (Dynamic maxn))) av /\
  srcpos + LENGTH (enc (vyper_to_abi_type env (ArrayT ety (Dynamic maxn))) av) < dimword (:256) /\
  eval_operand childsrc r = SOME (n2w srcpos) /\
  lookup_var child r = SOME (n2w e) /\ lookup_var root r = SOME (n2w d) /\
  abi_decoder_operand_live middle.cs_next_var childsrc /\
  abi_decoder_operand_live middle.cs_next_var (Var child) /\
  abi_decoder_operand_live middle.cs_next_var (Var root) /\
  ptr_covers G tn child r (type_memory_size tv) /\
  ptr_covers G tn root r outsz /\ op_taint tn childsrc = {} /\ op_prov G childsrc = NONE /\
  alloca_inv r /\ alloca_frontier_inv ctx fn site r /\
  unit_alloca_budget ctx < dimword (:256) /\
  FLOOKUP r.vs_allocas oid = SOME (base_addr,owner_cap) /\
  (oid < middle.cs_next_id \/ end_st.cs_next_id <= oid) /\
  base_addr <= e /\ e + type_memory_size tv <= base_addr + owner_cap /\
  e + type_memory_size tv < dimword (:256) /\
  (!id p k. middle.cs_next_id <= id /\ id < end_st.cs_next_id /\
    FLOOKUP r.vs_allocas id = SOME (p,k) ==>
    k = 32 /\ p < dimword (:256) /\ p+32 <= r.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  fn_has_code middle end_st fn /\ fn_inst_ids_distinct fn /\
  (middle.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  end_st.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit r /\
  allocas_from lower r /\ lower <= r.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~r.vs_halted /\ r.vs_current_bb = middle.cs_current_bb /\
  r.vs_inst_idx = LENGTH middle.cs_current_insts ==>
  ?t H u.
    abi_decode_sim ctx fn r t /\
    gas_path_mem ctx fn r 0 (OK t) /\
    (!D explicit. gas_origin_ptr_path (D, lower, explicit, ctx, fn, PG) (r, G, tn) [] (OK t, H, u)) /\
    ~t.vs_halted /\ t.vs_current_bb = end_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH end_st.cs_current_insts /\ fresh_vars_wrt limit t /\
    val_in_memory tv v e t.vs_memory /\
    (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
      val_in_memory tv v e mem) /\
    abi_decode_footprint_frame [(e,type_memory_size tv)] r t /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\ allocas_from lower t /\
    r.vs_alloca_next <= t.vs_alloca_next /\
    FLOOKUP t.vs_allocas oid = SOME (base_addr,owner_cap) /\
    (!id p k. FLOOKUP r.vs_allocas id = SOME (p,k) ==>
      FLOOKUP t.vs_allocas id = SOME (p,k)) /\
    (!id. id < middle.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP r.vs_allocas id) /\
    (!id p k. middle.cs_next_id <= id /\ id < end_st.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (p,k) ==>
      k = 32 /\ p < dimword (:256) /\ p+32 <= t.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    ptr_covers H u child t (type_memory_size tv) /\ ptr_covers H u root t outsz /\
    (!op. abi_decoder_operand_live middle.cs_next_var op ==>
      eval_operand op t = eval_operand op r) /\
    (!x. not_fresh_at middle x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint u (Var x) = op_taint tn (Var x)) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!D. (!fuel. ptr_safe_run D lower fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lower fuel ctx fn PG G tn r) /\
    t.vs_accounts = r.vs_accounts /\ t.vs_transient = r.vs_transient /\
    t.vs_logs = r.vs_logs /\ t.vs_outcomes = r.vs_outcomes /\
    t.vs_requests = r.vs_requests /\
    t.vs_pending_deletions = r.vs_pending_deletions /\ t.vs_tx_ctx = r.vs_tx_ctx /\
    t.vs_block_ctx = r.vs_block_ctx /\ t.vs_fmp = r.vs_fmp /\
    t.vs_gas_readings = r.vs_gas_readings /\
    t.vs_allocas = r.vs_allocas /\ t.vs_alloca_next = r.vs_alloca_next
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all source_bulk_array_layout >> strip_tac >>
  `evaluate_type env (ArrayT ety (Dynamic maxn)) = SOME tv` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  `type_to_abi_dec_info sf ce (ArrayT ety (Dynamic maxn)) =
    DecDynArray (type_to_abi_dec_info sf ce ety) (abi_embedded_static_size ce.ce_struct_fields ety)
      (type_memory_size etv) F maxn` by
    simp[exprLoweringTheory.type_to_abi_dec_info_def] >>
  `0 < type_slot_size etv /\
   1 + maxn * type_slot_size etv < dimword (:256)` by
    (qpat_x_assum `evaluate_type env (ArrayT _ _) = _` mp_tac >>
     pure_asm_rewrite_tac [Once vyperValueTheory.evaluate_type_def] >>
     simp_tac (srw_ss()) [LET_THM, AllCaseEqs(), vyperValueTheory.type_slot_size_def]) >>
  `maxn <= maxn * type_slot_size etv` by
    (Cases_on `type_slot_size etv` >- decide_tac >> simp[MULT_SUC]) >>
  `maxn < dimword (:256)` by decide_tac >>
  `type_memory_size tv = 32 + maxn * type_memory_size etv` by
    metis_tac[valueEncodingTheory.type_memory_size_def] >>
  `LENGTH vs * type_memory_size etv <= maxn * type_memory_size etv` by
    simp[LE_MULT_RCANCEL] >>
  `32 + LENGTH vs * type_memory_size etv <= type_memory_size tv /\
   e+32 < dimword (:256) /\ LENGTH vs * type_memory_size etv < dimword (:256)` by
    decide_tac >>
  `LENGTH (enc (vyper_to_abi_type env (ArrayT ety (Dynamic maxn))) av) =
    32 + LENGTH vs * type_memory_size etv` by
    (pure_asm_rewrite_tac [listTheory.LENGTH_APPEND] >> simp_tac (srw_ss()) []) >>
  `srcpos+32 < dimword (:256) /\ srcpos < dimword (:256)` by decide_tac >>
  `mem_word_at srcpos r.vs_call_ctx.cc_calldata = n2w (LENGTH vs) /\
   mem_bytes_at (srcpos+32) (LENGTH vs * type_memory_size etv)
     r.vs_call_ctx.cc_calldata = FLAT (MAP (enc (vyper_to_abi_type env ety)) avs)` by
    (irule abiDecoderBulkTheory.static_dynarray_source_windows >>
     pure_asm_rewrite_tac [] >>
     conj_tac >-
       (qpat_x_assum `mem_bytes_at srcpos _ _ = _` mp_tac >>
        pure_rewrite_tac [vyperABITheory.vyper_to_abi_type_def] >>
        pure_asm_rewrite_tac [] >> simp_tac bool_ss []) >>
     metis_tac[]) >>
  `abi_decode_load CALLDATALOAD (n2w srcpos : bytes32) r = n2w (LENGTH vs)` by
    (qpat_x_assum `mem_word_at srcpos _ = _` mp_tac >>
     simp_tac (srw_ss()) [abiDecoderContractTheory.abi_decode_load_def,
       abiDecoderContractTheory.abi_decode_source_def, valueEncodingDefsTheory.mem_word_at_def,
       valueEncodingDefsTheory.mem_bytes_at_def, wordsTheory.w2n_n2w] >>
     `srcpos MOD dimword (:256) = srcpos` by simp[] >>
     pure_asm_rewrite_tac [] >> simp_tac bool_ss []) >>
  `eval_operand (Var child) r = SOME (n2w e)` by simp[eval_operand_def] >>
  qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`
    (assume_tac o PURE_ONCE_REWRITE_RULE
      [exprLoweringTheory.type_to_abi_dec_info_def]) >>
  `compile_abi_decode_to_buf (Var child) childsrc CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray (type_to_abi_dec_info sf ce ety)
      (abi_embedded_static_size ce.ce_struct_fields ety) (type_memory_size etv) F maxn)
      middle = ((),end_st)` by metis_tac[] >>
  drule_all calldata_bulk_reentry_sequence >> strip_tac >>
  `base_addr + owner_cap <= r.vs_alloca_next` by
    metis_tac[alloca_inv_def, alloca_next_valid_def] >>
  `e + (32 + LENGTH vs * type_memory_size etv) <= r.vs_alloca_next /\
   e + (32 + LENGTH vs * type_memory_size etv) < dimword (:256)` by decide_tac >>
  `gas_path_mem ctx fn r 0
     (OK (t with vs_inst_idx := LENGTH end_st.cs_current_insts))` by
    (drule_all source_bulk_run_gas_path_mem >> simp_tac (srw_ss()) []) >>
  `not_fresh_at middle child /\ not_fresh_at middle root /\
   (!x. childsrc = Var x ==> not_fresh_at middle x)` by
    (conj_tac >- metis_tac[calldata_operand_live_not_fresh] >>
     conj_tac >- metis_tac[calldata_operand_live_not_fresh] >>
     rpt strip_tac >> metis_tac[calldata_operand_live_not_fresh]) >>
  drule_all calldata_bulk_decoder_endpoint_ptr_uniform >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `val_in_memory tv v e t.vs_memory` by
    (pure_asm_rewrite_tac [] >>
     irule static_dynarray_canonical_layout >> metis_tac[]) >>
  `!mem. mem_agree_outside u.t_mem t.vs_memory mem ==> val_in_memory tv v e mem` by
    (rpt strip_tac >> pure_asm_rewrite_tac [] >> irule clean_live_prefix_dynarray_robust >>
     metis_tac[vyperTypingTheory.all_have_type_EVERY]) >>
  `abi_decode_source_opcode CALLDATALOAD` by
    simp[abiDecoderContractTheory.abi_decode_source_opcode_def] >>
  drule_all abiDecoderBulkTheory.abi_decoder_bulk_shape >> strip_tac >>
  drule_all abi_decoder_bulk_allocation_shape >> strip_tac >>
  `inst_extends middle end_st` by
    (pure_asm_rewrite_tac [emitHelperPropsTheory.inst_extends_def,
       exprLoweringPropsTheory.emitted_insts_def] >>
     metis_tac[rich_listTheory.IS_PREFIX_APPEND, rich_listTheory.DROP_LENGTH_APPEND]) >>
  drule_all abi_decoder_run_sequence_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qpat_x_assum `t' = _` SUBST_ALL_TAC >>
  `t.vs_labels = r.vs_labels` by
    metis_tac[ctorAbiActualObservationsTheory.ctor_actual_sequence_labels] >>
  `!op. abi_decoder_operand_live middle.cs_next_var op ==>
    eval_operand op t = eval_operand op r` by
    (rpt strip_tac >> Cases_on `op` >>
     simp_tac (srw_ss()) [eval_operand_def] >>
     metis_tac[calldata_operand_live_not_fresh]) >>
  drule_all decoder_run_world_frame >> strip_tac >>
  `alloca_inv t` by
    (qpat_x_assum `alloca_inv r` mp_tac >>
     pure_asm_rewrite_tac [alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
     simp_tac bool_ss []) >>
  `alloca_frontier_inv ctx fn site t` by
    (qpat_x_assum `alloca_frontier_inv ctx fn site r` mp_tac >>
     pure_asm_rewrite_tac [alloca_frontier_inv_def, remaining_alloca_budget_def] >>
     simp_tac bool_ss []) >>
  `allocas_from lower (t with vs_inst_idx := LENGTH end_st.cs_current_insts)` by
    (qpat_x_assum `allocas_from lower r` mp_tac >>
     simp_tac (srw_ss()) [allocas_from_def] >> pure_asm_rewrite_tac [] >> simp_tac bool_ss []) >>
  `ptr_covers H u root t outsz` by
    (irule decoderGhostFramePtrTheory.ptr_covers_frame >> metis_tac[]) >>
  `abi_decode_frame e (type_memory_size tv) r t` by
    (irule abiDecoderFrameComposeTheory.abi_decode_frame_widen >>
     qexistsl [`e`,`32 + LENGTH vs * type_memory_size etv`] >>
     pure_asm_rewrite_tac [] >> decide_tac) >>
  `abi_decode_footprint_frame [(e,type_memory_size tv)] r
     (t with vs_inst_idx := LENGTH end_st.cs_current_insts)` by
    (simp_tac (srw_ss()) [GSYM abi_decode_frame_footprint,
       abiDecoderContractTheory.abi_decode_frame_def] >>
     metis_tac[abiDecoderContractTheory.abi_decode_frame_def]) >>
  qpat_x_assum `tv = _` SUBST_ALL_TAC >>
  qpat_x_assum `v = _` SUBST_ALL_TAC >>
  qexistsl [`t with vs_inst_idx := LENGTH end_st.cs_current_insts`,`H`,`u`] >>
  pure_asm_rewrite_tac [] >>
  simp_tac (srw_ss()) [loweringStateRelDefsTheory.fresh_vars_wrt_def,
    lookup_var_def, eval_operand_def] >>
  pure_asm_rewrite_tac [] >> simp_tac bool_ss [] >>
  conj_tac >- (qpat_assum `fresh_vars_wrt _ t` mp_tac >>
    simp_tac (srw_ss()) [loweringStateRelDefsTheory.fresh_vars_wrt_def]) >>
  simp_tac arith_ss [] >>
  conj_tac >- (qpat_x_assum `ptr_covers H u child t _` mp_tac >>
    pure_asm_rewrite_tac [] >> simp_tac arith_ss []) >>
  metis_tac[]
QED
