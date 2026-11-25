(* Paired memory and pointer certificates for successful primitive decoding. *)
Theory abiDecodePtrWordJoint
Ancestors
  abiEncoder abiDecoderClampedWord calldataClampPtr calldataWordLeaf entryHaltMem
  instSeqComposePtr decoderGhostFramePtr freshWrites fragGasCopyLoop fragGasCopySeqLiftProps
  bodyPtrBytestringBuiltinsUintGhost stmtReasonMemory fragExecPtr
  logAbiPrefixPtr assignTuplePtrLocalBytesCopy bodyPtrPrecompileBuiltinsRecoveryInput
  abiDecodePtrMemberFrame allocaFootprint abiDecoderReentry
  fragExec fragExecMem instIdxIndep exprLoweringProps emitHelperProps compileEnv
  venomInst venomState venomExecSemantics words list rich_list loweringStateRelDefs
  decoderSetupStepPtr reasonCopySourcePtr typedCopyPtr wordLoadStorePtr
  fragGasSeqPtr logInstSeqPtr ptrDiscipline bodyPtrDefs ghostPcTransportPtr
  finite_map string pred_set context venomInstProofs unitTransformDefs
  ptrSafeRun contextCodegenRel codegenRel memSafeRun arithmetic

Theorem allocated_word_decode_phases[local]:
  compile_abi_decode_to_buf (Var dst) pos MLOAD (Var src) hi
    (DecPrimWord clamp) sa = ((),sb) ==>
  ?addr value c1 c2 c3.
    emit_op ADD [Var src;pos] sa = (Var addr,c1) /\
    emit_op MLOAD [Var addr] c1 = (Var value,c2) /\
    compile_abi_clamp_basetype (Var value) clamp c2 = ((),c3) /\
    emit_void MSTORE [Var dst;Var value] c3 = ((),sb) /\
    cs_extends sa c1 /\ cs_extends c1 c2 /\
    cs_extends c2 c3 /\ cs_extends c3 sb /\
    sa.cs_next_var <= c1.cs_next_var /\ c1.cs_next_var <= c2.cs_next_var /\
    c2.cs_next_var <= c3.cs_next_var /\
    not_fresh_at c2 value /\
    emitted_insts sa sb = emitted_insts sa c1 ++ emitted_insts c1 c2 ++
      emitted_insts c2 c3 ++ emitted_insts c3 sb
Proof
  strip_tac >>
  Cases_on `emit_op ADD [Var src;pos] sa` >>
  rename1 `emit_op ADD [Var src;pos] sa = (addr,c1)` >>
  Cases_on `emit_op MLOAD [addr] c1` >>
  rename1 `emit_op MLOAD [addr] c1 = (value,c2)` >>
  Cases_on `compile_abi_clamp_basetype value clamp c2` >>
  rename1 `compile_abi_clamp_basetype value clamp c2 = (u,c3)` >>
  Cases_on `u` >>
  `emit_void MSTORE [Var dst;value] c3 = ((),sb)` by
    (qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
     simp[Once compile_abi_decode_to_buf_def, compile_abi_dec_addr_def,
          compile_abi_decode_static_def, comp_bind_def, comp_ignore_bind_def]) >>
  qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  qpat_assum `emit_op MLOAD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  `cs_extends sa c1 /\ cs_extends c1 c2` by
    metis_tac[exprSimAccountsTheory.emit_op_extends_next_var] >>
  drule calldata_clamp_instructions >> strip_tac >>
  drule emit_void_extends >> strip_tac >>
  `cs_extends c2 c3 /\ cs_extends c3 sb` by
    (conj_tac >> irule cs_extends_same_block >>
     fs[same_blocks_def, IS_PREFIX_APPEND]) >>
  `c2.cs_next_var <= c3.cs_next_var` by
    (qpat_assum `compile_abi_clamp_basetype _ _ _ = _`
       (mp_then Any (qspecl_then [`{}`,`UNIV`] mp_tac) abi_decode_clamp_scalar) >>
     simp[]) >>
  `emitted_insts sa sb = emitted_insts sa c1 ++ emitted_insts c1 c2 ++
      emitted_insts c2 c3 ++ emitted_insts c3 sb` by
    (`emitted_insts c2 sb = emitted_insts c2 c3 ++ emitted_insts c3 sb` by
       (irule emitted_insts_append >> simp[]) >>
     `emitted_insts c1 sb = emitted_insts c1 c2 ++ emitted_insts c2 sb` by
       (irule emitted_insts_append >> simp[APPEND_ASSOC]) >>
     `emitted_insts sa sb = emitted_insts sa c1 ++ emitted_insts c1 sb` by
       (irule emitted_insts_append >> simp[APPEND_ASSOC]) >> simp[]) >>
  gvs[not_fresh_at_def]
QED

(* The relative load leaves the destination and the source window intact.
   Only the cursor is advanced for the following clamp. *)
Theorem allocated_word_relative_load[local]:
  emit_op ADD [Var src;pos] sa = (Var addr,c1) /\
  emit_op MLOAD [Var addr] c1 = (Var value,c2) /\
  abi_decode_ptr_window G tn s src a n /\
  eval_operand pos s = SOME (n2w p) /\ op_taint tn pos = {} /\
  p+32 <= n /\ w2n a+n <= s.vs_alloca_next /\
  w2n a+p < dimword(:256) /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r G2 tn2.
    run_inst_seq (emitted_insts sa c1 ++ emitted_insts c1 c2) s = OK r /\
    run_inst_seq_mem_ok (emitted_insts sa c1 ++ emitted_insts c1 c2) s /\
    (!D. inst_seq_ptr D 0 ctx fn PG G tn
      (emitted_insts sa c1 ++ emitted_insts c1 c2) s G2 tn2) /\
    r.vs_inst_idx = s.vs_inst_idx /\ r.vs_halted = s.vs_halted /\
    r.vs_current_bb = s.vs_current_bb /\ c2.cs_current_bb = sa.cs_current_bb /\
    LENGTH c2.cs_current_insts = s.vs_inst_idx +
      LENGTH (emitted_insts sa c1 ++ emitted_insts c1 c2) /\
    r.vs_memory = s.vs_memory /\ r.vs_allocas = s.vs_allocas /\
    r.vs_alloca_next = s.vs_alloca_next /\
    lookup_var value r = SOME (mload (w2n a+p) s) /\
    op_taint tn2 (Var value) = {} /\ op_prov G2 (Var value) = NONE /\
    tn2.t_mem = tn.t_mem /\ tn2.t_stor = tn.t_stor /\
    tn2.t_trans = tn.t_trans /\ tn2.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x r = lookup_var x s /\
      FLOOKUP G2 x = FLOOKUP G x /\ op_taint tn2 (Var x) = op_taint tn (Var x)) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp r)
Proof
  strip_tac >>
  qhdtm_assum `abi_decode_ptr_window`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [abi_decode_ptr_window_def]) >>
  qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  qpat_assum `emit_op MLOAD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  `!x. not_fresh_at sa x ==> x <> addr /\ x <> value` by
    (rpt strip_tac >> gvs[not_fresh_at_def]) >>
  `c2.cs_current_bb = sa.cs_current_bb` by
    metis_tac[emit_op_same_blocks, same_blocks_def] >>
  qabbrev_tac `i = mk_inst sa.cs_next_id ADD [Var src;pos] [addr]` >>
  qabbrev_tac `j = mk_inst c1.cs_next_id MLOAD [Var addr] [value]` >>
  qabbrev_tac `w = a + (n2w p:256 word)` >>
  `p < dimword(:256)` by decide_tac >>
  `w2n w = w2n a+p` by simp[Abbr `w`, w2n_add_2, w2n_n2w, LESS_MOD] >>
  qabbrev_tac `u = update_var addr w s` >>
  `step_inst_base i s = OK u` by
    simp[Abbr `i`, Abbr `u`, Abbr `w`, step_inst_base_opcode_eqs, mk_inst_def,
         exec_pure2_def, eval_operand_def] >>
  qabbrev_tac `G1 = step_prov PG G i u` >>
  qabbrev_tac `tn1 = step_taint i s u tn` >>
  `?b cap. FLOOKUP G src = SOME (b,cap)` by fs[ptr_covers_def] >>
  `FLOOKUP G1 addr = FLOOKUP G src` by
    simp[Abbr `G1`, Abbr `i`, step_prov_def, out_prov_def, first_prov_def,
         op_prov_def, set_prov_def, mk_inst_def, FLOOKUP_UPDATE] >>
  `lookup_var addr u = SOME w` by simp[Abbr `u`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `op_taint tn (Var src) = {}` by fs[ptr_covers_def] >>
  `op_taint tn1 (Var addr) = {} /\ tn1.t_mem = tn.t_mem /\
   tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans /\
   (!x. x <> addr ==> FLOOKUP G1 x = FLOOKUP G x /\
      op_taint tn1 (Var x) = op_taint tn (Var x))` by
    simp[Abbr `G1`, Abbr `tn1`, Abbr `i`, Abbr `u`, copy_len_binop_ghost_frame] >>
  `tn1.t_imm = tn.t_imm` by
    simp[Abbr `tn1`, Abbr `i`, step_taint_def, set_var_taint_def,
         adopt_reset_def, imm_taint_def, mk_inst_def] >>
  `ptr_covers G tn src s (p+32)` by (irule ptr_covers_mono >> metis_tac[]) >>
  `ptr_covers G1 tn1 addr u 32` by
    (irule ptr_covers_offset_transport >> metis_tac[]) >>
  `!k. w2n w <= k /\ k < w2n w+32 ==> k NOTIN tn1.t_mem` by
    (simp[] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  qabbrev_tac `r = update_var value (mload (w2n w) u) u` >>
  `step_inst_base j u = OK r` by
    (simp[Abbr `j`, Abbr `r`, step_inst_base_opcode_eqs, mk_inst_def,
          exec_read1_def, eval_operand_def] >> gvs[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     simp[Abbr `u`, update_var_def, allocas_below_fmp_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp r` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp u` mp_tac >>
     simp[Abbr `r`, update_var_def, allocas_below_fmp_def]) >>
  qabbrev_tac `G2 = step_prov PG G1 j r` >>
  qabbrev_tac `tn2 = step_taint j u r tn1` >>
  `op_taint tn2 (Var value) = {} /\ op_prov G2 (Var value) = NONE /\
   r.vs_memory = u.vs_memory /\ r.vs_call_ctx = u.vs_call_ctx /\
   r.vs_allocas = u.vs_allocas /\ tn2.t_mem = tn1.t_mem /\
   tn2.t_stor = tn1.t_stor /\ tn2.t_trans = tn1.t_trans /\ tn2.t_imm = tn1.t_imm /\
   (!x. x <> value ==> lookup_var x r = lookup_var x u /\
      FLOOKUP G2 x = FLOOKUP G1 x /\ op_taint tn2 (Var x) = op_taint tn1 (Var x))` by
    (irule setup_mload_ghost >>
     qexistsl [`PG`,`w`,`c1.cs_next_id`,`addr`] >>
     simp[Abbr `G2`, Abbr `tn2`, Abbr `j`, Abbr `r`]) >>
  `run_inst_seq (emitted_insts sa c1) s = OK u` by
    (unabbrev_all_tac >> gvs[run_inst_seq_def]) >>
  qexistsl [`r`,`G2`,`tn2`] >>
  conj_tac >- (unabbrev_all_tac >> gvs[run_inst_seq_def]) >>
  conj_tac >-
    (`run_inst_seq_mem_ok (emitted_insts sa c1) s` by
       (irule emit_op_mem_ok >> goal_assum (drule_at Any) >>
        simp[inst_mem_below_frontier_def, inst_dload_in_section_def, mk_inst_def,
             source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
     `run_inst_seq_mem_ok (emitted_insts c1 c2) u` by
       (irule emit_mload_mem_ok >> goal_assum (drule_at Any) >>
        qexists `w` >> simp[eval_operand_def] >>
        fs[Abbr `u`, update_var_def] >> decide_tac) >>
     irule bodyLiteralBufferMemoryTheory.run_inst_seq_mem_ok_append_run >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexists `u` >> conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >-
    (gen_tac >> irule inst_seq_ptr_append_run >>
     conj_tac >- simp[mk_inst_def, is_terminator_def] >>
     qexistsl [`G1`,`u`,`tn1`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     `!k. step_inst_base j (u with vs_inst_idx := k) = OK (r with vs_inst_idx := k)` by
       (gen_tac >> `~is_terminator j.inst_opcode` by simp[Abbr `j`, mk_inst_def, is_terminator_def] >>
        simp[step_inst_inst_idx_indep, exec_result_map_def]) >>
     unabbrev_all_tac >> gvs[inst_seq_ptr_def] >>
     conj_tac >- (irule ptr_inst_ok_copy_len_binop >> simp[]) >>
     irule ptr_inst_ok_mload >> simp[]) >>
  simp[Abbr `r`, Abbr `u`, lookup_var_update_var, ssaOperandFrameTheory.mload_update_var,
       mload_def, update_var_def, FUPDATE_LIST_THM, FLOOKUP_UPDATE, ADD_ASSOC] >>
  rpt strip_tac >> res_tac >> gvs[]
QED

(* Transport the successful raw clamp cut to the cursor of the pointer run. *)
Theorem allocated_word_clamp_cut[local]:
  compile_abi_clamp_basetype (Var value) clamp c2 = ((),c3) /\
  lookup_var value r = SOME w /\ op_taint tn2 (Var value) = {} /\
  op_prov G2 (Var value) = NONE /\ not_fresh_at c2 value /\
  run_inst_seq (emitted_insts c2 c3) r = OK u /\
  fn_has_code c2 c3 fn /\ fn_inst_ids_distinct fn /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp r) /\ ~r.vs_halted /\ r.vs_current_bb = c2.cs_current_bb ==>
  ?G3 tn3.
    (!D. inst_seq_ptr D 0 ctx fn PG G2 tn2 (emitted_insts c2 c3)
      (r with vs_inst_idx := LENGTH c2.cs_current_insts) G3 tn3) /\
    run_inst_seq_mem_ok (emitted_insts c2 c3) r /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
                i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts c2 c3) /\
    c3.cs_current_bb = c2.cs_current_bb /\
    LENGTH c3.cs_current_insts = LENGTH c2.cs_current_insts + LENGTH (emitted_insts c2 c3) /\
    u.vs_allocas = r.vs_allocas /\ u.vs_alloca_next = r.vs_alloca_next /\
    u.vs_memory = r.vs_memory /\ u.vs_current_bb = r.vs_current_bb /\ ~u.vs_halted /\
    (!x z. not_fresh_at c2 x /\ lookup_var x r = SOME z ==> lookup_var x u = SOME z) /\
    (!x. not_fresh_at c2 x ==>
      FLOOKUP G3 x = FLOOKUP G2 x /\ op_taint tn3 (Var x) = op_taint tn2 (Var x)) /\
    tn3.t_mem = tn2.t_mem /\ tn3.t_stor = tn2.t_stor /\
    tn3.t_trans = tn2.t_trans /\ tn3.t_imm = tn2.t_imm /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u)
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts c2 c3) /\
   c3.cs_current_bb = c2.cs_current_bb /\
   LENGTH c3.cs_current_insts = LENGTH c2.cs_current_insts + LENGTH (emitted_insts c2 c3)` by
    (drule calldata_clamp_instructions >> rpt strip_tac >>
     gvs[mk_inst_def, is_terminator_def] >> Cases_on `signed` >> gvs[mk_inst_def, is_terminator_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c2 c3)` by fs[EVERY_MEM] >>
  qabbrev_tac `r' = r with vs_inst_idx := LENGTH c2.cs_current_insts` >>
  `run_inst_seq (emitted_insts c2 c3) r' =
    OK (u with vs_inst_idx := LENGTH c2.cs_current_insts)` by
    simp[Abbr `r'`, run_inst_seq_inst_idx, exec_result_map_def] >>
  `eval_operand (Var value) r' = SOME w /\ allocas_from 0 r' /\
   ~r'.vs_halted /\ r'.vs_current_bb = c2.cs_current_bb /\
   r'.vs_inst_idx = LENGTH c2.cs_current_insts` by
    gvs[Abbr `r'`, allocas_from_def, eval_operand_def, lookup_var_def] >>
  `!x. Var value = Var x ==> not_fresh_at c2 x` by simp[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp r'` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp r` mp_tac >>
     simp[Abbr `r'`, allocas_below_fmp_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (strip_tac >>
     irule fragGasSeqPtrContextTheory.run_inst_seq_allocas_below_fmp >>
     qexistsl [`emitted_insts c2 c3`, `r`] >> simp[] >>
     drule calldata_clamp_instructions >> rpt strip_tac >>
     gvs[mk_inst_def, is_alloca_op_def, is_terminator_def] >>
     Cases_on `signed` >> gvs[mk_inst_def, is_alloca_op_def, is_terminator_def]) >>
  drule_all calldata_clamp_overwrite_prefix_uniform_origin_joint >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl [`G'`,`tn'`] >>
  gvs[Abbr `r'`] >>
  conj_tac >- (irule compile_abi_clamp_basetype_mem_ok >> goal_assum (drule_at Any)) >>
  rpt strip_tac >>
  qpat_x_assum `!a v. _ ==> eval_operand a u = SOME v`
    (qspecl_then [`Var x`,`z`] mp_tac) >>
  gvs[eval_operand_def, lookup_var_def]
QED

Theorem allocated_word_store_cut[local]:
  emit_void MSTORE [Var dst;Var value] c3 = ((),sb) /\
  lookup_var dst u = SOME dw /\ lookup_var value u = SOME w /\
  ptr_covers G3 tn3 dst u 32 /\ op_taint tn3 (Var value) = {} /\
  w2n dw + 32 <= u.vs_alloca_next /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  run_inst_seq (emitted_insts c3 sb) u = OK v ==>
  v = mstore (w2n dw) w u /\
  run_inst_seq_mem_ok (emitted_insts c3 sb) u /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts c3 sb) /\
  !D. inst_seq_ptr D 0 ctx fn PG G3 tn3 (emitted_insts c3 sb)
    (u with vs_inst_idx := LENGTH c3.cs_current_insts) G3
    (tn3 with t_mem := tn3.t_mem DIFF {i | w2n dw <= i /\ i < w2n dw + 32})
Proof
  strip_tac >>
  `eval_operand (Var dst) u = SOME dw /\ eval_operand (Var value) u = SOME w` by
    simp[eval_operand_def] >>
  conj_tac >-
    (drule emitted_insts_emit_void >> strip_tac >>
     gvs[run_inst_seq_def, AllCaseEqs(), step_mstore_eq]) >>
  conj_tac >-
    (irule emit_mstore_mem_ok >>
     goal_assum (drule_at (Pat `emit_void _ _ _ = _`)) >> qexists `dw` >> simp[]) >>
  drule emitted_insts_emit_void >> strip_tac >>
  conj_tac >- simp[mk_inst_def, is_terminator_def] >>
  gen_tac >> qabbrev_tac `u' = u with vs_inst_idx := LENGTH c3.cs_current_insts` >>
  qabbrev_tac `i = mk_inst c3.cs_next_id MSTORE [Var dst;Var value] []` >>
  `lookup_var dst u' = SOME dw /\ eval_operand (Var value) u' = SOME w /\
   ptr_covers G3 tn3 dst u' 32` by
    gvs[Abbr `u'`, eval_operand_def, lookup_var_def] >>
  `step_inst_base i u' = OK (mstore (w2n dw) w u')` by
    simp[Abbr `i`, step_mstore_eq, eval_operand_def] >>
  `step_prov PG G3 i (mstore (w2n dw) w u') = G3` by
    metis_tac[Abbr `i`, cj 1 mstore_ghost_frame] >>
  `step_taint i u' (mstore (w2n dw) w u') tn3 =
     tn3 with t_mem := tn3.t_mem DIFF {i | w2n dw <= i /\ i < w2n dw + 32}` by
    (simp[Abbr `i`] >> irule clean_mstore_taint_state >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u'` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp u` mp_tac >>
     simp[Abbr `u'`, allocas_below_fmp_def]) >>
  gvs[Abbr `i`, inst_seq_ptr_def] >>
  irule ptr_inst_ok_mstore >> simp[]
QED

Theorem abi_decode_allocated_word_success_joint:
  compile_abi_decode_to_buf (Var dst) pos MLOAD (Var src) hi
    (DecPrimWord clamp) sa = ((),sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  abi_decode_ptr_window G tn s src a n /\
  eval_operand pos s = SOME (n2w p) /\ op_taint tn pos = {} /\
  p+32 <= n /\ w2n a+n <= s.vs_alloca_next /\ w2n a+p < dimword(:256) /\
  lookup_var dst s = SOME dw /\ ptr_covers G tn dst s 32 /\
  w2n dw+32 <= s.vs_alloca_next /\ not_fresh_at sa dst /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ fn_has_code sa sb fn /\
  fn_inst_ids_distinct fn /\ ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?H tf.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
       (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),H,tf)) /\
    tf.t_mem = tn.t_mem DIFF {i | w2n dw <= i /\ i < w2n dw + 32} /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP H x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule allocated_word_decode_phases >> strip_tac >>
  drule_all allocated_word_relative_load >>
  disch_then (qspecl_then [`fn`,`PG`] strip_assume_tac) >>
  qabbrev_tac `pre = emitted_insts sa c1 ++ emitted_insts c1 c2` >>
  qabbrev_tac `cl = emitted_insts c2 c3` >>
  qabbrev_tac `post = emitted_insts c3 sb` >>
  `emitted_insts sa sb = pre ++ (cl ++ post)` by simp[Abbr `pre`,Abbr `cl`,Abbr `post`,APPEND_ASSOC] >>
  `run_inst_seq (cl ++ post) r = OK t` by
    ((qpat_x_assum `run_inst_seq (emitted_insts sa sb) s = OK t` mp_tac >>
     simp[] >> drule run_inst_seq_append >> simp[] >> (metis_tac[run_inst_seq_append]))) >>
  drule instSeqComposePtrTheory.run_inst_seq_append_ok_split >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  `fn_has_code c2 c3 fn` by
    (irule fn_has_code_mid >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`sb`,`sa`] >> simp[] >> metis_tac[cs_extends_trans]) >>
  `run_inst_seq (emitted_insts c2 c3) r = OK u` by
    (qpat_x_assum `run_inst_seq cl r = OK u` mp_tac >> simp[Abbr `cl`]) >>
  `~r.vs_halted /\ r.vs_current_bb = c2.cs_current_bb` by simp[] >>
  drule_all allocated_word_clamp_cut >> disch_then (qspec_then `PG` strip_assume_tac) >>
  `!x. not_fresh_at sa x ==> not_fresh_at c2 x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono, LESS_EQ_TRANS] >>
  `lookup_var dst u = SOME dw /\ lookup_var value u = SOME (mload (w2n a+p) s)` by
    (conj_tac >> first_x_assum irule >> metis_tac[]) >>
  `ptr_covers G3 tn3 dst u 32` by
    (irule ptr_covers_frame >> qexistsl [`G`,`s`,`tn`] >> simp[] >> metis_tac[]) >>
  `op_taint tn3 (Var value) = {}` by
    (qpat_assum `!x. not_fresh_at c2 x ==> _` (qspec_then `value` mp_tac) >> simp[]) >>
  `w2n dw + 32 <= u.vs_alloca_next` by simp[] >>
  unabbrev_all_tac >>
  drule_all allocated_word_store_cut >> disch_then (qspecl_then [`fn`,`PG`] strip_assume_tac) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
                i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS)
     (emitted_insts sa c1 ++ emitted_insts c1 c2)` by
    (qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     qpat_assum `emit_op MLOAD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     simp[mk_inst_def, is_terminator_def]) >>
  qabbrev_tac `pre = emitted_insts sa c1 ++ emitted_insts c1 c2` >>
  qabbrev_tac `cl = emitted_insts c2 c3` >>
  qabbrev_tac `post = emitted_insts c3 sb` >>
  qabbrev_tac `tf = tn3 with t_mem := tn3.t_mem DIFF {i | w2n dw <= i /\ i < w2n dw + 32}` >>
  `run_inst_seq_mem_ok (cl ++ post) r` by
    (irule bodyLiteralBufferMemoryTheory.run_inst_seq_mem_ok_append_run >>
     conj_tac >- first_assum ACCEPT_TAC >> qexists `u` >> simp[]) >>
  `run_inst_seq_mem_ok (pre ++ (cl ++ post)) s` by
    (irule bodyLiteralBufferMemoryTheory.run_inst_seq_mem_ok_append_run >>
     conj_tac >- first_assum ACCEPT_TAC >> qexists `r` >> simp[]) >>
  `!D. inst_seq_ptr D 0 ctx fn PG G2 tn2 (cl ++ post)
         (r with vs_inst_idx := LENGTH c2.cs_current_insts) G3 tf` by
    ((`EVERY (\i. ~is_terminator i.inst_opcode) cl` by fs[EVERY_MEM] >>
     gen_tac >> irule inst_seq_ptr_append_run >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`G3`,`u with vs_inst_idx := LENGTH c2.cs_current_insts`,`tn3`] >>
     simp[run_inst_seq_inst_idx, exec_result_map_def] >> (gvs[EVERY_MEM, run_inst_seq_inst_idx, exec_result_map_def, inst_seq_ptr_append_run]))) >>
  `!D. inst_seq_ptr D 0 ctx fn PG G tn (pre ++ (cl ++ post)) s G3 tf` by
    ((`EVERY (\i. ~is_terminator i.inst_opcode) pre` by fs[EVERY_MEM] >>
     gen_tac >> irule inst_seq_ptr_append_run >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`G2`,`r`,`tn2`] >> simp[] >> (gvs[EVERY_MEM, inst_seq_ptr_append_run]))) >>
  qexistsl [`G3`,`tf`] >>
  reverse conj_tac >-
    (simp[Abbr `tf`, op_taint_def] >> rpt strip_tac >>
     rpt (first_x_assum drule >> strip_tac) >> fs[op_taint_def]) >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    (drule emitted_insts_emit_void >> strip_tac >>
     drule emit_void_same_blocks >> strip_tac >>
     drule calldata_clamp_instructions >> strip_tac >>
     qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     qpat_assum `emit_op MLOAD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     fs[same_blocks_def, Abbr `pre`, Abbr `cl`, Abbr `post`, APPEND_ASSOC]) >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def, IS_PREFIX_APPEND, APPEND_ASSOC] >>
     qexists `l` >> pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> REFL_TAC) >>
  `LENGTH sb.cs_current_insts = s.vs_inst_idx + LENGTH (emitted_insts sa sb)` by simp[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
               i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts sa sb)` by simp[] >>
  `EVERY (\i. i.inst_opcode <> DALLOCA) (pre ++ (cl ++ post))` by
    (simp[EVERY_APPEND] >> conj_tac >-
       (qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
        qpat_assum `emit_op MLOAD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
        simp[Abbr `pre`, mk_inst_def]) >>
     conj_tac >-
       (simp[Abbr `cl`] >> drule calldata_clamp_instructions >> rpt strip_tac >>
        gvs[mk_inst_def] >> Cases_on `signed` >> gvs[]) >>
     drule emitted_insts_emit_void >> strip_tac >> simp[Abbr `post`, mk_inst_def]) >>
  `(ctx_has_dalloca ctx ==>
    !px i sx u'. pre ++ (cl ++ post) = px ++ i::sx /\
      run_inst_seq px s = OK u' ==> dalloca_no_wrap i u')` by
    (strip_tac >> rpt gen_tac >>
     disch_then (CONJUNCTS_THEN2
       (fn eq => qpat_assum `EVERY (\i. i.inst_opcode <> DALLOCA) _`
         (mp_tac o ONCE_REWRITE_RULE [eq])) kall_tac) >>
     simp[EVERY_APPEND, dalloca_no_wrap_non_dalloca]) >>
  rpt gen_tac >>
  qpat_assum `LENGTH sb.cs_current_insts = _` (once_rewrite_tac o single) >>
  irule (cj 1 run_inst_seq_origin_ptr_lift) >> gvs[] >> first_assum ACCEPT_TAC
QED
