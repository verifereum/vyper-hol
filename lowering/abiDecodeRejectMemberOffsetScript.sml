(* Joint navigation through the dynamic member head of a malformed aggregate. *)
Theory abiDecodeRejectMemberOffset
Ancestors
  abiDecoderNavigationTotal abiMalformedNavigation abiDecoderReentry
  abiDecodePtrMemberFrame bodyPtrDefs decoderMemberPrefixPtr decoderNavigationPtr
  bodyPtrBopScalarOutcome bodyPtrBopScalarSeq
  abiEncoder emitHelperProps exprLoweringProps compileEnv fragExec
  venomInst venomExecSemantics venomState loweringStateRelDefs arithmetic words
  exprSimConvertBytes abiDecoderContract fragGasCopyLoop fragGasCopySeqLiftProps fragGasSeqPtr
  stmtReasonLitFragMemory instMemFrontier fragExecMem memSafeRun ptrDiscipline
  pred_set list rich_list fragGasOriginPtr instIdxIndep
  abiMalformedRecursiveInterface exprSimAbiDecodeMemberExecute valueEncodingProps vyperABI

(* No execution premise: all seven compile cuts exist even when ASSERT fails. *)
Theorem malformed_member_offset_emits[local]:
  compile_getelemptr_abi pos T ao MLOAD (Var source) hi sa = (out,sb) /\
  hi <> Lit 0w ==>
  ?head c1 addr c2 off c3 under c4 test c5 c6.
    emit_op ADD [pos; Lit (n2w ao)] sa = (head,c1) /\
    emit_op ADD [Var source;head] c1 = (addr,c2) /\
    emit_op MLOAD [addr] c2 = (off,c3) /\
    emit_op ADD [pos;off] c3 = (out,c4) /\
    emit_op LT [out;pos] c4 = (under,c5) /\
    emit_op ISZERO [under] c5 = (test,c6) /\
    emit_void ASSERT [test] c6 = ((),sb)
Proof
  strip_tac >>
  qpat_x_assum `compile_getelemptr_abi _ _ _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [compile_getelemptr_abi_def, compile_abi_dec_addr_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM,
    TypeBase.distinct_of ``:operand``] >>
  rpt (pairarg_tac >> fs[]) >> strip_tac >> gvs[] >>
  qpat_x_assum `comp_bind _ _ _ = _` mp_tac >>
  simp_tac bool_ss [comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> fs[]) >> strip_tac >> gvs[] >> metis_tac[]
QED

(* The symbolic sequence is split before the possibly failing arithmetic. *)
Theorem malformed_member_offset_code[local]:
  emit_op ADD [pos; Lit (n2w ao)] sa = (head,c1) /\
  emit_op ADD [Var source;head] c1 = (addr,c2) /\
  emit_op MLOAD [addr] c2 = (off,c3) /\
  emit_op ADD [pos;off] c3 = (out,c4) /\
  emit_op LT [out;pos] c4 = (under,c5) /\
  emit_op ISZERO [under] c5 = (test,c6) /\
  emit_void ASSERT [test] c6 = ((),sb) /\ fn_has_code sa sb func ==>
  fn_has_code sa c1 func /\ fn_has_code c1 c2 func /\
  fn_has_code c2 c3 func /\ fn_has_code c3 sb func /\
  c1.cs_current_bb = sa.cs_current_bb /\ c2.cs_current_bb = c1.cs_current_bb /\
  c3.cs_current_bb = c2.cs_current_bb /\ sb.cs_current_bb = c3.cs_current_bb /\
  inst_extends sa c1 /\ inst_extends c3 sb /\
  emitted_insts sa sb = emitted_insts sa c1 ++
    (emitted_insts c1 c2 ++ (emitted_insts c2 c3 ++ emitted_insts c3 sb)) /\
  bop_scalar_seq {x | not_fresh_at sa x} {pos;Lit (n2w ao)}
    (emitted_insts sa c1) {head;pos;Lit (n2w ao)} /\
  bop_scalar_seq {x | not_fresh_at c3 x} {pos;off}
    (emitted_insts c3 sb) {test;under;out;pos;off}
Proof
  strip_tac >>
  imp_res_tac (REWRITE_RULE [cs_appends_def] (cj 2 cs_appends_emit_helpers)) >>
  imp_res_tac (REWRITE_RULE [cs_appends_def] (cj 3 cs_appends_emit_helpers)) >>
  `cs_extends c3 sb /\ cs_extends c2 sb /\ cs_extends c1 sb` by
    metis_tac[cs_extends_trans] >>
  `fn_has_code sa c1 func /\ fn_has_code c1 c2 func /\
   fn_has_code c2 c3 func /\ fn_has_code c3 sb func` by
    (mp_tac (Q.SPECL [`sa`,`c1`,`sb`,`func`] fn_has_code_split) >> simp[] >> strip_tac >>
     mp_tac (Q.SPECL [`c1`,`c2`,`sb`,`func`] fn_has_code_split) >> simp[] >> strip_tac >>
     mp_tac (Q.SPECL [`c2`,`c3`,`sb`,`func`] fn_has_code_split) >> simp[]) >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends c3 sb /\ inst_extends c2 sb /\ inst_extends c1 sb /\
   inst_extends c4 sb /\ inst_extends c5 sb` by metis_tac[inst_extends_trans] >>
  `!a b. inst_extends a b ==> b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b`
    by simp[inst_extends_def] >>
  `emitted_insts sa sb = emitted_insts sa c1 ++ emitted_insts c1 sb /\
   emitted_insts c1 sb = emitted_insts c1 c2 ++ emitted_insts c2 sb /\
   emitted_insts c2 sb = emitted_insts c2 c3 ++ emitted_insts c3 sb /\
   emitted_insts c3 sb = emitted_insts c3 c4 ++ emitted_insts c4 sb /\
   emitted_insts c4 sb = emitted_insts c4 c5 ++ emitted_insts c5 sb /\
   emitted_insts c5 sb = emitted_insts c5 c6 ++ emitted_insts c6 sb` by
    (rpt conj_tac >> irule emitted_insts_append >> metis_tac[]) >>
  imp_res_tac emit_op_same_blocks >> imp_res_tac emit_void_same_blocks >>
  simp[same_blocks_def] >>
  fs[same_blocks_def] >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
  fs[] >>
  rpt (CHANGED_TAC (simp[Once bop_scalar_seq_def, mk_inst_def, not_fresh_at_def,
    ASCIInumbersTheory.toString_inj]))
QED

(* ADD defines its output even if the reentry state still has a stale value
   in that slot. Only operands older than this emit are framed. *)
Theorem malformed_member_raw_add[local]:
  emit_op ADD [a;b] sa = (out,sb) /\
  eval_operand a s = SOME x /\ eval_operand b s = SOME y ==>
  ?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
    u = s with vs_vars := u.vs_vars /\ eval_operand out u = SOME (x+y) /\
    (!q. not_fresh_at sa q ==> lookup_var q u = lookup_var q s)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  qexists `update_var (STRING #"%" (toString sa.cs_next_var)) (x+y) s` >>
  conj_tac
  >- (`step_inst_base (mk_inst sa.cs_next_id ADD [a;b]
        [STRING #"%" (toString sa.cs_next_var)]) s =
        OK (update_var (STRING #"%" (toString sa.cs_next_var)) (x+y) s)` by
        (irule slotCopyExecutionTheory.slot_copy_step_add >> simp[]) >>
      simp[run_inst_seq_def]) >>
  simp[slot_copy_operand_update, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]
QED

Theorem malformed_member_raw_prefix[local]:
  emit_op ADD [pos; Lit (n2w ao)] sa = (head,c1) /\
  emit_op ADD [Var source;head] c1 = (addr,c2) /\
  emit_op MLOAD [addr] c2 = (off,c3) /\
  eval_operand pos s = SOME (n2w b) /\ lookup_var source s = SOME (n2w B) /\
  not_fresh_at sa source ==>
  ?r1 r2 r3.
    run_inst_seq (emitted_insts sa c1) s = OK r1 /\
    run_inst_seq (emitted_insts c1 c2) r1 = OK r2 /\
    run_inst_seq (emitted_insts c2 c3) r2 = OK r3 /\
    r1 = s with vs_vars := r1.vs_vars /\ r2 = r1 with vs_vars := r2.vs_vars /\
    r3 = r2 with vs_vars := r3.vs_vars /\
    eval_operand head r1 = SOME (n2w (b+ao))
Proof
  strip_tac >>
  `eval_operand (Lit (n2w ao)) s = SOME (n2w ao)` by simp[eval_operand_def] >>
  drule_then (drule_all_then strip_assume_tac) malformed_member_raw_add >>
  rename1 `run_inst_seq (emitted_insts sa c1) s = OK r1` >>
  `eval_operand (Var source) r1 = SOME (n2w B) /\
   eval_operand head r1 = SOME (n2w (b+ao))` by simp[eval_operand_def, word_add_n2w] >>
  qpat_assum `emit_op ADD [Var source;head] _ = _`
    (mp_then Any (drule_all_then strip_assume_tac) malformed_member_raw_add) >>
  rename1 `run_inst_seq (emitted_insts c1 c2) r1 = OK r2` >>
  drule_all convert_mload_run >> disch_then assume_tac >>
  qexistsl [`r1`,`r2`,
    `update_var (STRING #"%" (toString c2.cs_next_var))
      (mload (w2n (n2w (B + (b + ao)) : bytes32)) r2) r2`] >>
  fs[update_var_def, word_add_n2w]
QED

(* The code and runtime frames select a single scalar ghost pair. *)
Theorem malformed_member_scalar_frame[local]:
  bop_scalar_seq {x | not_fresh_at sa x} A (emitted_insts sa sb) C /\
  (!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  fn_has_code sa sb func /\ inst_extends sa sb /\ sb.cs_current_bb = sa.cs_current_bb /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H u. (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),H,u)) /\
    t = s with vs_vars := t.vs_vars /\
    (!op. op IN C ==> op_prov H op = NONE /\ op_taint u op = {}) /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\
    u.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==> lookup_var q t = lookup_var q s /\
      FLOOKUP H q = FLOOKUP G q /\ op_taint u (Var q) = op_taint tn (Var q))
Proof
  strip_tac >> drule_all bop_scalar_seq_runtime_frame >> strip_tac >>
  drule_all bop_scalar_seq_run >>
  disch_then (fn th => assume_tac th >>
    qspecl_then [`func`,`PG`,`ARB:dead`] strip_assume_tac th) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `inst_extends sa sb` (assume_tac o REWRITE_RULE[inst_extends_def]) >>
     drule_all fn_has_code_code >> simp[] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
     i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    (drule bop_scalar_seq_opcodes >> simp[EVERY_MEM] >> rpt strip_tac >>
     drule_all bop_scalar_seq_outputs >> strip_tac >> gvs[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule run_inst_seq_mem_ok_every >> simp[EVERY_MEM] >>
     rpt gen_tac >> strip_tac >> gen_tac >>
     drule_all bop_scalar_seq_outputs >> strip_tac >>
     conj_tac >- (irule below_frontier_no_ranges >> gvs[]) >>
     irule inst_dload_in_section_other >> gvs[]) >>
  `ctx_has_dalloca ctx ==> !pre i post v.
     emitted_insts sa sb = pre ++ i::post /\ run_inst_seq pre s = OK v ==>
     dalloca_no_wrap i v` by
    (rpt strip_tac >>
     `MEM i (emitted_insts sa sb)` by simp[MEM_APPEND] >>
     irule dalloca_no_wrap_non_dalloca >>
     drule_all bop_scalar_seq_outputs >> strip_tac >> gvs[]) >>
  `LENGTH sb.cs_current_insts = s.vs_inst_idx + LENGTH (emitted_insts sa sb)` by
    fs[inst_extends_def] >>
  qexistsl [`G'`,`tn'`] >> simp[] >> reverse conj_tac
  >- (rpt strip_tac >> fs[lookup_var_def, op_taint_def]) >>
  rpt gen_tac >>
  `inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s G' tn'` by
    (qpat_assum `!fn PG D. _` (qspecl_then [`func`,`PG`,`D`] strip_assume_tac) >>
     metis_tac[inst_seq_ptr_ghost_unique]) >>
  drule_all run_inst_seq_origin_ptr_lift >> simp[]
QED

(* An empty-trace cut retains the same ghosts for every horizon. *)
Theorem malformed_member_path_join[local]:
  (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK m,H,u)) /\
  (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (m,H,u) [] (r,J,v)) ==>
  !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (r,J,v)
Proof
  metis_tac[gas_origin_ptr_path_append, APPEND_NIL]
QED

Theorem malformed_member_joint_prefix[local]:
  emit_op ADD [pos; Lit (n2w ao)] sa = (head,c1) /\
  emit_op ADD [Var source;head] c1 = (addr,c2) /\
  emit_op MLOAD [addr] c2 = (off,c3) /\
  fn_has_code sa c1 func /\ fn_has_code c1 c2 func /\ fn_has_code c2 c3 func /\
  c1.cs_current_bb = sa.cs_current_bb /\ c2.cs_current_bb = c1.cs_current_bb /\
  c3.cs_current_bb = c2.cs_current_bb /\ inst_extends sa c1 /\
  bop_scalar_seq {x | not_fresh_at sa x} {pos;Lit (n2w ao)}
    (emitted_insts sa c1) {head;pos;Lit (n2w ao)} /\
  run_inst_seq (emitted_insts sa c1) s = OK r1 /\
  run_inst_seq (emitted_insts c1 c2) r1 = OK r2 /\
  run_inst_seq (emitted_insts c2 c3) r2 = OK r3 /\
  r1 = s with vs_vars := r1.vs_vars /\ r2 = r1 with vs_vars := r2.vs_vars /\
  r3 = r2 with vs_vars := r3.vs_vars /\
  eval_operand head r1 = SOME (n2w (b+ao)) /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  b+ao+32 <= L /\ B+L < dimword (:256) /\ B+L <= s.vs_alloca_next /\
  not_fresh_at sa source /\ abi_decoder_operand_live sa.cs_next_var pos /\
  op_prov G pos = NONE /\ op_taint tn pos = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?H u. (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (s,G,tn) [] (OK (r3 with vs_inst_idx := LENGTH c3.cs_current_insts),H,u)) /\
    op_prov H pos = NONE /\ op_taint u pos = {} /\
    op_prov H off = NONE /\ op_taint u off = {} /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\
    u.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==> lookup_var q r3 = lookup_var q s /\
      FLOOKUP H q = FLOOKUP G q /\ op_taint u (Var q) = op_taint tn (Var q))
Proof
  strip_tac >>
  `!op. op IN {pos;Lit (n2w ao)} ==> op_prov G op = NONE /\ op_taint tn op = {}`
    by (simp[] >> rpt strip_tac >> gvs[] >> simp[op_prov_def, op_taint_def]) >>
  drule_all malformed_member_scalar_frame >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  rename1 `gas_origin_ptr_path _ (s,G,tn) [] (OK _,G1,tn1)` >>
  `abi_decode_ptr_window G1 tn1 r1 source (n2w B) L` by
    (irule abi_decode_ptr_window_frame >> goal_assum (drule_at Any) >> simp[]) >>
  `w2n (n2w B : bytes32) = B /\ w2n (n2w (B + (b+ao)) : bytes32) = B + (b+ao)` by
    (simp[w2n_n2w] >> conj_tac >> irule LESS_MOD >> decide_tac) >>
  `allocas_from lo r1 /\ r1.vs_current_bb = c1.cs_current_bb /\ ~r1.vs_halted` by
    ((qpat_assum `r1 = s with vs_vars := _` SUBST1_TAC >> simp[allocas_from_def] >>
     qpat_assum `allocas_from lo s` mp_tac >> simp[allocas_from_def] >> (gvs[allocas_from_def]))) >>
  `lookup_var source r1 = SOME (n2w B) /\ ptr_covers G1 tn1 source r1 L /\
    (!i. B <= i /\ i < B + L ==> i NOTIN tn1.t_mem)` by
    fs[abi_decode_ptr_window_def] >>
  `op_prov G1 head = NONE /\ op_taint tn1 head = {}` by simp[] >>
  `b + ao + 32 <= L /\ w2n (n2w B : bytes32) + (b+ao) < dimword (:256)` by
    (simp[] >> decide_tac) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp r1` by
    (qpat_assum `r1 = s with vs_vars := _` SUBST1_TAC >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     simp[NoAsms, allocas_below_fmp_def] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  drule_all (Q.INST [`n` |-> `32`] (SPEC_ALL member_navigation_emit_pointer_pc_uniform_origin)) >>
  disch_then (qspec_then `PG` (qx_choose_then `addr_reg` (qx_choose_then `G2`
    (qx_choose_then `tn2` strip_assume_tac)))) >>
  qpat_x_assum `addr = Var addr_reg` SUBST_ALL_TAC >>
  qabbrev_tac `at2 = r2 with vs_inst_idx := LENGTH c2.cs_current_insts` >>
  `B MOD dimword (:256) = B` by (irule LESS_MOD >> decide_tac) >>
  `lookup_var addr_reg at2 = SOME (n2w (B+(b+ao))) /\ ptr_covers G2 tn2 addr_reg at2 32` by
    (conj_tac >- fs[Abbr `at2`, lookup_var_def, AC ADD_ASSOC ADD_COMM] >>
     simp[Abbr `at2`, ptr_covers_def, lookup_var_def] >>
     qpat_assum `ptr_covers G2 tn2 addr_reg r2 32`
       (mp_tac o REWRITE_RULE[ptr_covers_def, lookup_var_def]) >> simp[]) >>
  `!i. w2n (n2w (B+(b+ao)) : bytes32) <= i /\
       i < w2n (n2w (B+(b+ao)) : bytes32) + 32 ==> i NOTIN tn2.t_mem` by
    (qx_gen_tac `i` >> strip_tac >>
     `B <= i /\ i < B+L` by
       (qpat_x_assum `w2n _ <= i` mp_tac >> qpat_x_assum `i < w2n _ + 32` mp_tac >>
        asm_rewrite_tac[] >> decide_tac) >>
     `i NOTIN tn1.t_mem` by
       (qpat_assum `!j. B <= j /\ j < B+L ==> j NOTIN tn1.t_mem` irule >> simp[]) >>
     metis_tac[]) >>
  `run_inst_seq (emitted_insts c2 c3) at2 =
     OK (r3 with vs_inst_idx := LENGTH c2.cs_current_insts)` by
    (qpat_assum `emit_op MLOAD _ _ = _` (mp_then Any mp_tac emit_op_run_pc) >>
     simp[Abbr `at2`, is_terminator_def, exec_result_map_def]) >>
  qpat_assum `run_inst_seq _ at2 = OK _`
    (mp_then Any (drule_all_then (qspecl_then [`ARB`,`ARB`,`ARB`,`PG`,`ARB`]
      (qx_choose_then `G3` (qx_choose_then `tn3` strip_assume_tac))))
      emit_mload_clean_endpoint_ptr_origin_core) >>
  `allocas_from lo at2 /\ ~at2.vs_halted /\ at2.vs_current_bb = c2.cs_current_bb /\
   at2.vs_inst_idx = LENGTH c2.cs_current_insts /\ at2.vs_alloca_next = s.vs_alloca_next` by
    (simp[Abbr `at2`] >> qpat_assum `r2 = r1 with vs_vars := _` SUBST1_TAC >>
     qpat_assum `r1 = s with vs_vars := _` SUBST1_TAC >>
     simp[allocas_from_def] >>
     qpat_assum `allocas_from lo s` (ACCEPT_TAC o REWRITE_RULE[allocas_from_def])) >>
  `w2n (n2w (B+(b+ao)) : bytes32) + 32 <= at2.vs_alloca_next` by
    (asm_rewrite_tac[] >> decide_tac) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp at2` by
    (simp[NoAsms, Abbr `at2`] >>
     qpat_assum `r2 = r1 with vs_vars := _` SUBST1_TAC >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp r1` mp_tac >>
     simp[NoAsms, allocas_below_fmp_def] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (at2,G2,tn2) []
     (OK (r3 with vs_inst_idx := LENGTH c3.cs_current_insts),G3,tn3)` by
    (rpt gen_tac >> qpat_assum `!D lower explicit ctx' func. _ ==> gas_origin_ptr_path _ _ _ _`
       (qspecl_then [`D`,`lo`,`explicit`,`ctx`,`func`] mp_tac) >>
     gvs[venom_state_fupdcanon]) >>
  `!q. not_fresh_at sa q ==> not_fresh_at c1 q /\ not_fresh_at c2 q` by
    (imp_res_tac exprSimAccountsTheory.emit_op_extends_next_var >>
     metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]) >>
  `!q. not_fresh_at sa q ==> lookup_var q r3 = lookup_var q s /\
       FLOOKUP G3 q = FLOOKUP G q /\ op_taint tn3 (Var q) = op_taint tn (Var q)` by
    (qx_gen_tac `q` >> strip_tac >>
     `not_fresh_at c1 q /\ not_fresh_at c2 q` by metis_tac[] >>
     qpat_assum `!x. not_fresh_at c2 x ==> lookup_var x _ = _ /\ _`
       (qspec_then `q` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     qpat_assum `!x. not_fresh_at c1 x ==> lookup_var x _ = _ /\ _`
       (qspec_then `q` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x _ = _ /\ _`
       (qspec_then `q` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     fs[Abbr `at2`, lookup_var_def]) >>
  qexistsl [`G3`,`tn3`] >> simp[] >> reverse conj_tac
  >- (Cases_on `pos` >> fs[op_prov_def, op_taint_def, abi_decoder_operand_live_def,
                           abi_decoder_older_vars_def, GSYM not_fresh_at_def] >>
      metis_tac[op_taint_def]) >>
  irule malformed_member_path_join >>
  qexistsl [`G2`,`at2`,`tn2`] >> simp[] >>
  irule malformed_member_path_join >>
  qexistsl [`G1`,`r1 with vs_inst_idx := LENGTH c1.cs_current_insts`,`tn1`] >> simp[]
QED

(* The raw totality theorem selects the scalar outcome; only the checked
   physical prefix and scalar lifts are used to build the joint path. *)
Theorem malformed_dynamic_member_offset_cut:
  (!R A code C G tn ctx lo s func bb t PG.
    bop_scalar_seq R A code C /\
    (!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    run_inst_seq code s = Abort Revert_abort t ==>
    ?u H z. u.vs_accounts = s.vs_accounts /\
      u.vs_transient = s.vs_transient /\ u.vs_call_ctx = s.vs_call_ctx /\
      u.vs_immutables = s.vs_immutables /\
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (Abort Revert_abort u,H,z))) /\
  compile_getelemptr_abi pos T ao MLOAD (Var source) hi sa = (out,sb) /\
  hi <> Lit 0w /\ eval_operand pos s = SOME (n2w b) /\
  abiMalformedRecursiveInterface$abi_malformed_allocated_window live B L xs s /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  b+ao+32 <= L /\ B+L <= s.vs_alloca_next /\
  not_fresh_at sa source /\ abi_decoder_operand_live sa.cs_next_var pos /\
  op_prov G pos = NONE /\ op_taint tn pos = {} /\
  sb.cs_next_var <= ceiling.cs_next_var /\ fresh_vars_wrt ceiling s /\
  fn_has_code sa sb func /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  (?u H z. u.vs_accounts = s.vs_accounts /\
      u.vs_transient = s.vs_transient /\ u.vs_call_ctx = s.vs_call_ctx /\
      u.vs_immutables = s.vs_immutables /\
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (Abort Revert_abort u,H,z))) \/
    ((b + abi_head_word (DROP (b+ao) xs)) < dimword (:256) /\
     ?u H z. eval_operand out u = SOME (n2w (b + abi_head_word (DROP (b+ao) xs))) /\
       abi_decoder_operand_live sb.cs_next_var out /\
       op_prov H out = NONE /\ op_taint z out = {} /\ fresh_vars_wrt ceiling u /\
       u = s with <|vs_inst_idx := LENGTH sb.cs_current_insts; vs_vars := u.vs_vars|> /\
       z.t_mem = tn.t_mem /\ z.t_stor = tn.t_stor /\ z.t_trans = tn.t_trans /\
       z.t_imm = tn.t_imm /\
       (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
         FLOOKUP H x = FLOOKUP G x /\ op_taint z (Var x) = op_taint tn (Var x)) /\
       (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
         (s,G,tn) [] (OK u,H,z)))
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all malformed_member_offset_emits >> strip_tac >>
  drule_all malformed_member_offset_code >> strip_tac >>
  `lookup_var source s = SOME (n2w B)` by fs[abi_decode_ptr_window_def] >>
  drule_all malformed_member_raw_prefix >> strip_tac >>
  `B+L < dimword (:256) /\ mem_bytes_at B L s.vs_memory = xs` by
    fs[abiMalformedRecursiveInterfaceTheory.abi_malformed_allocated_window_def] >>
  drule_all malformed_member_joint_prefix >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts c2 c3) r2 = OK r3` >>
  qabbrev_tac `payload = abi_head_word (DROP (b+ao) xs)` >>
  `LENGTH xs = L` by metis_tac[LENGTH_mem_bytes_at] >>
  `abi_decode_load MLOAD (n2w (B+(b+ao)) : bytes32) s = n2w payload` by
    (`xs = mem_bytes_at B (LENGTH xs) s.vs_memory /\
      b+ao+32 <= LENGTH xs /\ B+LENGTH xs < dimword (:256)` by simp[] >>
     drule_all abi_decode_member_offset_load >>
     simp[Abbr `payload`, DROP_DROP_T, AC ADD_ASSOC ADD_COMM] >> simp[]) >>
  `payload < dimword (:256)` by
    simp[Abbr `payload`, vyperABITheory.abi_head_word_def, w2n_lt] >>
  `b < dimword (:256)` by decide_tac >>
  `abi_decode_source_opcode MLOAD /\
   abi_decoder_operand_live sa.cs_next_var (Var source) /\
   eval_operand (Var source) s = SOME (n2w B)` by
    simp[abi_decode_source_opcode_def, abi_decoder_operand_live_def,
         abi_decoder_older_vars_def, GSYM not_fresh_at_def, eval_operand_def] >>
  `run_inst_seq (emitted_insts sa sb) s = run_inst_seq (emitted_insts c3 sb) r3` by
    (qpat_assum `emitted_insts sa sb = _ ++ _` SUBST1_TAC >>
     imp_res_tac run_inst_seq_append >> simp[]) >>
  qabbrev_tac `at3 = r3 with vs_inst_idx := LENGTH c3.cs_current_insts` >>
  `at3 = s with <|vs_inst_idx := LENGTH c3.cs_current_insts; vs_vars := at3.vs_vars|>` by
    (simp[Abbr `at3`] >>
     qpat_assum `r3 = r2 with vs_vars := _` SUBST1_TAC >>
     qpat_assum `r2 = r1 with vs_vars := _` SUBST1_TAC >>
     qpat_assum `r1 = s with vs_vars := _` SUBST1_TAC >> simp[venom_state_fupdcanon]) >>
  `allocas_from lo at3 /\ ~at3.vs_halted /\ at3.vs_current_bb = c3.cs_current_bb /\
   at3.vs_inst_idx = LENGTH c3.cs_current_insts` by
    (qpat_assum `at3 = _` SUBST1_TAC >>
     simp[allocas_from_def] >>
     qpat_assum `allocas_from lo s` (ACCEPT_TAC o REWRITE_RULE[allocas_from_def])) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp at3` by
    (qpat_assum `at3 = _` SUBST1_TAC >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     simp[NoAsms, allocas_below_fmp_def] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `!op. op IN {pos;off} ==> op_prov H op = NONE /\ op_taint u op = {}` by
    (simp[] >> metis_tac[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c3 sb)` by
    (qpat_assum `bop_scalar_seq _ _ (emitted_insts c3 sb) _`
       (mp_then Any mp_tac bop_scalar_seq_opcodes) >>
     simp[EVERY_MEM] >> metis_tac[]) >>
  `run_inst_seq (emitted_insts c3 sb) at3 =
   exec_result_map (\v. v with vs_inst_idx := LENGTH c3.cs_current_insts)
     (run_inst_seq (emitted_insts sa sb) s)` by
    simp[Abbr `at3`, run_inst_seq_inst_idx] >>
  `?bb. lookup_block at3.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts c3 sb) (DROP at3.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `inst_extends c3 sb` (assume_tac o REWRITE_RULE[inst_extends_def]) >>
     qpat_assum `fn_has_code c3 sb func` (mp_then Any (drule_all_then strip_assume_tac) fn_has_code_code) >>
     gvs[]) >>
  drule_all abi_decode_dynamic_member_total_reentry >> strip_tac
  >- (disj1_tac >>
      `run_inst_seq (emitted_insts c3 sb) at3 =
        Abort Revert_abort (t with vs_inst_idx := LENGTH c3.cs_current_insts)` by
        simp[exec_result_map_def] >>
      qpat_x_assum `!R A code C G tn ctx lo s func bb t PG. _`
        (drule_all_then (qspec_then `PG`
          (qx_choose_then `v` (qx_choose_then `J` (qx_choose_then `z` strip_assume_tac))))) >>
      qexistsl [`v`,`J`,`z`] >>
      `at3.vs_accounts = s.vs_accounts /\ at3.vs_transient = s.vs_transient /\
       at3.vs_call_ctx = s.vs_call_ctx /\ at3.vs_immutables = s.vs_immutables` by
        (qpat_assum `at3 = _` SUBST1_TAC >> simp[]) >>
      simp[] >> irule malformed_member_path_join >> qexistsl [`H`,`at3`,`u`] >> simp[]) >>
  disj2_tac >> conj_tac >- first_assum ACCEPT_TAC >>
  qabbrev_tac `t3 = t with vs_inst_idx := LENGTH c3.cs_current_insts` >>
  `run_inst_seq (emitted_insts c3 sb) at3 = OK t3` by
    simp[Abbr `t3`, exec_result_map_def] >>
  qpat_assum `run_inst_seq (emitted_insts c3 sb) at3 = OK t3`
    (mp_then Any (drule_all_then (qspec_then `PG`
       (qx_choose_then `J` (qx_choose_then `z` strip_assume_tac))))
       malformed_member_scalar_frame) >>
  `sa.cs_next_var <= c3.cs_next_var /\ c4.cs_next_var <= sb.cs_next_var` by
    (imp_res_tac exprSimAccountsTheory.emit_op_extends_next_var >>
     drule emitted_insts_emit_void >> strip_tac >> decide_tac) >>
  `abi_decoder_operand_live sb.cs_next_var out` by
    (irule abi_decoder_operand_live_mono >> qexists `c4.cs_next_var` >>
     metis_tac[abi_decoder_operand_live_emit]) >>
  `op_prov J out = NONE /\ op_taint z out = {}` by
    (qpat_assum `!op. op IN {test;under;out;pos;off} ==> _` (qspec_then `out` mp_tac) >> simp[]) >>
  qabbrev_tac `final = t3 with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `eval_operand out final = SOME (n2w (b+payload)) /\ fresh_vars_wrt ceiling final` by
    (simp[Abbr `final`, Abbr `t3`, venom_state_fupdcanon, fresh_vars_wrt_def] >>
     Cases_on `out` >> gvs[eval_operand_def, lookup_var_def, fresh_vars_wrt_def]) >>
  `final = s with <|vs_inst_idx := LENGTH sb.cs_current_insts; vs_vars := final.vs_vars|>` by
    (simp[Abbr `final`] >> qpat_assum `t3 = at3 with vs_vars := _` SUBST1_TAC >>
     qpat_assum `at3 = _` SUBST1_TAC >> simp[venom_state_fupdcanon]) >>
  `!x. not_fresh_at sa x ==> lookup_var x final = lookup_var x s /\
      FLOOKUP J x = FLOOKUP G x /\ op_taint z (Var x) = op_taint tn (Var x)` by
    (qx_gen_tac `x` >> strip_tac >>
     `not_fresh_at c3 x` by metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
     qpat_assum `!q. not_fresh_at c3 q ==> _` (qspec_then `x` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     qpat_assum `!q. not_fresh_at sa q ==> _` (qspec_then `x` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     fs[Abbr `final`, Abbr `at3`, lookup_var_def]) >>
  qexistsl [`final`,`J`,`z`] >> simp[] >>
  irule malformed_member_path_join >> qexistsl [`H`,`at3`,`u`] >> simp[Abbr `final`]
QED
