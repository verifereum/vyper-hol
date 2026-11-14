(* Aggregate append guard and stride-aware address boundary. *)
Theory bodyIntCallFamStmtMutationAppendAggregatePrefix
Ancestors
  appendStorageStageRuns exprLowering compileEnv exprLoweringProps
  stmtSimAppendStorageCompose stmtSimAppendStorage emitHelper emitHelperProps
  fragGasSeq fragGasSeqAbort fragGasPath fragGasMode
  exprSimHashBoundary stmtReasonLitFragMemory
  venomState venomInst stateFrame stmtLoweringMono reasonMemoryEncoderPtr

Theorem intcall_append_aggregate_suffix_parts:
  compile_dynarray_append ce bop vop 1 sz elem elem cap F
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sa = ((),sf) ==>
  ?lop valid dop off pop nop s1 s2 s3 s4 s5 s6 s7 s8.
    emit_op (if tr then TLOAD else SLOAD) [bop] sa = (lop,s1) /\
    emit_op LT [lop; Lit (n2w cap)] s1 = (valid,s2) /\
    emit_void ASSERT [valid] s2 = ((),s3) /\
    emit_op ADD [bop; Lit 1w] s3 = (dop,s4) /\
    emit_op MUL [lop; Lit (n2w sz)] s4 = (off,s5) /\
    emit_op ADD [dop;off] s5 = (pop,s6) /\
    compile_store_slots ce vop pop elem tr s6 = ((),s7) /\
    emit_op ADD [lop;Lit 1w] s7 = (nop,s8) /\
    emit_void (if tr then TSTORE else SSTORE) [bop;nop] s8 = ((),sf)
Proof
  Cases_on `tr` >>
  simp[compile_dynarray_append_def,comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem intcall_append_aggregate_address_stages:
  emit_op ADD [bop; Lit 1w] st3 = (dop,st4) /\
  emit_op MUL [lop; Lit (n2w sz)] st4 = (off,st5) /\
  emit_op ADD [dop; off] st5 = (pop,st6) /\
  eval_operand bop s3 = SOME slot /\ eval_operand lop s3 = SOME len /\
  fresh_vars_wrt st3 s3 ==>
  ?s4 s5 s6.
    run_inst_seq (emitted_insts st3 st4) s3 = OK s4 /\
    run_inst_seq (emitted_insts st4 st5) s4 = OK s5 /\
    run_inst_seq (emitted_insts st5 st6) s5 = OK s6 /\
    state_frame s4 = state_frame s3 /\ state_frame s5 = state_frame s4 /\
    state_frame s6 = state_frame s5 /\
    fresh_vars_wrt st4 s4 /\ fresh_vars_wrt st5 s5 /\ fresh_vars_wrt st6 s6 /\
    eval_operand pop s6 = SOME (slot+1w+len*n2w sz) /\
    (!op w. eval_operand op s3 = SOME w ==> eval_operand op s4 = SOME w) /\
    (!op w. eval_operand op s4 = SOME w ==> eval_operand op s5 = SOME w) /\
    (!op w. eval_operand op s5 = SOME w ==> eval_operand op s6 = SOME w)
Proof
  strip_tac >>
  `eval_operand (Lit 1w) s3 = SOME 1w` by simp[eval_operand_def] >>
  drule_all emitHelperPropsTheory.emit_op_ADD_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st3 st4) s3 = OK s4` >>
  `eval_operand lop s4 = SOME len /\
   eval_operand (Lit (n2w sz)) s4 = SOME (n2w sz)` by
    (simp[eval_operand_def] >> metis_tac[]) >>
  drule_all emitHelperPropsTheory.emit_op_MUL_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st4 st5) s4 = OK s5` >>
  `eval_operand dop s5 = SOME (slot+1w)` by metis_tac[] >>
  drule_all emitHelperPropsTheory.emit_op_ADD_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st5 st6) s5 = OK s6` >>
  `state_frame s4 = state_frame s3` by
    (irule append_storage_seq_frame >>
     qexists `emitted_insts st3 st4` >> simp[] >>
     qpat_assum `emit_op ADD [bop; _] _ = _`
       (mp_then Any mp_tac emitted_insts_emit_op) >> simp[mk_inst_def]) >>
  `state_frame s5 = state_frame s4` by
    (irule append_storage_seq_frame >>
     qexists `emitted_insts st4 st5` >> simp[] >>
     qpat_assum `emit_op MUL _ _ = _`
       (mp_then Any mp_tac emitted_insts_emit_op) >> simp[mk_inst_def]) >>
  `state_frame s6 = state_frame s5` by
    (irule append_storage_seq_frame >>
     qexists `emitted_insts st5 st6` >> simp[] >>
     qpat_assum `emit_op ADD [dop; off] _ = _`
       (mp_then Any mp_tac emitted_insts_emit_op) >> simp[mk_inst_def]) >>
  qexistsl [`s4`,`s5`,`s6`] >> asm_rewrite_tac[]
QED

Theorem intcall_append_aggregate_guard_address_run:
  emit_op (if tr then TLOAD else SLOAD) [bop] sa = (lop,s1) /\
  emit_op LT [lop;Lit (n2w cap)] s1 = (valid,s2) /\
  emit_void ASSERT [valid] s2 = ((),s3) /\
  emit_op ADD [bop;Lit 1w] s3 = (dop,s4) /\
  emit_op MUL [lop;Lit (n2w sz)] s4 = (off,s5) /\
  emit_op ADD [dop;off] s5 = (pop,s6) /\
  eval_operand bop s = SOME slot /\ fresh_vars_wrt sa s /\
  cap < dimword (:256) ==>
  ?u1 u2.
    run_inst_seq (emitted_insts sa s1) s = OK u1 /\
    run_inst_seq (emitted_insts s1 s2) u1 = OK u2 /\
    state_frame u2 = state_frame s /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op u2 = SOME w) /\
    (if cap <= w2n (if tr then tload slot s else sload slot s) then
       run_inst_seq (emitted_insts s2 s3) u2 =
         Abort Revert_abort (revert_state (set_returndata [] u2))
     else ?u4 u5 u6.
       run_inst_seq (emitted_insts s2 s3) u2 = OK u2 /\
       run_inst_seq (emitted_insts s3 s4) u2 = OK u4 /\
       run_inst_seq (emitted_insts s4 s5) u4 = OK u5 /\
       run_inst_seq (emitted_insts s5 s6) u5 = OK u6 /\
       state_frame u6 = state_frame s /\ fresh_vars_wrt s6 u6 /\
       eval_operand pop u6 = SOME
         (slot+1w+(if tr then tload slot s else sload slot s)*n2w sz) /\
       eval_operand lop u6 = SOME (if tr then tload slot s else sload slot s) /\
       (!op w. eval_operand op s = SOME w ==> eval_operand op u6 = SOME w))
Proof
  strip_tac >> drule_all append_storage_check_stages >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts s1 s2) u1 = OK u2` >>
  qexistsl [`u1`,`u2`] >>
  asm_rewrite_tac[] >>
  conj_tac >- metis_tac[] >>
  IF_CASES_TAC
  >- (irule append_storage_assert_abort_stage >> qexistsl [`F`,`valid`] >>
      gvs[arithmeticTheory.NOT_LESS]) >>
  `w2n (if tr then tload slot s else sload slot s) < cap` by decide_tac >>
  `run_inst_seq (emitted_insts s2 s3) u2 = OK u2 /\ fresh_vars_wrt s3 u2` by
    (irule append_storage_assert_success_stage >> asm_rewrite_tac[] >>
     qexistsl [`T`,`valid`] >> asm_rewrite_tac[]) >>
  `eval_operand bop u2 = SOME slot` by metis_tac[] >>
  drule_all intcall_append_aggregate_address_stages >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts s5 s6) u5 = OK u6` >>
  rename1 `run_inst_seq (emitted_insts s3 s4) u2 = OK u4` >>
  qexistsl [`u4`,`u5`,`u6`] >> asm_rewrite_tac[] >> metis_tac[]
QED

Theorem intcall_append_aggregate_prefix_structure:
  emit_op (if tr then TLOAD else SLOAD) [bop] sa = (lop,s1) /\
  emit_op LT [lop;Lit (n2w cap)] s1 = (valid,s2) /\
  emit_void ASSERT [valid] s2 = ((),s3) /\
  emit_op ADD [bop;Lit 1w] s3 = (dop,s4) /\
  emit_op MUL [lop;Lit (n2w sz)] s4 = (off,s5) /\
  emit_op ADD [dop;off] s5 = (pop,s6) ==>
  same_blocks sa s6 /\
  s6.cs_current_insts = sa.cs_current_insts ++
    (emitted_insts sa s1 ++ emitted_insts s1 s2 ++ emitted_insts s2 s3 ++
     emitted_insts s3 s4 ++ emitted_insts s4 s5 ++ emitted_insts s5 s6) /\
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
             ~is_terminator i.inst_opcode) (emitted_insts sa s6)
Proof
  Cases_on `tr` >>
  simp[emit_op_def,emit_void_def,fresh_id_def,fresh_var_def,emit_def,
       comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
  strip_tac >> gvs[] >>
  simp[same_blocks_def,emitted_insts_def] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC,rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[mk_inst_def,is_terminator_def,rich_listTheory.DROP_APPEND2]
QED

Theorem intcall_append_prefix_paths[local]:
  fn_has_code sa sb func /\ same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ code /\
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
             ~is_terminator i.inst_opcode) code /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  (!t. run_inst_seq code s = OK t ==>
    gas_marked_path F ctx func s 0 (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb) /\
  (!a t. run_inst_seq code s = Abort a t ==>
    ?j. gas_marked_path F ctx func s 0 (Abort a (t with vs_inst_idx := j)))
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
   FILTER (\i. i.inst_opcode = GAS) code = []` by
    (gvs[listTheory.EVERY_MEM,listTheory.FILTER_EQ_NIL] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> drule_all hash_run_path >> simp[]) >>
  drule_all fn_has_code_code >> strip_tac >> rpt strip_tac >>
  irule run_inst_seq_abort_zero_path >> asm_rewrite_tac[] >>
  qexistsl [`bb`,`code`] >> simp[]
QED

Theorem intcall_append_aggregate_prefix:
  emit_op (if tr then TLOAD else SLOAD) [bop] sa = (lop,s1) /\
  emit_op LT [lop;Lit (n2w cap)] s1 = (valid,s2) /\
  emit_void ASSERT [valid] s2 = ((),s3) /\
  emit_op ADD [bop;Lit 1w] s3 = (dop,s4) /\
  emit_op MUL [lop;Lit (n2w sz)] s4 = (off,s5) /\
  emit_op ADD [dop;off] s5 = (pop,s6) /\
  fn_has_code sa s6 func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand bop s = SOME slot /\ fresh_vars_wrt sa s /\
  cap < dimword (:256) ==>
  if cap <= w2n (if tr then tload slot s else sload slot s) then
    ?u j. state_frame u = state_frame s /\
      gas_marked_path F ctx func s 0
        (Abort Revert_abort (revert_state (set_returndata [] u) with vs_inst_idx := j))
  else ?u.
    gas_marked_path F ctx func s 0 (OK (u with vs_inst_idx := LENGTH s6.cs_current_insts)) /\
    ~u.vs_halted /\ u.vs_current_bb = s6.cs_current_bb /\
    state_frame u = state_frame s /\ fresh_vars_wrt s6 u /\
    eval_operand pop u = SOME
      (slot+1w+(if tr then tload slot s else sload slot s)*n2w sz) /\
    eval_operand lop u = SOME (if tr then tload slot s else sload slot s) /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op u = SOME w)
Proof
  strip_tac >>
  drule_all intcall_append_aggregate_prefix_structure >> strip_tac >>
  qmatch_asmsub_abbrev_tac `s6.cs_current_insts = sa.cs_current_insts ++ code` >>
  `emitted_insts sa s6 = code` by
    simp[emitted_insts_def,rich_listTheory.DROP_LENGTH_APPEND] >>
  fs[] >> drule_all intcall_append_prefix_paths >> strip_tac >>
  drule_all intcall_append_aggregate_guard_address_run >> strip_tac >>
  IF_CASES_TAC >>
  qpat_x_assum `if _ then _ else _` mp_tac >> asm_rewrite_tac[] >> strip_tac
  >- (`run_inst_seq code s = Abort Revert_abort (revert_state (set_returndata [] u2))` by
        (pure_rewrite_tac [markerTheory.Abbrev_def] >>
         simp[Abbr `code`] >> imp_res_tac run_inst_seq_append >>
         pure_rewrite_tac [GSYM listTheory.APPEND_ASSOC] >>
         asm_rewrite_tac[] >>
         irule EQ_TRANS >> qexists `run_inst_seq (emitted_insts s2 s3) u2` >>
         conj_tac >- (irule run_inst_seq_append_err >> asm_rewrite_tac[] >> simp[]) >>
         asm_rewrite_tac[]) >>
      qpat_x_assum `!ctx. _` (qspec_then `ctx` strip_assume_tac) >>
      qpat_x_assum `!a t. _` drule >> strip_tac >>
      qexistsl [`u2`,`j`] >> fs[state_frame_def]) >>
  rename1 `run_inst_seq (emitted_insts s5 s6) u5 = OK u6` >>
  `run_inst_seq code s = OK u6` by
    (simp[Abbr `code`] >> imp_res_tac run_inst_seq_append >>
     pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >> asm_rewrite_tac[]) >>
  qpat_x_assum `!ctx. _` (qspec_then `ctx` strip_assume_tac) >>
  qpat_x_assum `!t. _` drule >> strip_tac >>
  qexists `u6` >> gvs[state_frame_def,same_blocks_def]
QED

Theorem intcall_append_aggregate_suffix_code:
  emit_op (if tr then TLOAD else SLOAD) [bop] sa = (lop,s1) /\
  emit_op LT [lop;Lit (n2w cap)] s1 = (valid,s2) /\
  emit_void ASSERT [valid] s2 = ((),s3) /\
  emit_op ADD [bop;Lit 1w] s3 = (dop,s4) /\
  emit_op MUL [lop;Lit (n2w sz)] s4 = (off,s5) /\
  emit_op ADD [dop;off] s5 = (pop,s6) /\
  compile_store_slots ce vop pop elem tr s6 = ((),s7) /\
  emit_op ADD [lop;Lit 1w] s7 = (nop,s8) /\
  emit_void (if tr then TSTORE else SSTORE) [bop;nop] s8 = ((),sf) /\
  fn_has_code sa sf func ==>
  cs_extends sa s6 /\ cs_extends s6 s7 /\ cs_extends s7 s8 /\ cs_extends s8 sf /\
  fn_has_code sa s6 func /\ fn_has_code s6 s7 func /\
  fn_has_code s7 s8 func /\ fn_has_code s8 sf func
Proof
  strip_tac >>
  imp_res_tac reason_emit_op_cs_extends >>
  imp_res_tac reason_emit_void_cs_extends >>
  `cs_extends s6 s7` by
    (mp_tac (cj 1 ci_mono_compile_store_slots) >>
     simp[ci_mono_def] >> metis_tac[pairTheory.SND]) >>
  metis_tac[cs_extends_trans,fragExecTheory.fn_has_code_mid,
            fragExecTheory.fn_has_code_split]
QED
