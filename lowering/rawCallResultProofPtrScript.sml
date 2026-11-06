(* Finish-code boundaries for raw_call, after operand/output preparation. *)
Theory rawCallResultProofPtr
Ancestors
  rawCallOracleProofPtr rawCallBufferPtr builtinSystem context emitHelper
  compileEnv exprLoweringProps bodyPtrDefs builtinSimple
Libs
  monadsyntax

Theorem raw_call_finish_zero_bool_code:
  compile_raw_call_finish addr dp dl gas value ct 0 F ov op =
    (case ct of
       DelegateCall => emit_op DELEGATECALL [gas;addr;dp;dl;op;Lit 0w]
     | StaticCall => emit_op STATICCALL [gas;addr;dp;dl;op;Lit 0w]
     | RegularCall => emit_op CALL [gas;addr;value;dp;dl;op;Lit 0w])
Proof
  Cases_on `ct` >> simp[FUN_EQ_THM, compile_raw_call_finish_def,
    comp_bind_def, comp_return_def] >> gen_tac >> pairarg_tac >> simp[]
QED

Theorem raw_call_nonrevert_finish_code:
  compile_raw_call_finish addr dp dl gas value ct n F ov op sa = (result,sb) ==>
  ?ok sc. (case ct of
      DelegateCall => emit_op DELEGATECALL [gas;addr;dp;dl;op;Lit (n2w n)]
    | StaticCall => emit_op STATICCALL [gas;addr;dp;dl;op;Lit (n2w n)]
    | RegularCall => emit_op CALL [gas;addr;value;dp;dl;op;Lit (n2w n)]) sa = (ok,sc) /\
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
     else return ok) sc = (result,sb)
Proof
  simp[compile_raw_call_finish_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  qexistsl_tac [`success`, `s'`] >>
  gvs[comp_ignore_bind_def, comp_bind_def, arithmeticTheory.ADD_ASSOC]
QED

Theorem raw_call_tuple_suffix_steps:
  (do z <- emit_op RETURNDATASIZE [];
      cmp <- emit_op LT [z;Lit (n2w n)];
      cap <- compile_select cmp z (Lit (n2w n));
      emit_void MSTORE [ov;cap];
      buf <- compile_alloc_buffer (64 + ((n + 31) DIV 32) * 32);
      emit_void MSTORE [buf.buf_operand;ok];
      dst <- emit_op ADD [buf.buf_operand;Lit 32w];
      emit_void MCOPY [dst;ov;Lit (n2w (32 + ((n + 31) DIV 32) * 32))];
      return buf.buf_operand od) sa = (result,sb) ==>
  ?z s1 cmp s2 cap s3 s4 buf s5 s6 dst s7.
    emit_op RETURNDATASIZE [] sa = (z,s1) /\
    emit_op LT [z;Lit (n2w n)] s1 = (cmp,s2) /\
    compile_select cmp z (Lit (n2w n)) s2 = (cap,s3) /\
    emit_void MSTORE [ov;cap] s3 = ((),s4) /\
    compile_alloc_buffer (64 + ((n + 31) DIV 32) * 32) s4 = (buf,s5) /\
    emit_void MSTORE [buf.buf_operand;ok] s5 = ((),s6) /\
    emit_op ADD [buf.buf_operand;Lit 32w] s6 = (dst,s7) /\
    emit_void MCOPY [dst;ov;Lit (n2w (32 + ((n + 31) DIV 32) * 32))]
      s7 = ((),sb) /\ result = buf.buf_operand
Proof
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem raw_call_bytes_suffix_steps:
  (do z <- emit_op RETURNDATASIZE [];
      cmp <- emit_op LT [z;Lit (n2w n)];
      cap <- compile_select cmp z (Lit (n2w n));
      emit_void MSTORE [ov;cap]; return ov od) sa = (result,sb) ==>
  ?z s1 cmp s2 cap s3.
    emit_op RETURNDATASIZE [] sa = (z,s1) /\
    emit_op LT [z;Lit (n2w n)] s1 = (cmp,s2) /\
    compile_select cmp z (Lit (n2w n)) s2 = (cap,s3) /\
    emit_void MSTORE [ov;cap] s3 = ((),sb) /\ result = ov
Proof
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem raw_call_bytes_suffix_code:
  (do z <- emit_op RETURNDATASIZE [];
      cmp <- emit_op LT [z;Lit (n2w n)];
      cap <- compile_select cmp z (Lit (n2w n));
      emit_void MSTORE [ov;cap]; return ov od) sa = (result,sb) ==>
  same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  simp[compile_select_def, comp_bind_def, emit_op_def, fresh_var_def,
    fresh_id_def, comp_ignore_bind_def, comp_return_def, emit_def, emit_void_def] >>
  strip_tac >> gvs[] >> simp[same_blocks_def, emitted_insts_def] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC,
    rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]
QED

Theorem raw_call_returndatasize_step_base:
  step_inst_base (mk_inst iid RETURNDATASIZE [] [out]) s =
    OK (update_var out (n2w (LENGTH s.vs_returndata)) s)
Proof
  PURE_ONCE_REWRITE_TAC[venomExecSemanticsTheory.step_inst_base_def] >>
  simp[venomInstTheory.mk_inst_def, venomExecSemanticsTheory.exec_read0_def,
    venomExecSemanticsTheory.bind_outputs_def]
QED

Theorem ptr_inst_ok_returndatasize:
  ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx func G tn (mk_inst iid RETURNDATASIZE [] [out]) s
Proof
  strip_tac >>
  simp[ptrSafeRunTheory.ptr_inst_ok_def, ptrDisciplineTheory.access_ok_def,
    ptrDisciplineTheory.taint_ok_def, ptrDisciplineTheory.allocas_from_def,
    venomInstTheory.mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
    contextCodegenRelTheory.source_memory_read_ranges_def] >>
  simp[venomExecSemanticsTheory.step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[venomExecSemanticsTheory.step_inst_base_def] >>
  simp[venomInstTheory.mk_inst_def, venomExecSemanticsTheory.exec_read0_def,
    venomExecSemanticsTheory.bind_outputs_def, venomStateTheory.update_var_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem raw_call_returndatasize_path_ptr:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst iid RETURNDATASIZE [] [out]) /\
  u = update_var out (n2w (LENGTH s.vs_returndata)) s ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst iid RETURNDATASIZE [] [out]) u)
    (step_taint (mk_inst iid RETURNDATASIZE [] [out]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_inst_base (mk_inst iid RETURNDATASIZE [] [out]) s = OK u` by
    simp[raw_call_returndatasize_step_base] >>
  `ptr_inst_ok D 0 0 ctx func G tn (mk_inst iid RETURNDATASIZE [] [out]) s` by
    simp[ptr_inst_ok_returndatasize] >>
  `(mk_inst iid RETURNDATASIZE [] [out]).inst_opcode <> INVOKE /\
    ~is_terminator (mk_inst iid RETURNDATASIZE [] [out]).inst_opcode` by
    simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def] >>
  drule_all fragGasSeqPtrTheory.straight_line_ptr_edge >>
  disch_then (qspec_then `PG` mp_tac) >>
  simp[venomInstTheory.mk_inst_def] >> strip_tac >>
  drule (cj 2 fragGasPathPtrTheory.gas_path_ptr_rules) >>
  disch_then (qspec_then `0` mp_tac) >> simp[] >> disch_then irule >>
  irule (cj 1 fragGasPathPtrTheory.gas_path_ptr_rules) >>
  simp[venomStateTheory.update_var_def]
QED

Theorem raw_call_returndatasize_ghost_frame:
  ghost_inv dep cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~not_fresh_at sa out /\ u = update_var out w s /\
  H = step_prov PG G (mk_inst iid RETURNDATASIZE [] [out]) u /\
  un = step_taint (mk_inst iid RETURNDATASIZE [] [out]) s u tn ==>
  ghost_inv dep cenv cx es H un (u with vs_inst_idx := k) /\
  ghost_kept cenv es sa G tn s H un
Proof
  strip_tac >> simp[rawCallHeaderFramePtrTheory.ghost_inv_inst_idx] >>
  irule rawCallHeaderFramePtrTheory.raw_call_header_ghost_frame >>
  goal_assum (drule_at Any) >> simp[] >> conj_tac
  >- (rpt strip_tac >> `x <> out` by metis_tac[] >> gvs[] >>
      simp[decoderGhostFramePtrTheory.step_prov_other_output,
        decoderGhostFramePtrTheory.step_taint_other_output,
        venomInstTheory.mk_inst_def, venomStateTheory.update_var_def,
        venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  gvs[ptrDisciplineTheory.step_taint_def, ptrDisciplineTheory.mem_taint_def,
    ptrDisciplineTheory.new_site_bytes_def, ptrDisciplineTheory.step_writes_def,
    ptrDisciplineTheory.written_taint_def, ptrDisciplineTheory.adopt_reset_def,
    ptrDisciplineTheory.store_taint_def, ptrDisciplineTheory.imm_taint_def,
    ptrDisciplineTheory.range_bytes_def, venomStateTheory.update_var_def,
    venomInstTheory.mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
    finite_mapTheory.FLOOKUP_DEF] >>
  rpt (CASE_TAC >> gvs[]) >> simp[SF CONJ_ss]
QED

Theorem raw_call_reverting_finish_steps:
  compile_raw_call_finish addr dp dl gas value ct n T ov op sa = (result,sb) ==>
  ?ok sc fail s1 pass s2 s3 fblock s4 rds s5 buf s6 s7 s8 pblock s9.
    (case ct of
       DelegateCall => emit_op DELEGATECALL [gas;addr;dp;dl;op;Lit (n2w n)]
     | StaticCall => emit_op STATICCALL [gas;addr;dp;dl;op;Lit (n2w n)]
     | RegularCall => emit_op CALL [gas;addr;value;dp;dl;op;Lit (n2w n)]) sa = (ok,sc) /\
    fresh_label "call_failed" sc = (fail,s1) /\
    fresh_label "call_ok" s1 = (pass,s2) /\
    emit_inst JNZ [ok;Label pass;Label fail] [] s2 = ((),s3) /\
    new_block fail s3 = (fblock,s4) /\
    emit_op RETURNDATASIZE [] s4 = (rds,s5) /\
    compile_alloc_buffer 0 s5 = (buf,s6) /\
    emit_void RETURNDATACOPY [buf.buf_operand;Lit 0w;rds] s6 = ((),s7) /\
    emit_inst REVERT [buf.buf_operand;rds] [] s7 = ((),s8) /\
    new_block pass s8 = (pblock,s9) /\
    (if n > 0 then
       do z <- emit_op RETURNDATASIZE [];
          cmp <- emit_op LT [z;Lit (n2w n)];
          cap <- compile_select cmp z (Lit (n2w n));
          emit_void MSTORE [ov;cap]; return ov od
     else return (Lit 0w)) s9 = (result,sb)
Proof
  simp[compile_raw_call_finish_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem raw_call_emit_returndatasize_path_ptr:
  emit_op RETURNDATASIZE [] sa = (Var out,sb) /\ fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  u = update_var out (n2w (LENGTH s.vs_returndata)) s ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id RETURNDATASIZE [] [out]) u)
    (step_taint (mk_inst sa.cs_next_id RETURNDATASIZE [] [out]) s u tn)
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id RETURNDATASIZE [] [out]]` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
      fresh_id_def, emit_def, comp_return_def]) >>
  drule_all fragExecTheory.fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst sa.cs_next_id RETURNDATASIZE [] [out])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `LENGTH sb.cs_current_insts = SUC s.vs_inst_idx` by simp[] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  drule_all raw_call_returndatasize_path_ptr >> simp[]
QED

Theorem raw_call_returndatasize_step_taint:
  step_taint (mk_inst iid RETURNDATASIZE [] [out]) s (update_var out w s) tn =
  tn with t_var := tn.t_var |+ (out,{})
Proof
  simp[ptrDisciplineTheory.step_taint_def, venomInstTheory.mk_inst_def,
    ptrDisciplineTheory.out_taint_def, ptrDisciplineTheory.set_var_taint_def,
    ptrDisciplineTheory.adopt_reset_def, ptrDisciplineTheory.store_taint_def,
    ptrDisciplineTheory.imm_taint_def, ptrDisciplineTheory.mem_taint_def,
    ptrDisciplineTheory.new_site_bytes_def, ptrDisciplineTheory.step_writes_def,
    ptrDisciplineTheory.written_taint_def, ptrDisciplineTheory.range_bytes_def,
    codegenRelTheory.source_memory_write_ranges_def,
    venomStateTheory.update_var_def, finite_mapTheory.FLOOKUP_DEF] >>
  simp[SF CONJ_ss, ptrDisciplineTheory.taint_component_equality]
QED

Theorem raw_call_emit_returndatasize_stage:
  emit_op RETURNDATASIZE [] sa = (Var out,sb) /\ fn_has_code sa sb func /\
  stmt_state_rel ctx func cenv cx es s /\
  ghost_inv dep cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx ==>
  ?H un t. gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 H un (OK t) /\
    ghost_inv dep cenv cx es H un t /\ ghost_kept cenv es sa G tn s H un /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es sa s t /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    eval_operand (Var out) t = SOME (n2w (LENGTH s.vs_returndata)) /\
    t.vs_returndata = s.vs_returndata /\ op_taint un (Var out) = {} /\
    op_prov H (Var out) = NONE /\
    not_fresh_at sb out /\ t.vs_memory = s.vs_memory /\ un.t_mem = tn.t_mem
Proof
  strip_tac >> qabbrev_tac `u = update_var out (n2w (LENGTH s.vs_returndata)) s` >>
  `gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id RETURNDATASIZE [] [out]) u)
    (step_taint (mk_inst sa.cs_next_id RETURNDATASIZE [] [out]) s u tn)
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule raw_call_emit_returndatasize_path_ptr >> simp[Abbr `u`]) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr _ _ _ _ _ _ _ _ _ H un (OK t)` >>
  `~not_fresh_at sa out /\ not_fresh_at sb out /\
   sb.cs_current_bb = sa.cs_current_bb` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
       fresh_id_def, emit_def, comp_return_def] >> rpt strip_tac >> gvs[] >>
     fs[not_fresh_at_def]) >>
  `ghost_inv dep cenv cx es H un t /\ ghost_kept cenv es sa G tn s H un` by
    (qunabbrev_tac `t` >> irule raw_call_returndatasize_ghost_frame >>
     goal_assum (drule_at Any) >> simp[Abbr `H`, Abbr `un`] >>
     qexistsl_tac [`PG`, `sa.cs_next_id`] >> simp[] >>
     qexistsl_tac [`out`, `n2w (LENGTH s.vs_returndata)`] >> simp[Abbr `u`]) >>
  `stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es sa s t` by
    (simp[Abbr `t`, Abbr `u`] >>
     irule rawCallDataHeaderPtrTheory.raw_call_fresh_update_state_frame >> simp[]) >>
  qexistsl_tac [`H`, `un`, `t`] >> simp[] >>
  simp[Abbr `un`, Abbr `u`, raw_call_returndatasize_step_taint] >>
  simp[Abbr `t`, Abbr `H`, venomStateTheory.update_var_def,
    venomStateTheory.lookup_var_def, venomStateTheory.eval_operand_def,
    finite_mapTheory.FLOOKUP_UPDATE, ptrDisciplineTheory.op_taint_def,
    ptrDisciplineTheory.step_prov_def, ptrDisciplineTheory.set_prov_def,
    ptrDisciplineTheory.out_prov_def, ptrDisciplineTheory.op_prov_def,
    venomInstTheory.mk_inst_def, finite_mapTheory.FLOOKUP_DRESTRICT]
QED
