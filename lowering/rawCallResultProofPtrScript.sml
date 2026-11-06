(* Finish-code boundaries for raw_call, after operand/output preparation. *)
Theory rawCallResultProofPtr
Ancestors
  rawCallOracleProofPtr rawCallBufferPtr builtinSystem context emitHelper
  compileEnv exprLoweringProps bodyPtrDefs builtinSimple builtinProps
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
  gvs[venomStateTheory.update_var_def]
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
    not_fresh_at sb out /\ t.vs_memory = s.vs_memory /\ un.t_mem = tn.t_mem /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
      op_taint un (Var x) = op_taint tn (Var x))
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
    venomInstTheory.mk_inst_def, finite_mapTheory.FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> `x <> out` by metis_tac[] >> simp[]
QED

(* The capped-length prefix uses only integer operands.  In particular LT
   must not be treated as a same-site pointer comparison. *)
Theorem ptr_inst_ok_raw_call_length_binop:
  (opc = LT \/ opc = XOR \/ opc = MUL) /\
  op_prov G left = NONE /\ op_prov G right = NONE /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx func G tn
    (mk_inst iid opc [left;right] [out]) s
Proof
  strip_tac >> gvs[] >>
  simp[ptrSafeRunTheory.ptr_inst_ok_def, ptrDisciplineTheory.access_ok_def,
    ptrDisciplineTheory.taint_ok_def, ptrDisciplineTheory.allocas_from_def,
    venomInstTheory.mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
    contextCodegenRelTheory.source_memory_read_ranges_def] >>
  conj_tac >- (rpt strip_tac >>
    gvs[ptrDisciplineTheory.op_prov_def, finite_mapTheory.FLOOKUP_DEF]) >>
  simp[venomExecSemanticsTheory.step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[venomExecSemanticsTheory.step_inst_base_def] >>
  pure_rewrite_tac[venomInstTheory.instruction_accessors,
    venomInstTheory.instruction_accfupds, combinTheory.K_THM,
    venomInstTheory.opcode_case_def] >>
  simp[venomExecSemanticsTheory.exec_pure2_def, AllCaseEqs(),
    venomStateTheory.update_var_def] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem raw_call_length_binop_step_base:
  (opc = LT /\ f = (\x y. bool_to_word (w2n x < w2n y)) \/
   opc = XOR /\ f = word_xor \/ opc = MUL /\ f = word_mul) /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b ==>
  step_inst_base (mk_inst iid opc [left;right] [out]) s =
    OK (update_var out (f a b) s)
Proof
  strip_tac >> gvs[] >>
  PURE_ONCE_REWRITE_TAC[venomExecSemanticsTheory.step_inst_base_def] >>
  pure_rewrite_tac[venomInstTheory.mk_inst_def,
    venomInstTheory.instruction_accessors, venomInstTheory.instruction_accfupds,
    combinTheory.K_THM, venomInstTheory.opcode_case_def] >>
  simp[venomExecSemanticsTheory.exec_pure2_def]
QED

Theorem raw_call_length_binop_path_ptr:
  (opc = LT /\ f = (\x y. bool_to_word (w2n x < w2n y)) \/
   opc = XOR /\ f = word_xor \/ opc = MUL /\ f = word_mul) /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_prov G left = NONE /\ op_prov G right = NONE /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst iid opc [left;right] [out]) /\
  u = update_var out (f a b) s ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst iid opc [left;right] [out]) u)
    (step_taint (mk_inst iid opc [left;right] [out]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt gen_tac >> disch_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `step_inst_base (mk_inst iid opc [left;right] [out]) s = OK u` by
    (simp[] >> irule raw_call_length_binop_step_base >> metis_tac[]) >>
  `ptr_inst_ok D 0 0 ctx func G tn (mk_inst iid opc [left;right] [out]) s` by
    (irule ptr_inst_ok_raw_call_length_binop >> simp[] >> metis_tac[]) >>
  `(mk_inst iid opc [left;right] [out]).inst_opcode <> INVOKE /\
    ~is_terminator (mk_inst iid opc [left;right] [out]).inst_opcode /\
    opc <> GAS` by
    (qpat_x_assum `_ \/ _` strip_assume_tac >>
     simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]) >>
  drule_all fragGasSeqPtrTheory.straight_line_ptr_edge >>
  disch_then (qspec_then `PG` mp_tac) >>
  simp[venomInstTheory.mk_inst_def] >> strip_tac >>
  drule (cj 2 fragGasPathPtrTheory.gas_path_ptr_rules) >>
  disch_then (qspec_then `0` mp_tac) >> simp[] >> disch_then irule >>
  irule (cj 1 fragGasPathPtrTheory.gas_path_ptr_rules) >>
  gvs[venomStateTheory.update_var_def]
QED

Theorem raw_call_length_binop_step_ghost:
  (opc = LT \/ opc = XOR \/ opc = MUL) ==>
  step_taint (mk_inst iid opc [left;right] [out]) s (update_var out w s) tn =
    tn with t_var := tn.t_var |+ (out,{}) /\
  step_prov PG G (mk_inst iid opc [left;right] [out]) (update_var out w s) =
    DRESTRICT G (COMPL {out})
Proof
  strip_tac >> gvs[] >>
  simp[ptrDisciplineTheory.step_taint_def, venomInstTheory.mk_inst_def,
    ptrDisciplineTheory.out_taint_def, ptrDisciplineTheory.set_var_taint_def,
    ptrDisciplineTheory.adopt_reset_def, ptrDisciplineTheory.store_taint_def,
    ptrDisciplineTheory.imm_taint_def, ptrDisciplineTheory.mem_taint_def,
    ptrDisciplineTheory.new_site_bytes_def, ptrDisciplineTheory.step_writes_def,
    ptrDisciplineTheory.written_taint_def, ptrDisciplineTheory.range_bytes_def,
    codegenRelTheory.source_memory_write_ranges_def,
    venomStateTheory.update_var_def, finite_mapTheory.FLOOKUP_DEF,
    ptrDisciplineTheory.step_prov_def, ptrDisciplineTheory.set_prov_def,
    ptrDisciplineTheory.out_prov_def] >>
  Cases_on `eval_operand left s` >>
  simp[SF CONJ_ss, ptrDisciplineTheory.taint_component_equality]
QED

Theorem raw_call_length_binop_ghost_frame:
  ghost_inv dep cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~not_fresh_at sa out ==>
  ghost_inv dep cenv cx es (DRESTRICT G (COMPL {out}))
    (tn with t_var := tn.t_var |+ (out,{}))
    (update_var out w s with vs_inst_idx := k) /\
  ghost_kept cenv es sa G tn s (DRESTRICT G (COMPL {out}))
    (tn with t_var := tn.t_var |+ (out,{}))
Proof
  strip_tac >> simp[rawCallHeaderFramePtrTheory.ghost_inv_inst_idx] >>
  irule rawCallHeaderFramePtrTheory.raw_call_header_ghost_frame >>
  goal_assum (drule_at Any) >>
  simp[venomStateTheory.update_var_def] >> rpt strip_tac >>
  `x <> out` by metis_tac[] >>
  simp[venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
    finite_mapTheory.FLOOKUP_DRESTRICT, ptrDisciplineTheory.op_taint_def]
QED

Theorem raw_call_emit_length_binop_path_ptr:
  emit_op opc [left;right] sa = (Var out,sb) /\ fn_has_code sa sb func /\
  (opc = LT /\ f = (\x y. bool_to_word (w2n x < w2n y)) \/
   opc = XOR /\ f = word_xor \/ opc = MUL /\ f = word_mul) /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_prov G left = NONE /\ op_prov G right = NONE /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (DRESTRICT G (COMPL {out})) (tn with t_var := tn.t_var |+ (out,{}))
    (OK (update_var out (f a b) s with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  rpt gen_tac >> disch_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id opc [left;right] [out]]` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
      fresh_id_def, emit_def, comp_return_def]) >>
  drule_all fragExecTheory.fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst sa.cs_next_id opc [left;right] [out])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `LENGTH sb.cs_current_insts = SUC s.vs_inst_idx` by simp[] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `gas_path_ptr D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id opc [left;right] [out])
      (update_var out (f a b) s))
    (step_taint (mk_inst sa.cs_next_id opc [left;right] [out]) s
      (update_var out (f a b) s) tn)
    (OK (update_var out (f a b) s with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule raw_call_length_binop_path_ptr >> goal_assum (drule_at Any) >>
     simp[] >> conj_tac >- metis_tac[] >> qexists_tac `f` >> simp[]) >>
  qpat_x_assum `_ \/ _` strip_assume_tac >> gvs[] >>
  fs[raw_call_length_binop_step_ghost, arithmeticTheory.ADD1]
QED

Theorem raw_call_emit_length_binop_stage:
  emit_op opc [left;right] sa = (Var out,sb) /\ fn_has_code sa sb func /\
  (opc = LT /\ f = (\x y. bool_to_word (w2n x < w2n y)) \/
   opc = XOR /\ f = word_xor \/ opc = MUL /\ f = word_mul) /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_prov G left = NONE /\ op_prov G right = NONE /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
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
    eval_operand (Var out) t = SOME (f a b) /\
    op_taint un (Var out) = {} /\ op_prov H (Var out) = NONE /\
    not_fresh_at sb out /\ t.vs_memory = s.vs_memory /\ un.t_mem = tn.t_mem /\
    t.vs_returndata = s.vs_returndata /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
      op_taint un (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> disch_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `~not_fresh_at sa out /\ not_fresh_at sb out /\
   sb.cs_current_bb = sa.cs_current_bb` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
       fresh_id_def, emit_def, comp_return_def] >> rpt strip_tac >> gvs[] >>
     fs[not_fresh_at_def]) >>
  qexistsl_tac [`DRESTRICT G (COMPL {out})`,
    `tn with t_var := tn.t_var |+ (out,{})`,
    `update_var out (f a b) s with vs_inst_idx := LENGTH sb.cs_current_insts`] >>
  conj_tac
  >- (irule raw_call_emit_length_binop_path_ptr >> simp[] >>
      qexistsl_tac [`left`, `opc`, `right`, `sa`] >> simp[]) >>
  `ghost_inv dep cenv cx es (DRESTRICT G (COMPL {out}))
     (tn with t_var := tn.t_var |+ (out,{}))
     (update_var out (f a b) s with vs_inst_idx := LENGTH sb.cs_current_insts) /\
   ghost_kept cenv es sa G tn s (DRESTRICT G (COMPL {out}))
     (tn with t_var := tn.t_var |+ (out,{}))` by
    (irule raw_call_length_binop_ghost_frame >> simp[]) >>
  drule_all rawCallDataHeaderPtrTheory.raw_call_fresh_update_state_frame >>
  disch_then (qspecl_then [`f a b`, `LENGTH sb.cs_current_insts`] assume_tac) >>
  simp[venomStateTheory.update_var_def, venomStateTheory.lookup_var_def,
    venomStateTheory.eval_operand_def, finite_mapTheory.FLOOKUP_UPDATE,
    finite_mapTheory.FLOOKUP_DRESTRICT, ptrDisciplineTheory.op_taint_def,
    ptrDisciplineTheory.op_prov_def] >> rpt strip_tac >>
  `x <> out` by metis_tac[] >>
  simp[venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
    finite_mapTheory.FLOOKUP_UPDATE, finite_mapTheory.FLOOKUP_DRESTRICT,
    ptrDisciplineTheory.op_taint_def]
QED

Theorem raw_call_scalar_update_operand:
  p <> Var out ==>
  eval_operand p (update_var out w s with vs_inst_idx := k) = eval_operand p s /\
  op_prov (DRESTRICT G (COMPL {out})) p = op_prov G p /\
  op_taint (tn with t_var := tn.t_var |+ (out,{})) p = op_taint tn p
Proof
  Cases_on `p` >>
  simp[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
    venomStateTheory.update_var_def, ptrDisciplineTheory.op_prov_def,
    ptrDisciplineTheory.op_taint_def, finite_mapTheory.FLOOKUP_UPDATE,
    finite_mapTheory.FLOOKUP_DRESTRICT] >> rpt strip_tac >> gvs[]
QED

Theorem raw_call_update_var_pc[local]:
  update_var x w (s with vs_inst_idx := k) =
    (update_var x w s) with vs_inst_idx := k
Proof
  gvs[venomStateTheory.update_var_def]
QED

Theorem raw_call_select_inst_seq_ptr:
  eval_operand condop s = SOME cv /\ eval_operand tp s = SOME tv /\
  eval_operand ep s = SOME ev /\
  op_prov G condop = NONE /\ op_prov G tp = NONE /\ op_prov G ep = NONE /\
  op_taint tn condop = {} /\ op_taint tn tp = {} /\ op_taint tn ep = {} /\
  condop <> Var d /\ ep <> Var d /\ ep <> Var m /\ d <> m /\
  ~ctx_has_dalloca ctx ==>
  inst_seq_ptr D 0 ctx func PG G tn
    [mk_inst i XOR [tp;ep] [d]; mk_inst j MUL [condop;Var d] [m];
     mk_inst k XOR [ep;Var m] [out]] s
    (DRESTRICT (DRESTRICT (DRESTRICT G (COMPL {d})) (COMPL {m})) (COMPL {out}))
    (tn with t_var := ((tn.t_var |+ (d,{})) |+ (m,{})) |+ (out,{}))
Proof
  strip_tac >>
  simp[Once fragGasSeqPtrTheory.inst_seq_ptr_def] >> conj_tac
  >- (irule ptr_inst_ok_raw_call_length_binop >> simp[]) >>
  `step_inst_base (mk_inst i XOR [tp;ep] [d]) s =
    OK (update_var d (word_xor tv ev) s)` by
    (irule raw_call_length_binop_step_base >> simp[]) >>
  simp[] >>
  simp[raw_call_length_binop_step_ghost] >>
  `eval_operand condop (update_var d (word_xor tv ev) s with
     vs_inst_idx := SUC s.vs_inst_idx) = SOME cv /\
   op_prov (DRESTRICT G (COMPL {d})) condop = NONE /\
   op_taint (tn with t_var := tn.t_var |+ (d,{})) condop = {}` by
    (simp[raw_call_scalar_update_operand]) >>
  simp[Once fragGasSeqPtrTheory.inst_seq_ptr_def] >> conj_tac
  >- (irule ptr_inst_ok_raw_call_length_binop >>
      simp[ptrDisciplineTheory.op_prov_def, ptrDisciplineTheory.op_taint_def,
        finite_mapTheory.FLOOKUP_UPDATE, finite_mapTheory.FLOOKUP_DRESTRICT]) >>
  `step_inst_base (mk_inst j MUL [condop;Var d] [m])
      (update_var d (word_xor tv ev) s with vs_inst_idx := SUC s.vs_inst_idx) =
    OK (update_var m (word_mul cv (word_xor tv ev))
      (update_var d (word_xor tv ev) s with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule raw_call_length_binop_step_base >>
     simp[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
       venomStateTheory.update_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  simp[] >> simp[raw_call_update_var_pc, raw_call_length_binop_step_ghost] >>
  simp[Once fragGasSeqPtrTheory.inst_seq_ptr_def] >> conj_tac
  >- (irule ptr_inst_ok_raw_call_length_binop >>
      simp[raw_call_scalar_update_operand, ptrDisciplineTheory.op_prov_def,
        ptrDisciplineTheory.op_taint_def, finite_mapTheory.FLOOKUP_UPDATE,
        finite_mapTheory.FLOOKUP_DRESTRICT] >>
      Cases_on `ep` >> gvs[ptrDisciplineTheory.op_prov_def,
        ptrDisciplineTheory.op_taint_def]) >>
  `step_inst_base (mk_inst k XOR [ep;Var m] [out])
      (update_var m (word_mul cv (word_xor tv ev)) (update_var d (word_xor tv ev) s)
        with vs_inst_idx := SUC (SUC s.vs_inst_idx)) =
    OK (update_var out (word_xor ev (word_mul cv (word_xor tv ev)))
      (update_var m (word_mul cv (word_xor tv ev)) (update_var d (word_xor tv ev) s)
        with vs_inst_idx := SUC (SUC s.vs_inst_idx)))` by
    (irule raw_call_length_binop_step_base >>
     simp[raw_call_scalar_update_operand, venomStateTheory.eval_operand_def,
       venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
     Cases_on `ep` >> gvs[venomStateTheory.eval_operand_def,
       venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  simp[fragGasSeqPtrTheory.inst_seq_ptr_def, raw_call_update_var_pc,
    raw_call_length_binop_step_ghost, pred_setTheory.INTER_ASSOC]
QED

Theorem raw_call_select_code:
  compile_select condop tp ep sa = (op,sb) ==>
  ?d m out. op = Var out /\
    d = STRING #"%" (toString sa.cs_next_var) /\
    m = STRING #"%" (toString (sa.cs_next_var + 1)) /\
    out = STRING #"%" (toString (sa.cs_next_var + 2)) /\
    same_blocks sa sb /\
    sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst sa.cs_next_id XOR [tp;ep] [d];
       mk_inst (sa.cs_next_id + 1) MUL [condop;Var d] [m];
       mk_inst (sa.cs_next_id + 2) XOR [ep;Var m] [out]] /\
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id XOR [tp;ep] [d];
       mk_inst (sa.cs_next_id + 1) MUL [condop;Var d] [m];
       mk_inst (sa.cs_next_id + 2) XOR [ep;Var m] [out]]
Proof
  simp[compile_select_def, comp_bind_def, emit_op_def, fresh_var_def,
    fresh_id_def, comp_ignore_bind_def, comp_return_def, emit_def] >>
  strip_tac >> gvs[] >> simp[same_blocks_def, emitted_insts_def] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC,
    rich_listTheory.DROP_LENGTH_APPEND] >> simp[arithmeticTheory.ADD_ASSOC]
QED

Theorem raw_call_select_checked_code:
  compile_select condop tp ep sa = (op,sb) /\
  eval_operand condop s = SOME cv /\ eval_operand tp s = SOME tv /\
  eval_operand ep s = SOME ev /\
  op_prov G condop = NONE /\ op_prov G tp = NONE /\ op_prov G ep = NONE /\
  op_taint tn condop = {} /\ op_taint tn tp = {} /\ op_taint tn ep = {} /\
  (!x. condop = Var x ==> not_fresh_at sa x) /\
  (!x. ep = Var x ==> not_fresh_at sa x) /\ ~ctx_has_dalloca ctx ==>
  ?H un. inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s H un /\
    op_prov H op = NONE /\ op_taint un op = {} /\
    un.t_mem = tn.t_mem /\ un.t_stor = tn.t_stor /\
    un.t_trans = tn.t_trans /\ un.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP H x = FLOOKUP G x /\ op_taint un (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule raw_call_select_code >> strip_tac >> simp[] >>
  irule_at Any raw_call_select_inst_seq_ptr >> simp[] >>
  conj_tac
  >- (strip_tac >> fs[not_fresh_at_def] >>
      first_x_assum (qspec_then `sa.cs_next_var` mp_tac) >> simp[]) >>
  conj_tac
  >- (strip_tac >> fs[not_fresh_at_def] >>
      first_x_assum (qspec_then `sa.cs_next_var` mp_tac) >> simp[]) >>
  conj_tac
  >- (strip_tac >> fs[not_fresh_at_def] >>
      first_x_assum (qspec_then `sa.cs_next_var + 1` mp_tac) >> simp[]) >>
  simp[ptrDisciplineTheory.op_prov_def, ptrDisciplineTheory.op_taint_def,
    finite_mapTheory.FLOOKUP_DRESTRICT, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  `x <> STRING #"%" (toString sa.cs_next_var) /\
   x <> STRING #"%" (toString (sa.cs_next_var + 1)) /\
   x <> STRING #"%" (toString (sa.cs_next_var + 2))` by
    (fs[not_fresh_at_def]) >> simp[]
QED

Theorem raw_call_select_state_frame:
  compile_select condop tp ep sa = (op,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  t = s with vs_vars := t.vs_vars /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule raw_call_select_code >> strip_tac >>
  `!i u v. MEM i (emitted_insts sa sb) /\ step_inst_base i u = OK v ==>
     v = u with vs_vars := v.vs_vars /\
     (!x. not_fresh_at sa x ==> FLOOKUP v.vs_vars x = FLOOKUP u.vs_vars x)` by
    (rpt gen_tac >> strip_tac >>
     `MEM i.inst_opcode
       [ADD; SUB; MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD;
        EQ; LT; GT; SLT; SGT; ISZERO; AND; OR; XOR; NOT;
        SHL; SHR; SAR; SIGNEXTEND; BYTE; ASSERT; ASSERT_UNREACHABLE]` by
       (gvs[venomInstTheory.mk_inst_def]) >>
     drule_all emitHelperPropsTheory.step_pure_opcode_frame >> strip_tac >>
     conj_tac >- simp[] >> rpt strip_tac >> first_x_assum irule >>
     gvs[venomInstTheory.mk_inst_def] >> fs[not_fresh_at_def]) >>
  drule_all emitHelperPropsTheory.run_inst_seq_protected_frame >>
  simp[venomStateTheory.lookup_var_def]
QED

Theorem raw_call_select_run:
  eval_operand condop s = SOME (bool_to_word b) /\
  eval_operand tp s = SOME tv /\ eval_operand ep s = SOME ev /\
  condop <> Var d /\ ep <> Var d /\ ep <> Var m /\ d <> m ==>
  ?t. run_inst_seq
    [mk_inst i XOR [tp;ep] [d]; mk_inst j MUL [condop;Var d] [m];
     mk_inst k XOR [ep;Var m] [out]] s = OK t /\
    eval_operand (Var out) t = SOME (if b then tv else ev)
Proof
  strip_tac >>
  `step_inst_base (mk_inst i XOR [tp;ep] [d]) s =
    OK (update_var d (word_xor tv ev) s)` by
    (irule raw_call_length_binop_step_base >> simp[]) >>
  `eval_operand condop (update_var d (word_xor tv ev) s) =
     SOME (bool_to_word b)` by
    (Cases_on `condop` >> gvs[venomStateTheory.eval_operand_def,
      venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
      finite_mapTheory.FLOOKUP_UPDATE]) >>
  `step_inst_base (mk_inst j MUL [condop;Var d] [m])
    (update_var d (word_xor tv ev) s) =
    OK (update_var m (word_mul (bool_to_word b) (word_xor tv ev))
      (update_var d (word_xor tv ev) s))` by
    (irule raw_call_length_binop_step_base >>
     simp[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
       venomStateTheory.update_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  `eval_operand ep (update_var m (word_mul (bool_to_word b) (word_xor tv ev))
      (update_var d (word_xor tv ev) s)) = SOME ev` by
    (Cases_on `ep` >> gvs[venomStateTheory.eval_operand_def,
      venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
      finite_mapTheory.FLOOKUP_UPDATE]) >>
  `step_inst_base (mk_inst k XOR [ep;Var m] [out])
    (update_var m (word_mul (bool_to_word b) (word_xor tv ev))
      (update_var d (word_xor tv ev) s)) =
    OK (update_var out (word_xor ev (word_mul (bool_to_word b) (word_xor tv ev)))
      (update_var m (word_mul (bool_to_word b) (word_xor tv ev))
        (update_var d (word_xor tv ev) s)))` by
    (irule raw_call_length_binop_step_base >>
     simp[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
       venomStateTheory.update_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  simp[run_inst_seq_def] >>
  Cases_on `b` >> simp[venomExecSemanticsTheory.bool_to_word_def,
    venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
    venomStateTheory.update_var_def, finite_mapTheory.FLOOKUP_UPDATE,
    wordsTheory.WORD_MULT_CLAUSES, wordsTheory.WORD_XOR_CLAUSES] >>
  metis_tac[wordsTheory.WORD_XOR_ASSOC, wordsTheory.WORD_XOR_COMM,
    wordsTheory.WORD_XOR_CLAUSES]
QED

Theorem raw_call_select_run_code:
  compile_select condop tp ep sa = (op,sb) /\
  eval_operand condop s = SOME (bool_to_word b) /\
  eval_operand tp s = SOME tv /\ eval_operand ep s = SOME ev /\
  (!x. condop = Var x ==> not_fresh_at sa x) /\
  (!x. ep = Var x ==> not_fresh_at sa x) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (if b then tv else ev)
Proof
  strip_tac >> drule raw_call_select_code >> strip_tac >> simp[] >>
  irule raw_call_select_run >> simp[] >> rpt conj_tac >> strip_tac >>
  fs[not_fresh_at_def] >>
  first_x_assum (qspec_then `sa.cs_next_var` mp_tac) >> simp[]
QED

Theorem raw_call_select_path_ptr:
  compile_select condop tp ep sa = (op,sb) /\ fn_has_code sa sb func /\
  eval_operand condop s = SOME (bool_to_word b) /\
  eval_operand tp s = SOME tv /\ eval_operand ep s = SOME ev /\
  op_prov G condop = NONE /\ op_prov G tp = NONE /\ op_prov G ep = NONE /\
  op_taint tn condop = {} /\ op_taint tn tp = {} /\ op_taint tn ep = {} /\
  (!x. condop = Var x ==> not_fresh_at sa x) /\
  (!x. ep = Var x ==> not_fresh_at sa x) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx ==>
  ?H un t. gas_path_ptr D 0 ctx func PG G tn s 0 H un (OK t) /\
    eval_operand op t = SOME (if b then tv else ev) /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t = s with <|vs_vars := t.vs_vars; vs_inst_idx := LENGTH sb.cs_current_insts|> /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    op_prov H op = NONE /\ op_taint un op = {} /\
    un.t_mem = tn.t_mem /\ un.t_stor = tn.t_stor /\
    un.t_trans = tn.t_trans /\ un.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP H x = FLOOKUP G x /\ op_taint un (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all raw_call_select_run_code >> strip_tac >>
  drule_all raw_call_select_state_frame >> strip_tac >>
  drule_all raw_call_select_checked_code >>
  disch_then (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
  drule raw_call_select_code >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[fragExecTheory.fn_has_code_def, same_blocks_def] >>
     gvs[rich_listTheory.IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC,
       rich_listTheory.DROP_LENGTH_APPEND] >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)` by
    simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def] >>
  drule_all fragGasSeqPtrTheory.run_inst_seq_gas_path_ptr >>
  simp[venomInstTheory.mk_inst_def] >> strip_tac >>
  rpt (goal_assum (drule_at Any)) >>
  gvs[venomStateTheory.update_var_def] >> conj_tac
  >- (qpat_x_assum `_ = _ with vs_vars := _`
        (fn th => once_rewrite_tac[th]) >> simp[]) >>
  fs[venomStateTheory.lookup_var_def]
QED


Theorem raw_call_scalar_state_frame:
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  t = s with <|vs_vars := t.vs_vars; vs_inst_idx := k|> /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) ==>
  stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es sa s t
Proof
  strip_tac >> conj_tac
  >- (`stmt_state_rel ctx func cenv cx es (t with vs_inst_idx := s.vs_inst_idx)`
        suffices_by simp[exprLoweringPropsTheory.stmt_state_rel_inst_idx] >>
      irule exprSimHashTheory.hash_readonly_state_rel >>
      goal_assum (drule_at Any) >>
      qexists_tac `s` >> simp[venomStateTheory.lookup_var_def] >>
      qpat_x_assum `t = _` (fn th => once_rewrite_tac[th]) >>
      fs[venomStateTheory.lookup_var_def]) >>
  simp[loweringPostsTheory.wb_frame_def, loweringPostsTheory.locals_kept_def] >>
  qpat_x_assum `t = _` (fn th => once_rewrite_tac[th]) >>
  simp[venomStateTheory.lookup_var_def] >>
  fs[venomStateTheory.lookup_var_def]
QED

Theorem raw_call_select_stage:
  compile_select condop tp ep sa = (op,sb) /\ fn_has_code sa sb func /\
  eval_operand condop s = SOME (bool_to_word b) /\
  eval_operand tp s = SOME tv /\ eval_operand ep s = SOME ev /\
  op_prov G condop = NONE /\ op_prov G tp = NONE /\ op_prov G ep = NONE /\
  op_taint tn condop = {} /\ op_taint tn tp = {} /\ op_taint tn ep = {} /\
  (!x. condop = Var x ==> not_fresh_at sa x) /\
  (!x. ep = Var x ==> not_fresh_at sa x) /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv dep cenv cx es G tn s /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx ==>
  ?H un t. gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 H un (OK t) /\
    eval_operand op t = SOME (if b then tv else ev) /\
    ghost_inv dep cenv cx es H un t /\ ghost_kept cenv es sa G tn s H un /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es sa s t /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    op_prov H op = NONE /\ op_taint un op = {} /\
    t.vs_memory = s.vs_memory /\ un.t_mem = tn.t_mem /\
    t.vs_returndata = s.vs_returndata /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
      op_taint un (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all raw_call_select_path_ptr >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  `stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es sa s t` by
    (irule raw_call_scalar_state_frame >> goal_assum (drule_at Any) >> simp[] >>
     qexists_tac `LENGTH sb.cs_current_insts` >> simp[]) >>
  `ghost_inv dep cenv cx es H un t /\ ghost_kept cenv es sa G tn s H un` by
    (irule rawCallHeaderFramePtrTheory.raw_call_header_ghost_frame >>
     goal_assum (drule_at Any) >> simp[] >>
     qpat_x_assum `t = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  drule raw_call_select_code >> strip_tac >>
  qexistsl_tac [`H`, `un`, `t`] >> simp[] >>
  qpat_x_assum `t = _` (fn th => once_rewrite_tac[th]) >>
  fs[same_blocks_def]
QED

Theorem raw_call_length_compare_stage:
  emit_op RETURNDATASIZE [] sa = (Var rz,s1) /\
  emit_op LT [Var rz;Lit (n2w n)] s1 = (Var cmpx,s2) /\ fn_has_code sa s2 func /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv dep cenv cx es G tn s /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  LENGTH s.vs_returndata < dimword(:256) /\ n < dimword(:256) ==>
  ?H un t. gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 H un (OK t) /\
    ghost_inv dep cenv cx es H un t /\ ghost_kept cenv es sa G tn s H un /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es sa s t /\
    t.vs_current_bb = s2.cs_current_bb /\
    t.vs_inst_idx = LENGTH s2.cs_current_insts /\ ~t.vs_halted /\
    eval_operand (Var rz) t = SOME (n2w (LENGTH s.vs_returndata)) /\
    eval_operand (Var cmpx) t = SOME (bool_to_word (LENGTH s.vs_returndata < n)) /\
    op_prov H (Var rz) = NONE /\ op_taint un (Var rz) = {} /\
    op_prov H (Var cmpx) = NONE /\ op_taint un (Var cmpx) = {} /\
    not_fresh_at s2 rz /\ not_fresh_at s2 cmpx /\
    t.vs_memory = s.vs_memory /\ un.t_mem = tn.t_mem /\
    t.vs_returndata = s.vs_returndata /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
      op_taint un (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `ci_mono sa s1 /\ ci_mono s1 s2` by
    metis_tac[exprLoweringPropsTheory.ci_mono_emit_op, pairTheory.SND] >>
  `cs_extends sa s1 /\ cs_extends s1 s2` by
    fs[exprLoweringPropsTheory.ci_mono_def] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `local_ptrs_reserved cenv s1 /\
   (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x)` by
    (fs[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var,
       stmtFragPtrTheory.not_fresh_at_mono]) >>
  drule_all raw_call_emit_returndatasize_stage >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `eval_operand (Lit (n2w n)) t = SOME (n2w n) /\
   op_prov H (Lit (n2w n)) = NONE /\ op_taint un (Lit (n2w n)) = {}` by
    simp[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_prov_def,
      ptrDisciplineTheory.op_taint_def] >>
  drule_all (SRULE [] (Q.INST
    [`opc` |-> `LT`, `f` |-> `(\x y. bool_to_word (w2n x < w2n y))`]
    raw_call_emit_length_binop_stage)) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  suspend "compose"
QED

Resume raw_call_length_compare_stage[compose]:
  `gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 H' un' (OK t')` by
    (drule_all fragGasPathPtrTheory.gas_path_ptr_then >> simp[]) >>
  `wb_frame cenv es sa s t'` by
    (irule exprSimWordArgsTheory.wb_frame_trans >>
     goal_assum (drule_at Any) >> simp[] >> conj_tac
     >- (qexistsl_tac [`es`, `s1`, `t`] >>
         fs[exprLoweringPropsTheory.ci_mono_def]) >>
     goal_assum (drule_at Any)) >>
  `ghost_kept cenv es sa G tn s H' un'` by
    (irule wordOperandsPtrTheory.ghost_kept_trans >> simp[] >> conj_tac
     >- (qexists_tac `func` >>
         fs[exprLoweringPropsTheory.stmt_state_rel_def, compileEnvTheory.state_rel_def]) >>
     qexistsl_tac [`H`, `es`, `t`, `s1`, `un`] >>
     fs[exprLoweringPropsTheory.ci_mono_def]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at s1 x` by
    metis_tac[stmtFragPtrTheory.not_fresh_at_mono, exprLoweringPropsTheory.ci_mono_def] >>
  `not_fresh_at s2 rz` by
    metis_tac[stmtFragPtrTheory.not_fresh_at_mono, exprLoweringPropsTheory.ci_mono_def] >>
  qexistsl_tac [`H'`, `un'`, `t'`] >>
  fs[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD,
    venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_prov_def] >>
  metis_tac[]
QED

Finalise raw_call_length_compare_stage

Theorem raw_call_capped_length_stage:
  emit_op RETURNDATASIZE [] sa = (Var rz,s1) /\
  emit_op LT [Var rz;Lit (n2w n)] s1 = (Var cmpx,s2) /\
  compile_select (Var cmpx) (Var rz) (Lit (n2w n)) s2 = (cap,sb) /\
  fn_has_code sa sb func /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv dep cenv cx es G tn s /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  LENGTH s.vs_returndata < dimword(:256) /\ n < dimword(:256) ==>
  ?H un t. gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 H un (OK t) /\
    ghost_inv dep cenv cx es H un t /\ ghost_kept cenv es sa G tn s H un /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es sa s t /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    eval_operand cap t = SOME (n2w (MIN (LENGTH s.vs_returndata) n)) /\
    op_prov H cap = NONE /\ op_taint un cap = {} /\
    t.vs_memory = s.vs_memory /\ un.t_mem = tn.t_mem /\
    t.vs_returndata = s.vs_returndata /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
      op_taint un (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `ci_mono sa s1 /\ ci_mono s1 s2` by
    metis_tac[exprLoweringPropsTheory.ci_mono_emit_op, pairTheory.SND] >>
  `cs_extends sa s2` by
    metis_tac[compileEnvTheory.cs_extends_trans, exprLoweringPropsTheory.ci_mono_def] >>
  `cs_extends s2 sb` by
    (drule raw_call_select_code >> strip_tac >>
     simp[cs_extends_def] >> qexists_tac `[]` >>
     fs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  `fn_has_code sa s2 func /\ fn_has_code s2 sb func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `local_ptrs_reserved cenv s2 /\
   (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s2 x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s2 x) /\
   (!x. not_fresh_at sa x ==> not_fresh_at s2 x)` by
    (fs[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var,
       stmtFragPtrTheory.not_fresh_at_mono]) >>
  drule_all raw_call_length_compare_stage >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `(!x. Lit (n2w n) = Var x ==> not_fresh_at s2 x) /\
   (!x. Var cmpx = Var x ==> not_fresh_at s2 x) /\
   eval_operand (Lit (n2w n)) t = SOME (n2w n) /\
   op_prov H (Lit (n2w n)) = NONE /\ op_taint un (Lit (n2w n)) = {}` by
    simp[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_prov_def,
      ptrDisciplineTheory.op_taint_def] >>
  drule_all raw_call_select_stage >>
  disch_then (qspec_then `PG` strip_assume_tac) >> suspend "compose"
QED

Resume raw_call_capped_length_stage[compose]:
  `gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 H' un' (OK t')` by
    (drule_all fragGasPathPtrTheory.gas_path_ptr_then >> simp[]) >>
  `wb_frame cenv es sa s t'` by
    (irule exprSimWordArgsTheory.wb_frame_trans >>
     goal_assum (drule_at Any) >> simp[] >> conj_tac
     >- (qexistsl_tac [`es`, `s2`, `t`] >>
         fs[exprLoweringPropsTheory.ci_mono_def]) >>
     goal_assum (drule_at Any)) >>
  `ghost_kept cenv es sa G tn s H' un'` by
    (irule wordOperandsPtrTheory.ghost_kept_trans >> simp[] >> conj_tac
     >- (qexists_tac `func` >>
         fs[exprLoweringPropsTheory.stmt_state_rel_def, compileEnvTheory.state_rel_def]) >>
     qexistsl_tac [`H`, `es`, `t`, `s2`, `un`] >>
     fs[exprLoweringPropsTheory.ci_mono_def]) >>
  qexistsl_tac [`H'`, `un'`, `t'`] >> simp[arithmeticTheory.MIN_DEF] >>
  Cases_on `LENGTH s.vs_returndata < n` >> fs[] >> metis_tac[]
QED

Finalise raw_call_capped_length_stage
