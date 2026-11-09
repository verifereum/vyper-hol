(* Memory checks for the inline tuple result of nonreverting raw_call. *)
Theory rawCallTupleMemory
Ancestors
  rawCallFinishPathMemory exprSimRawCall fragExecMem instMemFrontier loweringStateRelDefs
  exprSafeOperand freshWrites emitHelper context compileEnv exprLoweringProps fragExec memSafeRun venomExecSemantics venomState
  venomInst words finite_map rich_list list
  exprSimRawCallCalldata allocaFootprint bodyMemEcArithPrefix valueCopy venomMemDefs
  abiDecoderIndexInit arithmeticProps emitHelperProps loweringHalt
  bodyMemRawCallFinish exprSimHash
Libs
  monadsyntax

Theorem raw_call_tuple_copy_seq_mem_ok[local]:
  emit_op ADD [pop;Lit 32w] sa = (dst,sb) /\
  emit_void MCOPY [dst;src;Lit (n2w sz)] sb = ((),sc) /\
  safe_operand sa src /\ eval_operand pop s = SOME w /\
  eval_operand src s = SOME a /\ sz < dimword (:256) /\
  w2n (w + 32w) + sz <= s.vs_alloca_next /\
  w2n a + sz <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sc) s
Proof
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[run_inst_seq_mem_ok_cons, below_frontier_no_ranges,
       inst_dload_in_section_other, mk_inst_def] >>
  simp[Once step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  `src <> Var (STRING #"%" (toString sa.cs_next_var))` by
    (strip_tac >> gvs[safe_operand_def, not_fresh_at_def]) >>
  `eval_operand src (update_var (STRING #"%" (toString sa.cs_next_var)) (w + 32w) s) = SOME a` by
    (Cases_on `src` >> gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  simp[run_inst_seq_mem_ok_last, GSYM mk_inst_def] >>
  simp[below_frontier_MCOPY, inst_dload_in_section_other] >>
  rpt strip_tac >> gvs[eval_operand_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE, w2n_n2w]
QED

Theorem raw_call_tuple_tail_mem_ok[local]:
  compile_alloc_buffer (32 + sz) sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand;ok] sm = ((),sb) /\
  emit_op ADD [buf.buf_operand;Lit 32w] sb = (dst,sc) /\
  emit_void MCOPY [dst;src;Lit (n2w sz)] sc = ((),sd) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ 32 + sz < dimword (:256) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w (32 + sz))]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
  safe_operand sa src /\ safe_operand sa ok /\
  eval_operand src s = SOME a /\ eval_operand ok s = SOME flag /\
  w2n a + sz <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sd) s
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es (s with vs_fmp := s.vs_fmp)` by simp[] >>
  drule_all raw_call_alloc_buffer_run >> strip_tac >>
  `!p. safe_operand sa p ==> eval_operand p t = eval_operand p s` by
    (Cases >> simp[safe_operand_def, eval_operand_def]) >>
  `eval_operand ok t = SOME flag` by simp[] >>
  drule_all emit_mstore_run >> strip_tac >>
  `s.vs_alloca_next <= t.vs_alloca_next` by
    (drule_all ec_alloc_buffer_frontier >> simp[]) >>
  `w2n w + (32 + sz) <= t.vs_alloca_next` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ (t with vs_fmp := _)` mp_tac >>
     simp[NoAsms, stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
     strip_tac >>
     qpat_x_assum `!aid base len. FLOOKUP t.vs_allocas aid = SOME (base,len) ==> _`
       (drule_then mp_tac) >> simp[]) >>
  suspend "compose"
QED

Resume raw_call_tuple_tail_mem_ok[compose]:
  `emitted_insts sa sd = emitted_insts sa sm ++
     (emitted_insts sm sb ++ emitted_insts sb sd)` by
    (`inst_extends sa sm` by (drule abi_decode_alloc_buffer_inst_extends >> simp[]) >>
     `inst_extends sm sb` by metis_tac[inst_extends_emit_void] >>
     `inst_extends sb sc` by (drule inst_extends_emit_op >> simp[]) >>
     `inst_extends sc sd` by metis_tac[inst_extends_emit_void] >>
     `inst_extends sb sd /\ inst_extends sm sd` by metis_tac[inst_extends_trans] >>
     `emitted_insts sa sd = emitted_insts sa sm ++ emitted_insts sm sd` by
       (irule emitted_insts_prefix_split >> fs[inst_extends_def] >> metis_tac[]) >>
     `emitted_insts sm sd = emitted_insts sm sb ++ emitted_insts sb sd` by
       (irule emitted_insts_prefix_split >> fs[inst_extends_def] >> metis_tac[]) >>
     simp[]) >>
  pop_assum SUBST1_TAC >>
  irule run_inst_seq_mem_ok_append >> reverse conj_tac
  >- (irule ec_alloc_buffer_mem_ok >> goal_assum (drule_at Any)) >>
  rpt strip_tac >> gvs[] >>
  irule run_inst_seq_mem_ok_append >> reverse conj_tac
  >- (irule emit_mstore_mem_ok >> goal_assum (drule_at Any) >>
      qexists_tac `ok` >> simp[] >> decide_tac) >>
  rpt strip_tac >> gvs[] >>
  irule raw_call_tuple_copy_seq_mem_ok >>
  goal_assum (drule_at (Pat `emit_void MCOPY _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_op ADD _ _ = _`)) >>
  qexistsl_tac [`a`,`w`] >>
  simp[mstore_def, write_memory_with_expansion_def, eval_operand_def, lookup_var_def] >>
  conj_tac
  >- (`w2n w + 32 < dimword (:256)` by decide_tac >>
      simp[w2n_add_2, w2n_n2w]) >>
  conj_tac >- gvs[eval_operand_def, lookup_var_def] >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
     rpt strip_tac >> gvs[]) >>
  irule safe_operand_mono >> qexists_tac `sa` >> simp[] >> decide_tac
QED

Finalise raw_call_tuple_tail_mem_ok

Theorem raw_call_nonrevert_positive_mem_ok:
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
     else return ok) sa = (result,sb) /\ 0 < n /\
  stmt_state_rel ctx func cenv cx es s /\ wb_frame cenv es0 sf s0 s /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  MEM alloc (fn_insts func) /\ alloc.inst_opcode = ALLOCA /\
  alloc.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas alloc.inst_id = SOME (w2n w,32 + ((n + 31) DIV 32) * 32) /\
  local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sa /\
  sf.cs_next_var <= sa.cs_next_var /\ sf.cs_next_id <= alloc.inst_id /\
  alloc.inst_id < sa.cs_next_id /\ MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  safe_operand sa ov /\ safe_operand sa ok /\
  eval_operand ov s = SOME w /\ eval_operand ok s = SOME (if success then 1w else 0w) /\
  LENGTH s.vs_returndata < dimword (:256) /\
  mem_bytes_at (w2n w + 32) (LENGTH (TAKE n s.vs_returndata)) s.vs_memory =
    TAKE n s.vs_returndata /\
  64 + ((n + 31) DIV 32) * 32 < dimword (:256) /\ n < dimword (:256) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >> drule_all raw_call_nonrevert_suffix_code >> strip_tac >>
  qpat_x_assum `(if _ then _ else _) _ = _` kall_tac >>
  `stmt_state_rel ctx func cenv cx es (s with vs_fmp := s.vs_fmp)` by simp[] >>
  drule_at (Pat `MEM _ (fn_insts _)`) raw_call_output_prefix_ready >>
  simp[] >> disch_then drule >> simp[] >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >> simp[] >>
  fs[wordsTheory.dimword_def] >>
  `stmt_state_rel ctx func cenv cx es (s with vs_fmp := s.vs_fmp)` by simp[] >>
  disch_then drule_all >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa s4) s = OK u` >>
  `u with vs_fmp := s.vs_fmp = u` by
    (qpat_assum `u.vs_fmp = _` (SUBST1_TAC o SYM) >> simp[]) >> fs[] >>
  suspend "compose"
QED

Resume raw_call_nonrevert_positive_mem_ok[compose]:
  `w2n w + (32 * ((n + 31) DIV 32) + 32) <= s.vs_alloca_next` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ s` mp_tac >>
     simp[NoAsms, stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
     strip_tac >>
     qpat_x_assum `!aid base len. FLOOKUP s.vs_allocas aid = SOME (base,len) ==> _`
       (drule_then mp_tac) >> simp[]) >>
  `FLOOKUP u.vs_allocas alloc.inst_id = SOME (w2n w,32 * ((n + 31) DIV 32) + 32)` by simp[] >>
  `w2n w + (32 * ((n + 31) DIV 32) + 32) <= u.vs_alloca_next` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ u` mp_tac >>
     simp[NoAsms, stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
     strip_tac >>
     qpat_x_assum `!aid base len. FLOOKUP u.vs_allocas aid = SOME (base,len) ==> _`
       (drule_then mp_tac) >> simp[]) >>
  `emitted_insts sa sb = emitted_insts sa s4 ++ emitted_insts s4 sb` by
    (irule emitted_insts_prefix_split >> fs[inst_extends_def] >> metis_tac[]) >>
  pop_assum SUBST1_TAC >>
  irule run_inst_seq_mem_ok_append >> reverse conj_tac
  >- (irule raw_call_success_mem_ok >>
      qexistsl_tac [`w`,`n`,`ov`,`ov`] >>
      simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
      fs[safe_operand_def] >> decide_tac) >>
  rpt strip_tac >> gvs[] >>
  `local_ptrs_reserved cenv s4 /\ safe_operand s4 ok /\ safe_operand s4 ov` by
    (fs[ci_mono_def] >> metis_tac[local_ptrs_reserved_next_var, safe_operand_mono]) >>
  `fn_has_code s4 sb func` by metis_tac[fn_has_code_split] >>
  `MEM (mk_inst s4.cs_next_id ALLOCA
     [Lit (n2w (32 * ((n + 31) DIV 32) + 64))]
     [STRING #"%" (toString s4.cs_next_var)]) (fn_insts func)` by
    (irule hash_emitted_inst_mem >> goal_assum (drule_at Any) >> simp[]) >>
  irule raw_call_tuple_tail_mem_ok >>
  goal_assum (drule_at (Pat `emit_void MCOPY _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_op ADD _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_void MSTORE [buf.buf_operand;ok] _ = _`)) >>
  qexistsl_tac [`w`,`cenv`,`ctx`,`cx`,`es`,`if success then 1w else 0w`,`func`] >>
  simp[wordsTheory.dimword_def]
QED

Finalise raw_call_nonrevert_positive_mem_ok
