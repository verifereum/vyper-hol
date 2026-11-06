Theory bodyMemEcArithPrefix
Ancestors
  exprSimAlloc loweringHalt fragExecMem instMemFrontier emitHelperProps exprLoweringProps compileEnv fragExec
  bodyLiteralBufferMemory allocaHistoryFragment exprSimWordBuiltins
  emitHelper context venomExecSemantics venomInst venomState valueEncodingProps

Theorem ec_alloc_buffer_mem_ok:
  compile_alloc_buffer sz sa = (buf,sm) ==>
  run_inst_seq_mem_ok (emitted_insts sa sm) s
Proof
  strip_tac >> drule compile_alloc_buffer_insts >> strip_tac >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1,
       run_inst_seq_mem_ok_last] >>
  irule below_frontier_no_ranges >> simp[]
QED

Theorem ec_alloc_buffer_frontier:
  compile_alloc_buffer sz sa = (buf,sm) /\
  run_inst_seq (emitted_insts sa sm) s = OK t ==>
  s.vs_alloca_next <= t.vs_alloca_next
Proof
  strip_tac >> drule compile_alloc_buffer_insts >> strip_tac >>
  gvs[emitted_insts_def, rich_listTheory.DROP_APPEND1] >>
  drule literal_alloca_frontier >> simp[]
QED

Theorem ec_alloc_buffer_endpoint:
  compile_alloc_buffer sz sa = (buf,sm) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  sz < dimword (:256) /\ alloca_history func s /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sm) s = OK t ==>
  (?w. eval_operand buf.buf_operand t = SOME w /\
       w2n w + sz <= t.vs_alloca_next) /\
  alloca_history func (t with vs_inst_idx := LENGTH sm.cs_current_insts)
Proof
  strip_tac >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
     [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    metis_tac[buffer_alloc_code] >>
  drule_all literal_alloc_buffer_run >> strip_tac >> gvs[] >>
  conj_tac
  >- (irule alloca_region_below_frontier >>
      conj_tac >- gvs[stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def] >>
      qexistsl [`sa.cs_next_id`, `w2n w`, `sz`] >> simp[]) >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  gvs[fn_has_code_def] >>
  gvs[rich_listTheory.IS_PREFIX_APPEND] >>
  `alloca_inv s` by gvs[stmt_state_rel_def] >>
  qpat_assum `run_inst_seq _ s = OK t`
    (mp_then Any mp_tac alloca_history_run_inst_seq) >>
  disch_then (qspecl_then [`func`, `bb`] mp_tac) >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1] >>
  disch_then irule >> simp[venomInstTheory.is_terminator_def]
QED

Theorem ec_point_word_transfer_mem:
  (do src <- emit_op ADD [point_op; Lit poff];
      value <- emit_op MLOAD [src];
      dst <- emit_op ADD [base_op; Lit boff];
      emit_void MSTORE [dst; value] od) sa = ((),sb) /\
  eval_operand point_op s = SOME point /\
  eval_operand base_op s = SOME bword /\
  (!x. MEM (Var x) [point_op;base_op] ==> not_fresh_at sa x) /\
  w2n (point + poff) + 32 <= s.vs_alloca_next /\
  w2n (bword + boff) + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  (!t. run_inst_seq (emitted_insts sa sb) s = OK t ==>
       t.vs_alloca_next = s.vs_alloca_next)
Proof
  strip_tac >>
  `!q k z t. MEM q [point_op;base_op] /\ sa.cs_next_var <= k ==>
     eval_operand q (update_var (STRING #"%" (toString k)) z t) =
     eval_operand q t` by
    (rpt strip_tac >> irule eval_operand_update_not_fresh >>
     simp[] >> metis_tac[]) >>
  qpat_x_assum `_ sa = ((),sb)` mp_tac >>
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1] >>
  conj_tac
  >- (simp[Once run_inst_seq_mem_ok_def, below_frontier_no_ranges,
           memSafeRunTheory.inst_dload_in_section_def, mk_inst_def] >>
      simp[step_inst_base_opcode_eqs, exec_pure2_def, bind_outputs_def,
           eval_operand_def] >>
      pure_rewrite_tac[GSYM mk_inst_def] >>
      simp[Once run_inst_seq_mem_ok_def, below_frontier_MLOAD,
           memSafeRunTheory.inst_dload_in_section_def, eval_operand_def,
           lookup_var_update_var, update_var_def, mk_inst_def] >>
      simp[step_inst_base_opcode_eqs, exec_read1_def, bind_outputs_def,
           eval_operand_def, lookup_var_update_var] >>
      pure_rewrite_tac[GSYM update_var_def] >>
      simp[lookup_var_update_var] >>
      pure_rewrite_tac[GSYM mk_inst_def] >>
      simp[Once run_inst_seq_mem_ok_def, below_frontier_no_ranges,
           memSafeRunTheory.inst_dload_in_section_def, mk_inst_def] >>
      simp[step_inst_base_opcode_eqs, exec_pure2_def, bind_outputs_def] >>
      simp[eval_operand_def, lookup_var_update_var] >>
      pure_rewrite_tac[GSYM mk_inst_def] >>
      simp[run_inst_seq_mem_ok_last, below_frontier_MSTORE,
           memSafeRunTheory.inst_dload_in_section_def,
           eval_operand_def, lookup_var_update_var, update_var_def]) >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure2_def, exec_read1_def, exec_write2_def, bind_outputs_def,
       eval_operand_def, lookup_var_update_var]
QED

Theorem ec_precompile_suffix_mem_ok:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL [gas; Lit target; ip; Lit insz; op; Lit 64w];
      emit_void ASSERT [success];
      comp_return op od) sm = (res,sb) /\
  eval_operand ip s = SOME wi /\ eval_operand op s = SOME wo /\
  (!z. ip = Var z ==> not_fresh_at sm z) /\
  (!z. op = Var z ==> not_fresh_at sm z) /\
  w2n wi + w2n insz <= s.vs_alloca_next /\
  w2n wo + 64 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sm sb) s
Proof
  strip_tac >>
  `!q k z t. MEM q [ip;op] /\ sm.cs_next_var <= k ==>
     eval_operand q (update_var (STRING #"%" (toString k)) z t) =
     eval_operand q t` by
    (rpt strip_tac >> irule eval_operand_update_not_fresh >>
     qexists_tac `sm` >> gvs[] >> metis_tac[]) >>
  qpat_x_assum `_ sm = (res,sb)` mp_tac >>
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1] >>
  simp[Once run_inst_seq_mem_ok_def, below_frontier_no_ranges,
       memSafeRunTheory.inst_dload_in_section_def, mk_inst_def] >>
  simp[step_inst_base_opcode_eqs, exec_gas_def, bind_outputs_def] >>
  Cases_on `s.vs_gas_readings` >> simp[] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  simp[Once run_inst_seq_mem_ok_def, below_frontier_STATICCALL,
       memSafeRunTheory.inst_dload_in_section_def] >>
  simp[run_inst_seq_mem_ok_last, below_frontier_no_ranges,
       memSafeRunTheory.inst_dload_in_section_def, mk_inst_def,
       eval_operand_def, lookup_var_update_var] >>
  simp[wordsTheory.dimword_def] >>
  CASE_TAC >> simp[]
QED
