(* Memory checks for ECRecover's finite instruction sequence. *)
Theory bodyMemBiECRecoverMemory
Ancestors
  bodyMemBiECRecoverStores bodyMemBiECRecoverBuffers
  bodyMemBiECRecoverSuffix bodyMemBiECRecoverRun
  fragExecMem instMemFrontier memSafeRun exprSimDefs exprSimProps exprLoweringProps
  compileEnv context emitHelper emitHelperProps abiDecodeStaticProps
  venomExecSemantics venomMemDefs venomState venomInst
  words rich_list list
Libs
  monadsyntax

Theorem ecrecover_input_stores_mem:
  (do emit_void MSTORE [base_op; h];
      p1 <- emit_op ADD [base_op; Lit 32w];
      emit_void MSTORE [p1; v];
      p2 <- emit_op ADD [base_op; Lit 64w];
      emit_void MSTORE [p2; r];
      p3 <- emit_op ADD [base_op; Lit 96w];
      emit_void MSTORE [p3; sig] od) sa = ((),sb) /\
  eval_operand base_op s = SOME p /\
  eval_operand h s = SOME wh /\ eval_operand v s = SOME wv /\
  eval_operand r s = SOME wr /\ eval_operand sig s = SOME ws /\
  (!x. MEM (Var x) [base_op;h;v;r;sig] ==> not_fresh_at sa x) /\
  w2n p + 128 < dimword (:256) /\
  w2n p + 128 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >>
  `!q k z t. MEM q [base_op;h;v;r;sig] /\ sa.cs_next_var <= k ==>
     eval_operand q (update_var (STRING #"%" (toString k)) z t) =
     eval_operand q t` by
    (rpt strip_tac >> irule ecrecover_operand_generated_update >>
     simp[] >> metis_tac[]) >>
  `w2n (p+32w) = w2n p + 32 /\
   w2n (p+64w) = w2n p + 64 /\
   w2n (p+96w) = w2n p + 96` by
    (rpt conj_tac >> irule w2n_add_n2w_lt >> decide_tac) >>
  qpat_x_assum `_ sa = ((),sb)` mp_tac >>
  simp[emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1] >>
  simp[Once run_inst_seq_mem_ok_cons, below_frontier_MSTORE,
       step_inst_base_def, mk_inst_def, exec_write2_def,
       inst_dload_in_section_def] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  simp[Once run_inst_seq_mem_ok_cons, below_frontier_no_ranges,
       step_inst_base_def, mk_inst_def, exec_pure2_def,
       bind_outputs_def, eval_operand_def, ecrecover_operand_mstore,
       inst_dload_in_section_def] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  simp[Once run_inst_seq_mem_ok_cons, below_frontier_MSTORE,
       step_inst_base_def, mk_inst_def, exec_write2_def,
       eval_operand_def, lookup_var_update_var, ecrecover_operand_mstore,
       inst_dload_in_section_def] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  simp[Once run_inst_seq_mem_ok_cons, below_frontier_no_ranges,
       step_inst_base_def, mk_inst_def, exec_pure2_def,
       bind_outputs_def, eval_operand_def, ecrecover_operand_mstore,
       inst_dload_in_section_def] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  simp[Once run_inst_seq_mem_ok_cons, below_frontier_MSTORE,
       step_inst_base_def, mk_inst_def, exec_write2_def,
       eval_operand_def, lookup_var_update_var, ecrecover_operand_mstore,
       inst_dload_in_section_def] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  simp[Once run_inst_seq_mem_ok_cons, below_frontier_no_ranges,
       step_inst_base_def, mk_inst_def, exec_pure2_def,
       bind_outputs_def, eval_operand_def, ecrecover_operand_mstore,
       inst_dload_in_section_def] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  simp[run_inst_seq_mem_ok_last, below_frontier_MSTORE,
       eval_operand_def, lookup_var_update_var, ecrecover_operand_mstore,
       inst_dload_in_section_def, mk_inst_def]
QED
