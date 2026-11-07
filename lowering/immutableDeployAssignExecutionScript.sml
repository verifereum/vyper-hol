(* Executable meaningful-prefix stores for constructor immutables. *)
Theory immutableDeployAssignExecution
Ancestors
  immutableDeployAssignTransfer immutableDeployAssignWord
  immutableDeployAssignRanges exprSimCopy emitHelperProps
  context compileEnv venomInst exprLoweringProps immutableCopyExecution
  placeTypedCopyPath fragExec venomState stmtLowering valueEncoding

Theorem immutable_store_one_insts[local]:
  immutable_store_one (SOME region) src dst off sa = ((),sb) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; ISTORE]) (emitted_insts sa sb)
Proof
  simp[immutable_store_one_def, immutable_comp_bind_cases] >> strip_tac >>
  imp_res_tac code_offset_insts >>
  imp_res_tac immutable_byte_offset_extends >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule compile_imm_store_word_result >> strip_tac >>
  pure_once_rewrite_tac[emitted_insts_def] >>
  qpat_x_assum `sb.cs_current_insts = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_x_assum `st1''.cs_current_insts = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_x_assum `st1'.cs_current_insts = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_x_assum `st1.cs_current_insts = _` (fn th => pure_rewrite_tac[th]) >>
  simp[listTheory.DROP_APPEND, GSYM arithmeticTheory.SUB_RIGHT_SUB,
       mk_inst_def] >>
  fs[listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem immutable_store_words_insts:
  !n off sa sb.
  compile_imm_store_words (SOME region) src dst n off sa = ((),sb) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; ISTORE]) (emitted_insts sa sb)
Proof
  Induct
  >- (simp[compile_imm_store_words_def, comp_return_def] >>
      rpt strip_tac >> gvs[emitted_insts_def]) >>
  simp[immutable_store_suc, comp_ignore_bind_def, immutable_comp_bind_cases] >>
  rpt gen_tac >> strip_tac >>
  drule immutable_store_one_insts >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa st1 ++ emitted_insts st1 sb` by
    (irule emitted_insts_append >> simp[]) >>
  fs[listTheory.APPEND_ASSOC]
QED

Theorem immutable_assign_words_prefix_path:
  compile_imm_store_words (SOME region) src dst n 0 sa = ((),sb) /\
  eval_operand src s = SOME (n2w a) /\ eval_operand dst s = SOME (n2w b) /\
  eval_operand region s = SOME 0w /\ fresh_vars_wrt sa s /\
  k <= 32*n /\ a+k < dimword (:256) /\ b+32*n < dimword (:256) /\
  (a+k <= b \/ b+32*n <= a) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. immutable_execution_frame sa s sb u /\
    gas_marked_path F ctx func s 0
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    mem_bytes_at b k u.vs_memory = mem_bytes_at a k s.vs_memory /\
    (!p len. p+len <= b \/ b+32*n <= p ==>
      mem_bytes_at p len u.vs_memory = mem_bytes_at p len s.vs_memory) /\
    u.vs_immutables = (immutable_transfers T T (n2w a) (n2w b) n 0 s).vs_immutables
Proof
  strip_tac >> (
  drule immutableDeployAssignTransferTheory.compile_imm_store_words_prefix >>
  disch_then (qspecl_then [`s`,`k`,`b`,`a`] mp_tac) >> simp[] >>
  strip_tac >> qexists_tac `s'` >> simp[] >>
  reverse conj_tac >- metis_tac[] >>
  irule placeTypedCopyPathTheory.place_copy_seq_path >> simp[] >>
  qexists_tac `sa` >> fs[immutable_execution_frame_def] >>
  drule immutable_store_words_insts >> strip_tac >>
  fs[listTheory.EVERY_MEM] >> rpt strip_tac >>
  qpat_x_assum `!i. MEM i (emitted_insts sa sb) ==> _`
    (qspec_then `i` mp_tac) >> simp[] >>
  strip_tac >> gvs[is_terminator_def] >> metis_tac[is_terminator_def])
QED

Theorem immutable_assign_direct_composite_path:
  compile_assign_value cenv dst LocCode src F src_loc dty sty da mem_size sa = ((),sb) /\
  cenv.ce_imm_alloca = SOME region /\
  (dty = sty \/ (is_bytestring_type dty /\ is_bytestring_type sty)) /\
  copy_size = (if is_bytestring_type dty then type_memory_bytes cenv sty else mem_size) /\
  n = (if copy_size <= 32 then 1 else (copy_size+31) DIV 32) /\
  eval_operand src s = SOME (n2w a) /\ eval_operand dst s = SOME (n2w b) /\
  eval_operand region s = SOME 0w /\ fresh_vars_wrt sa s /\
  k <= 32*n /\ a+k < dimword (:256) /\ b+32*n < dimword (:256) /\
  (a+k <= b \/ b+32*n <= a) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. immutable_execution_frame sa s sb u /\
    gas_marked_path F ctx func s 0
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    mem_bytes_at b k u.vs_memory = mem_bytes_at a k s.vs_memory /\
    (!p len. p+len <= b \/ b+32*n <= p ==>
      mem_bytes_at p len u.vs_memory = mem_bytes_at p len s.vs_memory) /\
    u.vs_immutables = (immutable_transfers T T (n2w a) (n2w b) n 0 s).vs_immutables
Proof
  rpt gen_tac >> disch_tac >>
  gvs[compile_assign_value_def, immutable_comp_bind_cases,
      comp_return_def] >>
  (qmatch_asmsub_abbrev_tac `copybytes <= 32` >>
   Cases_on `copybytes <= 32` >> gvs[]
   >- (drule immutable_assign_short_path >>
       disch_then (qspec_then `s` mp_tac) >> simp[] >>
       disch_then (qspecl_then [`func`,`ctx`] mp_tac) >> simp[] >> strip_tac >>
       `a < dimword (:256) /\ b < dimword (:256)` by decide_tac >>
       `(immutable_transfers T T (n2w a) (n2w b) 1 0 s).vs_memory =
          (mstore b (mload a s) s).vs_memory` by
         (pure_rewrite_tac[arithmeticTheory.ONE] >>
          simp[immutable_transfers_def, immutable_word_transfer_fields,
              immutable_copy_read_def, wordsTheory.WORD_ADD_0]) >>
       qexists_tac `u` >> simp[] >>
       qpat_assum `(immutable_transfers _ _ _ _ _ _ _).vs_memory = _`
         (fn th => once_rewrite_tac[GSYM th]) >>
       conj_tac
       >- (irule immutable_transfers_memory_prefix >> simp[] >> decide_tac) >>
       conj_tac
       >- (rpt strip_tac >> irule immutable_transfers_memory_frame >> simp[]) >>
       pure_rewrite_tac[arithmeticTheory.ONE] >>
       simp[immutable_transfers_def, immutable_word_transfer_fields,
            immutable_copy_read_def, wordsTheory.WORD_ADD_0]) >>
   irule (SRULE [arithmeticTheory.ADD_COMM] immutable_assign_words_prefix_path) >>
   simp[] >> metis_tac[])
QED
