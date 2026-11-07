(* Memory checks for raw_call result handling. *)
Theory bodyMemRawCallFinish
Ancestors
  bodyMemRawCallBounds rawCallResultFrame rawCallCountedRun rawCallRevertPathMemory exprSimRawCall builtinSimple emitHelper context
  exprLoweringProps fragExecMem fragExec fragGasSeqMem instMemFrontier memSafeRun compileEnv
  venomState venomExecSemantics venomInst finite_map rich_list list
Libs
  monadsyntax

Theorem raw_call_success_mem_ok:
  (do len <- emit_op RETURNDATASIZE [];
      cmp <- emit_op LT [len;Lit (n2w cap)];
      capped <- compile_select cmp len (Lit (n2w cap));
      emit_void MSTORE [ov;capped]; return ov od) sa = (result,sb) /\
  eval_operand ov s = SOME addr /\
  (!x. ov = Var x ==> not_fresh_at sa x) /\
  w2n addr + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  simp[compile_select_def, comp_bind_def, emit_op_def, fresh_var_def,
       fresh_id_def, comp_ignore_bind_def, comp_return_def, emit_def,
       emit_void_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq_mem_ok code s` >>
  `code = TAKE 5 code ++ DROP 5 code` by simp[] >>
  pop_assum (fn th => once_rewrite_tac[th]) >>
  irule run_inst_seq_mem_ok_append >> reverse conj_tac
  >- (irule raw_call_result_prefix_mem_ok >> simp[Abbr `code`, mk_inst_def]) >>
  rpt strip_tac >>
  `EVERY (\i. MEM i.inst_opcode [RETURNDATASIZE; LT; XOR; MUL] /\
      (!v. ov = Var v ==> ~MEM v i.inst_outputs)) (TAKE 5 code)` by
    (simp[Abbr `code`, mk_inst_def] >> rpt strip_tac >>
     first_x_assum drule >> simp[not_fresh_at_def] >>
     metis_tac[ASCIInumbersTheory.toString_inj, arithmeticTheory.LESS_EQ_REFL,
       arithmeticTheory.LESS_EQ_ADD]) >>
  drule_all raw_call_result_prefix_operand >> strip_tac >>
  `EVERY (\i. MEM i.inst_opcode [RETURNDATASIZE; LT; XOR; MUL])
     (TAKE 5 code)` by fs[EVERY_MEM] >>
  drule_all raw_call_result_prefix_frontier >> strip_tac >>
  simp[Abbr `code`, run_inst_seq_mem_ok_last, below_frontier_MSTORE] >>
  rpt strip_tac >> gvs[]
QED

Theorem raw_call_success_frag_mem:
  (do len <- emit_op RETURNDATASIZE [];
      cmp <- emit_op LT [len;Lit (n2w cap)];
      capped <- compile_select cmp len (Lit (n2w cap));
      emit_void MSTORE [ov;capped]; return ov od) sa = (result,sb) /\
  eval_operand ov s = SOME addr /\
  (!x. ov = Var x ==> not_fresh_at sa x) /\
  w2n addr + 32 <= s.vs_alloca_next /\
  cap < dimword (:256) /\ LENGTH s.vs_returndata < dimword (:256) ==>
  frag_exec_mem ctx sa sb (\t. t = s)
    (\t. result = ov /\ eval_operand result t = SOME addr /\
      (!a w. (!x. a = Var x ==> not_fresh_at sa x) /\
        eval_operand a s = SOME w ==> eval_operand a t = SOME w) /\
      raw_call_finish_view t = raw_call_finish_view
        (mstore (w2n addr) (n2w (MIN (LENGTH s.vs_returndata) cap)) s)) R
Proof
  strip_tac >> drule raw_call_success_code >> strip_tac >>
  irule frag_exec_mem_run_inst_seq >>
  fs[same_blocks_def, IS_PREFIX_APPEND] >>
  rpt strip_tac >> gvs[]
  >- (irule raw_call_success_mem_ok >> metis_tac[]) >>
  drule_all raw_call_success_run_aged >> strip_tac >>
  disj1_tac >> goal_assum (drule_at Any) >>
  simp[raw_call_finish_view_control] >>
  gvs[eval_operand_def, lookup_var_def]
QED

Theorem raw_call_failure_prefix_mem_ok:
  emit_op RETURNDATASIZE [] sa = (rds,sb) /\
  compile_alloc_buffer 0 sb = (buf,sc) ==>
  run_inst_seq_mem_ok (emitted_insts sa sc) s
Proof
  simp[compile_alloc_buffer_def, comp_bind_def, emit_op_def, fresh_var_def,
       fresh_id_def, comp_ignore_bind_def, comp_return_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  irule run_inst_seq_mem_ok_every >>
  simp[below_frontier_no_ranges, inst_dload_in_section_other, mk_inst_def]
QED

Theorem raw_call_success_counted_mem:
  (do len <- emit_op RETURNDATASIZE [];
      cmp <- emit_op LT [len;Lit (n2w cap)];
      capped <- compile_select cmp len (Lit (n2w cap));
      emit_void MSTORE [ov;capped]; return ov od) sa = (result,sb) /\
  eval_operand ov s = SOME addr /\
  (!x. ov = Var x ==> not_fresh_at sa x) /\
  w2n addr + 32 <= s.vs_alloca_next /\
  cap < dimword (:256) /\ LENGTH s.vs_returndata < dimword (:256) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    result = ov /\ eval_operand result t = SOME addr /\
    (!a w. (!x. a = Var x ==> not_fresh_at sa x) /\
      eval_operand a s = SOME w ==> eval_operand a t = SOME w) /\
    raw_call_finish_view t = raw_call_finish_view
      (mstore (w2n addr) (n2w (MIN (LENGTH s.vs_returndata) cap)) s)
Proof
  strip_tac >> drule raw_call_success_code >> strip_tac >>
  drule_all raw_call_success_run_aged >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule raw_call_success_mem_ok >> metis_tac[]) >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0` by
    (qpat_x_assum `comp_bind _ _ _ = _` mp_tac >>
     simp[compile_select_def, comp_bind_def, emit_op_def, fresh_var_def,
          fresh_id_def, comp_ignore_bind_def, comp_return_def, emit_def,
          emit_void_def] >> strip_tac >> gvs[] >>
     simp[emitted_insts_def] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
     simp[mk_inst_def]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]) >>
  drule_all run_inst_seq_gas_path_mem >> strip_tac >>
  `t.vs_current_bb = s.vs_current_bb` by
    (drule_all exec_block_run_inst_seq >>
     disch_then (qspec_then `0` mp_tac) >> simp[] >> metis_tac[]) >>
  qexists_tac `t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)` >>
  simp[raw_call_finish_view_control, eval_operand_def, lookup_var_def] >>
  fs[same_blocks_def, listTheory.LENGTH_APPEND] >>
  first_x_assum (qspec_then `ctx` mp_tac) >> simp[arithmeticTheory.ADD_COMM]
QED
