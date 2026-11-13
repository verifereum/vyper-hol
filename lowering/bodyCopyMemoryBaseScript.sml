(* Memory-frontier checks of the copy fragments: plain and bytestring
   memory copies stay below the allocation frontier. *)
Theory bodyCopyMemoryBase
Ancestors
  exprSimBufferStore exprSimVVFrame fragExec fragExecMem instMemFrontier
  allocaHistoryFragment exprLoweringProps exprLowering emitHelperProps emitHelper
  compileEnv loweringStateRelDefs context venomInst venomState venomExecSemantics venomMemDefs
  valueEncoding valueEncodingProofs list rich_list finite_map words arithmetic

Theorem compile_copy_memory_body_mem_ok:
  compile_copy_memory dst src n sa = ((),sb) /\
  eval_operand dst s = SOME d /\ eval_operand src s = SOME w /\
  n < dimword (:256) /\ w2n w + n <= s.vs_alloca_next /\
  w2n d + n <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  rpt strip_tac >> Cases_on `n`
  >- gvs[compile_copy_memory_def, comp_return_def, emitted_insts_def,
         run_inst_seq_mem_ok_def] >>
  gvs[compile_copy_memory_def] >>
  drule emitted_insts_emit_void >> strip_tac >>
  simp[run_inst_seq_mem_ok_last, below_frontier_MCOPY, eval_operand_def]
QED

Theorem copy_len_arithmetic_mem_ok[local]:
  run_inst_seq_mem_ok
    [mk_inst n NOT ops0 ws; mk_inst a ADD ops xs; mk_inst b AND ops' ys;
     mk_inst c ADD ops'' zs] s
Proof
  `!s. inst_mem_below_frontier (mk_inst n NOT ops0 ws) s /\
       inst_mem_below_frontier (mk_inst a ADD ops xs) s /\
       inst_mem_below_frontier (mk_inst b AND ops' ys) s /\
       inst_mem_below_frontier (mk_inst c ADD ops'' zs) s` by
    simp[below_frontier_no_ranges, mk_inst_def] >>
  simp[run_inst_seq_mem_ok_cons] >>
  Cases_on `step_inst_base (mk_inst n NOT ops0 ws) s` >> simp[] >>
  Cases_on `step_inst_base (mk_inst a ADD ops xs) v` >> simp[] >>
  Cases_on `step_inst_base (mk_inst b AND ops' ys) v'` >>
  simp[run_inst_seq_mem_ok_last]
QED

Theorem compile_bytestring_copy_len_body_mem_ok:
  compile_bytestring_copy_len src sa = (out,sb) /\
  eval_operand src s = SOME w /\ w2n w + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  rpt strip_tac >>
  gvs[compile_bytestring_copy_len_def, emit_op_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
      emit_def, emitted_insts_def, DROP_APPEND1] >>
  pure_once_rewrite_tac[run_inst_seq_mem_ok_cons] >>
  simp[below_frontier_MLOAD, copy_len_arithmetic_mem_ok] >>
  Cases_on `step_inst_base (mk_inst sa.cs_next_id MLOAD [src]
    [STRING #"%" (toString sa.cs_next_var)]) s` >> simp[]
QED

Theorem compile_store_bytestring_body_mem_ok:
  compile_store_bytestring src dst sa = ((),sb) /\
  eval_operand src s = SOME w /\ eval_operand dst s = SOME d /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  mload (w2n w) s = n2w len /\
  32 + 32 * word_size len < dimword (:256) /\
  w2n w + (32 + 32 * word_size len) <= s.vs_alloca_next /\
  w2n d + (32 + 32 * word_size len) <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  rpt strip_tac >>
  qpat_x_assum `compile_store_bytestring _ _ _ = _` mp_tac >>
  simp_tac bool_ss [compile_store_bytestring_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >> strip_tac >>
  rename1 `compile_bytestring_copy_len src sa = (out,mid)` >>
  drule_all buffer_copy_len_run >> strip_tac >>
  drule buffer_copy_len_shape >> strip_tac >>
  drule emit_void_extends >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa mid ++ emitted_insts mid sb` by
    (irule emitted_insts_append >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa mid) s` by
    (irule compile_bytestring_copy_len_body_mem_ok >>
     qexistsl_tac [`out`, `src`, `w`] >> simp[] >> decide_tac) >>
  asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_append >>
  simp[] >> rpt strip_tac >> gvs[] >>
  `q.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `q with vs_vars := _ = s` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  `eval_operand src q = SOME w` by
    (`eval_operand src q = eval_operand src s` by
       (irule literal_operand_frame >> simp[] >> qexists_tac `sa` >> simp[]) >> simp[]) >>
  `eval_operand dst q = SOME d` by
    (`eval_operand dst q = eval_operand dst s` by
       (irule literal_operand_frame >> simp[] >> qexists_tac `sa` >> simp[]) >> simp[]) >>
  drule emitted_insts_emit_void >> strip_tac >>
  simp[run_inst_seq_mem_ok_last, below_frontier_MCOPY]
QED
