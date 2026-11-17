Theory bodyFullStoreSlotsOffset
Ancestors
  immutableOffsetPtr fragGasCopyLoop typedCopyOriginPtrBase
  context compileEnv exprSimCopy fragGasOriginPtr venomExecSemantics
  ptrDiscipline venomState words venomInst fragExec instMemFrontier
  logTopicScalarPtr typedCopyPtr fragGasSeqPtr fragExecMem
  exprSimStorageCopy exprLoweringProps unitTransformDefs memSafeRun
  contextCodegenRel codegenRel bodyFullStoreSlotsRetired emitHelperProps stmtSimStoreCopy

Theorem offset_add_joint[local]:
  eval_operand op s = SOME a /\ op_taint tn op = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ allocas_from lo s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id ADD [op;Lit off] [out]]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  inst_seq_ptr ARB 0 ctx func PG G tn
    [mk_inst id ADD [op;Lit off] [out]] s Gf tf ==>
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK ((update_var out (a+off) s) with vs_inst_idx := SUC s.vs_inst_idx),Gf,tf)) /\
  tf.t_imm = tn.t_imm
Proof
  strip_tac >>
  `step_inst_base (mk_inst id ADD [op;Lit off] [out]) s =
    OK (update_var out (a+off) s)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, eval_operand_def] >>
  `!D. inst_seq_ptr D 0 ctx func PG G tn
    [mk_inst id ADD [op;Lit off] [out]] s Gf tf` by
    (gvs[fragGasSeqPtrTheory.inst_seq_ptr_def] >> rpt gen_tac >>
     irule typedCopyPtrTheory.ptr_inst_ok_copy_len_binop >> simp[op_taint_def]) >>
  conj_tac
  >- (gen_tac >>
      irule (SRULE [GSYM arithmeticTheory.ADD1]
        (Q.INST [`code` |-> `[mk_inst id ADD [op;Lit off] [out]]`]
          (cj 1 run_inst_seq_origin_ptr_lift))) >>
      simp[is_terminator_def] >>
      qexistsl [`id`,`off`,`op`,`out`] >>
      simp[run_inst_seq_def, run_inst_seq_mem_ok_def,
        inst_mem_below_frontier_def, inst_dload_in_section_def,
        source_memory_read_ranges_def, source_memory_write_ranges_def,
        mk_inst_def, is_terminator_def] >>
      Cases_on `DROP s.vs_inst_idx bb.bb_instructions` >> gvs[mk_inst_def]) >>
  irule logTopicScalarPtrTheory.inst_seq_ptr_immutable_taint_frame >>
  goal_assum (drule_at Any) >> simp[mk_inst_def]
QED

Theorem compile_lit_byte_offset_origin_ptr_path:
 !op off sa r sb s a tn ctx func lo explicit PG G.
  compile_lit_byte_offset op off sa = (r,sb) /\
  copy_old_operand sa op /\ eval_operand op s = SOME a /\
  op_taint tn op = {} /\ ~ctx_has_dalloca ctx /\
  fn_has_code sa sb func /\ ~s.vs_halted /\ allocas_from lo s /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tf.
   (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
   eval_operand r t = SOME (a+n2w off) /\ copy_old_operand sb r /\
   op_taint tf r = {} /\ op_prov Gf r = op_prov G op /\
   tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
   tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
   (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x)) /\
   t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
   t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels /\
   t.vs_call_ctx = s.vs_call_ctx /\ ~t.vs_halted /\
   t.vs_current_bb = sb.cs_current_bb /\
   t.vs_inst_idx = LENGTH sb.cs_current_insts /\
   store_copy_normalize s t = s
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `off = 0`
  >- (gvs[compile_lit_byte_offset_def, comp_return_def] >>
      qexistsl [`s`,`G`,`tn`] >> simp[gas_origin_ptr_path_rules, WORD_ADD_0, store_copy_normalize_def, venom_state_component_equality]) >>
  Cases_on `op`
  >- (gvs[compile_lit_byte_offset_def, comp_return_def, eval_operand_def] >>
      qexistsl [`s`,`G`,`tn`] >>
      simp[gas_origin_ptr_path_rules, op_taint_def, op_prov_def, copy_old_operand_def,
        store_copy_normalize_def, venom_state_component_equality]) >>
  drule_all compile_lit_byte_offset_checked >>
  disch_then (qspecl_then [`func`,`PG`,`G`,`ARB`] strip_assume_tac) >>
  gvs[compile_lit_byte_offset_def] >>
  drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
  gvs[copy_runtime_frame_def] >>
  drule_all bop_suffix_placement >> strip_tac >>
  qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `s.vs_inst_idx` assume_tac) >> fs[] >>
  drule_all (SRULE [] offset_add_joint) >> strip_tac >>
  qexistsl [`t with vs_inst_idx := SUC s.vs_inst_idx`,`Gf`,`tf`] >>
  gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
      exec_pure2_def, eval_operand_def] >>
  gvs[update_var_def, lookup_var_def, same_blocks_def,
      arithmeticTheory.ADD1, store_copy_normalize_def, venom_state_component_equality]
QED
