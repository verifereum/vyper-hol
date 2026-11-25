Theory bodyFullStoreSlotsOffset
Ancestors
  immutableOffsetPtr fragGasCopyLoop fragGasCopySeqLiftProps typedCopyOriginPtrBase
  context compileEnv exprSimCopy fragGasOriginPtr venomExecSemantics
  ptrDiscipline venomState words venomInst fragExec instMemFrontier
  logTopicScalarPtr typedCopyPtr fragGasSeqPtr fragExecMem
  exprSimStorageCopy exprLoweringProps unitTransformDefs memSafeRun
  contextCodegenRel codegenRel bodyFullStoreSlotsRetired emitHelperProps stmtSimStoreCopy
  bodyPtrAttributeAdd

Theorem offset_add_joint[local]:
  eval_operand op s = SOME a /\ op_taint tn op = {} /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\ allocas_from lo s /\
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
     irule (cj 1 typed_copy_origin_ptr_binop_checks) >>
     simp[op_taint_def, ptrDisciplineTheory.allocas_from_def] >>
     metis_tac[ptrDisciplineTheory.allocas_from_def]) >>
  `(ctx_has_dalloca ctx ==> !pre i post u.
       [mk_inst id ADD [op;Lit off] [out]] = pre ++ i::post /\
       run_inst_seq pre s = OK u ==> dalloca_no_wrap i u)` by
    (rpt strip_tac >>
     qpat_x_assum `[_] = _ ++ _` (mp_tac o SYM) >>
     simp[listTheory.APPEND_EQ_SING] >> strip_tac >>
     simp[dalloca_no_wrap_non_dalloca, mk_inst_def]) >>
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
      Cases_on `DROP s.vs_inst_idx bb.bb_instructions` >> gvs[mk_inst_def] >>
      first_assum ACCEPT_TAC) >>
  irule logTopicScalarPtrTheory.inst_seq_ptr_immutable_taint_frame >>
  goal_assum (drule_at Any) >> simp[mk_inst_def]
QED

Theorem compile_lit_byte_offset_origin_ptr_path:
 !op off sa r sb s a tn ctx func lo explicit PG G.
  compile_lit_byte_offset op off sa = (r,sb) /\
  copy_old_operand sa op /\ eval_operand op s = SOME a /\
  op_taint tn op = {} /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
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
  (drule_all copy_runtime_offset >> strip_tac >>
  gvs[compile_lit_byte_offset_def] >>
  `eval_operand (Lit (n2w off)) s = SOME (n2w off) /\
   op_taint tn (Lit (n2w off)) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`,
    `w` |-> `(x:256 word) + y`] typed_copy_origin_ptr_binop_path)) >>
  disch_then (qspecl_then [`0`,`0`,`explicit`,`PG`,`G`,`ARB`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `emit_op ADD [left;Lit (n2w off)] sa = _` >>
  `step_inst_base (mk_inst sa.cs_next_id ADD [left;Lit (n2w off)] [out]) s =
     OK (update_var out (a+n2w off) s)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, eval_operand_def] >>
  `inst_seq_ptr ARB 0 ctx func PG G tn
     [mk_inst sa.cs_next_id ADD [left;Lit (n2w off)] [out]] s
     (step_prov PG G (mk_inst sa.cs_next_id ADD [left;Lit (n2w off)] [out])
       (update_var out (a+n2w off) s))
     (step_taint (mk_inst sa.cs_next_id ADD [left;Lit (n2w off)] [out]) s
       (update_var out (a+n2w off) s) tn)` by
    (simp[inst_seq_ptr_def] >> irule (cj 1 typed_copy_origin_ptr_binop_checks) >>
     simp[op_taint_def, allocas_from_def] >> metis_tac[allocas_from_def]) >>
  drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
  gvs[copy_runtime_frame_def] >>
  `s.vs_current_bb = sa.cs_current_bb` by metis_tac[] >>
  drule_all bop_suffix_placement >> strip_tac >>
  drule_all offset_add_joint >> strip_tac >>
  qmatch_asmsub_abbrev_tac `inst_seq_ptr ARB 0 ctx func PG G tn
    [mk_inst _ ADD _ [out]] s Gf tf` >>
  qexistsl [`update_var out (a+n2w off) s with vs_inst_idx := SUC s.vs_inst_idx`,
    `step_prov PG G (mk_inst sa.cs_next_id ADD [left;Lit (n2w off)] [out])
       (update_var out (a+n2w off) s)`,
    `step_taint (mk_inst sa.cs_next_id ADD [left;Lit (n2w off)] [out]) s
       (update_var out (a+n2w off) s) tn`] >>
  simp[typed_copy_origin_ptr_binop_ghost_frame, copy_old_operand_def] >>
  qpat_x_assum `!explicit. _` (qspec_then `explicit` strip_assume_tac) >>
  `!x. not_fresh_at sa x ==> x <> out` by
    (gvs[Abbr `out`, loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- simp[Abbr `Gf`, op_prov_def, attribute_add_provenance, Abbr `left`] >>
  simp[Abbr `Gf`, update_var_def, store_copy_normalize_def,
    venom_state_component_equality] >>
  rpt strip_tac >> `x <> out` by metis_tac[] >>
  simp[Abbr `tf`, typed_copy_origin_ptr_binop_ghost_frame,
    update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[GSYM update_var_def, typed_copy_origin_ptr_binop_ghost_frame])
QED
