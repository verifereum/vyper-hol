(* Runtime immutable TopLevelName copies use one raw execution for both checks. *)
Theory bodyFullToplevelCodeRuntime
Ancestors
  bodyFullUnwrapRun exprPtrCodeCopyInduction bodyImmutableCopyMemory fragGasSeqPtr
  exprSimCopy exprLoweringProps entrySinkExtraction venomState venomInst
  exprLowering list rich_list

Theorem toplevel_code_runtime_range_full:
  compile_expr cenv ty (TopLevelName ann nsid) sx = (vv,sm) /\
  compile_imm_copy_to_memory F imm src (Var root) n off sa = ((),sb) /\
  copy_old_operand sa src /\ not_fresh_at sa root /\
  eval_operand src s = SOME a /\ lookup_var root s = SOME b /\
  op_taint tn src = {} /\ ptr_covers G tn root s capacity /\
  off + 32*n <= capacity /\ w2n b + capacity < dimword(:256) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  w2n b + off + 32*n <= s.vs_alloca_next /\
  w2n a + off + 32*n <= LENGTH s.vs_data_section /\
  w2n a + off + 32*n < dimword(:256) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?Gf tnf t.
    copy_runtime_frame sa s sb t /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tnf)) /\
    t.vs_current_bb = sb.cs_current_bb /\ ~t.vs_halted /\
    tnf.t_mem = tn.t_mem DIFF
      {j | w2n b+off <= j /\ j < w2n b+off+32*n} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p sz. not_fresh_at sa p /\ ptr_covers G tn p s sz ==>
      ptr_covers Gf tnf p t sz)
Proof
  strip_tac >>
  drule_all code_copy_range_ptr >>
  disch_then (qspecl_then [`func`,`PG`,`ARB`] strip_assume_tac) >>
  `copy_old_operand sa (Var root) /\ eval_operand (Var root) s = SOME b` by
    simp[copy_old_operand_def, eval_operand_def] >>
  `w2n b + off + 32*n < dimword(:256)` by decide_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule body_immutable_copy_mem_ok >> metis_tac[]) >>
  drule code_copy_insts >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
      ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (fs[emitted_insts_def, DROP_APPEND, EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> strip_tac >> gvs[is_terminator_def]) >>
  `run_inst_seq (emitted_insts sa sb) s = OK t /\
   sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    fs[copy_runtime_frame_def, same_blocks_def] >>
  `t.vs_current_bb = sb.cs_current_bb /\ ~t.vs_halted` by
    (drule run_inst_seq_preserves_entry_control >>
     impl_tac >- fs[EVERY_MEM] >> simp[]) >>
  qexistsl [`Gf`,`tnf`,`t`] >>
  (conj_tac >- first_assum ACCEPT_TAC) >> conj_tac
  >- (gen_tac >> drule_all code_copy_range_ptr >>
      disch_then (qspecl_then [`func`,`PG`,`D`] strip_assume_tac) >>
      `Gf' = Gf /\ tnf' = tnf` by
        (irule inst_seq_ptr_ghost_unique >> metis_tac[]) >>
      `inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s Gf tnf` by
        (qpat_x_assum `!k. inst_seq_ptr D _ _ _ _ _ _ _ _ _ _`
          (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
      irule emitted_origin_ptr_path >>
      simp[] >> qexistsl [`emitted_insts sa sb`,`sa`] >> simp[]) >>
  simp[]
QED
