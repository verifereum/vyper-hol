Theory bodyFullBopBytestringDigest
Ancestors
  exprBopSimProps bodyPtrBopScalarCompile bodyPtrBopScalarSeq
  fragGasCopyLoop fragGasSeqPtr fragExecMem bodyPtrIfExpBytesFrame
  ptrDiscipline emitHelper emitHelperProps exprLoweringProps exprLowering compileEnv
  venomInst venomState finite_map pred_set list loweringStateRelDefs
  unitTransformDefs memSafeRun contextCodegenRel codegenRel
  exprSimConcatPath ghostPcTransportPtr

Theorem bop_bytestring_digest_operational:
  (if bop = vyperAST$Eq then emit_op EQ [h1;h2] sa
   else emit_op ISZERO [FST (emit_op EQ [h1;h2] sa)] (SND (emit_op EQ [h1;h2] sa))) = (op,sb) /\
  (bop = Eq \/ bop = NotEq) /\
  eval_operand h1 s = SOME w1 /\ eval_operand h2 s = SOME w2 /\
  op_prov G h1 = NONE /\ op_prov G h2 = NONE /\
  op_taint tn h1 = {} /\ op_taint tn h2 = {} /\
  (!x. h1 = Var x ==> not_fresh_at sa x) /\
  (!x. h2 = Var x ==> not_fresh_at sa x) /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ ~s.vs_halted /\
  fn_has_code sa sb func /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?raw t Gf tnf.
    t = (raw with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    run_inst_seq (emitted_insts sa sb) s = OK raw /\
    (raw with vs_vars := s.vs_vars) = s /\
    eval_operand op t = SOME (bool_to_word (if bop = Eq then w1 = w2 else w1 <> w2)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ FLOOKUP tnf.t_var x = FLOOKUP tn.t_var x) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    op_prov Gf op = NONE /\ op_taint tnf op = {} /\
    (!x. op = Var x ==> not_fresh_at sb x) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tnf))
Proof
  strip_tac >> drule_all (SRULE [LET_THM, pairTheory.UNCURRY] comparison_digest_run) >>
  disch_then (qx_choose_then `raw` strip_assume_tac) >>
  drule (SRULE [LET_THM, pairTheory.UNCURRY] comparison_digest_shape) >> strip_tac >>
  `?B. bop_scalar_seq {x | not_fresh_at sa x} {h1;h2}
        (emitted_insts sa sb) B /\ op IN B` by
    (Cases_on `bop = Eq` >>
     qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
     simp[emit_op_def, fresh_id_def, fresh_var_def, emit_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     strip_tac >> gvs[] >>
     simp[emitted_insts_def, DROP_APPEND, bop_scalar_seq_def,
          mk_inst_def, not_fresh_at_def,
          ASCIInumbersTheory.toString_inj] >>
     `LENGTH sa.cs_current_insts - (LENGTH sa.cs_current_insts + 1) = 0` by decide_tac >>
     simp[bop_scalar_seq_def, mk_inst_def, not_fresh_at_def,
          ASCIInumbersTheory.toString_inj]) >>
  `!a. a IN {h1;h2} ==> op_prov G a = NONE /\ op_taint tn a = {}` by (rw[] >> simp[]) >>
  drule_all bop_scalar_seq_run >>
  disch_then (fn th => assume_tac th >>
    qspecl_then [`func`, `PG`, `ARB`] strip_assume_tac th) >>
  rename1 `inst_seq_ptr _ 0 ctx func PG G tn _ s Gf tnf` >>
  `!D. inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s Gf tnf` by
    (gen_tac >>
     qpat_assum `!fn PG D. _` (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
     `G' = Gf /\ tn' = tnf` by metis_tac[inst_seq_ptr_ghost_unique] >> gvs[]) >>
  `!D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s Gf tnf` by
    (gen_tac >> irule inst_seq_ptr_lower_bound_transport >>
     reverse conj_tac >- (simp[] >> qexists_tac `0` >> simp[]) >>
     fs[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `!i. MEM i _ ==> i.inst_opcode = EQ \/ _`
       (drule_then strip_assume_tac) >> gvs[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule run_inst_seq_mem_ok_every >>
     fs[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `!i. MEM i _ ==> i.inst_opcode = EQ \/ _`
       (drule_then strip_assume_tac) >>
     simp[inst_mem_below_frontier_def, inst_dload_in_section_def,
          source_memory_write_ranges_def, source_memory_read_ranges_def]) >>
  drule_all concat_code_prefix >> strip_tac >>
  `raw.vs_halted = s.vs_halted /\ raw.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `raw with vs_vars := _ = s` mp_tac >>
     disch_then (fn th => mp_tac (Q.AP_TERM `\st. st.vs_halted` th) >>
                         mp_tac (Q.AP_TERM `\st. st.vs_current_bb` th)) >> simp[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (raw with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tnf)` by
    (gen_tac >>
     qpat_x_assum `inst_seq_ptr ARB 0 _ _ _ _ _ _ _ _ _` kall_tac >>
     qpat_x_assum `!D. inst_seq_ptr D 0 _ _ _ _ _ _ _ _ _` kall_tac >>
     qpat_x_assum `!D. inst_seq_ptr D lo _ _ _ _ _ _ _ _ _`
       (qspec_then `D` assume_tac) >>
     drule_all run_inst_seq_gas_origin_ptr_path >> simp[]) >>
  qexistsl_tac [`raw`, `raw with vs_inst_idx := LENGTH sb.cs_current_insts`, `Gf`, `tnf`] >>
  fs[lookup_var_def] >> metis_tac[]
QED
