(* Physical widening copy: fixed raw execution and uniform origin ghosts. *)
Theory bodyFullConvertCopyRun
Ancestors
  bodyFullAllocaFresh typedCopyPtr exprSimConvertBytes allocaFootprint
  bodyFullHashKeccakFixed[qualified,ignore_grammar]
  ghostPcTransportPtr fragGasOriginPtrLoop
  exprSimAlloc fragExecMem instMemFrontier ptrSafetyTransport fragGasSeqPtr
  bodyFullUnwrapRun allocationPtr fragExecPtr fragGasOriginPtr
  decoderGhostFramePtr abiBuiltinAllocation emitHelperProps exprLoweringProps
  loweringHalt bodyPtrDefs loweringStateRelDefs ptrDiscipline venomMemDefs
  venomExecSemantics venomState venomInst finite_map pred_set

(* The copy edge uses one concrete taint update, independent of the horizon. *)
Theorem copy_mcopy_path[local]:
  emit_void MCOPY [Var dst; Var src; Lit (n2w k)] sa = ((),sb) /\
  fn_has_code sa sb func /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ k < dimword(:256) /\
  lookup_var dst s = SOME b /\ lookup_var src s = SOME a /\
  ptr_covers G tn dst s k /\ ptr_covers G tn src s k /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  w2n b+k <= s.vs_alloca_next /\ w2n a+k <= s.vs_alloca_next ==>
  run_inst_seq (emitted_insts sa sb) s = OK (mcopy (w2n b) (w2n a) k s) /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK ((mcopy (w2n b) (w2n a) k s) with vs_inst_idx := LENGTH sb.cs_current_insts),
     step_prov PG G (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;Lit (n2w k)] [])
       (mcopy (w2n b) (w2n a) k s),
     step_taint (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;Lit (n2w k)] []) s
       (mcopy (w2n b) (w2n a) k s) tn))
Proof
  strip_tac >> simp[] >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_extends >> strip_tac >>
  `run_inst_seq (emitted_insts sa sb) s = OK (mcopy (w2n b) (w2n a) k s)` by
    (simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (drule emit_mcopy_mem_ok >> disch_then irule >> simp[eval_operand_def]) >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >>
  gen_tac >> irule emitted_origin_ptr_path >>
  conj_tac >- simp[] >>
  qexistsl_tac [`emitted_insts sa sb`, `sa`] >>
  simp[mk_inst_def, is_terminator_def] >>
  conj_tac >- fs[same_blocks_def] >>
  rewrite_tac[GSYM mk_inst_def] >>
  simp[inst_seq_ptr_def] >>
  conj_tac >-
    (rpt strip_tac >> irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
     Cases_on `pre` >> gvs[mk_inst_def]) >>
  conj_tac
  >- (irule ptr_inst_ok_lower_bound_transport >> simp[] >> qexists_tac `0` >>
      simp[] >> irule ptr_inst_ok_mcopy_operand >> simp[eval_operand_def,op_taint_def]) >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def]
QED

Theorem convert_widen_copy_origin_ptr_path:
  compile_bytestring_widen_copy d (Var src) k sm = (op,sb) /\
  0 < k /\ k <= d /\ d < dimword(:256) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel H ctx func cenv cx es s /\ local_ptrs_reserved cenv sm /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  not_fresh_at sm src /\ lookup_var src s = SOME a /\
  ptr_covers G tn src s k /\ w2n a+k <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u q Gf tnf dst dw z Ga tna sc buf r.
    op = Var dst /\ q = u with vs_inst_idx := LENGTH sb.cs_current_insts /\
    run_inst_seq (emitted_insts sm sb) s = OK u /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK q,Gf,tnf)) /\
    q.vs_current_bb = sb.cs_current_bb /\ q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func q /\ s.vs_alloca_next <= q.vs_alloca_next /\
    allocas_from lo q /\ lookup_var dst q = SOME dw /\
    FLOOKUP q.vs_allocas sm.cs_next_id = SOME (w2n dw,d) /\
    w2n dw+d < dimword(:256) /\ w2n dw+d <= q.vs_alloca_next /\
    ptr_covers Gf tnf dst q d /\
    q.vs_memory = (mcopy (w2n dw) (w2n a) k s).vs_memory /\
    q.vs_accounts = s.vs_accounts /\ q.vs_transient = s.vs_transient /\
    q.vs_call_ctx = s.vs_call_ctx /\ q.vs_requests = s.vs_requests /\
    q.vs_immutables = s.vs_immutables /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sm x ==> lookup_var x q = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
    compile_alloc_buffer d sm = (buf,sc) /\ buf.buf_operand = Var dst /\
    not_fresh_at sc dst /\
    emit_void MCOPY [Var dst;Var src;Lit (n2w k)] sc = ((),sb) /\
    run_inst_seq (emitted_insts sm sc) s = OK r /\
    z = r with vs_inst_idx := LENGTH sc.cs_current_insts /\
    Ga = step_prov PG G (mk_inst sm.cs_next_id ALLOCA [Lit (n2w d)] [dst]) r /\
    tna = step_taint (mk_inst sm.cs_next_id ALLOCA [Lit (n2w d)] [dst]) s r tn /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Ga,tna)) /\
    z.vs_current_bb = sc.cs_current_bb /\ z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    z with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
             vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|> = s /\
    (!H'. stmt_state_rel H' ctx func cenv cx es s ==> stmt_state_rel H' ctx func cenv cx es z) /\
    alloca_history func z /\ allocas_from lo z /\ s.vs_alloca_next <= z.vs_alloca_next /\
    lookup_var dst z = SOME dw /\ ptr_covers Ga tna dst z d /\
    FLOOKUP z.vs_allocas sm.cs_next_id = SOME (w2n dw,d) /\
    w2n dw+d < dimword(:256) /\ w2n dw+d <= z.vs_alloca_next /\
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==> FLOOKUP z.vs_allocas aid = SOME e) /\
    (!aid b len. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n dw) d b len) /\
    (!name b len. local_region cenv es.scopes z name b len ==> regions_disjoint (w2n dw) d b len) /\
    tna.t_stor = tn.t_stor /\ tna.t_trans = tn.t_trans /\ tna.t_imm = tn.t_imm /\
    (!i. i IN tna.t_mem <=> i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < w2n dw+d)) /\
    (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x s /\
      FLOOKUP Ga x = FLOOKUP G x /\ op_taint tna (Var x) = op_taint tn (Var x)) /\
    Gf = step_prov PG Ga (mk_inst sc.cs_next_id MCOPY [Var dst;Var src;Lit (n2w k)] [])
      (mcopy (w2n dw) (w2n a) k z) /\
    tnf = step_taint (mk_inst sc.cs_next_id MCOPY [Var dst;Var src;Lit (n2w k)] []) z
      (mcopy (w2n dw) (w2n a) k z) tna
Proof
  strip_tac >> drule_all convert_widen_copy_code >> strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  qpat_assum `stmt_state_rel _ _ _ _ _ _ s`
    (assume_tac o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
  drule_all bodyFullAllocaFreshTheory.alloc_buffer_origin_ptr_path_with_raw_endpoint >>
  disch_then (qspecl_then [`tn`, `explicit`, `PG`, `G`]
    (qx_choosel_then [`dst`, `w'`, `z`, `Ga`, `tna`, `r`] strip_assume_tac)) >>
  `r = t` by
    (qpat_x_assum `run_inst_seq (emitted_insts sm mid) s = OK r` mp_tac >>
     qpat_assum `run_inst_seq (emitted_insts sm mid) s = OK t`
       (fn th => pure_rewrite_tac [th]) >> simp[]) >>
  qpat_x_assum `r = t` SUBST_ALL_TAC >>
  `p = dst` by
    (qpat_x_assum `buf.buf_operand = Var p` mp_tac >>
     qpat_assum `buf.buf_operand = Var dst`
       (fn th => pure_rewrite_tac [th]) >> simp[]) >>
  qpat_x_assum `p = dst` SUBST_ALL_TAC >>
  `w = w'` by gvs[eval_operand_def, lookup_var_def] >>
  qpat_x_assum `w = w'` SUBST_ALL_TAC >>
  `ptr_covers Ga tna src z k` by
    (fs[ptr_covers_def] >> metis_tac[]) >>
  `ptr_covers Ga tna dst z k` by
    (fs[ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_MONO_ADD_EQ]) >>
  `lookup_var src z = SOME a /\ ~z.vs_halted /\
   w2n a+k <= z.vs_alloca_next /\ lo <= z.vs_alloca_next /\ k < dimword(:256)` by
    (conj_tac >- metis_tac[] >>
     conj_tac >- (qpat_assum `z with <|vs_vars := _; vs_allocas := _; vs_alloca_next := _; vs_inst_idx := _|> = s` mp_tac >>
                  simp[venom_state_component_equality] >> metis_tac[]) >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_LESS_TRANS]) >>
  `w2n w'+k <= z.vs_alloca_next` by
    gvs[] >>
  `stmt_state_rel H ctx func cenv cx es z` by
    (qpat_assum `z = t with vs_inst_idx := _` SUBST1_TAC >>
     simp[stmt_state_rel_inst_idx]) >>
  qpat_assum `stmt_state_rel _ _ _ _ _ _ z`
    (assume_tac o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
  drule_all copy_mcopy_path >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  `emit_op ALLOCA [Lit (n2w d)] sm = (buf.buf_operand,mid)` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[contextTheory.compile_alloc_buffer_def, compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def] >>
     pairarg_tac >> strip_tac >> gvs[]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `emitted_insts sm sb = emitted_insts sm mid ++ emitted_insts mid sb` by
    (irule emitted_insts_append >> simp[]) >>
  `lookup_var dst t = SOME w' /\ lookup_var src t = SOME a` by
    (gvs[lookup_var_def, eval_operand_def]) >>
  `run_inst_seq (emitted_insts sm sb) s = OK (mcopy (w2n w') (w2n a) k t)` by
    (qpat_assum `emitted_insts sm sb = _ ++ _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `run_inst_seq (emitted_insts sm mid) s = OK t`
       (mp_then Any (qspec_then `emitted_insts mid sb` (fn th => rewrite_tac[th])) run_inst_seq_append) >>
     simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def]) >>
  qmatch_asmsub_abbrev_tac `step_prov PG Ga ci cu` >>
  qexistsl_tac [`mcopy (w2n w') (w2n a) k t`,
    `cu with vs_inst_idx := LENGTH sb.cs_current_insts`,
    `step_prov PG Ga ci cu`, `step_taint ci z cu tna`,
    `dst`, `w'`, `z`, `Ga`, `tna`, `mid`, `buf`, `t`] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (simp[Abbr `cu`, mcopy_def]) >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >>
  conj_tac >- (gen_tac >> irule gas_origin_ptr_path_trans >>
               qexistsl_tac [`Ga`, `z`, `tna`] >> simp[]) >>
  `sb.cs_current_bb = mid.cs_current_bb` by
    (drule emit_void_extends >> simp[same_blocks_def]) >>
  `alloca_inv z` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx es t`
       (strip_assume_tac o REWRITE_RULE[stmt_state_rel_def]) >>
     qpat_assum `alloca_inv t` mp_tac >>
     simp[NoAsms, alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
     simp[]) >>
  `alloca_history func (cu with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (qspecl_then [`[ci]`, `mid`, `sb`, `z`, `cu`] mp_tac emitted_alloca_history >>
     gvs[Abbr `ci`, mk_inst_def, is_terminator_def, stmt_state_rel_def]) >>
  simp[IgnAsm `z = _`, IgnAsm `Ga = _`, IgnAsm `tna = _`,
       Abbr `ci`, Abbr `cu`, mcopy_def, write_memory_with_expansion_def,
       lookup_var_def, step_prov_other_output, step_taint_other_output,
       step_taint_nonmemory_frame, mk_inst_def] >>
  conj_tac >- (gvs[allocas_from_def] >> metis_tac[]) >>
  conj_tac >- fs[lookup_var_def] >>
  conj_tac >- (gvs[ptr_covers_def, step_prov_other_output, step_taint_other_output, mk_inst_def, lookup_var_def] >> metis_tac[]) >>
  qpat_assum `z with <|vs_vars := _; vs_allocas := _; vs_alloca_next := _; vs_inst_idx := _|> = s` mp_tac >>
  simp[venom_state_component_equality] >> strip_tac >>
  gvs[lookup_var_def, mk_inst_def] >> metis_tac[]
QED
