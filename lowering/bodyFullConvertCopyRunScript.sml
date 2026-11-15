(* Physical widening copy: fixed raw execution and uniform origin ghosts. *)
Theory bodyFullConvertCopyRun
Ancestors
  bodyFullAllocaFresh typedCopyPtr exprSimConvertBytes allocaFootprint
  ghostPcTransportPtr fragGasOriginPtrLoop
  exprSimAlloc fragExecMem instMemFrontier ptrSafetyTransport fragGasSeqPtr
  bodyFullUnwrapRun allocationPtr fragExecPtr fragGasOriginPtr
  decoderGhostFramePtr abiBuiltinAllocation emitHelperProps exprLoweringProps
  loweringHalt bodyPtrDefs loweringStateRelDefs ptrDiscipline venomMemDefs
  venomExecSemantics venomState venomInst finite_map pred_set

(* Only the exact raw ALLOCA calculation is repeated here: the public
   allocation producer does not expose its raw execution witness. *)
Theorem copy_alloca_exact[local]:
  !id n out s t tn.
    stmt_state_rel H ctx func cenv cx es s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
    n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK t ==>
    ?b. FLOOKUP t.vs_allocas id = SOME (b,n) /\
        lookup_var out t = SOME (n2w b) /\ b + n < dimword (:256) /\
        t with <| vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
                  vs_alloca_next := s.vs_alloca_next |> = s /\
        s.vs_alloca_next <= t.vs_alloca_next /\
        b + n <= t.vs_alloca_next /\
        (!lo. allocas_from lo s /\ lo <= s.vs_alloca_next ==>
              allocas_from lo t) /\
        (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn).t_stor =
          tn.t_stor /\
        (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn).t_trans =
          tn.t_trans /\
        (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn).t_imm =
          tn.t_imm /\
        (!i. i IN (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out])
                     s t tn).t_mem <=>
             i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < b + n))
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule_all stmt_state_rel_alloca_fresh_bound >> strip_tac >>
      drule_all fresh_alloca_ghost >>
      disch_then (qspecl_then [`[]`, `FEMPTY`, `tn`] strip_assume_tac) >>
      drule step_alloca_fresh >> disch_then (qspec_then `n` mp_tac) >>
      simp[] >> disch_then (qspec_then `out` assume_tac) >> gvs[] >>
      qexists_tac `s.vs_alloca_next` >>
      simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE,
           venom_state_component_equality] >>
      simp[allocas_from_def, FLOOKUP_UPDATE] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >> res_tac) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  `site0 + n <= s.vs_alloca_next` by
    (fs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
     res_tac >> decide_tac) >>
  drule reused_alloca_ghost >>
  disch_then (qspecl_then [`out`, `[]`, `FEMPTY`, `tn`] strip_assume_tac) >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >>
  gvs[] >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       venom_state_component_equality, allocas_from_def] >>
  rpt strip_tac >> eq_tac >> rpt strip_tac >> gvs[]
QED

Theorem copy_alloc_packet[local]:
  compile_alloc_buffer n sa = (buf,sb) /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  n < dimword (:256) /\
  stmt_state_rel H ctx func cenv cx es s /\ alloca_history func s /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK r ==>
  ?dst w z Ga tna.
    buf.buf_operand = Var dst /\ not_fresh_at sb dst /\
    z = r with vs_inst_idx := LENGTH sb.cs_current_insts /\
    Ga = step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [dst]) r /\
    tna = step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [dst]) s r tn /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
           (s,G,tn) [] (OK z,Ga,tna)) /\
    z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    z with <| vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
              vs_alloca_next := s.vs_alloca_next;
              vs_inst_idx := s.vs_inst_idx |> = s /\
    (!H'. stmt_state_rel H' ctx func cenv cx es s ==>
          stmt_state_rel H' ctx func cenv cx es z) /\
    alloca_history func z /\ allocas_from lo z /\
    s.vs_alloca_next <= z.vs_alloca_next /\
    lookup_var dst z = SOME w /\ ptr_covers Ga tna dst z n /\
    FLOOKUP z.vs_allocas sa.cs_next_id = SOME (w2n w,n) /\
    w2n w+n < dimword(:256) /\ w2n w+n <= z.vs_alloca_next /\
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==>
             FLOOKUP z.vs_allocas aid = SOME e) /\
    (!aid b len. aid < sa.cs_next_id /\
                 FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
                 regions_disjoint (w2n w) n b len) /\
    (!name b len. local_region cenv es.scopes z name b len ==>
                  regions_disjoint (w2n w) n b len) /\
    tna.t_stor = tn.t_stor /\ tna.t_trans = tn.t_trans /\
    tna.t_imm = tn.t_imm /\
    (!i. i IN tna.t_mem <=>
         i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < w2n w+n)) /\
    (!x. not_fresh_at sa x ==>
         lookup_var x z = lookup_var x s /\ FLOOKUP Ga x = FLOOKUP G x /\
         op_taint tna (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  `t = r` by gvs[] >> qpat_x_assum `t = r` SUBST_ALL_TAC >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  `p = STRING #"%" (toString sa.cs_next_var)` by gvs[] >>
  qpat_x_assum `p = _` SUBST_ALL_TAC >>
  qabbrev_tac `dst = STRING #"%" (toString sa.cs_next_var)` >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [dst]) s = OK r` by
    (gvs[run_inst_seq_def, AllCaseEqs()]) >>
  drule_all copy_alloca_exact >>
  disch_then (qspec_then `tn` strip_assume_tac) >>
  drule_all alloca_step_ptr_covers >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] assume_tac) >>
  qabbrev_tac `ins = mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [dst]` >>
  `w = n2w b` by gvs[eval_operand_def] >>
  `b < dimword(:256)` by decide_tac >>
  `w2n w = b` by simp[wordsTheory.w2n_n2w] >>
  qpat_x_assum `w2n w = b` (SUBST_ALL_TAC o SYM) >>
  `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  `run_inst_seq_mem_ok [ins] s` by
    (simp[run_inst_seq_mem_ok_last] >> conj_tac
     >- (irule below_frontier_no_ranges >> simp[Abbr `ins`, mk_inst_def]) >>
     simp[Abbr `ins`, mk_inst_def, memSafeRunTheory.inst_dload_in_section_def]) >>
  `!D. inst_seq_ptr D lo ctx func PG G tn [ins] s
         (step_prov PG G ins r) (step_taint ins s r tn)` by
    (gen_tac >> simp[inst_seq_ptr_def] >>
     irule ptr_inst_ok_lower_bound_transport >> simp[] >>
     qexists_tac `0` >> simp[Abbr `ins`, ptr_inst_ok_alloca]) >>
  `!x. not_fresh_at sa x ==> x <> dst` by
    (rpt strip_tac >> fs[not_fresh_at_def] >>
     first_x_assum (qspec_then `sa.cs_next_var` mp_tac) >> simp[Abbr `dst`]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (r with vs_inst_idx := LENGTH sb.cs_current_insts),
      step_prov PG G ins r, step_taint ins s r tn)` by
    (gen_tac >> irule bodyFullUnwrapRunTheory.emitted_origin_ptr_path >>
     conj_tac >- simp[] >> qexistsl_tac [`[ins]`, `sa`] >>
     gvs[Abbr `ins`, mk_inst_def, is_terminator_def]) >>
  qexistsl_tac [`dst`, `w`, `r with vs_inst_idx := LENGTH sb.cs_current_insts`,
                `step_prov PG G ins r`, `step_taint ins s r tn`] >>
  simp[Abbr `ins`] >>
  rpt conj_tac
  >- (qpat_assum `r with <| vs_vars := _; vs_allocas := _;
                          vs_alloca_next := _ |> = s`
        mp_tac >> simp[venom_state_component_equality])
  >- (qpat_x_assum `r with <| vs_vars := _; vs_allocas := _;
                             vs_alloca_next := _ |> = s` mp_tac >>
      simp[venom_state_component_equality])
  >- (rpt strip_tac >> simp[stmt_state_rel_inst_idx] >>
      irule stmt_state_rel_fields_transport >>
      rpt (first_assum (irule_at Any)) >> simp[] >>
      qpat_x_assum `r with <| vs_vars := _; vs_allocas := _;
                             vs_alloca_next := _ |> = s` mp_tac >>
      simp[venom_state_component_equality])
  >- (qspecl_then [`[mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [dst]]`,
                   `sa`, `sb`, `s`, `r`] mp_tac emitted_alloca_history >>
      gvs[mk_inst_def, is_terminator_def, stmt_state_rel_def])
  >- (qpat_x_assum `!lo. allocas_from lo s /\ _ ==> _`
        (qspec_then `lo` mp_tac) >>
      impl_tac >- simp[] >> simp[allocas_from_def])
  >- gvs[lookup_var_def]
  >- (qpat_x_assum `ptr_covers _ _ dst r n` mp_tac >>
      simp[ptr_covers_def, lookup_var_def] >> strip_tac >>
      gvs[lookup_var_def])
  >- (rpt strip_tac >>
      qpat_x_assum `!name b len. local_region _ _ r _ _ _ ==> _` irule >>
      fs[local_region_def, lookup_var_def] >> metis_tac[])
  >> rpt strip_tac
  >- (fs[lookup_var_def])
  >- simp[step_prov_other_output, mk_inst_def]
  >> simp[step_taint_other_output, mk_inst_def]
QED

(* The copy edge uses one concrete taint update, independent of the horizon. *)
Theorem copy_mcopy_path[local]:
  emit_void MCOPY [Var dst; Var src; Lit (n2w k)] sa = ((),sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
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
  simp[inst_seq_ptr_def] >> conj_tac
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
  ~ctx_has_dalloca ctx /\ not_fresh_at sm src /\ lookup_var src s = SOME a /\
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
  drule_all copy_alloc_packet >>
  disch_then (qspecl_then [`tn`, `explicit`, `PG`, `G`] strip_assume_tac) >>
  `p = dst` by metis_tac[operand_11] >>
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
