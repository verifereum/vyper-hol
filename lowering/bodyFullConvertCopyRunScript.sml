(* Physical widening copy: fixed raw execution and uniform origin ghosts. *)
Theory bodyFullConvertCopyRun
Ancestors
  bodyFullAllocaFresh typedCopyPtr exprSimConvertBytes allocaFootprint
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
      qpat_x_assum `!aid b len. aid < _ /\ _ ==> _` irule >>
      qexists_tac `aid` >> simp[])
  >- (rpt strip_tac >>
      qpat_x_assum `!name b len. local_region _ _ r _ _ _ ==> _` irule >>
      fs[local_region_def, lookup_var_def] >> metis_tac[])
  >> rpt strip_tac
  >- (fs[lookup_var_def])
  >- simp[step_prov_other_output, mk_inst_def]
  >> simp[step_taint_other_output, mk_inst_def]
QED
