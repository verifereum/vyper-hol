Theory bodyFullAbiEncodeAllocOrigin
Ancestors
  bodyFullAllocaFresh bodyPtrIfExpAllocationSite decoderGhostFramePtr
  bodyFullUnwrapRun bodyFullGhostFrame exprSimAlloc allocationPtr
  ptrSafetyTransport fragExecPtr fragGasSeqPtr fragExecMem instMemFrontier
  abiBuiltinAllocation emitHelperProps exprLoweringProps loweringHalt
  bodyPtrDefs loweringStateRelDefs ptrDiscipline venomMemDefs
  venomExecSemantics venomState venomInst finite_map pred_set

(* Only the finite record/taint effects are calculated here. Site bounds,
   execution and separation come from the existing allocation providers. *)
Theorem alloc_effects[local]:
  stmt_state_rel H ctx func ce cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  n < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK t /\
  FLOOKUP t.vs_allocas id = SOME (b,n) ==>
  t with <| vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
            vs_alloca_next := s.vs_alloca_next |> = s /\
  s.vs_alloca_next <= t.vs_alloca_next /\ b + n <= t.vs_alloca_next /\
  (!lo. allocas_from lo s /\ lo <= s.vs_alloca_next ==> allocas_from lo t) /\
  (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn).t_trans = tn.t_trans /\
  (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn).t_imm = tn.t_imm /\
  (!i. i IN (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn).t_mem <=>
       i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < b+n))
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule_all fresh_alloca_ghost >>
      disch_then (qspecl_then [`[]`, `FEMPTY`, `tn`] strip_assume_tac) >>
      drule step_alloca_fresh >> disch_then (qspec_then `n` mp_tac) >>
      simp[] >> disch_then (qspec_then `out` assume_tac) >>
      gvs[] >>
      gvs[update_var_def, FLOOKUP_UPDATE, venom_state_component_equality,
          allocas_from_def] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  `site0 + n <= s.vs_alloca_next` by
    (`alloca_inv s` by metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca] >>
     fs[alloca_inv_def, alloca_next_valid_def] >>
     qpat_x_assum `!aid base sz. FLOOKUP _ aid = SOME (base,sz) ==> _` drule >>
     decide_tac) >>
  drule reused_alloca_ghost >>
  disch_then (qspecl_then [`out`, `[]`, `FEMPTY`, `tn`] strip_assume_tac) >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >>
  gvs[] >>
  gvs[update_var_def, venom_state_component_equality, allocas_from_def] >>
  rpt strip_tac >> eq_tac >> rpt strip_tac >> gvs[]
QED

Theorem alloc_origin_fields[local]:
  n < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK t ==>
  t.vs_allocas = (abi_builtin_allocate_state id n s).vs_allocas /\
  t.vs_alloca_next = (abi_builtin_allocate_state id n s).vs_alloca_next
Proof
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_alloca_def] >>
  strip_tac >> gvs[AllCaseEqs(), abi_builtin_allocate_state_def,
                   update_var_def, wordsTheory.w2n_n2w]
QED

Theorem abi_encode_alloc_origin_run:
  compile_alloc_buffer n sa = (buf,sb) /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  n < dimword (:256) /\
  stmt_state_rel H ctx func cenv cx es s /\ alloca_history func s /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q w t G' tn'.
    (?raw. run_inst_seq (emitted_insts sa sb) s = OK raw /\
           t = raw with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    buf.buf_operand = Var q /\ not_fresh_at sb q /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
           (s,G,tn) [] (OK t,G',tn')) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t with <| vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
              vs_alloca_next := s.vs_alloca_next;
              vs_inst_idx := s.vs_inst_idx |> = s /\
    (!H'. stmt_state_rel H' ctx func cenv cx es s ==>
          stmt_state_rel H' ctx func cenv cx es t) /\
    alloca_history func t /\
    allocas_from lo t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    lookup_var q t = SOME w /\ ptr_covers G' tn' q t n /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,n) /\
    w2n w + n < dimword (:256) /\ w2n w + n <= t.vs_alloca_next /\
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==>
             FLOOKUP t.vs_allocas aid = SOME e) /\
    (!aid b len. aid < sa.cs_next_id /\
                 FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
                 regions_disjoint (w2n w) n b len) /\
    (!name b len. local_region cenv es.scopes t name b len ==>
                  regions_disjoint (w2n w) n b len) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    (!i. i IN tn'.t_mem <=>
         i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < w2n w + n)) /\
    (!x. not_fresh_at sa x ==>
         lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)) /\
    FLOOKUP G' q = SOME (w2n w,n) /\
    t.vs_allocas = (abi_builtin_allocate_state sa.cs_next_id n s).vs_allocas /\
    t.vs_alloca_next = (abi_builtin_allocate_state sa.cs_next_id n s).vs_alloca_next
Proof
  strip_tac >> drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  qabbrev_tac `q = STRING #"%" (toString sa.cs_next_var)` >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [q]) s = OK t` by
    (qpat_x_assum `run_inst_seq _ _ = OK t` mp_tac >>
     simp[run_inst_seq_def, AllCaseEqs()]) >>
  drule_all alloc_origin_fields >> disch_then (mk_asm "alloc_fields") >>
  drule_all ifexp_alloca_step_exact_provenance >>
  disch_then (qspecl_then [`PG`, `G`] strip_assume_tac) >>
  `w = n2w b /\ w2n w = b` by
    (gvs[eval_operand_def] >> simp[wordsTheory.w2n_n2w]) >>
  qpat_x_assum `w = n2w b` SUBST_ALL_TAC >>
  drule_all alloc_effects >> disch_then (qspec_then `tn` strip_assume_tac) >>
  drule_all alloca_step_ptr_covers >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] assume_tac) >>
  qabbrev_tac `ins = mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [q]` >>
  `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  `!x. not_fresh_at sa x ==> x <> q` by
    (rpt strip_tac >> fs[not_fresh_at_def] >>
     first_x_assum (qspec_then `sa.cs_next_var` mp_tac) >> simp[Abbr `q`]) >>
  `run_inst_seq_mem_ok [ins] s` by
    (simp[run_inst_seq_mem_ok_last] >> conj_tac
     >- (irule below_frontier_no_ranges >> simp[Abbr `ins`, mk_inst_def]) >>
     simp[Abbr `ins`, mk_inst_def, memSafeRunTheory.inst_dload_in_section_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (strip_tac >>
     fs[stmt_state_rel_def, fmp_room_def, allocas_below_fmp_def,
        venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def] >>
     rpt strip_tac >> res_tac >> decide_tac) >>
  `!D. inst_seq_ptr D lo ctx func PG G tn [ins] s
         (step_prov PG G ins t) (step_taint ins s t tn)` by
    (gen_tac >> simp[inst_seq_ptr_def] >>
     irule ptr_inst_ok_lower_bound_transport >> simp[] >>
     qexists_tac `0` >> simp[Abbr `ins`, ptr_inst_ok_alloca]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
               ~is_terminator i.inst_opcode) [ins]` by
    simp[Abbr `ins`, mk_inst_def, is_terminator_def] >>
  `t.vs_current_bb = s.vs_current_bb` by
    (qpat_assum `t with <| vs_vars := _; vs_allocas := _; vs_alloca_next := _ |> = s`
       (SUBST1_TAC o SYM) >> simp[]) >>
  `run_inst_seq [ins] s = OK t` by simp[run_inst_seq_def] >>
  `(ctx_has_dalloca ctx ==>
    !pre i post u. [ins] = pre ++ i::post /\ run_inst_seq pre s = OK u ==>
      unitTransformDefs$dalloca_no_wrap i u)` by
    (strip_tac >> rpt gen_tac >> Cases_on `pre` >>
     simp[] >> strip_tac >>
     gvs[Abbr `ins`, mk_inst_def, unitTransformDefsTheory.dalloca_no_wrap_def]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
       (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),
        step_prov PG G ins t, step_taint ins s t tn)` by
    (gen_tac >> irule bodyFullUnwrapRunTheory.emitted_origin_ptr_path >>
     (conj_tac >- simp[]) >> qexistsl_tac [`[ins]`, `sa`] >>
     asm_rewrite_tac[] >> simp[]) >>
  `alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule emitted_alloca_history >> simp[] >>
     qexistsl_tac [`[ins]`, `s`, `sa`] >>
     simp[Abbr `ins`, mk_inst_def, is_terminator_def] >>
     simp[GSYM mk_inst_def] >> metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca]) >>
  qexistsl_tac [`q`, `n2w b`, `t with vs_inst_idx := LENGTH sb.cs_current_insts`,
                `step_prov PG G ins t`, `step_taint ins s t tn`] >>
  conj_tac >- (qexists_tac `t` >> simp[]) >>
  simp[op_prov_def] >>
  conj_tac >- gvs[] >>
  simp[] >>
  conj_tac
  >- (qpat_x_assum `t with <| vs_vars := _; vs_allocas := _; vs_alloca_next := _ |> = s`
        mp_tac >> simp[venom_state_component_equality]) >>
  conj_tac
  >- (rpt strip_tac >> simp[stmt_state_rel_inst_idx] >>
      irule stmt_state_rel_fields_transport >>
      rpt (first_assum (irule_at Any)) >> simp[] >>
      qpat_assum `t with <| vs_vars := _; vs_allocas := _; vs_alloca_next := _ |> = s`
        (SUBST1_TAC o SYM) >> simp[]) >>
  simp[allocas_from_def, lookup_var_def, ptr_covers_def,
       local_region_def, op_prov_def] >>
  conj_tac
  >- (qpat_x_assum `!lo. allocas_from lo s /\ _ ==> _`
        (qspec_then `lo` mp_tac) >> simp[allocas_from_def]) >>
  conj_tac >- gvs[eval_operand_def, lookup_var_def] >>
  conj_tac >- gvs[ptr_covers_def, lookup_var_def] >>
  conj_tac
  >- (qpat_x_assum `!aid b len. aid < _ /\ _ ==> _` mp_tac >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `!name b len. local_region _ _ _ _ _ _ ==> _` mp_tac >>
      simp[local_region_def, lookup_var_def]) >>
  conj_tac
  >- (rpt strip_tac >>
      simp[Abbr `ins`, step_prov_other_output, step_taint_other_output, mk_inst_def] >>
      qpat_x_assum `!x. not_fresh_at sa x ==> lookup_var x t = _`
        drule >> simp[lookup_var_def]) >>
  fs[op_prov_def, markerLib.L "alloc_fields"]
QED

Theorem abi_encode_alloc_origin_exact:
  compile_alloc_buffer n sa = (buf,sb) /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  n < dimword (:256) /\
  stmt_state_rel H ctx func cenv cx es s /\ alloca_history func s /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q w t G' tn'.
    buf.buf_operand = Var q /\ not_fresh_at sb q /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
           (s,G,tn) [] (OK t,G',tn')) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t with <| vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
              vs_alloca_next := s.vs_alloca_next;
              vs_inst_idx := s.vs_inst_idx |> = s /\
    (!H'. stmt_state_rel H' ctx func cenv cx es s ==>
          stmt_state_rel H' ctx func cenv cx es t) /\
    alloca_history func t /\
    allocas_from lo t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    lookup_var q t = SOME w /\ ptr_covers G' tn' q t n /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,n) /\
    w2n w + n < dimword (:256) /\ w2n w + n <= t.vs_alloca_next /\
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==>
             FLOOKUP t.vs_allocas aid = SOME e) /\
    (!aid b len. aid < sa.cs_next_id /\
                 FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
                 regions_disjoint (w2n w) n b len) /\
    (!name b len. local_region cenv es.scopes t name b len ==>
                  regions_disjoint (w2n w) n b len) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    (!i. i IN tn'.t_mem <=>
         i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < w2n w + n)) /\
    (!x. not_fresh_at sa x ==>
         lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)) /\
    FLOOKUP G' q = SOME (w2n w,n) /\
    t.vs_allocas = (abi_builtin_allocate_state sa.cs_next_id n s).vs_allocas /\
    t.vs_alloca_next = (abi_builtin_allocate_state sa.cs_next_id n s).vs_alloca_next
Proof
  strip_tac >> drule_all abi_encode_alloc_origin_run >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`]
    (qx_choosel_then [`q`,`w`,`t`,`G'`,`tn'`] strip_assume_tac)) >>
  qexistsl_tac [`q`,`w`,`t`,`G'`,`tn'`] >> asm_rewrite_tac[]
QED
