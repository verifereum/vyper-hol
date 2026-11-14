(*
 * One fresh buffer on the joint path: compile_alloc_buffer's single
 * ALLOCA at any dead mask and bound lo, whether the site is new or reused,
 * with the frames the full-body callers rebuild their ghosts from.
 *
 * TOP-LEVEL:
 *   alloc_buffer_origin_ptr_path_exact - the ALLOCA as one joint path, its buffer
 *     disjoint from older sites and locals, the taint grown only above the
 *     old frontier, with its exact output provenance
 *   alloc_buffer_origin_ptr_path - the existing covering-region interface
 *   alloc_buffer_ghost_inv_at - ghost_inv_at across that conclusion
 *   alloc_buffer_ghost_kept_at - ghost_kept_at across that conclusion
 *)
Theory bodyFullAllocaFresh
Ancestors
  bodyFullUnwrapRun bodyFullGhostFrame exprSimAlloc allocationPtr
  bodyPtrIfExpAllocLocals bodyPtrStructLitMonotoneRepresentation
  ptrSafetyTransport fragExecPtr fragGasSeqPtr fragExecMem instMemFrontier
  decoderGhostFramePtr abiBuiltinAllocation emitHelperProps exprLoweringProps
  loweringHalt bodyPtrDefs loweringStateRelDefs ptrDiscipline venomMemDefs
  venomExecSemantics venomState venomInst finite_map pred_set

(* Helper: the ALLOCA step itself, new or reused site. *)
Theorem alloca_step_exact[local]:
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

(* TOP-LEVEL: compile_alloc_buffer's ALLOCA on the joint path. *)
Theorem alloc_buffer_origin_ptr_path_exact:
  compile_alloc_buffer n sa = (buf,sb) /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  n < dimword (:256) /\
  stmt_state_rel H ctx func cenv cx es s /\ alloca_history func s /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
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
    FLOOKUP G' q = SOME (w2n w,n) /\
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
         op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  qabbrev_tac `q = STRING #"%" (toString sa.cs_next_var)` >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [q]) s = OK t` by
    (qpat_x_assum `run_inst_seq _ _ = OK t` mp_tac >>
     simp[run_inst_seq_def, AllCaseEqs()]) >>
  drule_all alloca_step_exact >>
  disch_then (qspec_then `tn` strip_assume_tac) >>
  drule_all alloca_step_ptr_covers >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] assume_tac) >>
  qabbrev_tac `ins = mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [q]` >>
  `w = n2w b` by gvs[eval_operand_def] >>
  `b < dimword (:256)` by decide_tac >>
  `w2n w = b` by simp[wordsTheory.w2n_n2w] >>
  qpat_x_assum `w2n w = b` (SUBST_ALL_TAC o SYM) >>
  `t.vs_current_bb = s.vs_current_bb /\ t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\ t.vs_requests = s.vs_requests /\ t.vs_call_ctx = s.vs_call_ctx` by
    (qpat_assum `t with <| vs_vars := _; vs_allocas := _;
                           vs_alloca_next := _ |> = s`
       (SUBST1_TAC o SYM) >> simp[]) >>
  `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  `run_inst_seq [ins] s = OK t /\ sb.cs_current_insts = sa.cs_current_insts ++ [ins]` by gvs[] >>
  `run_inst_seq_mem_ok [ins] s` by
    (simp[run_inst_seq_mem_ok_last] >> conj_tac
     >- (irule below_frontier_no_ranges >> simp[Abbr `ins`, mk_inst_def]) >>
     simp[Abbr `ins`, mk_inst_def, memSafeRunTheory.inst_dload_in_section_def]) >>
  `!D. inst_seq_ptr D lo ctx func PG G tn [ins] s
         (step_prov PG G ins t) (step_taint ins s t tn)` by
    (gen_tac >> simp[inst_seq_ptr_def] >>
     irule ptr_inst_ok_lower_bound_transport >> simp[] >>
     qexists_tac `0` >> simp[Abbr `ins`, ptr_inst_ok_alloca]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
              ~is_terminator i.inst_opcode) [ins]` by
    simp[Abbr `ins`, mk_inst_def, is_terminator_def] >>
  `!x. not_fresh_at sa x ==> x <> q` by
    (rpt strip_tac >> fs[not_fresh_at_def] >>
     first_x_assum (qspec_then `sa.cs_next_var` mp_tac) >> simp[Abbr `q`]) >>
  qexistsl_tac [`q`, `w`, `t with vs_inst_idx := LENGTH sb.cs_current_insts`,
                `step_prov PG G ins t`, `step_taint ins s t tn`] >>
  conj_tac >- gvs[] >>
  conj_tac >- gvs[] >>
  conj_tac
  >- (gen_tac >>
      qspecl_then [`[ins]`, `sa`, `sb`, `s`, `t`, `G`, `tn`,
                   `step_prov PG G ins t`, `step_taint ins s t tn`]
        mp_tac emitted_origin_ptr_path >>
      simp[]) >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac
  >- (qpat_x_assum `t with <| vs_vars := _; vs_allocas := _;
                              vs_alloca_next := _ |> = s` mp_tac >>
      simp[venom_state_component_equality]) >>
  conj_tac
  >- (rpt strip_tac >> simp[stmt_state_rel_inst_idx] >>
      irule stmt_state_rel_fields_transport >>
      rpt (first_assum (irule_at Any)) >> simp[]) >>
  conj_tac
  >- (qspecl_then [`[ins]`, `sa`, `sb`, `s`, `t`] mp_tac emitted_alloca_history >>
      simp[Abbr `ins`, mk_inst_def, is_terminator_def] >>
      disch_then irule >> fs[stmt_state_rel_def]) >>
  conj_tac
  >- (qpat_x_assum `!lo. allocas_from lo s /\ _ ==> _` (qspec_then `lo` mp_tac) >>
      impl_tac >- simp[] >> simp[allocas_from_def]) >>
  conj_tac >- simp[] >>
  conj_tac >- gvs[lookup_var_def] >>
  conj_tac
  >- (qpat_x_assum `ptr_covers _ _ q t n` mp_tac >>
      simp[ptr_covers_def, lookup_var_def] >> strip_tac >>
      gvs[lookup_var_def]) >>
  conj_tac >- simp[] >>
  conj_tac
  >- simp[Abbr `ins`, step_prov_def, out_prov_def, set_prov_def,
          mk_inst_def, FLOOKUP_UPDATE] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (rpt strip_tac >>
               qpat_x_assum `!name b len. local_region _ _ t _ _ _ ==> _` irule >>
               fs[local_region_def, lookup_var_def] >> metis_tac[]) >>
  simp[] >> rpt strip_tac
  >- (`lookup_var x t = lookup_var x s` by metis_tac[] >>
      fs[lookup_var_def])
  >- simp[Abbr `ins`, step_prov_other_output, mk_inst_def] >>
  simp[Abbr `ins`, step_taint_other_output, mk_inst_def]
QED

(* The previous interface follows from the same execution and ghosts. *)
Theorem alloc_buffer_origin_ptr_path:
  compile_alloc_buffer n sa = (buf,sb) /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  n < dimword (:256) /\
  stmt_state_rel H ctx func cenv cx es s /\ alloca_history func s /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
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
         op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all alloc_buffer_origin_ptr_path_exact >>
  disch_then (qspecl_then [`tn`, `explicit`, `PG`, `G`] strip_assume_tac) >>
  qexistsl_tac [`q`, `w`, `t`, `G'`, `tn'`] >> simp[] >> metis_tac[]
QED

(* TOP-LEVEL: ghost_inv_at across the buffer's ALLOCA, stated over
   alloc_buffer_origin_ptr_path's conclusion. *)
Theorem alloc_buffer_ghost_inv_at:
  ghost_inv_at D lo d cenv cx es G tn s /\
  stmt_state_rel H ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
  t with <| vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
            vs_alloca_next := s.vs_alloca_next;
            vs_inst_idx := s.vs_inst_idx |> = s /\
  allocas_from lo t /\ s.vs_alloca_next <= t.vs_alloca_next /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
  tn'.t_imm = tn.t_imm /\
  (!i. i IN tn'.t_mem <=>
       i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < e)) ==>
  ghost_inv_at D lo d cenv cx es G' tn' t
Proof
  strip_tac >>
  `t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
   t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
   t.vs_immutables = s.vs_immutables` by
    (qpat_assum `t with <| vs_vars := _; vs_allocas := _;
                           vs_alloca_next := _; vs_inst_idx := _ |> = s`
       (SUBST1_TAC o SYM) >> simp[]) >>
  `!i. i IN tn'.t_mem /\ i < s.vs_alloca_next ==> i IN tn.t_mem` by
    (qpat_x_assum `!i. i IN tn'.t_mem <=> _` (fn th => rewrite_tac[th]) >>
     rpt strip_tac >> fs[]) >>
  `!p sz. not_fresh_at sa p /\ ptr_covers G tn p s sz ==>
          ptr_covers G' tn' p t sz` by
    (rw[ptr_covers_def] >> metis_tac[]) >>
  `state_rel H func cenv cx es s` by fs[stmt_state_rel_def] >>
  qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[ghost_inv_at_def] >> strip_tac >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
      first_x_assum (drule_all_then strip_assume_tac) >>
      conj_tac >- metis_tac[] >>
      rpt strip_tac >>
      `lookup_var p s = SOME w` by metis_tac[] >>
      drule_all local_ptr_footprint_below_frontier >> strip_tac >>
      qspecl_then [`entry.type`, `entry.value`, `w2n w`, `w2n w`,
                   `val_footprint entry.type entry.value`, `tn.t_mem`,
                   `tn'.t_mem`, `s.vs_memory`, `t.vs_memory`]
        mp_tac robust_val_in_memory_copy_transport_mono >>
      impl_tac
      >- (simp[] >> rpt strip_tac >>
          qpat_x_assum `!i. i IN tn'.t_mem /\ _ ==> _` irule >> simp[]) >>
      disch_then irule >> simp[])
  >- (Cases_on `d` >> gvs[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME rb)` >> PairCases_on `rb` >>
      gvs[return_buf_ptr_def] >> metis_tac[])
  >- metis_tac[]
  >- fs[stor_taint_ok_at_def]
  >- (rpt strip_tac >> `i IN tn.t_mem` by (first_x_assum irule >> simp[]) >>
      metis_tac[])
  >- (rpt strip_tac >> `not_fresh_at sa x` by fs[local_ptrs_reserved_def] >>
      metis_tac[])
  >- simp[] >>
  decide_tac
QED

(* TOP-LEVEL: ghost_kept_at across the buffer's ALLOCA, for a frame whose
   older sites and locals all lie below the old frontier. *)
Theorem alloc_buffer_ghost_kept_at:
  ghost_kept_at lo cenv es0 sk G0 tn0 s0 G tn /\
  (!x. not_fresh_at sk x ==>
       FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
  (!i. i IN tn'.t_mem <=>
       i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < e)) /\
  lo <= s.vs_alloca_next /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
                aid < sk.cs_next_id ==> off + sz <= s.vs_alloca_next) /\
  (!name b sz. local_region cenv es0.scopes s0 name b sz ==>
               b + sz <= s.vs_alloca_next) ==>
  ghost_kept_at lo cenv es0 sk G0 tn0 s0 G' tn'
Proof
  strip_tac >>
  `!i. i IN tn'.t_mem /\ i < s.vs_alloca_next ==> i IN tn.t_mem` by
    (qpat_x_assum `!i. i IN tn'.t_mem <=> _` (fn th => rewrite_tac[th]) >>
     rpt strip_tac >> fs[]) >>
  qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[ghost_kept_at_def] >> strip_tac >> rpt conj_tac
  >- metis_tac[]
  >- (rpt strip_tac >>
      `off + sz <= s.vs_alloca_next` by metis_tac[] >>
      `i IN tn.t_mem` by (first_x_assum irule >> simp[]) >>
      metis_tac[])
  >- (rpt strip_tac >>
      `b + sz <= s.vs_alloca_next` by metis_tac[] >>
      `i IN tn.t_mem` by (first_x_assum irule >> simp[]) >>
      metis_tac[]) >>
  rpt strip_tac >>
  `i IN tn.t_mem` by (first_x_assum irule >> simp[]) >>
  metis_tac[]
QED
