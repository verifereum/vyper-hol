(* A single linked allocation edge in the ECMul staging prefix. *)
Theory bodyECMulAllocEdgeMods
Ancestors
  bodyFullAllocaFresh bodyFullGhostFrame bodyECAddAllocFrameMods bodyFullPostsMods
  bodyMemoryDefs exprSimAlloc exprSimWordArgs loweringPosts loweringStateRelDefs
  stateRelProj compileEnv venomInst venomState venomMemDefs wordArgsPtr finite_map words

Theorem ecmul_alloc_edge_mods:
  (n = 96 \/ n = 64) /\
  compile_alloc_buffer n sa = (buf,sb) /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  alloca_history func s /\ ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ (?H. P H) /\
  (!H : (bool # bytes32 # type_value) list # num list. P H ==>
    stmt_state_rel H ctx func cenv cx es s /\ immutable_frame_mods func cenv cx es s /\
    ghost_inv_at_mods (DF H) lo d cenv cx es G tn s) ==>
  ?dst w t Ga tna.
    buf.buf_operand = Var dst /\ not_fresh_at sb dst /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [dst]) (fn_insts func) /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,n) /\
    lookup_var dst t = SOME w /\ ptr_covers Ga tna dst t n /\
    FLOOKUP Ga dst = SOME (w2n w,n) /\ op_taint tna (Var dst) = {} /\
    lo <= w2n w /\ w2n w+n < dimword (:256) /\ w2n w+n <= t.vs_alloca_next /\
    s.vs_alloca_next <= t.vs_alloca_next /\ allocas_from lo t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Ga,tna)) /\
    t with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
             vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|> = s /\
    t.vs_memory = s.vs_memory /\
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==> FLOOKUP t.vs_allocas aid = SOME e) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Ga x = FLOOKUP G x /\
      op_taint tna (Var x) = op_taint tn (Var x)) /\
    tna.t_stor = tn.t_stor /\ tna.t_trans = tn.t_trans /\ tna.t_imm = tn.t_imm /\
    (!i. i IN tna.t_mem <=> i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < w2n w+n)) /\
    (!name b k. local_region cenv es.scopes t name b k ==> regions_disjoint (w2n w) n b k) /\
    (!aid b k. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) ==>
      regions_disjoint (w2n w) n b k) /\
    (!aid b k. aid < sa.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,k) ==>
      regions_disjoint (w2n w) n b k) /\
    (!src tops. ALOOKUP cenv.ce_modules src = SOME tops /\ cenv.ce_is_ctor ==>
      !name tv iv off.
        FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
        FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
          | SOME imms => get_source_immutables src imms) name = SOME (tv,iv) ==>
        regions_disjoint (w2n w) n off (type_memory_size tv)) /\
    wb_frame cenv es es sa s t /\ pure_frame cenv func es sa s t /\
    ghost_kept_at lo cenv es sa G tn s Ga tna /\
    (!H. P H ==> stmt_state_rel H ctx func cenv cx es t /\
      immutable_frame_mods func cenv cx es t /\ ghost_inv_at_mods (DF H) lo d cenv cx es Ga tna t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?H. P H` (qx_choose_then `H0` assume_tac) >>
  qpat_assum `!H. P H ==> _` (drule_then strip_assume_tac) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def] >>
  drule_then assume_tac bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >>
  `n < dimword (:256)` by (qpat_assum `n = 96 \/ n = 64` strip_assume_tac >> simp[dimword_def]) >>
  drule_all (INST_TYPE [beta |-> alpha] alloc_buffer_origin_ptr_path_with_raw_endpoint) >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`]
    (qx_choosel_then [`dst`,`w`,`t`,`Ga`,`tna`,`raw`] strip_assume_tac)) >>
  suspend "frames"
QED

Resume ecmul_alloc_edge_mods[frames]:
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [dst]) (fn_insts func)` by
    (drule loweringHaltTheory.compile_alloc_buffer_insts >> strip_tac >>
     `dst = STRING #"%" (toString sa.cs_next_var)` by metis_tac[operand_11] >>
     drule_all buffer_alloc_code >> simp[]) >>
  `!H. P H ==> stmt_state_rel H ctx func cenv cx es t /\
              immutable_frame_mods func cenv cx es t /\
              ghost_inv_at_mods (DF H) lo d cenv cx es Ga tna t` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. P H ==> _` (qspec_then `H` (drule_then strip_assume_tac)) >>
     drule_all bodyECAddAllocFrameModsTheory.ecadd_alloc_frame_mods >>
     simp[]) >>
  `t.vs_memory = s.vs_memory /\ ~t.vs_halted` by
    (qpat_assum `~s.vs_halted` mp_tac >>
     qpat_assum `t with <|vs_vars := _; vs_allocas := _;
                    vs_alloca_next := _; vs_inst_idx := _|> = s`
       (SUBST1_TAC o SYM) >> simp[]) >>
  `wb_frame cenv es es sa s t` by
    (irule wb_frame_readonly_tail >> qexistsl_tac [`sa`,`s`] >> simp[wb_frame_refl] >>
     rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> _` (drule_then strip_assume_tac) >> simp[]) >>
  `pure_frame cenv func es sa s t` by simp[pure_frame_mem_eq] >>
  `!aid b k. FLOOKUP s.vs_allocas aid = SOME (b,k) ==> b+k <= s.vs_alloca_next` by
    (qpat_assum `stmt_state_rel H0 _ _ _ _ _ s`
       (mp_then Any mp_tac stmt_state_rel_local_ptrs_alloca) >>
     simp[alloca_inv_def,alloca_next_valid_def] >>
     strip_tac >> rpt strip_tac >> first_x_assum drule >> decide_tac) >>
  `!name b k. local_region cenv es.scopes s name b k ==> b+k <= s.vs_alloca_next` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC body_local_region_frontier) >>
  `ghost_kept_at lo cenv es sa G tn s Ga tna` by
    (irule alloc_buffer_ghost_kept_at >>
     qexistsl_tac [`G`,`w2n w+n`,`s`,`tn`] >> simp[ghost_kept_at_refl] >> metis_tac[]) >>
  suspend "separation"
QED

Resume ecmul_alloc_edge_mods[separation]:
  `stmt_state_rel H0 ctx func cenv cx es t` by
    (qpat_assum `!H'. stmt_state_rel H' _ _ _ _ _ s ==> _`
       (drule_then ACCEPT_TAC)) >>
  `allocas_non_overlapping t` by
    (qpat_assum `stmt_state_rel H0 _ _ _ _ _ t`
       (mp_then Any mp_tac stmt_state_rel_local_ptrs_alloca) >> simp[alloca_inv_def]) >>
  `!aid b k. aid < sa.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,k) ==>
       regions_disjoint (w2n w) n b k` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `allocas_non_overlapping t`
       (mp_tac o REWRITE_RULE[allocas_non_overlapping_def]) >>
     disch_then (qspecl_then [`sa.cs_next_id`,`aid`,`w2n w`,`n`,`b`,`k`] mp_tac) >>
     `sa.cs_next_id <> aid` by decide_tac >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  qpat_assum `run_inst_seq (emitted_insts sa sb) s = OK raw`
    (mp_then Any mp_tac ecadd_alloc_frame_mods) >>
  disch_then drule_all >> strip_tac >>
  `op_taint tna (Var dst) = {}` by fs[bodyPtrDefsTheory.ptr_covers_def] >>
  `lo <= w2n w` by
    (qpat_assum `allocas_from lo t` (assume_tac o REWRITE_RULE[ptrDisciplineTheory.allocas_from_def]) >>
     qpat_assum `!aid b k. FLOOKUP t.vs_allocas aid = _ ==> _` (drule_then ACCEPT_TAC)) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (qpat_assum `stmt_state_rel H0 _ _ _ _ _ t`
       (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  qexistsl_tac [`dst`,`w`,`t`,`Ga`,`tna`] >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!src tops. _ ==> (_ /\ _)` (drule_all_then (ACCEPT_TAC o CONJUNCT2))
QED

Finalise ecmul_alloc_edge_mods
