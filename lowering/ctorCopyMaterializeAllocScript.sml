(* Observation of the allocation used by the nonword materializer. *)
Theory ctorCopyMaterializeAlloc
Ancestors
  bodyFullExtCallDefaultAlloc

Theorem copied_head_alloc_observed:
  compile_alloc_buffer n sm = (buf,sn) /\ fn_has_code sm sn func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sm /\
  n < dimword (:256) /\ sa.cs_next_var <= sm.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post H ctx func cenv cx e es sa sm s0 ee tv vv s /\
     ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
  stmt_state_rel H0 ctx func cenv cx es s0 /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  alloca_history func s /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!q r. buf.buf_operand = Var q /\
     step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit (n2w n)] [q]) s = OK r ==>
     R s (r with vs_inst_idx := SUC s.vs_inst_idx)) ==>
  ?q w u Ga ta.
    R s u /\
    buf.buf_operand = Var q /\ not_fresh_at sn q /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
           (s,G,tn) [] (OK u,Ga,ta)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       vv_post H ctx func cenv cx e es sa sm s0 ee tv vv u /\
       ghost_inv_at (DF H) lo d cenv cx ee Ga ta u) /\
    ghost_kept_at lo cenv es sa Gi ti s0 Ga ta /\
    ~u.vs_halted /\ u.vs_current_bb = sn.cs_current_bb /\
    u.vs_inst_idx = LENGTH sn.cs_current_insts /\
    u with <| vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
              vs_alloca_next := s.vs_alloca_next;
              vs_inst_idx := s.vs_inst_idx |> = s /\
    u.vs_memory = s.vs_memory /\
    alloca_history func u /\ allocas_from lo u /\
    s.vs_alloca_next <= u.vs_alloca_next /\
    s0.vs_alloca_next <= u.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    lookup_var q u = SOME w /\ ptr_covers Ga ta q u n /\
    FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n w,n) /\
    FLOOKUP Ga q = SOME (w2n w,n) /\
    w2n w + n < dimword (:256) /\ w2n w + n <= u.vs_alloca_next /\
    (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==>
               FLOOKUP u.vs_allocas aid = SOME ent) /\
    (!aid b len. aid < sm.cs_next_id /\
                 FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
                 regions_disjoint (w2n w) n b len) /\
    (!name b len. local_region cenv ee.scopes u name b len ==>
                  regions_disjoint (w2n w) n b len) /\
    ta.t_stor = tn.t_stor /\ ta.t_trans = tn.t_trans /\ ta.t_imm = tn.t_imm /\
    (!i. i IN ta.t_mem <=>
         i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < w2n w + n)) /\
    (!x. not_fresh_at sm x ==>
         lookup_var x u = lookup_var x s /\ FLOOKUP Ga x = FLOOKUP G x /\
         op_taint ta (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (SPEC_ALL extcall_default_alloc_cut_step) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choosel_then [`q`,`w`,`u`,`Ga`,`ta`] strip_assume_tac) >>
  qexistsl_tac [`q`,`w`,`u`,`Ga`,`ta`] >>
  conj_tac >- (qpat_x_assum `u = _` SUBST1_TAC >> metis_tac[]) >>
  qpat_x_assum `u = _` kall_tac >> asm_rewrite_tac[]
QED
