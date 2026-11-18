(* Homogeneous elements reuse the joint full-H tuple traversal. *)
Theory bodyFullMakeArrayElements
Ancestors
  bodyFullMakeArrayLoop exprSimAggregateEncoding rich_list list gasOutcomeFull
  exprSimDefs[qualified,ignore_grammar]

val _ = Parse.hide "base";

Theorem make_array_elements_full:
  !args et tv header off ps sa sb shadow_sa shadow_sb es s G tn.
    body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env ebase /\
    csbase.cs_next_id <= aid /\ csbase.cs_next_id <= sa.cs_next_id /\
    csbase.cs_next_var <= sa.cs_next_var /\
    local_ptrs_reserved cenv csbase /\ local_ptrs_reserved cenv sa /\
    ctx_inst_ids_distinct ctx /\ fn_inst_ids_distinct func /\
    gas_shadow_context ctx shadow_ctx /\ gas_shadow_function func shadow_func /\
    MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
    ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==>
           not_fresh_at csbase x) /\
    (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==>
           not_fresh_at csbase x) /\
    (!H. valid_horizon cx st0 H ebase.storage_trace ==>
         stmt_state_rel H ctx func cenv cx ebase sbase) /\
    body_exprs_full_ok cx args /\
    (!e ee. MEM e args /\ expr_sim_inv cenv cx env ee ==>
            expr_body_pre cenv cx env e ee) /\
    expr_sim_inv cenv cx env es /\
    EVERY (\e. arg_type_fits (expr_type e) et) args /\
    evaluate_type (get_tenv cx) et = SOME tv /\
    type_memory_bytes cenv et = type_memory_size tv /\
    off = (if header then 32 else 0) /\
    off + LENGTH args * type_memory_size tv <= cap /\
    ((\cs ee s G tn.
      (?events. ee.storage_trace = ebase.storage_trace ++ events) /\
      FLOOKUP s.vs_allocas aid = SOME (base,cap) /\
      lookup_var q s = SOME (n2w base) /\
      ptr_covers G tn q s cap /\ not_fresh_at cs q /\
      aid < cs.cs_next_id /\ base+cap < dimword (:256) /\
      base+cap <= s.vs_alloca_next /\
      (!name b n. local_region cenv ee.scopes s name b n ==>
                  loweringStateRelDefs$regions_disjoint base cap b n) /\
      alloca_history func s /\ sbase.vs_alloca_next <= s.vs_alloca_next /\
      (!a b. FLOOKUP sbase.vs_allocas a = SOME b ==>
             FLOOKUP s.vs_allocas a = SOME b) /\
      MAP FDOM ebase.scopes = MAP FDOM ee.scopes /\
      wb_frame cenv ebase ee csbase sbase s /\
      ghost_kept_at lo cenv ebase csbase Gbase tnbase sbase G tn /\
      return_buf_frame d cenv cs s /\ ~s.vs_halted /\
      s.vs_current_bb = cs.cs_current_bb /\
      s.vs_inst_idx = LENGTH cs.cs_current_insts /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
           stmt_state_rel H ctx func cenv cx ee s /\
           storage_well_formed_on cx ee (FST H) /\
           ghost_inv_at (DF H) lo d cenv cx ee G tn s))) sa es s G tn /\
    EVERY (\(rt,v,p,n).
      val_wf rt v /\ val_footprint rt v <= n /\
      base <= p /\ p+n <= base+off /\
      (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
           val_in_memory rt v p m)) ps /\
    compile_make_array_elems compile_expr cenv args et (type_memory_bytes cenv et)
      header (Var q) 0 sa = (Var q,sb) /\
    compile_make_array_elems compile_expr cenv (MAP gas_shadow_expr args) et
      (type_memory_bytes cenv et) header (Var q) 0 shadow_sa = (Var q,shadow_sb) /\
    gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
    fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func ==>
    gas_outcome_full
      (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (eval_exprs cx args) (es,s,G,tn)
      (\H res ee Gf tnf t.
        ?vs. res = INL vs /\ LENGTH vs = LENGTH args /\
          LIST_REL value_has_type (REPLICATE (LENGTH args) tv) vs /\
          LIST_REL val_wf (REPLICATE (LENGTH args) tv) vs /\
          expr_sim_inv cenv cx env ee /\
          ((\cs ee s G tn.
            (?events. ee.storage_trace = ebase.storage_trace ++ events) /\
            FLOOKUP s.vs_allocas aid = SOME (base,cap) /\
            lookup_var q s = SOME (n2w base) /\
            ptr_covers G tn q s cap /\ not_fresh_at cs q /\
            aid < cs.cs_next_id /\ base+cap < dimword (:256) /\
            base+cap <= s.vs_alloca_next /\
            (!name b n. local_region cenv ee.scopes s name b n ==>
                        loweringStateRelDefs$regions_disjoint base cap b n) /\
            alloca_history func s /\ sbase.vs_alloca_next <= s.vs_alloca_next /\
            (!a b. FLOOKUP sbase.vs_allocas a = SOME b ==>
                   FLOOKUP s.vs_allocas a = SOME b) /\
            MAP FDOM ebase.scopes = MAP FDOM ee.scopes /\
            wb_frame cenv ebase ee csbase sbase s /\
            ghost_kept_at lo cenv ebase csbase Gbase tnbase sbase G tn /\
            return_buf_frame d cenv cs s /\ ~s.vs_halted /\
            s.vs_current_bb = cs.cs_current_bb /\
            s.vs_inst_idx = LENGTH cs.cs_current_insts /\
            (!H. valid_horizon cx st0 H ee.storage_trace ==>
                 stmt_state_rel H ctx func cenv cx ee s /\
                 storage_well_formed_on cx ee (FST H) /\
                 ghost_inv_at (DF H) lo d cenv cx ee G tn s))) sb ee t Gf tnf /\
          EVERY (\(rt,v,p,n).
            val_wf rt v /\ val_footprint rt v <= n /\
            base <= p /\ p+n <= base+off /\
            (!m. mem_agree_outside tnf.t_mem t.vs_memory m ==>
                 val_in_memory rt v p m)) ps /\
          (!m. mem_agree_outside tnf.t_mem t.vs_memory m ==>
               elems_in_memory vs (base+off) tv m) /\
          (!p n. base+off+LENGTH args * type_memory_size tv <= p /\ p+n <= base+cap ==>
                 mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory) /\
          (~EXISTS expr_has_effect args ==>
            (!name b n. local_region cenv es.scopes s name b n ==>
              mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory) /\
            !p n. (p+n <= base \/ base+cap <= p) /\
              (!inst b sz. MEM inst (fn_insts func) /\
                inst.inst_opcode = ALLOCA /\ sa.cs_next_id <= inst.inst_id /\
                FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==>
                loweringStateRelDefs$regions_disjoint p n b sz) ==>
              mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory))
      (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r)
Proof
  rpt gen_tac >> strip_tac >>
  `OPT_MMAP (evaluate_type (get_tenv cx)) (REPLICATE (LENGTH args) et) =
    SOME (REPLICATE (LENGTH args) tv)` by
    (qspec_tac (`LENGTH args`, `n`) >> Induct >> simp[REPLICATE]) >>
  `LIST_REL (\ty e. arg_type_fits (expr_type e) ty)
    (REPLICATE (LENGTH args) et) args` by
    gvs[LIST_REL_EL_EQN, EL_REPLICATE, EVERY_EL] >>
  `LIST_REL (\ty tv. type_memory_bytes cenv ty = type_memory_size tv)
    (REPLICATE (LENGTH args) et) (REPLICATE (LENGTH args) tv)` by
    simp[LIST_REL_REPLICATE_same] >>
  fs[exprSimAggregateLoopsTheory.compile_make_array_elems_as_tuple] >>
  irule gas_outcome_full_post_mono >>
  irule_at (Pos last) make_array_loop_full >> BETA_TAC >>
  first_assum (irule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  first_assum (irule_at (Pat `compile_make_tuple _ _ args _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `compile_make_tuple _ _ _ _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `OPT_MMAP _ _ = _`)) >>
  qpat_assum `FLOOKUP s.vs_allocas aid = SOME (base,cap)`
    (irule_at (Pat `FLOOKUP _ _ = _`)) >>
  first_assum (irule_at (Pat `body_inv _ _ _ _`)) >>
  first_assum (irule_at (Pat `gas_shadow_function _ _`)) >>
  first_assum (irule_at (Pat `expr_sim_inv _ _ _ _`)) >>
  first_assum (irule_at (Pat `return_buf_frame _ _ _ _`)) >>
  simp[type_memory_size_list_replicate, arithmeticTheory.ADD_SYM] >>
  qexists_tac `ps` >>
  conj_tac >- gvs[arithmeticTheory.ADD_SYM] >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- gvs[] >>
  rpt gen_tac >> strip_tac >>
  `LENGTH vs = LENGTH args` by (imp_res_tac LIST_REL_LENGTH >> gvs[]) >>
  simp[] >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  reverse conj_tac >- (first_assum ACCEPT_TAC) >>
  simp[GSYM tuple_in_memory_replicate_elems]
QED
