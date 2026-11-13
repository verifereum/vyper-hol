(* Recursive typed stores keep the literal's exterior frame. *)
Theory bodyPtrPhysicalStoreFrame
Ancestors
  aggregateStorePtrFrame bodyPtrMakeArrayPositiveFrame bodyPtrMakeArrayAllocationFrame
  bodyPtrMakeArrayCopyStateFrame bodyPtrMakeArrayStoreFrame
  exprSimPtrLiteralBuffer typedMemoryCopy loweringStateRelDefs
  bodyPtrMakeArrayConsInvariant bodyPtrDefs compileEnv freshWrites
  venomState ptrDiscipline list pair pred_set
  exprSimWordArgs wordArgsPtr
  exprSimAggregateChildren tupleMemoryFrame



Theorem literal_typed_loop_store_frame:
  literal_loop_frame pure ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf es sa G tn s cells off /\
  literal_prefix_ok cells tn s /\ ~ce.ce_is_ctor /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce fr /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  typed_copy_state_frame sa (addr+off) k s t /\ off+k <= capacity /\
  (!x. not_fresh_at sa x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
    op_taint tm (Var x) = op_taint tn (Var x)) /\
  (!i. ~(addr+off <= i /\ i < addr+off+k) ==>
    (i IN tm.t_mem <=> i IN tn.t_mem)) /\
  tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ~t.vs_halted /\ val_wf tv v /\ val_footprint tv v <= k /\
  (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
    val_in_memory tv v (addr+off) m) ==>
  literal_loop_frame pure ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf es sb H tm t (cells ++ [(tv,v,addr+off,k)]) (off+k) /\
  literal_prefix_ok (cells ++ [(tv,v,addr+off,k)]) tm t
Proof
  strip_tac >> drule literal_loop_frame_runtime >> strip_tac >>
  `!name p n. local_region ce es.scopes s name p n ==>
      regions_disjoint (addr+off) k p n` by
    (rpt strip_tac >>
     `addr+capacity <= p \/ p+n <= addr` by
       (fs[literal_loop_frame_def] >> metis_tac[]) >>
     simp[regions_disjoint_def] >> decide_tac) >>
  `stmt_state_rel ctx func ce cx es t` by
    (irule (Q.INST [`sa` |-> `sa`, `s` |-> `s`, `dst` |-> `addr+off`,
                    `n` |-> `k`] aggregate_store_control_frame) >>
     qexistsl_tac [`addr`, `k`, `off`, `s`, `sa`] >>
     fs[typed_copy_state_frame_def, typed_copy_frame_def] >> conj_tac
     >- (rpt strip_tac >>
         qpat_x_assum `!name p n. local_region ce es.scopes s name p n ==>
           regions_disjoint _ _ p n` drule >>
         simp[regions_disjoint_def] >> decide_tac) >>
     rpt strip_tac >>
     qpat_x_assum `!a n. _ ==> mem_bytes_at a n t.vs_memory = _` irule >> simp[]) >>
  `ghost_inv d ce cx es H tm t` by
    (irule literal_typed_copy_ghost_frame >>
     qexistsl_tac [`G`, `addr+off`, `ctx`, `func`, `k`, `s`, `sa`, `tn`] >>
     simp[] >> metis_tac[]) >>
  `!i. ~(addr+off <= i /\ i < addr+off+k) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory` by
    (fs[typed_copy_state_frame_def, typed_copy_frame_def] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `ghost_kept ce es fr Gf tnf sf H tm` by
    (drule literal_loop_store_ghost >> strip_tac >>
     qpat_assum `ghost_kept ce es fr Gf tnf sf G tn`
       (strip_assume_tac o REWRITE_RULE [ghost_kept_def]) >>
     simp_tac std_ss [ghost_kept_def] >> conj_tac
     >- (rpt strip_tac >>
         `not_fresh_at sa x` by
           (fs[literal_loop_frame_def] >> metis_tac[not_fresh_at_mono]) >>
         metis_tac[]) >>
     conj_tac
     >- (qx_genl_tac [`old`, `p`, `n`, `i`] >> strip_tac >>
         `addr+capacity <= p \/ p+n <= addr` by
           (fs[literal_loop_frame_def] >> metis_tac[]) >>
         `~(addr+off <= i /\ i < addr+off+k)` by decide_tac >>
         metis_tac[]) >>
     qx_genl_tac [`name`, `p`, `n`, `i`] >> strip_tac >>
     `local_region ce ees.scopes sf name p n` by
       (fs[literal_loop_frame_def] >>
        metis_tac[local_region_scopes_domain]) >>
     `addr+capacity <= p \/ p+n <= addr` by
       (fs[literal_loop_frame_def] >> metis_tac[]) >>
     `~(addr+off <= i /\ i < addr+off+k)` by decide_tac >> metis_tac[]) >>
  `t.vs_allocas = s.vs_allocas` by
    (fs[typed_copy_state_frame_def] >>
     qpat_x_assum `_ = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `FLOOKUP H root = SOME (addr,capacity) /\ ptr_covers H tm root t capacity` by
    (drule literal_loop_frame_allocation >> strip_tac >>
     `lookup_var root t = lookup_var root s /\
      FLOOKUP H root = FLOOKUP G root /\
      op_taint tm (Var root) = op_taint tn (Var root)` by metis_tac[] >>
     gvs[ptr_covers_def] >> metis_tac[]) >>
  `literal_loop_frame pure ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf es sb H tm t cells off` by
    (irule literal_loop_store_endpoint >> simp[] >>
     qexistsl_tac [`G`, `k`, `s`, `sa`, `tn`] >> simp[] >> metis_tac[]) >>
  `EVERY (\(tv,v,p,k). p+k <= addr+off) cells` by
    (gvs[literal_loop_frame_def, EVERY_MEM, FORALL_PROD] >> metis_tac[]) >>
  `literal_prefix_ok cells tm t` by
    (irule literal_prefix_store_frame >>
     qexistsl_tac [`addr+off`, `k`, `s`, `tn`] >> simp[] >> metis_tac[]) >>
  conj_tac >- (irule literal_loop_frame_advance >> simp[]) >>
  simp[literal_prefix_cell] >> metis_tac[]
QED
