(* The slot copy endpoint, with the literal allocation retained for linked joins. *)
Theory bodyCopySlotRhsEndpointMods
Ancestors
  bodyCopySlotRhsRunMods exprPtrUnwrapAllocation exprPtrUnwrapAllocSemantic
  exprSimAlloc exprLoweringProps compileEnv loweringStateRelDefs stateRelProj
  bodyPtrDefs venomState venomInst words finite_map arithmetic

Theorem copy_slot_rhs_endpoint_mods:
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\ ~is_word_type t /\
  unwrap_value ce (LocatedValue t p) sm = (op,sc) /\ fn_has_code sm sc func /\
  local_ptrs_reserved ce sm /\ fn_inst_ids_distinct func /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
  type_memory_bytes ce (post_value_type ce e) = type_memory_size rt /\
  type_memory_size rt < 2**64 /\ read_result cx tv ee = (INL v,ee) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es sa sm entry ee tv
      (LocatedValue t p) s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  ptr_vv_ok cx (post_value_type ce e) tv (LocatedValue t p) ee G tn s ==>
  ?root dst mid buf u0 z Gf tnf.
    op = Var root /\
    root = STRING #"%" (toString sm.cs_next_var) /\
    compile_alloc_buffer (type_memory_size rt) sm = (buf,mid) /\
    buf.buf_operand = Var root /\ buf.buf_size = type_memory_size rt /\
    MEM (mk_inst sm.cs_next_id ALLOCA
      [Lit (n2w (type_memory_size rt))] [root]) (fn_insts func) /\
    exec_alloca (mk_inst sm.cs_next_id ALLOCA
      [Lit (n2w (type_memory_size rt))] [root]) s
      (n2w (type_memory_size rt) : bytes32) = OK u0 /\
    FLOOKUP u0.vs_allocas sm.cs_next_id =
      SOME (buffer_allocation_base s sm.cs_next_id,type_memory_size rt) /\
    FLOOKUP u0.vs_allocas sm.cs_next_id = SOME (w2n dst,type_memory_size rt) /\
    copy_static z = copy_static u0 /\
    sm.cs_next_var < sc.cs_next_var /\
    sm.cs_next_id < sc.cs_next_id /\
    z.vs_accounts = s.vs_accounts /\
    z.vs_transient = s.vs_transient /\
    z.vs_call_ctx = s.vs_call_ctx /\
    z.vs_immutables = s.vs_immutables /\
    z.vs_data_section = s.vs_data_section /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK z,Gf,tnf)) /\
    ~z.vs_halted /\ z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    alloca_history func z /\ allocas_from lo z /\
    s.vs_alloca_next <= z.vs_alloca_next /\
    eval_operand op z = SOME dst /\
    ptr_covers Gf tnf root z (type_memory_size rt) /\
    lo <= w2n dst /\
    w2n dst + type_memory_size rt < dimword (:256) /\
    w2n dst + type_memory_size rt <= z.vs_alloca_next /\
    val_wf rt v /\
    (!mem. mem_agree_outside tnf.t_mem z.vs_memory mem ==>
      val_in_memory rt v (w2n dst) mem) /\
    (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==>
      FLOOKUP z.vs_allocas aid = SOME ent) /\
    (!aid b len. aid < sm.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n dst) (type_memory_size rt) b len) /\
    (!name b len. local_region ce ee.scopes s name b len ==>
      b + len <= w2n dst \/
      w2n dst + type_memory_size rt <= b) /\
    (!off len. off + len <= w2n dst \/
      w2n dst + type_memory_size rt <= off ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
    (!i. i < w2n dst \/ w2n dst + type_memory_size rt <= i ==>
      i IN tnf.t_mem ==> i IN tn.t_mem) /\
    (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x)) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_imm = tn.t_imm /\
    LENGTH s.vs_memory <= LENGTH z.vs_memory
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all copy_slot_rhs_run_mods >>
  disch_then (qspec_then `explicit` strip_assume_tac) >>
  last_x_assum (qspec_then `PG` (qx_choosel_then
    [`root`,`dst`,`mid`,`buf`,`u`,`z`,`Gf`,`tnf`] strip_assume_tac)) >>
  `compile_alloc_buffer (type_memory_size rt) sm = (buf,mid)` by
    first_assum ACCEPT_TAC >>
  `buf.buf_size = type_memory_size rt` by
    (qpat_assum `compile_alloc_buffer _ _ = (buf,mid)` mp_tac >>
     drule unwrap_alloc_generated_code >> strip_tac >> gvs[]) >>
  `root = STRING #"%" (toString sm.cs_next_var)` by
    (drule_all unwrap_alloc_generated_code >> strip_tac >> gvs[]) >>
  `MEM (mk_inst sm.cs_next_id ALLOCA
      [Lit (n2w (type_memory_size rt))] [root]) (fn_insts func)` by
    metis_tac[buffer_alloc_code] >>
  `type_memory_size rt < dimword (:256)` by
    (qpat_x_assum `type_memory_size rt < 2 ** 64` mp_tac >> decide_tac) >>
  `step_inst_base (mk_inst sm.cs_next_id ALLOCA
      [Lit (n2w (type_memory_size rt))] [root]) s =
      OK (update_var root
        (n2w (buffer_allocation_base s sm.cs_next_id))
        (buffer_allocation_fields s sm.cs_next_id (type_memory_size rt)))` by
    (drule_all unwrap_alloc_generated_step >> strip_tac >> gvs[]) >>
  `exec_alloca (mk_inst sm.cs_next_id ALLOCA
      [Lit (n2w (type_memory_size rt))] [root]) s
      (n2w (type_memory_size rt) : bytes32) = OK
        (update_var root
          (n2w (buffer_allocation_base s sm.cs_next_id))
          (buffer_allocation_fields s sm.cs_next_id (type_memory_size rt)))` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[venomExecSemanticsTheory.step_inst_base_opcode_eqs, venomInstTheory.mk_inst_def, venomExecSemanticsTheory.exec_alloca_def]) >>
  `copy_static z = copy_static
      (update_var root
        (n2w (buffer_allocation_base s sm.cs_next_id))
        (buffer_allocation_fields s sm.cs_next_id (type_memory_size rt)))` by
    (qpat_x_assum `copy_static z = copy_static _` (fn th =>
       pure_rewrite_tac[th]) >>
     gvs[exprSimStorageCopyTheory.copy_static_def, venomStateTheory.update_var_def]) >>
  `sm.cs_next_var < mid.cs_next_var` by
    (drule unwrap_alloc_generated_code >> strip_tac >>
     gvs[contextTheory.compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
       comp_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
       comp_ignore_bind_def, emit_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
      ee.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
      vv_post_mods H ctx func ce cx e es sa sm entry ee tv
        (LocatedValue t p) s /\ _`
    (drule_then strip_assume_tac) >>
  `stmt_state_rel H0 ctx func ce cx ee s` by
    fs[bodyFullPostsModsTheory.vv_post_mods_def] >>
  `p.ptr_location = slot_loc (p.ptr_location = LocTransient)` by
    (qpat_assum `p.ptr_location = LocStorage \/ _` strip_assume_tac >>
     simp[loweringPostsTheory.slot_loc_def]) >>
  `t = post_value_type ce e` by
    (qpat_assum `vv_post_mods H0 ctx func ce cx e es sa sm entry ee tv
        (LocatedValue t p) s`
       (strip_assume_tac o SIMP_RULE (srw_ss())
        [bodyFullPostsModsTheory.vv_post_mods_def,
         bodyFullPostsModsTheory.vv_holds_mods_def,
         loweringPostsTheory.vv_holds_def]) >>
     Cases_on `p.ptr_location` >> gvs[loweringPostsTheory.slot_loc_def]) >>
  `mid.cs_next_var ≤ sc.cs_next_var` by
    (qpat_x_assum `unwrap_value ce (LocatedValue t p) sm = (op,sc)` mp_tac >>
     simp[exprLoweringTheory.unwrap_value_def] >>
     Cases_on `p.ptr_location` >> gvs[loweringPostsTheory.slot_loc_def] >> strip_tac >>
     qpat_x_assum `compile_ensure_in_memory _ _ _ _ _ _ _ = _` mp_tac >>
     simp[contextTheory.compile_ensure_in_memory_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
     Cases_on `((type_memory_size rt + 31) DIV 32 = 1)` >>
     gvs[contextTheory.compile_storage_to_memory_def,
       contextTheory.compile_transient_to_memory_def,
       GSYM contextTheory.compile_slot_to_memory_def,
       copyExecutionTheory.compile_slot_to_memory_shape,
       copyExecutionTheory.slot_copy_final_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, emitHelperTheory.emit_op_def,
       emitHelperTheory.emit_void_def, emit_def, fresh_var_def, fresh_id_def,
       contextTheory.compile_alloc_buffer_def] >> strip_tac >> gvs[]) >>
  `sm.cs_next_var < sc.cs_next_var` by
    (qpat_assum `sm.cs_next_var < mid.cs_next_var` mp_tac >>
     qpat_assum `mid.cs_next_var ≤ sc.cs_next_var` mp_tac >>
     decide_tac) >>
  `FLOOKUP (buffer_allocation_fields s sm.cs_next_id (type_memory_size rt)).vs_allocas
       sm.cs_next_id = SOME (buffer_allocation_base s sm.cs_next_id,type_memory_size rt)` by
    (Cases_on `FLOOKUP s.vs_allocas sm.cs_next_id` >>
     simp[bufferAllocationExecutionTheory.buffer_allocation_base_def,
       bufferAllocationExecutionTheory.buffer_allocation_fields_def,
       FLOOKUP_UPDATE] >>
     rename1 `FLOOKUP s.vs_allocas sm.cs_next_id = SOME x` >>
     PairCases_on `x` >> gvs[] >>
     `x1 = w2n (n2w (type_memory_size rt) : bytes32)` by
       (drule stateRelProjTheory.stmt_state_rel_alloca_size >>
        disch_then
          (qspecl_then
             [`mk_inst sm.cs_next_id ALLOCA
                [Lit (n2w (type_memory_size rt))]
                [STRING #"%" (toString sm.cs_next_var)]`,
              `n2w (type_memory_size rt) : bytes32`, `x0`, `x1`] mp_tac) >>
        qpat_assum `MEM (mk_inst _ ALLOCA _ _) (fn_insts func)`
          (assume_tac o SIMP_RULE (srw_ss()) [mk_inst_def]) >>
        simp[mk_inst_def]) >>
     fs[w2n_n2w]) >>
  `FLOOKUP (update_var root (n2w (buffer_allocation_base s sm.cs_next_id))
       (buffer_allocation_fields s sm.cs_next_id (type_memory_size rt))).vs_allocas
       sm.cs_next_id = SOME (w2n dst,type_memory_size rt)` by
    (qpat_assum `copy_static z = copy_static (update_var _ _ _)`
       (mp_then Any strip_assume_tac exprSimStorageCopyTheory.copy_static_fields) >>
     qpat_assum `z.vs_allocas = _` (fn th => pure_rewrite_tac[GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  qexistsl_tac [`root`,`dst`,`mid`,`buf`,
    `update_var root (n2w (buffer_allocation_base s sm.cs_next_id))
      (buffer_allocation_fields s sm.cs_next_id (type_memory_size rt))`,
    `z`,`Gf`,`tnf`] >>
  `z.vs_accounts = s.vs_accounts /\ z.vs_transient = s.vs_transient /\
   z.vs_call_ctx = s.vs_call_ctx /\ z.vs_immutables = s.vs_immutables /\
   z.vs_data_section = s.vs_data_section` by
    (Cases_on `FLOOKUP s.vs_allocas sm.cs_next_id` >>
     qpat_assum `FLOOKUP s.vs_allocas sm.cs_next_id = _`
       (fn look =>
         qpat_assum `copy_static z = copy_static (buffer_allocation_fields _ _ _)`
           (ACCEPT_TAC o SRULE [look, exprSimStorageCopyTheory.copy_static_def,
            bufferAllocationExecutionTheory.buffer_allocation_fields_def] o
            Q.AP_TERM `\x. (x.vs_accounts,x.vs_transient,x.vs_call_ctx,
                             x.vs_immutables,x.vs_data_section)`))) >>
  pop_assum strip_assume_tac >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[] >>
  (rpt conj_tac >> TRY (first_assum ACCEPT_TAC))
  >- (qpat_x_assum `FLOOKUP (update_var _ _ _).vs_allocas _ = SOME (w2n dst,_)`
        (mp_tac o SRULE [venomStateTheory.update_var_def]) >> simp[])
  >- (qpat_assum `!name b len. local_region ce ee.scopes s name b len ==> _`
        mp_tac >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def, DISJ_COMM]) >>
  rpt gen_tac >> disch_tac >> disch_tac >>
  qpat_assum `!j. _ /\ j IN tnf.t_mem ==> _`
    (qspec_then `i` irule) >> simp[] >> decide_tac
QED
