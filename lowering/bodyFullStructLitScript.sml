(* Struct literals over the joint finite-horizon body judgments.
   Allocation and each field's compilation share one source-GAS witness,
   target endpoint and pointer ghosts across the valid horizons.
   bodyFullAttribute is the existing joint case; bodyPtrStructLit and
   exprSimStructLitBodyCounted supply the corresponding loop machinery.
   The old pointer judgment alone does not imply this joint result. *)
Theory bodyFullStructLit
Ancestors
  bodyFullShadowBodyInv
  bodyFullIfExpReach[qualified,ignore_grammar]
  bodyFullOfVV bodyFullPreds bodySimFull gasOutcomeFullCompose gasContext exprSimDefs
  gasShadowCompile bodyFullStructLitAdd bodyFullStructLitInputs
  bodyFullStructLitBytes bodyFullStructLitZeroStore
  bodyFullStructLitFrames bodyPtrDefs bodyPtrMakeArrayEmission
  bodyFullAllocaFresh bodyFullAllocGeneric bodyMemoryDefs bodyFullPathHistory
  exprSimAggregateLayout exprSimAggregateSource exprSimHyps exprSimHypsDefs
  exprLoweringProps exprSimUnwrap loweringHalt fragExec allocLimits
  loweringPosts compileEnv vyperTypeSystem
  vyperTyping vyperInterpreter vyperState vyperAST list
  vyperStorageTrace vyperStorageFootprint venomExecProps
  bodyInvCodeProps exprBodyPreProps exprSimFullBundleProps

val _ = Parse.hide "body";

Theorem structlit_operand_frame[local]:
  t.vs_labels = s.vs_labels /\
  (!p. op = Var p ==> lookup_var p t = lookup_var p s) ==>
  eval_operand op t = eval_operand op s
Proof
  Cases_on `op` >> simp[venomStateTheory.eval_operand_def]
QED

Theorem structlit_ghost_kept_trans[local]:
  stmt_state_rel H ctx func ce cx ees sf /\ local_ptrs_reserved ce fr /\
  MAP FDOM ees.scopes = MAP FDOM es.scopes /\
  wb_frame ce ees es fr sf s0 /\
  fr.cs_next_var <= si.cs_next_var /\ fr.cs_next_id <= si.cs_next_id /\
  ghost_kept_at lo ce ees fr Gf tnf sf G0 tn0 /\
  ghost_kept_at lo ce es si G0 tn0 s0 G tn ==>
  ghost_kept_at lo ce ees fr Gf tnf sf G tn
Proof
  strip_tac >>
  `ghost_kept ce ees fr Gf tnf sf G0 tn0 /\
   ghost_kept ce es si G0 tn0 s0 G tn` by
    (fs[ghost_kept_at_def, ghost_kept_def] >> metis_tac[]) >>
  `ghost_kept ce ees fr Gf tnf sf G tn` by
    (irule wordArgsPtrTheory.ghost_kept_wb_trans >> metis_tac[]) >>
  fs[ghost_kept_def, ghost_kept_at_def] >> metis_tac[]
QED

Theorem structlit_prefix_child_frame[local]:
  wb_frame ce es ee si s z /\ ghost_kept_at lo ce es si G0 tn0 s G tn /\
  FLOOKUP s.vs_allocas aid = SOME (addr,capacity) /\ aid < si.cs_next_id /\
  (!name p k. local_region ce es.scopes s name p k ==>
     addr+capacity <= p \/ p+k <= addr) /\
  EVERY (\(tv,v,p,k). addr <= p /\ p+k <= addr+capacity) cells /\
  literal_prefix_ok cells tn0 s ==>
  literal_prefix_ok cells tn z
Proof
  strip_tac >>
  `mem_bytes_at addr capacity z.vs_memory = mem_bytes_at addr capacity s.vs_memory /\
   (!i. addr <= i /\ i < addr+capacity /\ i IN tn.t_mem ==> i IN tn0.t_mem)` by
    (fs[wb_frame_def, ghost_kept_at_def] >>
     conj_tac
     >- (qpat_x_assum `!aid off sz. _` irule >>
         conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
         qexists_tac `aid` >> simp[]) >>
     rpt strip_tac >> qpat_x_assum `!aid off sz i. FLOOKUP _ _ = _ /\ _ ==> _` irule >>
     simp[] >> qexistsl_tac [`aid`, `addr`, `capacity`] >> simp[] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  irule bodyPtrMakeArrayMemoryFrameTheory.literal_prefix_transport >>
  qexistsl_tac [`s`, `tn0`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `val_wf tv v /\ val_footprint tv v <= k` by
    metis_tac[bodyPtrMakeArrayMemoryFrameTheory.literal_prefix_lookup] >>
  `addr <= p /\ p+k <= addr+capacity` by
    (fs[EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  gen_tac >> strip_tac >>
  irule bodyPtrMakeArrayMemoryFrameTheory.robust_val_in_memory_shrinking_frame >>
  simp[] >> qexistsl_tac [`tn0.t_mem`, `tn.t_mem`, `s.vs_memory`, `z.vs_memory`, `k`] >> simp[] >>
  irule abiDecodeStaticPropsTheory.mem_bytes_at_bytewise >>
  rpt strip_tac >> irule representationCleanPtrTheory.mem_bytes_at_eq_byte >>
  qexistsl_tac [`addr`, `capacity`] >> simp[] >> decide_tac
QED

Theorem structlit_list_admissible[local]:
  gas_admissible (eval_expr cx (StructLit ann nsid fs)) expr_vv_res_ok es ==>
  gas_admissible (eval_exprs cx (MAP SND fs))
    (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc)) es
Proof
  rewrite_tac[gas_admissible_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `res` >- simp[] >>
  drule aggregate_eval_struct >> disch_then (qspecl_then [`nsid`, `ann`] assume_tac) >>
  first_x_assum drule >> simp[expr_vv_res_ok_def, expr_res_ok_def]
QED

Theorem structlit_eval_exprs_cons[local]:
  eval_exprs cx (e::args) =
  bind (bind (eval_expr cx e) (read_result cx))
    (\v. bind (eval_exprs cx args) (\vs. return (v::vs)))
Proof
  simp[Once evaluate_def, bind_assoc]
QED

Theorem structlit_tail_admissible[local]:
  gas_admissible (eval_exprs cx (e::args))
    (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc)) es /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := marks ++ tail) = (INL v, mid with gas_obs := tail)) ==>
  gas_admissible (eval_exprs cx args)
    (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc))
    (mid with gas_obs := [])
Proof
  rewrite_tac[gas_admissible_gas_obs, gas_admissible_def] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `res` >- simp[] >>
  qpat_x_assum `!gs res ee. _` (qspec_then `marks ++ gs` mp_tac) >>
  simp[structlit_eval_exprs_cons, bind_def] >> metis_tac[]
QED

(* Keep the base run of the allocator with its chosen endpoint and ghosts. *)
Theorem structlit_alloc_init_full:
  compile_alloc_buffer n sa = (ba,sm) /\ fn_has_code sa sm func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  n < dimword(:256) /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q w t G tn raw.
    ba.buf_operand = Var q /\
    run_inst_seq (emitted_insts sa sm) s0 = OK raw /\
    t = raw with vs_inst_idx := LENGTH sm.cs_current_insts /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s0,G0,tn0) [] (OK t,G,tn)) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es t /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx es G tn t) /\
    wb_frame cenv es es sa s0 t /\ pure_frame cenv func es sa s0 t /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
    ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    not_fresh_at sm q /\ lookup_var q t = SOME w /\
    ptr_covers G tn q t n /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,n) /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [q]) (fn_insts func) /\
    lo <= w2n w /\ w2n w+n < dimword(:256) /\
    sa.cs_next_id < sm.cs_next_id /\ sa.cs_next_var <= sm.cs_next_var /\
    (!name p k. local_region cenv es.scopes t name p k ==>
      w2n w+n <= p \/ p+k <= w2n w) /\
    (!name p k. local_region cenv es.scopes s0 name p k ==>
      w2n w+n <= p \/ p+k <= w2n w) /\
    (!old p k. FLOOKUP s0.vs_allocas old = SOME (p,k) /\ old < sa.cs_next_id ==>
      w2n w+n <= p \/ p+k <= w2n w) /\
    t.vs_memory = s0.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s0 /\
      FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x))
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[storage_trace_domain_def] >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es s0 /\
   allocas_from lo s0 /\ lo <= s0.vs_alloca_next` by
    (qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
       (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
     simp[bodyPtrDefsTheory.ghost_inv_at_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s0` by
    (qpat_assum `stmt_state_rel _ ctx func cenv cx es s0`
       (mp_tac o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
     simp[]) >>
  drule_all (INST_TYPE [``:'b`` |-> ``:256``] alloc_buffer_origin_ptr_path_with_raw_endpoint) >>
  disch_then (qspecl_then [`tn0`, `explicit`, `PG`, `G0`] strip_assume_tac) >>
  qpat_x_assum `t = r with vs_inst_idx := _`
    (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def]) >>
  qpat_x_assum `G' = step_prov _ _ _ r` kall_tac >>
  qpat_x_assum `tn' = step_taint _ _ r _` kall_tac >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es t /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G' tn' t` by
    (rpt gen_tac >> strip_tac >>
     `stmt_state_rel H ctx func cenv cx es s0 /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0` by metis_tac[] >>
     conj_tac >- (qpat_x_assum `!hh. _ ==> stmt_state_rel hh _ _ _ _ _ t`
       (qspec_then `H` mp_tac) >> simp[]) >> conj_tac >- simp[] >>
     irule (INST_TYPE [``:'a`` |-> ``:256``] alloc_buffer_ghost_inv_at) >>
     rpt (first_assum (irule_at Any)) >> gvs[] >>
     qexists_tac `w2n w + n` >> simp[]) >>
  `t.vs_memory = s0.vs_memory /\ ~t.vs_halted` by
    (qpat_x_assum `t with <| vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _ |> = s0`
       mp_tac >> simp[venomStateTheory.venom_state_component_equality] >> metis_tac[]) >>
  `wb_frame cenv es es sa s0 t` by
    (simp[wb_frame_def, locals_kept_def, popped_kept_def,
          vyperEvalScopesProgressTheory.scopes_progress_refl] >> metis_tac[]) >>
  `pure_frame cenv func es sa s0 t` by simp[] >>
  `!aid b sz. FLOOKUP s0.vs_allocas aid = SOME (b,sz) ==>
     b + sz <= s0.vs_alloca_next` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _ s0` mp_tac >>
     pure_rewrite_tac [stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.alloca_next_valid_def] >> metis_tac[]) >>
  `!name b sz. local_region cenv es.scopes s0 name b sz ==>
     b + sz <= s0.vs_alloca_next` by
    (rpt strip_tac >> drule_all body_local_region_frontier >> simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'` by
    (irule (Q.INST [`G` |-> `G0`, `tn` |-> `tn0`, `s` |-> `s0`,
       `e` |-> `w2n (w:256 word) + n`] alloc_buffer_ghost_kept_at) >>
     simp[bodyPtrDefsTheory.ghost_kept_at_def] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (rpt strip_tac >>
       qpat_x_assum `!aid b sz. FLOOKUP s0.vs_allocas aid = _ ==> _` drule >> simp[]) >>
     qexistsl_tac [`n`, `w`] >> simp[]) >>
  `sa.cs_next_id < sm.cs_next_id /\ sa.cs_next_var <= sm.cs_next_var /\
   MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [q]) (fn_insts func)` by
    (drule_all exprSimAllocTheory.buffer_alloc_code >>
     drule compile_alloc_buffer_parts >> simp[] >> strip_tac >> gvs[]) >>
  `lo <= w2n w` by
    (qpat_x_assum `allocas_from lo t` mp_tac >>
     simp[ptrDisciplineTheory.allocas_from_def] >> disch_then drule >> simp[]) >>
  `!old p k. FLOOKUP s0.vs_allocas old = SOME (p,k) /\ old < sa.cs_next_id ==>
     w2n w+n <= p \/ p+k <= w2n w` by
    (rpt strip_tac >>
     qpat_x_assum `!aid b len. _ /\ _ ==> regions_disjoint _ _ _ _`
       drule_all >> simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  `!name p k. local_region cenv es.scopes t name p k ==>
     w2n w+n <= p \/ p+k <= w2n w` by
    (rpt strip_tac >>
     qpat_x_assum `!name b len. _ ==> regions_disjoint _ _ _ _`
       drule >> simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  `!name p k. local_region cenv es.scopes s0 name p k ==>
     w2n w+n <= p \/ p+k <= w2n w` by
    (rpt strip_tac >>
     `local_region cenv es.scopes t name p k` by
       (irule exprSimPropsTheory.local_region_frame_fwd >>
        qexistsl_tac [`s0`, `sa`, `es.scopes`] >> simp[] >> metis_tac[]) >>
     qpat_x_assum `!name p k. local_region _ _ t _ _ _ ==> _` drule >> simp[]) >>
  qexistsl_tac [`q`, `w`, `t`, `G'`, `tn'`, `r`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp[Abbr `t`] >>
  simp[] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem structlit_store_inv_step[local]:
  !inv'. inv' = (\H ee cs G tn s cells off.
    stmt_state_rel H ctx func ce cx ee s /\
    storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d ce cx ee G tn s /\
    wb_frame ce ees ee fr sf s /\ ghost_kept_at lo ce ees fr Gf tnf sf G tn /\
    MAP FDOM ees.scopes = MAP FDOM ee.scopes /\
    ~s.vs_halted /\ s.vs_current_bb = cs.cs_current_bb /\
    s.vs_inst_idx = LENGTH cs.cs_current_insts /\
    alloca_history func s /\ sf.vs_alloca_next <= s.vs_alloca_next /\
    not_fresh_at cs root /\ lookup_var root s = SOME (n2w addr) /\
    ptr_covers G tn root s capacity /\
    FLOOKUP s.vs_allocas aid = SOME (addr,capacity) /\
    MEM (mk_inst aid ALLOCA [Lit(n2w capacity)] [root]) (fn_insts func) /\
    lo <= addr /\ addr+capacity < dimword(:256) /\
    fr.cs_next_id <= aid /\ aid < cs.cs_next_id /\
    fr.cs_next_var <= cs.cs_next_var /\ off <= capacity /\
    (!name p k. local_region ce ee.scopes s name p k ==>
      addr+capacity <= p \/ p+k <= addr) /\
    (!name p k. local_region ce ees.scopes sf name p k ==>
      addr+capacity <= p \/ p+k <= addr) /\
    (!old p k. FLOOKUP sf.vs_allocas old = SOME(p,k) /\ old < fr.cs_next_id ==>
      addr+capacity <= p \/ p+k <= addr) /\
    EVERY (\(tv,v,p,k). addr <= p /\ p+k <= addr+off) cells /\
    literal_prefix_ok cells tn s /\
    (pure ==> pure_frame ce func ees fr sf s)) ==>
  inv' H ee su G tn z cells off /\ n = type_memory_size ftv /\
  val_wf ftv v /\ off+n <= capacity /\ ci_mono su ss /\
  local_ptrs_reserved ce su /\
  typed_copy_state_frame su (addr+off) n z u /\
  ~u.vs_halted /\ u.vs_current_bb = ss.cs_current_bb /\
  u.vs_inst_idx = LENGTH ss.cs_current_insts /\ alloca_history func u /\
  (!p. not_fresh_at su p ==> FLOOKUP G2 p = FLOOKUP G p /\
    op_taint tn2 (Var p) = op_taint tn (Var p)) /\
  tn2.t_imm = tn.t_imm /\ tn2.t_stor = tn.t_stor /\ tn2.t_trans = tn.t_trans /\
  (!i. ~(addr+off <= i /\ i < addr+off+n) ==>
    (i IN tn2.t_mem <=> i IN tn.t_mem)) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x) /\
  (!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at su x) /\
  (!m. mem_agree_outside tn2.t_mem u.vs_memory m ==>
    val_in_memory ftv v (addr+off) m) ==>
  inv' H ee ss G2 tn2 u (cells ++ [(ftv,v,addr+off,n)]) (off+n)
Proof
  gen_tac >> disch_then SUBST1_TAC >> BETA_TAC >> strip_tac >>
  `u.vs_allocas = z.vs_allocas /\ u.vs_alloca_next = z.vs_alloca_next` by
    gvs[typedMemoryCopyTheory.typed_copy_state_frame_def,
        venomStateTheory.venom_state_component_equality] >>
  `!p. not_fresh_at su p ==> lookup_var p u = lookup_var p z` by
    gvs[typedMemoryCopyTheory.typed_copy_state_frame_def] >>
  `!p k. k+p <= addr+off \/ addr+off+n <= p ==>
    mem_bytes_at p k u.vs_memory = mem_bytes_at p k z.vs_memory` by
    (gvs[typedMemoryCopyTheory.typed_copy_state_frame_def,
        typedMemoryCopyTheory.typed_copy_frame_def] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `stmt_state_rel H ctx func ce cx ee u /\ literal_prefix_ok cells tn2 u` by
    (irule structlit_store_state_prefix_frame >>
     qexistsl_tac [`addr`, `aid`, `capacity`, `n`, `off`, `root`, `z`, `su`, `tn`] >>
     simp[] >> conj_tac >- metis_tac[loweringStateRelDefsTheory.regions_disjoint_def] >>
     gvs[EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]) >>
  `!name entry p sz w. lookup_scopes name ee.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) /\ lookup_var p z = SOME w ==>
    val_wf entry.type entry.value /\
    (w2n w + val_footprint entry.type entry.value <= addr+off \/
     addr+off+n <= w2n w)` by
    (rpt gen_tac >> strip_tac >>
     `local_ptrs_rel func ce ee.scopes z` by fs[stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def] >>
     `val_wf entry.type entry.value /\ type_memory_size entry.type <= sz` by
       (fs[loweringStateRelDefsTheory.local_ptrs_rel_def] >> metis_tac[optionTheory.SOME_11]) >>
     `local_region ce ee.scopes z name (w2n w) sz` by
       (simp[loweringStateRelDefsTheory.local_region_def] >> metis_tac[]) >>
     `addr+capacity <= w2n w \/ w2n w+sz <= addr` by metis_tac[] >>
     drule exprSimPropsTheory.val_footprint_le >> strip_tac >> simp[] >> decide_tac) >>
  `ghost_inv_at (DF H) lo d ce cx ee G2 tn2 u /\
   ghost_kept_at lo ce ees fr Gf tnf sf G2 tn2` by
    (irule structlit_store_ghost_frame >>
     qexistsl_tac [`addr+off`, `G`, `n`, `su`, `z`, `tn`] >>
     simp[] >> conj_tac
     >- (rpt gen_tac >> strip_tac >>
         qpat_x_assum `!name p k. local_region ce ees.scopes sf name p k ==> _`
           drule >> decide_tac) >>
     conj_tac
     >- (rpt gen_tac >> strip_tac >>
         qpat_x_assum `!name entry p sz w. _ ==> val_wf _ _ /\ _`
           drule_all >> strip_tac >> simp[] >> decide_tac) >>
     rpt gen_tac >> strip_tac >>
     qpat_x_assum `!old p k. FLOOKUP sf.vs_allocas old = _ /\ _ ==> addr+capacity <= p \/ p+k <= addr`
       drule_all >> decide_tac) >>
  `!name p k. local_region ce ee.scopes u name p k ==>
     addr+capacity <= p \/ p+k <= addr` by
    (rpt strip_tac >>
     `local_region ce ee.scopes z name p k` by
       (drule_all exprSimCopyTheory.copy_buffer_local_region_frame >> metis_tac[]) >>
     metis_tac[]) >>
  `!x. not_fresh_at fr x ==> lookup_var x u = lookup_var x z` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!name p k. local_region ce ees.scopes sf name p k ==>
    mem_bytes_at p k u.vs_memory = mem_bytes_at p k z.vs_memory` by
    (rpt strip_tac >>
     qpat_x_assum `!name p k. local_region ce ees.scopes sf name p k ==> _`
       drule >> strip_tac >> first_x_assum irule >> decide_tac) >>
  `locals_kept ce ees ee sf u` by
    (irule exprSimPropsTheory.locals_kept_regions_tail >>
     qexists_tac `z` >> fs[wb_frame_def] >> metis_tac[]) >>
  `wb_frame ce ees ee fr sf u` by
    (qpat_x_assum `wb_frame ce ees ee fr sf z` mp_tac >>
     pure_rewrite_tac[wb_frame_def] >> strip_tac >> simp[] >>
     rpt gen_tac >> strip_tac >> rename1 `FLOOKUP sf.vs_allocas old = SOME (p,k)` >>
     `mem_bytes_at p k u.vs_memory = mem_bytes_at p k z.vs_memory` by
       (qpat_x_assum `!p k. _ ==> mem_bytes_at p k u.vs_memory = _` irule >>
        qpat_x_assum `!old p k. FLOOKUP sf.vs_allocas old = _ /\ _ ==> addr+capacity <= p \/ p+k <= addr`
          drule_all >> decide_tac) >> metis_tac[]) >>
  `(pure ==> pure_frame ce func ees fr sf u)` by
    (strip_tac >> irule exprSimPropsTheory.pure_frame_buffer_tail >>
     qexistsl_tac [`addr`, `capacity`, `mk_inst aid ALLOCA [Lit(n2w capacity)] [root]`, `z`] >>
     simp[] >> conj_tac
     >- metis_tac[loweringStateRelDefsTheory.regions_disjoint_def] >>
     conj_tac
     >- (rpt gen_tac >> strip_tac >>
         qpat_x_assum `!p k. _ ==> mem_bytes_at p k u.vs_memory = _` irule >>
         gvs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
     simp[venomInstTheory.mk_inst_def]) >>
  `literal_prefix_ok (cells ++ [(ftv,v,addr+off,n)]) tn2 u` by
    (simp[bodyPtrMakeArrayMemoryFrameTheory.literal_prefix_cell] >> metis_tac[exprSimPropsTheory.val_footprint_le]) >>
  `ptr_covers G2 tn2 root u capacity` by
    (gvs[bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[]) >>
  `su.cs_next_var <= ss.cs_next_var /\ su.cs_next_id <= ss.cs_next_id` by
    fs[exprLoweringPropsTheory.ci_mono_def] >>
  `not_fresh_at ss root` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  simp[arithmeticTheory.ADD_COMM] >>
  conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
  conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
  conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
  gvs[EVERY_MEM, pairTheory.FORALL_PROD] >> rpt strip_tac >>
  qpat_x_assum `!a b p k. MEM (a,b,p,k) cells ==> _` drule >>
  strip_tac >> simp[] >> decide_tac
QED

Theorem structlit_fields_cons_continuation[local]:
  !inv'. inv' = (\H ee cs G tn s cells off.
    stmt_state_rel H ctx func ce cx ee s /\
    storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d ce cx ee G tn s /\
    wb_frame ce ees ee fr sf s /\ ghost_kept_at lo ce ees fr Gf tnf sf G tn /\
    MAP FDOM ees.scopes = MAP FDOM ee.scopes /\
    ~s.vs_halted /\ s.vs_current_bb = cs.cs_current_bb /\
    s.vs_inst_idx = LENGTH cs.cs_current_insts /\
    alloca_history func s /\ sf.vs_alloca_next <= s.vs_alloca_next /\
    not_fresh_at cs root /\ lookup_var root s = SOME (n2w addr) /\
    ptr_covers G tn root s capacity /\
    FLOOKUP s.vs_allocas aid = SOME (addr,capacity) /\
    MEM (mk_inst aid ALLOCA [Lit(n2w capacity)] [root]) (fn_insts func) /\
    lo <= addr /\ addr+capacity < dimword(:256) /\
    fr.cs_next_id <= aid /\ aid < cs.cs_next_id /\
    fr.cs_next_var <= cs.cs_next_var /\ off <= capacity /\
    (!name p k. local_region ce ee.scopes s name p k ==>
      addr+capacity <= p \/ p+k <= addr) /\
    (!name p k. local_region ce ees.scopes sf name p k ==>
      addr+capacity <= p \/ p+k <= addr) /\
    (!old p k. FLOOKUP sf.vs_allocas old = SOME(p,k) /\ old < fr.cs_next_id ==>
      addr+capacity <= p \/ p+k <= addr) /\
    EVERY (\(tv,v,p,k). addr <= p /\ p+k <= addr+off) cells /\
    literal_prefix_ok cells tn s /\
    (pure ==> pure_frame ce func ees fr sf s)) ==>
  read_result cx tv mid = (INL v,mid) /\ value_has_type ftv v /\
  mid.gas_obs = [] /\ ~t.vs_halted /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (t,G1,tn1) [] (OK u,G2,tn2)) /\
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (eval_exprs cx (MAP SND fs)) (mid,u,G2,tn2)
    (\H res ee G tn z. ?vs added. res = INL vs /\ expr_sim_inv ce cx env ee /\
      LIST_REL value_has_type tvs vs /\
      inv' H ee sb G tn z
        ((cells++[(ftv,v,addr+off,type_memory_size ftv)])++added)
        ((off+type_memory_size ftv)+type_memory_size_list tvs) /\
      (!m. mem_agree_outside tn.t_mem z.vs_memory m ==>
        fields_in_memory (ZIP(MAP FST fs,vs)) (ZIP(MAP FST fs,tvs))
          (addr+(off+type_memory_size ftv)) m))
    (\H res ee gt r. ?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) r /\
      halt_exit H cx ee (INR exc : eval_result + exception) r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (bind (read_result cx tv) (\v. bind (eval_exprs cx (MAP SND fs))
      (\vs. return (v::vs)))) (mid,t,G1,tn1)
    (\H res ee G tn z. ?vs added. res = INL vs /\ expr_sim_inv ce cx env ee /\
      LIST_REL value_has_type (ftv::tvs) vs /\
      inv' H ee sb G tn z (cells++added) (off+type_memory_size_list (ftv::tvs)) /\
      (!m. mem_agree_outside tn.t_mem z.vs_memory m ==>
        fields_in_memory (ZIP(fname::MAP FST fs,vs))
          (ZIP(fname::MAP FST fs,ftv::tvs)) (addr+off) m))
    (\H res ee gt r. ?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) r /\
      halt_exit H cx ee (INR exc : eval_result + exception) r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  gen_tac >> disch_then (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def]) >>
  strip_tac >> irule gas_outcome_full_bind >>
  rpt conj_tac
  >~ [`storage_trace_frame (read_result _ _)`]
  >- simp[storage_trace_frame_read_result]
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
      qexistsl_tac [`mid'`, `t'`, `v'`] >> fs[])
  >- (gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_return])
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >> simp[]) >>
  irule gas_outcome_full_pure >> simp[] >>
  qexistsl_tac [`G2`, `mid`, `INL v`, `u`, `tn2`] >>
  conj_tac >- metis_tac[exprSimMemorySourceTheory.read_result_gas_obs] >>
  rpt gen_tac >> strip_tac >> simp[] >>
  `mid with gas_obs := [] = mid` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  simp[] >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _`
    (mp_then Any (qspecl_then
      [`bind (eval_exprs cx (MAP SND fs)) (\vs. return (v::vs))`,
       `\res. case res of INL vs => INL (v::vs) | INR ex => INR ex`]
      mp_tac) gas_outcome_full_source_map) >>
  (impl_tac >-
    (simp[bind_def, return_def] >> gen_tac >>
     Cases_on `eval_exprs cx (MAP SND fs) es` >>
     rename1 `eval_exprs cx (MAP SND fs) es = (rr,ee)` >>
     Cases_on `rr` >> simp[])) >>
  disch_then (mp_then Any irule gasOutcomeFullTheory.gas_outcome_full_post_mono) >>
  BETA_TAC >> reverse conj_tac >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  qexists_tac `[(ftv,v,addr+off,type_memory_size ftv)] ++ added` >>
  conj_tac >- gvs[typeLayoutPropsTheory.type_memory_size_list_sum, APPEND_ASSOC] >>
  `literal_prefix_ok
     (cells ++ [(ftv,v,addr+off,type_memory_size ftv)] ++ added) tn' t'` by
    fs[Abbr `inv'`] >>
  `!m. mem_agree_outside tn'.t_mem t'.vs_memory m ==>
      val_in_memory ftv v (addr+off) m` by
    (rpt strip_tac >>
     irule (cj 3 bodyPtrMakeArrayMemoryFrameTheory.literal_prefix_lookup) >>
     qexistsl_tac [`cells ++ [(ftv,v,addr+off,type_memory_size ftv)] ++ added`,
                    `type_memory_size ftv`, `t'`, `tn'`] >> simp[]) >>
  rpt strip_tac >>
  pure_once_rewrite_tac[valueEncodingDefsTheory.val_in_memory_def] >>
  simp[GSYM arithmeticTheory.ADD_ASSOC]
QED

Theorem structlit_fields_bundled_full[local]:
  !inv'. inv' = (\H ee cs G tn s cells off.
    stmt_state_rel H ctx func ce cx ee s /\
    storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d ce cx ee G tn s /\
    wb_frame ce ees ee fr sf s /\ ghost_kept_at lo ce ees fr Gf tnf sf G tn /\
    MAP FDOM ees.scopes = MAP FDOM ee.scopes /\
    ~s.vs_halted /\ expr_sim_full_endpoint func cs sf s /\
    not_fresh_at cs root /\ lookup_var root s = SOME (n2w addr) /\
    ptr_covers G tn root s capacity /\
    FLOOKUP s.vs_allocas aid = SOME (addr,capacity) /\
    MEM (mk_inst aid ALLOCA [Lit(n2w capacity)] [root]) (fn_insts func) /\
    lo <= addr /\ addr+capacity < dimword(:256) /\
    fr.cs_next_id <= aid /\ aid < cs.cs_next_id /\
    fr.cs_next_var <= cs.cs_next_var /\ off <= capacity /\
    (!name p k. local_region ce ee.scopes s name p k ==>
      addr+capacity <= p \/ p+k <= addr) /\
    (!name p k. local_region ce ees.scopes sf name p k ==>
      addr+capacity <= p \/ p+k <= addr) /\
    (!old p k. FLOOKUP sf.vs_allocas old = SOME(p,k) /\ old < fr.cs_next_id ==>
      addr+capacity <= p \/ p+k <= addr) /\
    EVERY (\(tv,v,p,k). addr <= p /\ p+k <= addr+off) cells /\
    literal_prefix_ok cells tn s /\
    (pure ==> pure_frame ce func ees fr sf s)) ==>
  !fs tys tvs es si sb shadow_si shadow_sb s0 G0 tn0 cells off out.
    compile_struct_lit compile_expr ce (StructT nsid) fs (Var root) off si = (out,sb) /\
    compile_struct_lit compile_expr (gas_shadow_env T ce) (StructT nsid)
      (MAP (I ## gas_shadow_expr) fs) (Var root) off shadow_si = (out,shadow_sb) /\
    expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (si,sb,shadow_si,shadow_sb) /\
    body_const_cells_agree [(NONE,cx_tops cx)] cx env es /\
    body_inv (cx_tops cx) ctx ce cx /\
    shadow_body_inv (cx_tops cx) ctx shadow_ctx /\
    body_exprs_full_ok cx (MAP SND fs) /\
    (?Hbase. stmt_state_rel Hbase ctx func ce cx ees sf) /\
    LIST_REL (\t (name,e). ALOOKUP
      (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)) name =
      SOME(t,type_memory_bytes ce t)) tys fs /\
    LIST_REL (\t e. arg_type_fits (expr_type e) t) tys (MAP SND fs) /\
    OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
    local_ptrs_reserved ce si /\ local_ptrs_reserved ce fr /\
    (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
    (!H. dead_lo_ok H (DF H) lo ce cx) /\
    (!x sz. ce.ce_return_buf = SOME(PtrVar(Var x) sz) ==> not_fresh_at si x) /\
    (!x sz. ce.ce_return_pc = SOME(PtrVar(Var x) sz) ==> not_fresh_at si x) /\
    return_buf_frame d ce si s0 /\
    (!e st. MEM e (MAP SND fs) /\ expr_sim_inv ce cx env st ==>
      expr_body_pre ce cx env e st) /\
    (pure ==> ~EXISTS expr_has_effect (MAP SND fs)) /\ expr_sim_inv ce cx env es /\
    storage_trace_domain cx st0 es.storage_trace /\
    off + type_memory_size_list tvs <= capacity /\
    gas_admissible (eval_exprs cx (MAP SND fs))
      (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc)) es /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      inv' H es si G0 tn0 s0 cells off) ==>
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (eval_exprs cx (MAP SND fs)) (es,s0,G0,tn0)
      (\H res ee G tn z. ?vs added. res = INL vs /\ expr_sim_inv ce cx env ee /\
        LIST_REL value_has_type tvs vs /\
        inv' H ee sb G tn z (cells++added) (off+type_memory_size_list tvs) /\
        (!m. mem_agree_outside tn.t_mem z.vs_memory m ==>
          fields_in_memory (ZIP(MAP FST fs,vs)) (ZIP(MAP FST fs,tvs)) (addr+off) m))
      (\H res ee gt r. ?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) r /\
      halt_exit H cx ee (INR exc : eval_result + exception) r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  PURE_REWRITE_TAC [expr_sim_full_endpoint_def, GSYM CONJ_ASSOC] >>
  gen_tac >>
  disch_then (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def]) >>
  Induct
  >- (simp_tac bool_ss [expr_sim_full_code_def] >> rpt strip_tac >>
      gvs[exprLoweringTheory.compile_struct_lit_def, comp_return_def] >>
      `~s0.vs_halted` by
        (`valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
           fs[storage_trace_domain_def] >>
         qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
           (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
         simp[Abbr `inv'`]) >>
      irule gas_outcome_full_pure >> reverse conj_tac >- simp[] >>
      qexistsl_tac [`G0`, `es`, `INL []`, `s0`, `tn0`] >>
      conj_tac >- simp[Once vyperInterpreterTheory.evaluate_def, return_def] >>
      rpt gen_tac >> strip_tac >>
      conj_tac >- metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_rules] >>
      BETA_TAC >>
      qexists_tac `[]` >> simp[valueEncodingTheory.type_memory_size_def] >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` drule >>
      simp[Abbr `inv'`, valueEncodingDefsTheory.val_in_memory_def,
           stmt_state_rel_start_gas_obs] >> strip_tac >>
      `!b. get_storage cx (es with gas_obs := []) b = get_storage cx es b` by
        (Cases >> simp[vyperStorageBackendTheory.get_storage_def]) >>
      gvs[storage_well_formed_on_def, bodyPtrDefsTheory.ghost_inv_at_def,
          wb_frame_def, locals_kept_def, popped_kept_def] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> simp_tac bool_ss [expr_sim_full_code_def] >> rpt disch_tac >>
  PairCases_on `h` >> Cases_on `tys` >>
  gvs[LIST_REL_CONS1] >>
  rename1 `ALOOKUP _ fname = SOME (fty,type_memory_bytes ce fty)` >>
  rename1 `arg_type_fits (expr_type e) fty` >>
  rename1 `evaluate_type (get_tenv cx) fty = SOME ftv` >>
  rename1 `OPT_MMAP (evaluate_type (get_tenv cx)) rest_tys = SOME rest_tvs` >>
  Cases_on `compile_expr ce (expr_type e) e si` >>
  rename1 `compile_expr ce (expr_type e) e si = (vv,sm)` >>
  Cases_on `emit_op ADD [Var root; Lit(n2w off)] sm` >>
  rename1 `emit_op ADD _ sm = (dst,sn)` >>
  Cases_on `unwrap_value ce vv sn` >>
  rename1 `unwrap_value ce vv sn = (op,su)` >>
  Cases_on `compile_store_memory ce op dst fty (lowered_value_type ce e) su` >>
  rename1 `compile_store_memory ce op dst fty (lowered_value_type ce e) su = (uu,ss)` >>
  qpat_x_assum `compile_struct_lit _ _ _ ((fname,e)::_) _ _ _ = _` mp_tac >>
  simp[Once exprLoweringTheory.compile_struct_lit_def, comp_ignore_bind_def, comp_bind_def] >> strip_tac >>
  `?shadow_sm. compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e)
      shadow_si = (vv,shadow_sm) /\ gas_shadow_state sm shadow_sm` by
    (mp_tac (cj 1 gas_shadow_compile_expr_env |> Q.INST [`sd` |-> `T`] |>
       Q.SPECL [`ce`, `expr_type e`, `e`, `T`]) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     qpat_x_assum `gas_shadow_state sb shadow_sb` kall_tac >>
     disch_then drule >> simp[] >>
     Cases_on `compile_expr (gas_shadow_env T ce) (expr_type e)
       (gas_shadow_expr e) shadow_si` >> simp[]) >>
  `?shadow_sn. emit_op ADD [Var root; Lit(n2w off)] shadow_sm =
      (dst,shadow_sn) /\ gas_shadow_state sn shadow_sn` by
    (mp_tac (gasShadowCompileContextTheory.gas_shadow_compiles_emit_op_same |>
       Q.INST [`opc` |-> `ADD`, `ops` |-> `[Var root; Lit(n2w off)]`] |>
       REWRITE_RULE [gasShadowStateTheory.gas_shadow_compiles_def]) >>
     disch_then (qspecl_then [`sm`, `shadow_sm`] mp_tac) >> simp[] >>
     Cases_on `emit_op ADD [Var root; Lit(n2w off)] shadow_sm` >> gvs[]) >>
  `?shadow_su. unwrap_value ce vv shadow_sn = (op,shadow_su) /\
      gas_shadow_state su shadow_su` by
    (mp_tac (gasShadowCompileConvertTheory.gas_shadow_compiles_unwrap_value |>
       Q.INST [`cenv` |-> `ce`, `vv` |-> `vv`] |>
       REWRITE_RULE [gasShadowStateTheory.gas_shadow_compiles_def]) >>
     disch_then (qspecl_then [`sn`, `shadow_sn`] mp_tac) >> simp[] >>
     Cases_on `unwrap_value ce vv shadow_sn` >> gvs[]) >>
  `?shadow_ss. compile_store_memory ce op dst fty (lowered_value_type ce e) shadow_su =
      (uu,shadow_ss) /\ gas_shadow_state ss shadow_ss` by
    (mp_tac (gasShadowCompileContextTheory.gas_shadow_compiles_store_memory |>
       Q.INST [`cenv` |-> `ce`, `src` |-> `op`, `dst` |-> `dst`,
         `dst_ty` |-> `fty`, `src_ty` |-> `lowered_value_type ce e`] |>
       REWRITE_RULE [gasShadowStateTheory.gas_shadow_compiles_def]) >>
     disch_then (qspecl_then [`su`, `shadow_su`] mp_tac) >> simp[] >>
     Cases_on `compile_store_memory ce op dst fty (lowered_value_type ce e) shadow_su` >> gvs[]) >>
  qpat_x_assum `compile_struct_lit _ _ _ ((fname,gas_shadow_expr e)::_) _ _ _ = _` mp_tac >>
  simp[Once exprLoweringTheory.compile_struct_lit_def, comp_ignore_bind_def,
       comp_bind_def, gasShadowTheory.gas_shadow_expr_type] >> strip_tac >>
  `cs_extends si sm /\ cs_extends sm sn /\ cs_extends sn su /\
   cs_extends su ss /\ cs_extends ss sb` by
    (imp_res_tac compile_expr_extends >> imp_res_tac unwrap_value_extends >>
     mp_tac (Q.SPECL [`ADD`, `[Var root; Lit(n2w off)]`, `sm`] ci_mono_emit_op) >>
     mp_tac (Q.SPECL [`ce`, `op`, `dst`, `fty`, `lowered_value_type ce e`, `su`]
       ci_mono_compile_store_memory) >>
     mp_tac (Q.SPECL [`compile_expr`, `ce`, `StructT nsid`, `fs`, `Var root`,
       `off + type_memory_bytes ce fty`, `ss`] ci_mono_compile_struct_lit_cfn) >>
     simp[ci_mono_def] >>
     (impl_tac >- (rpt gen_tac >> Cases_on `compile_expr cenv' ty' e' sa'` >>
       drule (cj 1 compile_expr_grows) >> simp[])) >> simp[]) >>
  `cs_extends shadow_si shadow_sm /\ cs_extends shadow_sm shadow_sn /\
   cs_extends shadow_sn shadow_su /\ cs_extends shadow_su shadow_ss /\
   cs_extends shadow_ss shadow_sb` by
    (imp_res_tac compile_expr_extends >> imp_res_tac unwrap_value_extends >>
     mp_tac (Q.SPECL [`ADD`, `[Var root; Lit(n2w off)]`, `shadow_sm`] ci_mono_emit_op) >>
     mp_tac (Q.SPECL [`ce`, `op`, `dst`, `fty`, `lowered_value_type ce e`, `shadow_su`]
       ci_mono_compile_store_memory) >>
     mp_tac (Q.SPECL [`compile_expr`, `gas_shadow_env T ce`, `StructT nsid`,
       `MAP (I ## gas_shadow_expr) fs`, `Var root`,
       `off + type_memory_bytes ce fty`, `shadow_ss`] ci_mono_compile_struct_lit_cfn) >>
     simp[ci_mono_def] >>
     (impl_tac >- (rpt gen_tac >> Cases_on `compile_expr cenv' ty' e' sa'` >>
       drule (cj 1 compile_expr_grows) >> simp[])) >> simp[]) >>
  `fn_has_code si sm func /\ fn_has_code sm sn func /\
   fn_has_code sn su func /\ fn_has_code su ss func /\ fn_has_code ss sb func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `fn_has_code shadow_si shadow_sm shadow_func /\
   fn_has_code shadow_sm shadow_sn shadow_func /\
   fn_has_code shadow_sn shadow_su shadow_func /\
   fn_has_code shadow_su shadow_ss shadow_func /\
   fn_has_code shadow_ss shadow_sb shadow_func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `expr_body_pre ce cx env e es` by metis_tac[] >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[expr_body_pre_vv_gas_admissible] >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      ce cx (expr_type e) e es` by
    (gvs[body_exprs_full_ok_def, body_expr_full_ok_def] >> metis_tac[]) >>
  `inv' (storage_trace_horizon es.storage_trace) es si G0 tn0 s0 cells off` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> inv' _ _ _ _ _ _ _ _`
       (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
     gvs[storage_trace_domain_def]) >>
  `alloca_history func s0` by gvs[Abbr `inv'`] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s0` by
    (qpat_assum `Abbrev (inv' = _)` (fn eq =>
       qpat_assum `inv' _ es si G0 tn0 s0 cells off`
         (mp_tac o REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] eq])) >>
     BETA_TAC >> disch_then (ACCEPT_TAC o MATCH_MP
       bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp o CONJUNCT1)) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (qpat_assum `body_inv (cx_tops cx) ctx ce cx` (fn inv =>
       qpat_assum `MEM func ctx.ctx_functions` (fn member =>
         ACCEPT_TAC (MATCH_MP bodyFullIfExpReachTheory.body_inv_no_phi (CONJ inv member))))) >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ e _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_full_def]) >>
  disch_then (qspecl_then [`st0`, `si`, `sm`, `shadow_si`, `shadow_sm`,
                          `vv`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> gvs[Abbr `inv'`] >> metis_tac[])) >> strip_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  rewrite_tac[structlit_eval_exprs_cons, bind_assoc] >>
  irule gas_outcome_full_bind_all_path >>
  rpt conj_tac
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_result >>
      qexistsl_tac [`mid`, `t`, `v`] >> fs[])
  >- (gen_tac >> simp[] >> irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_read_result] >> gen_tac >>
      irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_return])
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_result >> simp[]) >>
  qexists_tac `\H res ee G tn t. childQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >>
      first_assum (irule_at Any) >> simp[Abbr `childR`] >>
      rpt gen_tac >> Cases_on `res` >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `childQ (storage_trace_horizon mid.storage_trace) res mid G1 tn1 t /\
   ~t.vs_halted /\ mid.gas_obs = []` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ H res mid G1 tn1 t`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     gvs[storage_trace_domain_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  `gas_origin_ptr_path (DF (storage_trace_horizon mid.storage_trace),lo,
      gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s0,G0,tn0) marks (OK t,G1,tn1)` by
    (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
         gas_origin_ptr_path _ (s0,G0,tn0) marks (OK t,G1,tn1)` drule >> simp[]) >>
  `!fn inst s. frag_reachable ctx func t fn inst s ==> dalloca_fmp_headroom inst s` by
    (qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) marks (OK t,G1,tn1)` (fn path =>
       qpat_assum `!bb. MEM bb func.fn_blocks ==> _` (fn no_phi =>
       qpat_assum `!fn inst s. frag_reachable ctx func s0 fn inst s ==> _` (fn safe =>
         ACCEPT_TAC (MATCH_MP bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom
           (LIST_CONJ [path,no_phi,safe])))))) >>
  qpat_assum `Abbrev (childQ = _)` (fn eq =>
    qpat_x_assum `childQ _ _ _ _ _ _`
      (mp_tac o REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] eq])) >>
  BETA_TAC >> strip_tac >> gvs[] >>
  `not_fresh_at si root /\ lookup_var root s0 = SOME (n2w addr) /\
   ptr_covers G0 tn0 root s0 capacity /\ addr + capacity < dimword(:256) /\
   off <= capacity` by
    (qpat_assum `inv' _ es si G0 tn0 s0 cells off` mp_tac >>
     simp[Abbr `inv'`, NoAsms] >> strip_tac >> simp[]) >>
  `lookup_var root t = SOME (n2w addr) /\ ~t.vs_halted` by
    (conj_tac >-
       (qpat_assum `vv_post _ _ _ _ _ e _ _ _ _ _ _ vv t`
          (strip_assume_tac o PURE_REWRITE_RULE [vv_post_def]) >>
        first_x_assum (qspecl_then [`root`, `n2w addr`] mp_tac) >> simp[]) >>
     first_assum ACCEPT_TAC) >>
  `op_taint tn1 (Var root) = {} /\
   ?region_base cap. FLOOKUP G1 root = SOME (region_base,cap) /\
     region_base <= w2n (n2w addr : bytes32) /\
     w2n (n2w addr : bytes32) + capacity <= region_base + cap` by
    (fs[ghost_kept_at_def, ptr_covers_def] >> gvs[]) >>
  `ptr_covers G1 tn1 root t capacity` by
    (simp[ptr_covers_def] >> gvs[]) >>
  `si.cs_next_var <= sm.cs_next_var` by
    (qspec_then `ce` mp_tac (CONJUNCT1 compile_expr_ci_mono) >>
     disch_then (qspecl_then [`expr_type e`, `e`, `si`] mp_tac) >>
     simp[ci_mono_def]) >>
  `!p. vv_operand vv = Var p ==> not_fresh_at sm p` by
    metis_tac[exprOperandVarTheory.compiler_compile_var] >>
  `alloca_inv t` by fs[vv_post_def, stmt_state_rel_def] >>
  `w2n (n2w addr : bytes32) + off < dimword(:256) /\
   off + type_memory_size ftv <= capacity` by
    (gvs[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
  drule_all emit_op_fetch_boundary >> strip_tac >> gvs[] >>
  `w2n (n2w addr : bytes32) + off < dimword(:256)` by
    (simp[] >> decide_tac) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by simp[] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       vv_post H ctx func ce cx e es si sm s0 mid tv vv t /\
       ghost_inv_at (DF H) lo d ce cx mid G1 tn1 t` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ H (INL tv) mid G1 tn1 t`
       (drule_then mp_tac) >>
     simp[Abbr `childQ`, NoAsms]) >>
  drule_all (structlit_child_add_full |> Q.INST
    [`n` |-> `type_memory_size ftv`, `sm` |-> `sm`, `sn` |-> `sn`]) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `t'.vs_labels = t.vs_labels` by
    (qpat_assum `!D lo' explicit. allocas_from lo' t ==> _`
       (qspecl_then [`DF (storage_trace_horizon mid.storage_trace)`, `0`,
                     `gas_explicit_sites ctx shadow_ctx`] mp_tac) >>
     (impl_tac >- simp[ptrDisciplineTheory.allocas_from_def]) >>
     disch_then (mp_then Any mp_tac
       (cj 2 fragGasOriginPtrTheory.gas_origin_ptr_path_projections)) >>
     disch_then (mp_then Any mp_tac fragGasPathPtrTheory.gas_path_ptr_erase) >>
     disch_then (mp_then Any mp_tac fragGasPathTheory.gas_path_labels) >> simp[]) >>
  `eval_operand (vv_operand vv) t' = eval_operand (vv_operand vv) t` by
    (irule structlit_operand_frame >> simp[] >> metis_tac[]) >>
  `expr_body_pre ce cx env e es` by metis_tac[] >>
  `si.cs_next_id <= sm.cs_next_id` by
    (qspec_then `ce` mp_tac (CONJUNCT1 compile_expr_ci_mono) >>
     disch_then (qspecl_then [`expr_type e`, `e`, `si`] mp_tac) >>
     simp[ci_mono_def]) >>
  `sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id` by
    (mp_tac (Q.SPECL [`ADD`, `[Var root; Lit(n2w off)]`, `sm`] ci_mono_emit_op) >>
     simp[ci_mono_def]) >>
  `local_ptrs_reserved ce sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL tv,mid)` by
    (`mid with gas_obs := [] = mid` by
       (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
     qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` mp_tac) >>
     pure_rewrite_tac[APPEND_NIL] >> asm_rewrite_tac[]) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >> simp[]) >>
  drule_all post_type_evaluates >> strip_tac >>
  drule aggregateEvaluatedLayoutTheory.body_post_type_allocation_bound >> disch_tac >>
  `!v. read_result cx tv mid = (INL v,mid) ==> value_has_type tv' v` by
    (rpt strip_tac >>
     `expr_body_pre ce cx env e
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
     `bind (eval_expr cx e) (read_result cx)
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,mid)` by
       simp[bind_def] >>
     `value_runtime_typed env (post_value_type ce e) v` by
       (irule memory_rhs_read_post_typed >>
        qexistsl_tac [`cx`, `es with gas_obs := gas_explicit marks s0.vs_gas_readings`, `mid`] >>
        simp[bind_def]) >>
     qpat_x_assum `value_runtime_typed _ _ _` mp_tac >>
     pure_rewrite_tac[vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
     `env.type_defs = get_tenv cx` by
       (qpat_assum `expr_sim_inv ce cx env es` mp_tac >>
        pure_rewrite_tac[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
          vyperTypeInvariantsTheory.env_context_consistent_def] >>
        strip_tac >> first_assum ACCEPT_TAC) >>
     simp[]) >>
  qpat_assum `compile_expr ce (expr_type e) e si = (vv,sm)`
    (mp_then Any mp_tac bodyFullUnwrapTheory.unwrap_value_origin_ptr) >>
  disch_then (fn th => qpat_assum `unwrap_value ce vv sn = (op,su)`
    (mp_then (Pat `unwrap_value _ _ _ = _`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `vv_store_bound _ _ _ mid tv vv t'`
    (mp_then (Pat `vv_store_bound _ _ _ _ _ _ _`) mp_tac th)) >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `storage_trace_domain _ _ _`)) >>
  disch_then (fn th => qpat_assum `evaluate_type _ (post_value_type ce e) = SOME tv'`
    (mp_then (Pat `evaluate_type _ _ = SOME _`) mp_tac th)) >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`, `d`, `ctx`, `PG`, `DF`] mp_tac) >>
  (impl_tac >- (simp[] >> strip_tac >>
    qpat_assum `ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==> _` mp_tac >>
    (impl_tac >- simp[]) >> strip_tac >> qexists_tac `val` >> simp[] >>
    metis_tac[])) >> strip_tac >>
  `expr_post (storage_trace_horizon mid.storage_trace) ctx func ce cx e es si su s0 mid v op z /\
   ghost_inv_at (DF (storage_trace_horizon mid.storage_trace)) lo d ce cx mid G'' tn'' z` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     gvs[storage_trace_domain_def]) >>
  `bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,mid)` by
    simp[bind_def] >>
  `not_fresh_at sn (STRING #"%" (toString sm.cs_next_var))` by
    (qpat_assum `emit_op ADD _ sm = _` mp_tac >>
     disch_then (mp_then Any strip_assume_tac emitHelperPropsTheory.emitted_insts_emit_op) >>
     gvs[] >> simp[loweringStateRelDefsTheory.not_fresh_at_def, ASCIInumbersTheory.toString_inj]) >>
  `lookup_var (STRING #"%" (toString sm.cs_next_var)) z = SOME (n2w (addr+off)) /\
   ptr_covers G'' tn'' (STRING #"%" (toString sm.cs_next_var)) z (type_memory_size ftv)` by
    (qpat_assum `!x. not_fresh_at sn x ==> _`
       (qspec_then `STRING #"%" (toString sm.cs_next_var)` mp_tac) >>
     simp[] >> strip_tac >> fs[ptr_covers_def, wordsTheory.word_add_n2w] >>
     `addr + off < dimword (:256)` by decide_tac >>
     fs[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     inv' H mid su G'' tn'' z cells off` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     qpat_assum `inv' _ es si G0 tn0 s0 cells off` mp_tac >>
     pure_rewrite_tac[markerTheory.Abbrev_def] >>
     simp[Abbr `inv'`, NoAsms] >> strip_tac >>
     `wb_frame ce es mid si s0 z` by
       metis_tac[exprSimWordArgsTheory.expr_post_frame] >>
     `fr.cs_next_id <= si.cs_next_id /\
      si.cs_next_id <= su.cs_next_id /\ si.cs_next_var <= su.cs_next_var` by
       (qspec_then `ce` mp_tac ci_mono_unwrap_value >>
        disch_then (qspecl_then [`vv`, `sn`] mp_tac) >>
        simp[ci_mono_def] >> decide_tac) >>
     `wb_frame ce ees mid fr sf z` by
       (irule exprSimWordArgsTheory.wb_frame_trans >> simp[] >>
        reverse conj_tac >- metis_tac[] >>
        qexistsl_tac [`es`, `si`, `s0`] >> simp[]) >>
     `!name p k. local_region ce mid.scopes z name p k <=>
                 local_region ce es.scopes s0 name p k` by
       metis_tac[wordArgsPtrTheory.wb_frame_local_regions] >>
     `pure ==> pure_frame ce func ees fr sf z` by
       (strip_tac >> irule exprSimPropsTheory.pure_frame_trans >> simp[] >>
        qexistsl_tac [`es`, `si`, `s0`] >> simp[] >>
        conj_tac >- (qpat_assum `wb_frame ce ees es fr sf s0`
          (mp_tac o SIMP_RULE (srw_ss()) [wb_frame_def]) >> simp[]) >>
        conj_tac >- (qpat_assum `wb_frame ce es mid si s0 z`
          (mp_tac o SIMP_RULE (srw_ss()) [wb_frame_def]) >> simp[]) >>
        qpat_assum `expr_post H ctx func ce cx e es si su s0 mid v op z`
          (mp_tac o SIMP_RULE (srw_ss()) [expr_post_def]) >> simp[]) >>
     `lookup_var root z = SOME (n2w addr) /\
      FLOOKUP z.vs_allocas aid = SOME (addr,capacity)` by
       (qpat_assum `wb_frame ce es mid si s0 z`
          (mp_tac o SIMP_RULE (srw_ss()) [wb_frame_def]) >> simp[]) >>
     `ptr_covers G'' tn'' root z capacity` by
       (qpat_assum `ghost_kept_at lo ce es si G0 tn0 s0 G'' tn''`
          (mp_tac o Q.SPEC `root` o CONJUNCT1 o
           SIMP_RULE (srw_ss()) [ghost_kept_at_def]) >>
         (impl_tac >- simp[]) >> disch_then strip_assume_tac >>
         qpat_assum `ptr_covers G0 tn0 root s0 capacity`
           (strip_assume_tac o SIMP_RULE (srw_ss()) [ptr_covers_def]) >>
         qpat_x_assum `lookup_var root s0 = SOME w` mp_tac >>
         simp[] >> disch_then SUBST_ALL_TAC >>
         simp[ptr_covers_def, wordsTheory.w2n_n2w]) >>
     `ghost_kept_at lo ce ees fr Gf tnf sf G'' tn''` by
       (irule structlit_ghost_kept_trans >> simp[] >>
        conj_tac >- metis_tac[] >>
        qexistsl_tac [`G0`, `es`, `s0`, `si`, `tn0`] >> simp[]) >>
     `EVERY (\(tv,v,p,k). addr <= p /\ p+k <= addr+capacity) cells` by
       (qpat_assum `EVERY _ cells` mp_tac >>
        qpat_assum `off <= capacity` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        simp[EVERY_MEM, pairTheory.FORALL_PROD] >> rpt strip_tac >>
        first_x_assum drule >> strip_tac >> decide_tac) >>
     `literal_prefix_ok cells tn'' z` by
       (irule (INST_TYPE [``:'a`` |-> ``:num # num``] structlit_prefix_child_frame) >>
        qexistsl_tac [`G''`, `G0`, `addr`, `aid`, `capacity`, `ce`, `mid`, `es`, `lo`, `s0`, `si`, `tn0`] >>
        simp[] >> first_assum ACCEPT_TAC) >>
     simp[] >>
     qpat_assum `expr_post H ctx func ce cx e es si su s0 mid v op z`
       (strip_assume_tac o SIMP_RULE (srw_ss()) [expr_post_def]) >>
     simp[] >>
     conj_tac
     >- (qpat_assum `gas_origin_ptr_path _ _ _ _`
           (mp_then Any mp_tac (cj 2 fragGasOriginPtrTheory.gas_origin_ptr_path_projections)) >>
         metis_tac[fragGasSeqPtrTheory.gas_path_ptr_ok_not_halted]) >>
     conj_tac
     >- (qpat_assum `not_fresh_at si root`
           (mp_tac o SIMP_RULE (srw_ss()) [loweringStateRelDefsTheory.not_fresh_at_def]) >>
         simp[loweringStateRelDefsTheory.not_fresh_at_def] >> decide_tac) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func ce cx mid z` by
    (qpat_assum `expr_post (storage_trace_horizon mid.storage_trace) ctx func ce cx e es si su s0 mid v op z`
       (ACCEPT_TAC o CONJUNCT1 o PURE_REWRITE_RULE [expr_post_def])) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp z` by
    (qpat_assum `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func ce cx mid z`
       (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  `?u G2 tn2.
     (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (z,G'',tn'') [] (OK u,G2,tn2)) /\
     val_wf ftv v /\
     typed_copy_state_frame su (addr+off) (type_memory_size ftv) z u /\
     ~u.vs_halted /\ u.vs_current_bb = ss.cs_current_bb /\
     u.vs_inst_idx = LENGTH ss.cs_current_insts /\
     tn2.t_imm = tn''.t_imm /\ tn2.t_stor = tn''.t_stor /\ tn2.t_trans = tn''.t_trans /\
     (!i. ~(addr+off <= i /\ i < addr+off+type_memory_size ftv) ==>
       (i IN tn2.t_mem <=> i IN tn''.t_mem)) /\
     (!mem. mem_agree_outside tn2.t_mem u.vs_memory mem ==>
       val_in_memory ftv v (addr+off) mem) /\
     (!p. not_fresh_at su p ==> FLOOKUP G2 p = FLOOKUP G'' p /\
       op_taint tn2 (Var p) = op_taint tn'' (Var p))` by
   (Cases_on `is_word_type (lowered_value_type ce e)`
  >- (`type_widens_to (get_tenv cx) (lowered_value_type ce e) (expr_type e)` by
        (irule immutableDeployPhysicalSourceTheory.immutable_rhs_physical_widens >>
         qexistsl_tac [`env`, `es`] >> simp[type_widens_to_def]) >>
      `is_word_type (expr_type e) /\ is_word_type fty` by
        metis_tac[type_widens_to_def, aggregateEvaluatedLayoutTheory.arg_type_fits_word_type] >>
      `lowered_value_type ce e = expr_type e` by
        metis_tac[compileEnvTheory.type_widens_to_word] >>
      `expr_type e = fty` by
        (irule compileEnvTheory.type_widens_to_word >>
         conj_tac >- simp[] >> qexists_tac `get_tenv cx` >>
         simp[type_widens_to_def, well_formed_type_def]) >>
      `~is_bytestring_type (lowered_value_type ce e)` by
        (qpat_assum `is_word_type (lowered_value_type ce e)` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         Cases_on `lowered_value_type ce e` >>
         simp[is_word_type_def, is_bytestring_type_def] >>
         rename1 `BaseT bt` >> Cases_on `bt` >>
         gvs[is_word_type_def, is_bytestring_type_def] >>
         rename1 `BytesT bd` >> Cases_on `bd` >>
         gvs[is_word_type_def, is_bytestring_type_def]) >>
      `post_value_type ce e = fty` by
        metis_tac[immutableDeployPhysicalSourceTheory.immutable_rhs_post_physical_classify] >>
      `value_has_type ftv v` by
        metis_tac[optionTheory.SOME_11] >>
      `val_wf ftv v` by metis_tac[cj 1 valueEncodingTypingTheory.value_has_type_val_wf] >>
      `eval_operand op z = SOME (typed_val_to_w256 ftv v)` by
        metis_tac[expr_post_def, expr_val_at_def, expr_val_rel_def] >>
      `type_memory_size ftv = 32` by metis_tac[exprSimPropsTheory.word_tv_memory_size] >>
      `op_taint tn'' op = {} /\ allocas_from lo z /\ lo <= z.vs_alloca_next` by
        (fs[ptr_val_ok_def, ghost_inv_at_def]) >>
      `addr+capacity <= s0.vs_alloca_next` by
        (qpat_assum `inv' _ es si _ _ s0 _ _` mp_tac >>
         simp[Abbr `inv'`] >>
         metis_tac[allocaSiteResourceTheory.alloca_site_registered_below,
                   stmt_state_rel_def]) >>
      `addr+off+32 < dimword (:256) /\ addr+off+32 <= z.vs_alloca_next` by
        (fs[] >> decide_tac) >>
      `w2n ((n2w (addr+off)):256 word) = addr+off` by
        (simp[wordsTheory.w2n_n2w] >> fs[] >> decide_tac) >>
      `~z.vs_halted` by
        (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
           (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
         (impl_tac >- gvs[storage_trace_domain_def]) >>
         disch_then (mp_tac o CONJUNCT1) >>
         disch_then (mp_then Any mp_tac
           (cj 2 fragGasOriginPtrTheory.gas_origin_ptr_path_projections)) >>
         disch_then (mp_then Any ACCEPT_TAC fragGasSeqPtrTheory.gas_path_ptr_ok_not_halted)) >>
      qpat_assum `compile_store_memory ce op _ fty _ su = ((),ss)`
        (mp_then Any mp_tac logStoreDataOriginPtrTheory.compile_store_memory_word_origin_ptr_path) >>
      disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
      disch_then (drule_at (Pat `evaluate_type _ _ = SOME _`)) >>
      disch_then (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
      disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
      disch_then (mp_tac o Q.INST
        [`lo` |-> `lo`, `explicit` |-> `gas_explicit_sites ctx shadow_ctx`, `PG` |-> `PG`,
         `ctx` |-> `ctx`, `tn` |-> `tn''`, `G` |-> `G''`] o SPEC_ALL) >>
      (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `expr_post (storage_trace_horizon mid.storage_trace) ctx func ce cx e
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) si su s0 mid v op z` by
    simp[gasOutcomeInitialObsPtrTheory.expr_post_initial_obs] >>
  qpat_assum `expr_post _ ctx func ce cx e (es with gas_obs := _) si su s0 mid v op z`
    (mp_then Any mp_tac structlit_unwrapped_physical_inputs) >>
  disch_then (drule_at (Pat `ptr_val_ok _ _ _ _ _ _ _`)) >>
  disch_then (mp_tac o SPEC_ALL) >>
  (impl_tac >- (simp[] >>
    qpat_assum `bind (eval_expr cx e) (read_result cx) _ = _` mp_tac >>
    CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[])) >>
  disch_then (REPEAT_TCL CHOOSE_THEN (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  `type_widens_to (get_tenv cx) (lowered_value_type ce e) (expr_type e)` by
    (irule immutableDeployPhysicalSourceTheory.immutable_rhs_physical_widens >>
     qexistsl_tac [`env`, `es`] >> simp[type_widens_to_def]) >>
  `type_widens_to (get_tenv cx) (lowered_value_type ce e) fty` by
    (irule typedCopyCompatibilityTheory.type_widens_to_trans >>
     qexists_tac `expr_type e` >> simp[type_widens_to_def, well_formed_type_def]) >>
  `~is_word_type fty` by metis_tac[compileEnvTheory.type_widens_to_word] >>
  `value_has_type ftv v /\ val_wf ftv v` by
    (mp_tac (Q.INST [`tenv` |-> `get_tenv cx`,
       `t` |-> `lowered_value_type ce e`, `u` |-> `fty`, `tv` |-> `stv`, `v` |-> `v`]
       vyperTypeArgFitsTheory.type_widens_to_value_has_type) >>
     simp[] >> strip_tac >>
     simp[cj 1 valueEncodingTypingTheory.value_has_type_val_wf]) >>
  `type_memory_bytes ce fty = type_memory_size ftv` by
    (irule expr_sim_inv_memory_size >> qexistsl_tac [`cx`, `env`, `es`] >> simp[]) >>
  `sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
   (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
       sz = type_memory_size tv) fields)` by
    (qpat_assum `expr_sim_inv ce cx env es` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[expr_sim_inv_def] >> metis_tac[]) >>
  `acyclic_struct_metadata ce.ce_struct_fields` by
    (drule_then (ACCEPT_TAC o MATCH_MP contract_inv_acyclic_struct_metadata)
       bodySimTheory.body_inv_contract) >>
  Cases_on `type_memory_size stv = 0`
  >- (`lowered_value_type ce e = fty` by
        metis_tac[wideningZeroLayoutTheory.type_widens_to_zero_layout] >>
      `ftv = stv` by metis_tac[optionTheory.SOME_11] >>
      `~z.vs_halted` by
        (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
           (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
         (impl_tac >- gvs[storage_trace_domain_def]) >>
         disch_then (mp_then Any mp_tac
           (cj 2 fragGasOriginPtrTheory.gas_origin_ptr_path_projections) o CONJUNCT1) >>
         metis_tac[fragGasSeqPtrTheory.gas_path_ptr_ok_not_halted]) >>
      qpat_assum `compile_store_memory ce op _ fty _ su = ((),ss)`
        (mp_then Any mp_tac structlit_zero_physical_store_path) >>
      disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
      disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
      disch_then (drule_at (Pat `evaluate_type _ _ = SOME _`)) >>
      disch_then (mp_tac o Q.INST
        [`lo` |-> `lo`, `explicit` |-> `gas_explicit_sites ctx shadow_ctx`, `PG` |-> `PG`,
         `ctx` |-> `ctx`, `tn` |-> `tn''`, `G` |-> `G''`, `dtv` |-> `ftv`] o SPEC_ALL) >>
      (impl_tac >- (simp[wordsTheory.w2n_lt] >>
        TRY (conj_tac >- (irule loweringShapeDefsTheory.not_fresh_at_mono >>
          qexists_tac `sn` >> simp[] >>
          qspec_then `ce` mp_tac ci_mono_unwrap_value >>
          disch_then (qspecl_then [`vv`, `sn`] mp_tac) >>
          simp[ci_mono_def])) >>
        qpat_assum `Abbrev (inv' = _)` (fn eq =>
          qpat_assum `!H. valid_horizon _ _ H _ ==> inv' H mid su _ _ _ _ _`
            (qspec_then `storage_trace_horizon mid.storage_trace`
             (mp_tac o REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] eq]))) >>
        BETA_TAC >>
        (impl_tac >- gvs[storage_trace_domain_def]) >>
        strip_tac >> fs[bodyPtrDefsTheory.ghost_inv_at_def])) >>
      strip_tac >> goal_assum (drule_at Any) >> simp[] >>
      qexists_tac `t''` >>
      `addr + off < dimword(:256)` by decide_tac >>
      simp[wordsTheory.w2n_n2w] >>
      conj_tac
      >- (qpat_assum `typed_copy_state_frame su _ _ z t''` mp_tac >>
          qpat_assum `ftv = stv` mp_tac >>
          qpat_assum `type_memory_size stv = 0` mp_tac >>
          qpat_assum `addr + off < dimword(:256)` mp_tac >>
          POP_ASSUM_LIST (K all_tac) >> simp[]) >>
      qpat_assum `!mem. mem_agree_outside _ _ mem ==> val_in_memory ftv _ _ mem` mp_tac >>
      qpat_assum `ftv = stv` mp_tac >>
      qpat_assum `addr + off < dimword(:256)` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `0 < type_memory_size stv` by decide_tac >>
  qpat_assum `0 < type_memory_size stv ==> _` drule >> strip_tac >>
  `sn.cs_next_var <= su.cs_next_var` by
    (qspec_then `ce` mp_tac ci_mono_unwrap_value >>
     disch_then (qspecl_then [`vv`, `sn`] mp_tac) >> simp[ci_mono_def]) >>
  `addr + off < dimword(:256)` by decide_tac >>
  `w2n ((n2w (addr+off)):256 word) = addr+off` by simp[] >>
  `not_fresh_at su src` by
    (qpat_assum `unwrap_value ce vv sn = (op,su)`
       (mp_then Any mp_tac exprOperandVarTheory.compiler_unwrap_value_var) >>
     disch_then (qspec_then `src` mp_tac) >> simp[] >>
     (impl_tac >-
       (qpat_assum `!p. vv_operand vv = Var p ==> _` mp_tac >>
        qpat_assum `sm.cs_next_var <= sn.cs_next_var` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> Cases_on `vv` >>
        simp[contextTheory.vv_operand_def] >> rpt strip_tac >>
        irule loweringShapeDefsTheory.not_fresh_at_mono >>
        qexists_tac `sm` >> simp[])) >> simp[]) >>
  `not_fresh_at su (STRING #"%" (toString sm.cs_next_var))` by
    (irule loweringShapeDefsTheory.not_fresh_at_mono >>
     qexists_tac `sn` >> simp[]) >>
  `z.vs_alloca_next < dimword(:256)` by
    (qpat_assum `stmt_state_rel _ ctx func ce cx mid z` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[stmt_state_rel_def, alloca_room_def] >> decide_tac) >>
  `w2n sw + type_memory_size stv < dimword(:256)` by decide_tac >>
  `addr+capacity <= z.vs_alloca_next` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> inv' H mid su _ _ _ _ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     (impl_tac >- gvs[storage_trace_domain_def]) >>
     qpat_assum `Abbrev (inv' = _)`
       (fn eq => PURE_ONCE_REWRITE_TAC[REWRITE_RULE [markerTheory.Abbrev_def] eq]) >>
     BETA_TAC >> strip_tac >>
     qpat_assum `FLOOKUP z.vs_allocas aid = SOME (addr,capacity)` mp_tac >>
     qpat_assum `stmt_state_rel _ ctx func ce cx mid z`
       (mp_tac o CONJUNCT2 o MATCH_MP stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[allocaSiteResourceTheory.alloca_site_registered_below]) >>
  `addr+off+type_memory_size ftv < dimword(:256) /\
   addr+off+type_memory_size ftv <= z.vs_alloca_next` by decide_tac >>
  `lookup_var src z = SOME sw` by
    (qpat_assum `eval_operand op z = SOME sw` mp_tac >>
     qpat_assum `op = Var src` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp[venomStateTheory.eval_operand_def]) >>
  `allocas_from lo z /\ lo <= z.vs_alloca_next` by
    (qpat_assum `ghost_inv_at _ lo d ce cx mid G'' tn'' z` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[ghost_inv_at_def]) >>
  `~z.vs_halted` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     (impl_tac >- gvs[storage_trace_domain_def]) >>
     disch_then (mp_tac o CONJUNCT1) >>
     disch_then (mp_then Any mp_tac
       (cj 2 fragGasOriginPtrTheory.gas_origin_ptr_path_projections)) >>
     disch_then (mp_then Any ACCEPT_TAC fragGasSeqPtrTheory.gas_path_ptr_ok_not_halted)) >>
  Cases_on `is_bytestring_type fty`
  >- (`is_bytestring_type (lowered_value_type ce e)` by
        metis_tac[typedMemoryCopyTheory.typed_copy_bytestring_source] >>
      qpat_assum `op = Var src` (fn eq =>
        qpat_assum `compile_store_memory ce op _ fty _ su = ((),ss)`
          (mp_then Any mp_tac structlit_bytes_store_origin_ptr_path o PURE_REWRITE_RULE [eq])) >>
      disch_then (drule_at (Pat `evaluate_type _ _ = SOME _`)) >>
      disch_then (drule_at (Pat `lookup_var src z = SOME sw`)) >>
      disch_then (mp_tac o Q.INST
        [`lo` |-> `lo`, `explicit` |-> `gas_explicit_sites ctx shadow_ctx`, `PG` |-> `PG`,
         `ctx` |-> `ctx`, `tn` |-> `tn''`, `G` |-> `G''`, `dtv` |-> `ftv`,
         `dw` |-> `(n2w (addr+off)):256 word`] o SPEC_ALL) >>
      (impl_tac >- simp[]) >>
      strip_tac >> goal_assum (drule_at Any) >> simp[] >>
      goal_assum (drule_at Any) >> simp[] >>
      qpat_assum `typed_copy_state_frame su _ _ z u` mp_tac >>
      qpat_assum `!mem. mem_agree_outside tn2.t_mem u.vs_memory mem ==> _` mp_tac >>
      qpat_assum `w2n ((n2w (addr+off)):256 word) = addr+off` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `~is_bytestring_type (lowered_value_type ce e)` by
    metis_tac[typedMemoryCopyTheory.type_widens_from_bytestring] >>
  `post_value_type ce e = lowered_value_type ce e` by
    metis_tac[immutableDeployPhysicalSourceTheory.immutable_rhs_post_physical_classify] >>
  `val_footprint stv v = type_memory_size stv` by
    metis_tac[exprSimAggregateChildrenTheory.evaluated_nonbytes_footprint] >>
  `expr_val_at ce cx (lowered_value_type ce e) si su mid v op z` by
    metis_tac[expr_post_def] >>
  `aid < si.cs_next_id` by
    (qpat_assum `inv' _ es si G0 tn0 s0 cells off` mp_tac >>
     qpat_assum `Abbrev (inv' = _)` (fn eq =>
       PURE_ONCE_REWRITE_TAC[REWRITE_RULE [markerTheory.Abbrev_def] eq]) >>
     BETA_TAC >> strip_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  qpat_assum `stmt_state_rel _ ctx func ce cx mid z`
    (mp_then Any mp_tac structlit_physical_footprint_bounds) >>
  disch_then (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand op z = SOME sw`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = SOME _`)) >>
  disch_then (mp_tac o Q.INST
    [`did` |-> `aid`, `b` |-> `addr`, `k` |-> `capacity`,
     `dst` |-> `addr+off`, `dlen` |-> `type_memory_size ftv`] o SPEC_ALL) >>
  (impl_tac >- (
    qpat_assum `!H. valid_horizon _ _ H _ ==> inv' H mid su _ _ z cells off`
      (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
    (impl_tac >- gvs[storage_trace_domain_def]) >>
    qpat_assum `Abbrev (inv' = _)` (fn eq =>
      PURE_ONCE_REWRITE_TAC[REWRITE_RULE [markerTheory.Abbrev_def] eq]) >>
    BETA_TAC >> strip_tac >>
    simp[] >> rpt strip_tac >>
    qpat_assum `!name p k. local_region ce mid.scopes z name p k ==> _`
      (drule_then strip_assume_tac) >>
    decide_tac)) >>
  strip_tac >>
  qpat_assum `op = Var src` (fn eq =>
    qpat_assum `compile_store_memory ce op _ fty _ su = ((),ss)`
      (mp_then Any mp_tac logStoreDataOriginPtrTheory.compile_store_memory_origin_ptr_path o
       PURE_REWRITE_RULE [eq])) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `lookup_var src z = SOME sw`)) >>
  disch_then (mp_tac o Q.INST
    [`lo` |-> `lo`, `explicit` |-> `gas_explicit_sites ctx shadow_ctx`, `PG` |-> `PG`,
     `ctx` |-> `ctx`, `tn` |-> `tn''`, `G` |-> `G''`, `dtv` |-> `ftv`,
     `dw` |-> `(n2w (addr+off)):256 word`] o SPEC_ALL) >>
  (impl_tac >- simp[]) >>
  strip_tac >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  qpat_assum `typed_copy_state_frame su _ _ z u` mp_tac >>
  qpat_assum `!mem. mem_agree_outside tn2.t_mem u.vs_memory mem ==> _` mp_tac >>
  qpat_assum `w2n ((n2w (addr+off)):256 word) = addr+off` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `alloca_inv z` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ z`
       (mp_tac o SIMP_RULE (srw_ss()) [expr_post_def]) >>
     metis_tac[stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def]) >>
  `alloca_history func u` by
    (qpat_assum `!D. gas_origin_ptr_path _ (z,_,_) [] (OK u,_,_)`
      (qspec_then `DF (storage_trace_horizon mid.storage_trace)` mp_tac) >>
     strip_tac >> drule_all body_full_path_alloca_history >> simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     inv' H mid ss G2 tn2 u
       (cells++[(ftv,v,addr+off,type_memory_size ftv)]) (off+type_memory_size ftv)` by
    (rpt strip_tac >>
     qpat_assum `addr+capacity < dimword(:256)` (fn bound =>
       qpat_assum `Abbrev (inv' = _)`
         (mp_then Any mp_tac
           (SIMP_RULE pure_ss [bound, arithmeticTheory.ADD_COMM, boolTheory.AND_CLAUSES]
             (Q.INST [`addr` |-> `addr`, `capacity` |-> `capacity`]
                (SPEC_ALL structlit_store_inv_step))) o
          REWRITE_RULE [markerTheory.Abbrev_def])) >>
     disch_then (fn step =>
       qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> inv' H mid su _ _ z cells off`
         (qspec_then `H` mp_tac) >>
       (impl_tac >- simp[]) >>
       disch_then (mp_then Any
         (mp_tac o Q.INST [`n` |-> `type_memory_size ftv`] o SPEC_ALL) step)) >>
     simp_tac pure_ss [arithmeticTheory.ADD_COMM] >>
     disch_then irule >>
     simp[] >>
     `si.cs_next_var <= su.cs_next_var` by
       (qspec_then `ce` mp_tac ci_mono_unwrap_value >>
        disch_then (qspecl_then [`vv`, `sn`] mp_tac) >> simp[ci_mono_def] >> decide_tac) >>
     `local_ptrs_reserved ce su` by
       (irule local_ptrs_reserved_next_var >> qexists_tac `si` >> simp[]) >>
     `ci_mono su ss` by
       (qspec_then `ce` mp_tac ci_mono_compile_store_memory >>
        disch_then (qspecl_then [`op`, `Var (STRING #"%" (toString sm.cs_next_var))`,
          `fty`, `lowered_value_type ce e`, `su`] mp_tac) >> simp[]) >>
     simp[] >> rpt conj_tac
     >- (rpt strip_tac >> simp[loweringStateRelDefsTheory.not_fresh_at_def] >>
         qpat_x_assum `!x sz. ce.ce_return_buf = _ ==> _` drule >>
         simp[loweringStateRelDefsTheory.not_fresh_at_def])
     >- (rpt strip_tac >> simp[loweringStateRelDefsTheory.not_fresh_at_def] >>
         qpat_x_assum `!x sz. ce.ce_return_pc = _ ==> _` drule >>
         simp[loweringStateRelDefsTheory.not_fresh_at_def]) >>
     metis_tac[local_ptrs_reserved_imm_base]) >>
  `type_memory_bytes ce fty = type_memory_size ftv` by
    (irule expr_sim_inv_memory_size >> qexistsl_tac [`cx`, `env`, `es`] >> simp[]) >>
  `allocas_from lo t` by
    (qpat_assum `ghost_inv_at _ lo d ce cx mid G1 tn1 t`
       (mp_tac o SIMP_RULE (srw_ss()) [ghost_inv_at_def]) >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `gas_origin_ptr_path (DF (storage_trace_horizon mid.storage_trace),lo,
      gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (t,G1,tn1) [] (OK u,G2,tn2)` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`G'`, `t'`, `tn'`] >> conj_tac
     >- (qpat_assum `!D lo' explicit. allocas_from lo' t ==> _`
          (qspecl_then [`DF (storage_trace_horizon mid.storage_trace)`, `lo`,
                        `gas_explicit_sites ctx shadow_ctx`] mp_tac) >>
         simp[ghost_inv_at_def]) >>
     irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`G''`, `z`, `tn''`] >> simp[]) >>
  `!fn inst s. frag_reachable ctx func u fn inst s ==> dalloca_fmp_headroom inst s` by
    (qpat_assum `gas_origin_ptr_path _ (t,G1,tn1) [] (OK u,G2,tn2)` (fn path =>
       qpat_assum `!bb. MEM bb func.fn_blocks ==> _` (fn no_phi =>
       qpat_assum `!fn inst s. frag_reachable ctx func t fn inst s ==> _` (fn safe =>
         ACCEPT_TAC (MATCH_MP bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom
           (LIST_CONJ [path,no_phi,safe])))))) >>
  `body_const_cells_agree [(NONE,cx_tops cx)] cx env mid` by
    (`well_typed_expr env e` by
       qpat_assum `expr_body_pre _ cx env e _`
         (ACCEPT_TAC o cj 2 o MATCH_MP exprBodyPrePropsTheory.expr_body_pre_static_facts) >>
     qpat_assum `!tail. eval_expr cx e _ = _`
       (qspec_then `mid.gas_obs` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
     irule body_const_cells_agree_expr >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >> simp[]) >>
  qpat_assum `!tys tvs' es' si' sb' shadow_si' shadow_sb' s0' G0' tn0' cells' off' out'. _`
    (fn ih => qpat_assum `compile_struct_lit compile_expr ce (StructT nsid) fs (Var root) _ ss = _`
      (mp_then Any mp_tac ih)) >>
  disch_then (drule_at (Pat `OPT_MMAP _ _ = SOME _`)) >>
  disch_then (fn ih =>
    qpat_assum `type_memory_bytes ce fty = type_memory_size ftv` (fn layout =>
      qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> inv' H mid ss G2 tn2 u _ _`
        (mp_then (Pat `!H. valid_horizon _ _ H _ ==> inv' H _ _ _ _ _ _ _`)
          mp_tac (REWRITE_RULE [layout] ih)))) >>
  disch_then (qspecl_then [`shadow_ss`, `shadow_sb`] mp_tac) >>
  simp[expr_sim_full_code_def] >>
  `si.cs_next_var <= ss.cs_next_var` by
    (qspec_then `ce` mp_tac ci_mono_unwrap_value >>
     disch_then (qspecl_then [`vv`, `sn`] mp_tac) >>
     qspec_then `ce` mp_tac ci_mono_compile_store_memory >>
     disch_then (qspecl_then [`op`, `Var (STRING #"%" (toString sm.cs_next_var))`,
       `fty`, `lowered_value_type ce e`, `su`] mp_tac) >>
     simp[ci_mono_def] >> decide_tac) >>
  (impl_tac >- (simp[GSYM typeLayoutPropsTheory.type_memory_size_list_sum] >>
    rpt conj_tac
    >- metis_tac[]
    >- (qpat_assum `body_exprs_full_ok cx (e::_)` mp_tac >>
        pure_rewrite_tac[body_exprs_full_ok_def] >> strip_tac >>
        qpat_x_assum `( ?s tv t s1 v t1. _) ==> body_exprs_full_ok _ _` irule >>
        qpat_assum `!tail. eval_expr cx e _ = _` (qspec_then `[]` mp_tac) >>
        qpat_assum `read_result cx tv mid = (INL v,mid)` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> metis_tac[])
    >- (irule local_ptrs_reserved_next_var >> qexists_tac `si` >> simp[])
    >- FIRST_ASSUM ACCEPT_TAC
    >- (rpt strip_tac >> simp[loweringStateRelDefsTheory.not_fresh_at_def] >>
        qpat_x_assum `!x sz. ce.ce_return_buf = _ ==> _` drule >>
        simp[loweringStateRelDefsTheory.not_fresh_at_def])
    >- (rpt strip_tac >> simp[loweringStateRelDefsTheory.not_fresh_at_def] >>
        qpat_x_assum `!x sz. ce.ce_return_pc = _ ==> _` drule >>
        simp[loweringStateRelDefsTheory.not_fresh_at_def])
    >- (`wb_frame ce es mid si s0 z` by
          (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
             (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
           (impl_tac >- gvs[storage_trace_domain_def]) >> strip_tac >>
           metis_tac[exprSimWordArgsTheory.expr_post_frame]) >>
        `si.cs_next_var <= su.cs_next_var` by
          (qspec_then `ce` mp_tac ci_mono_unwrap_value >>
           disch_then (qspecl_then [`vv`, `sn`] mp_tac) >>
           simp[ci_mono_def] >> decide_tac) >>
        `z.vs_alloca_next <= u.vs_alloca_next` by
          (qpat_assum `typed_copy_state_frame su _ _ z u`
             (mp_tac o SIMP_RULE (srw_ss()) [typedMemoryCopyTheory.typed_copy_state_frame_def]) >>
           disch_then (mp_tac o AP_TERM ``\s:venom_state. s.vs_alloca_next`` o cj 1) >> simp[]) >>
        irule return_buf_frame_frame >>
        qexistsl_tac [`ce`, `s0`, `si`] >> simp[] >>
        (qpat_assum `wb_frame ce es mid si s0 z`
              (mp_tac o SIMP_RULE (srw_ss()) [wb_frame_def]) >>
            qpat_assum `typed_copy_state_frame su _ _ z u`
              (mp_tac o SIMP_RULE (srw_ss()) [typedMemoryCopyTheory.typed_copy_state_frame_def]) >>
            simp[loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[]))
    >- (`expr_body_pre ce cx env e es` by metis_tac[] >>
        `expr_body_pre ce cx env e
          (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ [])` by simp[] >>
        qpat_assum `!tail. eval_expr cx e _ = _` (qspec_then `[]` assume_tac) >>
        drule_all exprSimSourceTheory.expr_body_pre_eval_result >> simp[])
    >- (qpat_assum `off + type_memory_size_list (ftv::rest_tvs) <= capacity` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        simp[typeLayoutPropsTheory.type_memory_size_list_sum] >> decide_tac)
    >> qpat_assum `gas_admissible (eval_exprs cx (e::_)) _ es` mp_tac >>
       qpat_assum `!tail. eval_expr cx e _ = _` mp_tac >>
       qpat_assum `read_result cx tv mid = (INL v,mid)` mp_tac >>
       qpat_assum `mid.gas_obs = []` mp_tac >>
       POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
       irule (SRULE [gas_admissible_gas_obs] structlit_tail_admissible) >>
       qexistsl_tac [`e`, `es`, `gas_explicit marks s0.vs_gas_readings`, `v`] >>
       simp[bind_def] >> metis_tac[exprSimMemorySourceTheory.read_result_gas_obs])) >>
  strip_tac >>
  qspec_then `inv'` mp_tac
    (Q.INST [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`,
             `tvs` |-> `rest_tvs`] structlit_fields_cons_continuation) >>
  (impl_tac >- simp[Abbr `inv'`]) >>
  disch_then (irule o PURE_REWRITE_RULE [LIST_REL_CONS1, ZIP]) >>
  simp[] >>
  reverse conj_tac
  >- (`expr_body_pre ce cx env e es` by metis_tac[] >>
      `expr_body_pre ce cx env e
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ [])` by simp[] >>
      qpat_assum `!tail. eval_expr cx e _ = _` (qspec_then `[]` assume_tac) >>
      drule_all exprSimSourceTheory.expr_body_pre_runtime_typed >>
      strip_tac >>
      qpat_assum `read_result cx tv mid = (INL v,mid)` mp_tac >>
      qpat_assum `!v'. read_result cx tv _ = _ ==> _` mp_tac >>
      qpat_assum `evaluate_type (get_tenv cx) (expr_type e) = SOME _` mp_tac >>
      qpat_assum `evaluate_type (get_tenv cx) fty = SOME ftv` mp_tac >>
      qpat_assum `arg_type_fits (expr_type e) fty` mp_tac >>
      qpat_assum `mid.gas_obs = []` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> simp[] >>
      rpt strip_tac >>
      `mid with gas_obs := [] = mid` by
        (qpat_x_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >> gvs[] >>
      drule_all (cj 1 vyperTypeArgFitsTheory.arg_type_fits_value_has_type) >> simp[]) >>
  rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
  irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
  qexistsl_tac [`G'`, `t'`, `tn'`] >> conj_tac
  >- (qpat_assum `!D lo' explicit. allocas_from lo' t ==> _`
        (qspecl_then [`DF H`, `lo`, `gas_explicit_sites ctx shadow_ctx`] mp_tac) >> simp[]) >>
  irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
  qexistsl_tac [`G''`, `z`, `tn''`] >> simp[]
QED

Theorem structlit_allocated_fields_bundled_full[local]:
  !ctx func ce cx DF lo d es sa s0 G0 tn0 pure root w tvs inv'
    shadow_ctx shadow_func PG env st0 nsid fs tys sm sb shadow_sm shadow_sb
    out t G tn.
  inv' = (\H ee cs G tn s cells off.
    stmt_state_rel H ctx func ce cx ee s /\
    storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d ce cx ee G tn s /\
    wb_frame ce es ee sa s0 s /\ ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    ~s.vs_halted /\ expr_sim_full_endpoint func cs s0 s /\
    not_fresh_at cs root /\ lookup_var root s = SOME (n2w (w2n w)) /\
    ptr_covers G tn root s (type_memory_size_list tvs) /\
    FLOOKUP s.vs_allocas sa.cs_next_id = SOME (w2n w,type_memory_size_list tvs) /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit(n2w (type_memory_size_list tvs))] [root])
      (fn_insts func) /\
    lo <= w2n w /\ w2n w+type_memory_size_list tvs < dimword(:256) /\
    sa.cs_next_id <= sa.cs_next_id /\ sa.cs_next_id < cs.cs_next_id /\
    sa.cs_next_var <= cs.cs_next_var /\ off <= type_memory_size_list tvs /\
    (!name p k. local_region ce ee.scopes s name p k ==>
      w2n w+type_memory_size_list tvs <= p \/ p+k <= w2n w) /\
    (!name p k. local_region ce es.scopes s0 name p k ==>
      w2n w+type_memory_size_list tvs <= p \/ p+k <= w2n w) /\
    (!old p k. FLOOKUP s0.vs_allocas old = SOME(p,k) /\ old < sa.cs_next_id ==>
      w2n w+type_memory_size_list tvs <= p \/ p+k <= w2n w) /\
    EVERY (\(tv,v,p,k). w2n w <= p /\ p+k <= w2n w+off) cells /\
    literal_prefix_ok cells tn s /\
    (pure ==> pure_frame ce func es sa s0 s)) /\
  compile_struct_lit compile_expr ce (StructT nsid) fs (Var root) 0 sm = (out,sb) /\
  compile_struct_lit compile_expr (gas_shadow_env T ce) (StructT nsid)
    (MAP (I ## gas_shadow_expr) fs) (Var root) 0 shadow_sm = (out,shadow_sb) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sm,sb,shadow_sm,shadow_sb) /\
  body_const_cells_agree [(NONE,cx_tops cx)] cx env es /\
  body_inv (cx_tops cx) ctx ce cx /\
  shadow_body_inv (cx_tops cx) ctx shadow_ctx /\ body_exprs_full_ok cx (MAP SND fs) /\
  (?Hbase. stmt_state_rel Hbase ctx func ce cx es s0) /\
  LIST_REL (\t (name,e). ALOOKUP
    (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)) name =
    SOME(t,type_memory_bytes ce t)) tys fs /\
  LIST_REL (\t e. arg_type_fits (expr_type e) t) tys (MAP SND fs) /\
  OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce sa /\
    (!fn inst s. frag_reachable ctx func t fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME(PtrVar(Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. ce.ce_return_pc = SOME(PtrVar(Var x) sz) ==> not_fresh_at sm x) /\
  return_buf_frame d ce sm t /\
  (!e st. MEM e (MAP SND fs) /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st) /\
  (pure ==> ~EXISTS expr_has_effect (MAP SND fs)) /\ expr_sim_inv ce cx env es /\
  storage_trace_domain cx st0 es.storage_trace /\
  gas_admissible (eval_exprs cx (MAP SND fs))
    (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc)) es /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es t /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at (DF H) lo d ce cx es G tn t) /\
  wb_frame ce es es sa s0 t /\ pure_frame ce func es sa s0 t /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
  ~t.vs_halted /\ expr_sim_full_endpoint func sm s0 t /\
  not_fresh_at sm root /\ lookup_var root t = SOME w /\
  ptr_covers G tn root t (type_memory_size_list tvs) /\
  FLOOKUP t.vs_allocas sa.cs_next_id = SOME(w2n w,type_memory_size_list tvs) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit(n2w (type_memory_size_list tvs))] [root])
    (fn_insts func) /\
  lo <= w2n w /\ w2n w+type_memory_size_list tvs < dimword(:256) /\
  sa.cs_next_id < sm.cs_next_id /\ sa.cs_next_var <= sm.cs_next_var /\
  (!name p k. local_region ce es.scopes t name p k ==>
    w2n w+type_memory_size_list tvs <= p \/ p+k <= w2n w) /\
  (!name p k. local_region ce es.scopes s0 name p k ==>
    w2n w+type_memory_size_list tvs <= p \/ p+k <= w2n w) /\
  (!old p k. FLOOKUP s0.vs_allocas old = SOME(p,k) /\ old < sa.cs_next_id ==>
    w2n w+type_memory_size_list tvs <= p \/ p+k <= w2n w) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (eval_exprs cx (MAP SND fs)) (es,t,G,tn)
    (\H res ee G tn z. ?vs added. res = INL vs /\ expr_sim_inv ce cx env ee /\
      LIST_REL value_has_type tvs vs /\
      inv' H ee sb G tn z ([]++added) (0+type_memory_size_list tvs) /\
      (!m. mem_agree_outside tn.t_mem z.vs_memory m ==>
        fields_in_memory (ZIP(MAP FST fs,vs)) (ZIP(MAP FST fs,tvs)) (w2n w+0) m))
    (\H res ee gt r. ?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) r /\
      halt_exit H cx ee (INR exc : eval_result + exception) r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  rpt gen_tac >> strip_tac >>
  irule (Q.INST [`ees` |-> `es`, `sf` |-> `s0`, `fr` |-> `sa`,
    `Gf` |-> `G0`, `tnf` |-> `tn0`, `aid` |-> `sa.cs_next_id`,
    `addr` |-> `w2n (w:bytes32)`, `capacity` |-> `type_memory_size_list tvs`]
    structlit_fields_bundled_full |> Q.SPEC `inv'` |> UNDISCH) >>
  simp[] >> conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[NOT_EXISTS] >>
  conj_tac >-
    (qpat_assum `pure ==> ~EXISTS expr_has_effect (MAP SND fs)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[EXISTS_MEM, EVERY_MEM, combinTheory.o_THM]) >>
  qexistsl_tac [`nsid`, `out`, `shadow_func`, `shadow_sb`, `shadow_sm`, `sm`, `tys`] >>
  simp[arithmeticTheory.ADD_COMM] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem structlit_endpoint_full_post[local]:
  !H ctx func ce cx v7 nsid kes tvs vs root ba w es sa sb s0 ee G tn s.
  v7 = StructT nsid /\ ba.buf_operand = Var root /\
  evaluate_type (get_tenv cx) v7 = SOME (StructTV (ZIP(MAP FST kes,tvs))) /\
  LENGTH kes = LENGTH tvs /\ LIST_REL value_has_type tvs vs /\
  type_memory_bytes ce v7 = type_memory_size_list tvs /\
  stmt_state_rel H ctx func ce cx ee s /\ storage_well_formed_on cx ee (FST H) /\
  wb_frame ce es ee sa s0 s /\
  (~expr_has_effect (StructLit v7 nsid kes) ==> pure_frame ce func es sa s0 s) /\
  lookup_var root s = SOME (w:bytes32) /\
  ptr_covers G tn root s (type_memory_size_list tvs) /\
  FLOOKUP s.vs_allocas sa.cs_next_id = SOME(w2n w,type_memory_size_list tvs) /\
  sa.cs_next_id < sb.cs_next_id /\
  (!name p k. local_region ce ee.scopes s name p k ==>
    w2n w+type_memory_size_list tvs <= p \/ p+k <= w2n w) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    fields_in_memory (ZIP(MAP FST kes,vs)) (ZIP(MAP FST kes,tvs)) (w2n w) m) ==>
  vv_post H ctx func ce cx (StructLit v7 nsid kes) es sa sb s0 ee
    (Value(StructV(ZIP(MAP FST kes,vs))))
    (LocatedValue (expr_type(StructLit v7 nsid kes)) (base_ptr ba)) s /\
  vv_store_bound cx (expr_type(StructLit v7 nsid kes))
    (lowered_value_type ce (StructLit v7 nsid kes)) ee
    (Value(StructV(ZIP(MAP FST kes,vs))))
    (LocatedValue (expr_type(StructLit v7 nsid kes)) (base_ptr ba)) s /\
  ptr_vv_ok cx (expr_type(StructLit v7 nsid kes))
    (Value(StructV(ZIP(MAP FST kes,vs))))
    (LocatedValue (expr_type(StructLit v7 nsid kes)) (base_ptr ba)) ee G tn s /\
  ptr_buf_ok ce (StructLit v7 nsid kes) (base_ptr ba).ptr_operand G s
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `v7 = _` SUBST_ALL_TAC >>
  `LENGTH tvs = LENGTH vs` by metis_tac[LIST_REL_LENGTH] >>
  `type_memory_size (StructTV (ZIP(MAP FST kes,tvs))) = type_memory_size_list tvs` by
    simp[valueEncodingTheory.type_memory_size_def, struct_layout_size_zip] >>
  `value_has_type (StructTV (ZIP(MAP FST kes,tvs)))
    (StructV(ZIP(MAP FST kes,vs)))` by
    (simp[value_has_type_def] >>
     irule vyperTypeEvalCaseProofsTheory.struct_has_type_zip_same_names_stmt >> simp[]) >>
  `val_wf (StructTV (ZIP(MAP FST kes,tvs))) (StructV(ZIP(MAP FST kes,vs)))` by
    metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory (StructTV (ZIP(MAP FST kes,tvs)))
      (StructV(ZIP(MAP FST kes,vs))) (w2n w) m` by
    simp[valueEncodingDefsTheory.val_in_memory_def] >>
  `val_in_memory (StructTV (ZIP(MAP FST kes,tvs)))
      (StructV(ZIP(MAP FST kes,vs))) (w2n w) s.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `val_footprint (StructTV (ZIP(MAP FST kes,tvs)))
      (StructV(ZIP(MAP FST kes,vs))) <= type_memory_size_list tvs` by
    metis_tac[exprSimPropsTheory.val_footprint_le] >>
  conj_tac
  >- (simp[vv_post_def, vv_holds_def, vv_at_def, post_value_type_def,
        contextTheory.base_ptr_def, expr_type_def, is_word_type_def,
        vyperStateTheory.read_result_def, vyperStateTheory.return_def, venomStateTheory.eval_operand_def] >>
      conj_tac
      >- (disj1_tac >> qexistsl_tac [`sa.cs_next_id`, `w2n w`, `type_memory_size_list tvs`] >>
          simp[] >> rpt strip_tac >>
          qpat_x_assum `!name p k. local_region ce ee.scopes s name p k ==> _`
            (drule_then mp_tac) >> decide_tac) >>
      fs[wb_frame_def] >> metis_tac[]) >>
  `w2n w + type_memory_size_list tvs <= s.vs_alloca_next` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _ _`
       (mp_tac o SIMP_RULE (srw_ss()) [stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def,
         venomMemDefsTheory.alloca_next_valid_def]) >> metis_tac[]) >>
  conj_tac
  >- (simp[exprSimMemDefsTheory.vv_store_bound_def, contextTheory.base_ptr_def, expr_type_def,
        exprLoweringTheory.lowered_value_type_def, vyperStateTheory.read_result_def, vyperStateTheory.return_def,
        venomStateTheory.eval_operand_def, exprSimPropsTheory.val_store_size_def] >>
      rpt gen_tac >> strip_tac >> gvs[]) >>
  simp[ptr_vv_ok_def, ptr_mem_ok_def, ptr_buf_ok_def,
    contextTheory.base_ptr_def, expr_type_def, exprLoweringTheory.lowered_value_type_def,
    vyperStateTheory.read_result_def, vyperStateTheory.return_def,
    venomStateTheory.eval_operand_def] >>
  gvs[ptr_covers_def, exprSimPropsTheory.val_store_size_def]
QED

Theorem structlit_vv_sim_full[local]:
  !cx v7 src_id_opt id kes DF lo d PG tops ctx shadow_ctx func shadow_func
     cenv env ty es.
    body_exprs_full_ok cx (MAP SND kes) /\
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_body_pre cenv cx env (StructLit v7 (src_id_opt,id) kes) es ==>
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (StructLit v7 (src_id_opt,id) kes) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[expr_vv_sim_full_def] >> rpt gen_tac >> strip_tac >>
  drule compile_struct_literal_inv >> strip_tac >> gvs[] >>
  drule struct_literal_lookup_types >> strip_tac >>
  drule struct_literal_evaluated_layout >> strip_tac >>
  drule_then strip_assume_tac expr_body_pre_static_facts >>
  `!e st. MEM e (MAP SND kes) /\ expr_sim_inv cenv cx env st ==>
    expr_body_pre cenv cx env e st` by metis_tac[expr_body_pre_struct_field] >>
  `v7 = StructT (src_id_opt,id)` by fs[well_typed_expr_def] >>
  `type_memory_size_list tvs < dimword(:256)` by
    (fs[alloc_limits_expr_def, type_memory_bytes_def] >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  `compile_alloc_buffer (type_memory_size_list tvs) sa = (ba,sm)` by metis_tac[] >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    (drule compile_alloc_buffer_extends >> strip_tac >>
     mp_tac (Q.SPECL [`compile_expr`, `cenv`, `StructT (src_id_opt,id)`,
       `kes`, `ba.buf_operand`, `0`, `sm`] ci_mono_compile_struct_lit_cfn) >>
     simp[ci_mono_def] >>
     (impl_tac >- (rpt gen_tac >> Cases_on `compile_expr cenv' ty' e' sa'` >>
       drule (cj 1 compile_expr_grows) >> simp[])) >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (drule_all fn_has_code_split >> simp[]) >>
  irule gas_outcome_full_initial_domain >>
  conj_tac >- simp[evaluate_storage_trace_frame] >>
  conj_tac >- simp[] >> strip_tac >>
  `?Hbase:((bool # bytes32 # type_value) list # num list).
       stmt_state_rel Hbase ctx func cenv cx es s0` by
    (qexists_tac `storage_trace_horizon es.storage_trace` >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
     gvs[storage_trace_domain_def]) >>
  drule_all structlit_alloc_init_full >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`, `PG`] strip_assume_tac) >>
  qpat_x_assum `t = raw with vs_inst_idx := _` kall_tac >>
  qpat_x_assum `run_inst_seq _ _ = OK raw` kall_tac >>
  `?shadow_sm. compile_alloc_buffer (type_memory_size_list tvs) shadow_sa = (ba,shadow_sm) /\
      gas_shadow_state sm shadow_sm` by
    (mp_tac (Q.SPEC `type_memory_size_list tvs`
       bodyFullExprGenericTheory.gas_shadow_compiles_alloc_buffer) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[] >>
     Cases_on `compile_alloc_buffer (type_memory_size_list tvs) shadow_sa` >> gvs[]) >>
  `compile_struct_lit compile_expr (gas_shadow_env T cenv) (StructT (src_id_opt,id))
     (MAP (I ## gas_shadow_expr) kes) (Var q) 0 shadow_sm = (u,shadow_sb)` by
    (qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _`
       (strip_assume_tac o MATCH_MP compile_struct_literal_inv o
        REWRITE_RULE [gasShadowTheory.gas_shadow_expr_def]) >>
     gvs[] >> imp_res_tac exprOperandVarTheory.compiler_struct_lit_result >> gvs[]) >>
  `fn_has_code shadow_sm shadow_sb shadow_func` by
    (drule compile_alloc_buffer_extends >> strip_tac >>
     `cs_extends shadow_sm shadow_sb` by
       (mp_tac (Q.SPECL [`compile_expr`, `gas_shadow_env T cenv`, `StructT (src_id_opt,id)`,
          `MAP (I ## gas_shadow_expr) kes`, `Var q`, `0`, `shadow_sm`]
          ci_mono_compile_struct_lit_cfn) >> simp[ci_mono_def] >>
        (impl_tac >- (rpt gen_tac >> Cases_on `compile_expr cenv' ty' e' sa'` >>
          drule (cj 1 compile_expr_grows) >> simp[])) >> simp[]) >>
     drule_all fn_has_code_split >> simp[]) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `(!x sz. cenv.ce_return_buf = SOME(PtrVar(Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. cenv.ce_return_pc = SOME(PtrVar(Var x) sz) ==> not_fresh_at sm x)` by
    (fs[loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `return_buf_frame d cenv sm t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `s0`, `sa`] >>
     simp[] >> metis_tac[]) >>
  qabbrev_tac `inv' = (\H ee cs G tn s cells off.
    stmt_state_rel H ctx func cenv cx ee s /\
    storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s /\
    wb_frame cenv es ee sa s0 s /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    ~s.vs_halted /\ s.vs_current_bb = cs.cs_current_bb /\
    s.vs_inst_idx = LENGTH cs.cs_current_insts /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    not_fresh_at cs q /\ lookup_var q s = SOME (n2w (w2n w)) /\
    ptr_covers G tn q s (type_memory_size_list tvs) /\
    FLOOKUP s.vs_allocas sa.cs_next_id = SOME (w2n w,type_memory_size_list tvs) /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit(n2w (type_memory_size_list tvs))] [q])
      (fn_insts func) /\
    lo <= w2n w /\ w2n w+type_memory_size_list tvs < dimword(:256) /\
    sa.cs_next_id <= sa.cs_next_id /\ sa.cs_next_id < cs.cs_next_id /\
    sa.cs_next_var <= cs.cs_next_var /\ off <= type_memory_size_list tvs /\
    (!name p k. local_region cenv ee.scopes s name p k ==>
      w2n w+type_memory_size_list tvs <= p \/ p+k <= w2n w) /\
    (!name p k. local_region cenv es.scopes s0 name p k ==>
      w2n w+type_memory_size_list tvs <= p \/ p+k <= w2n w) /\
    (!old p k. FLOOKUP s0.vs_allocas old = SOME(p,k) /\ old < sa.cs_next_id ==>
      w2n w+type_memory_size_list tvs <= p \/ p+k <= w2n w) /\
    EVERY (\(tv,v,p,k). w2n w <= p /\ p+k <= w2n w+off) cells /\
    literal_prefix_ok cells tn s /\
    (~expr_has_effect (StructLit v7 (src_id_opt,id) kes) ==>
      pure_frame cenv func es sa s0 s))` >>
  pop_assum (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (qpat_assum `body_inv tops ctx cenv cx` (fn inv =>
       qpat_assum `MEM func ctx.ctx_functions` (fn member =>
         ACCEPT_TAC (MATCH_MP bodyFullIfExpReachTheory.body_inv_no_phi (CONJ inv member))))) >>
  `!fn inst s. frag_reachable ctx func t fn inst s ==> dalloca_fmp_headroom inst s` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s0,G0,tn0) [] (OK t,G,tn)` (qspec_then `DF (storage_trace_horizon es.storage_trace)` (fn path =>
       qpat_assum `!bb. MEM bb func.fn_blocks ==> _` (fn no_phi =>
       qpat_assum `!fn inst s. frag_reachable ctx func s0 fn inst s ==> _` (fn safe =>
         ACCEPT_TAC (MATCH_MP bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom
           (LIST_CONJ [path,no_phi,safe]))))))) >>
  `cx_tops cx = tops` by
    metis_tac[body_inv_main_code] >>
  `shadow_body_inv (cx_tops cx) ctx shadow_ctx` by simp[] >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cenv`, `cx`, `DF`, `lo`, `d`, `es`,
    `sa`, `s0`, `G0`, `tn0`, `~expr_has_effect (StructLit v7 (src_id_opt,id) kes)`,
    `q`, `w`, `tvs`, `inv'`, `shadow_ctx`, `shadow_func`, `PG`, `env`, `st0`,
    `(src_id_opt,id)`, `kes`,
    `MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields
      (nsid_to_string (src_id_opt,id)))`, `sm`, `sb`, `shadow_sm`, `shadow_sb`,
    `u`, `t`, `G`, `tn`]
    (INST_TYPE [alpha |-> ``:256``] structlit_allocated_fields_bundled_full)) >>
  (impl_tac >- (simp[expr_sim_full_code_def, expr_sim_full_endpoint_def,
                   GSYM CONJ_ASSOC] >> rpt conj_tac >>
    TRY (FIRST_ASSUM ACCEPT_TAC) >>
    TRY (qexists_tac `Hbase` >> FIRST_ASSUM ACCEPT_TAC) >>
    TRY (qpat_assum `ba.buf_operand = Var q` (fn eq =>
      qpat_assum `compile_struct_lit compile_expr cenv _ kes ba.buf_operand 0 sm = _`
        (ACCEPT_TAC o REWRITE_RULE [eq]))) >>
    TRY (irule structlit_list_admissible >>
      qexistsl_tac [`v7`, `(src_id_opt,id)`] >> first_assum ACCEPT_TAC) >>
    TRY (qpat_assum `type_memory_size_list tvs = _` (fn size =>
      PURE_REWRITE_TAC [GSYM (REWRITE_RULE [combinTheory.o_DEF] size)]) >>
      rpt gen_tac >> strip_tac >>
      FIRST [
        qpat_assum `!n p sz. local_region cenv es.scopes t n p sz ==> _` (drule_then strip_assume_tac),
        qpat_assum `!n p sz. local_region cenv es.scopes s0 n p sz ==> _` (drule_then strip_assume_tac),
        qpat_assum `!old p k. FLOOKUP s0.vs_allocas old = SOME (p,k) /\ _ ==> _` (drule_all_then strip_assume_tac)] >>
      decide_tac) >>
    simp[EVERY_MAP, combinTheory.o_DEF])) >>
  strip_tac >>
  drule_at Any gasOutcomeFullStmtsTheory.gas_outcome_full_zero_prefix >>
  disch_then (mp_tac o Q.INST [`s0'` |-> `s0`, `G0'` |-> `G0`, `tn0'` |-> `tn0`] o SPEC_ALL) >>
  (impl_tac >- (gen_tac >> first_x_assum (qspec_then `DF H` ACCEPT_TAC))) >>
  strip_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ (es,t,G,tn) _ _` kall_tac >>
  drule_at Any (INST_TYPE [alpha |-> ``:eval_result``] gas_outcome_full_source_map) >>
  disch_then (mp_tac o Q.INST
    [`source'` |-> `eval_expr cx (StructLit (StructT (src_id_opt,id)) (src_id_opt,id) kes)`,
     `f'` |-> `(\res. case res of INL vs => INL (Value (StructV (ZIP(MAP FST kes,vs)))) | INR exc => INR exc)`] o SPEC_ALL) >>
  (impl_tac >- (simp[] >> gen_tac >>
    Cases_on `eval_exprs cx (MAP SND kes) es'` >>
    drule aggregate_eval_struct >>
    disch_then (qspecl_then [`(src_id_opt,id)`, `StructT (src_id_opt,id)`] mp_tac) >> simp[])) >>
  strip_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ (eval_exprs _ _) _ _ _` kall_tac >>
  qpat_assum `v7 = StructT (src_id_opt,id)` SUBST_ALL_TAC >>
  irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
  goal_assum (drule_at Any) >>
  reverse conj_tac >- (rpt gen_tac >> simp[] >> strip_tac >> gvs[]) >>
  rpt gen_tac >> simp[] >> strip_tac >> gvs[] >>
  `LENGTH kes = LENGTH tvs` by
    (qpat_assum `LIST_REL (\t (name,e). _) _ kes`
       (mp_tac o MATCH_MP LIST_REL_LENGTH) >>
     drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]) >>
  `type_memory_bytes cenv (StructT (src_id_opt,id)) = type_memory_size_list tvs` by
    simp[compileEnvTheory.type_memory_bytes_def] >>
  `~expr_has_effect (StructLit (StructT (src_id_opt,id)) (src_id_opt,id) kes) ==>
     pure_frame cenv func es sa s0 t'` by
    simp[EVERY_MAP, combinTheory.o_DEF, GSYM EVERY_NOT_EXISTS] >>
  drule_at (Pat `wb_frame _ _ _ _ _ _`)
    (SIMP_RULE (srw_ss()) [] (INST_TYPE [alpha |-> ``:256``] structlit_endpoint_full_post)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `_.buf_operand = Var _`)) >>
  simp[] >>
  disch_then (qspecl_then [`vs`, `sb`, `G'`, `tn'`] mp_tac) >>
  (impl_tac >- (simp[] >>
    qpat_assum `!name p k. local_region cenv ee.scopes t' name p k ==> _` mp_tac >>
    simp[NoAsms, arithmeticTheory.ADD_COMM])) >> strip_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t'` by
    (qpat_assum `stmt_state_rel _ ctx func cenv cx ee t'`
      (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  simp[contextTheory.base_ptr_def, contextTheory.vv_location_def] >>
  simp[vv_own_def, post_value_type_def, expr_type_def,
    contextTheory.base_ptr_def, read_result_def, return_def,
    venomStateTheory.eval_operand_def] >>
  rpt strip_tac >> gvs[] >>
  disj1_tac >>
  qexistsl_tac [`sa.cs_next_id`, `w2n w`, `type_memory_size_list tvs`] >>
  simp[] >> conj_tac
  >- simp[val_footprint_def,
          valueEncodingTheory.type_memory_size_def, struct_layout_size_zip] >>
  rpt strip_tac >>
  qpat_x_assum `!name p k. local_region cenv ee.scopes t' name p k ==> _`
    (drule_then mp_tac) >> decide_tac

QED

Theorem structlit_expr_full_ok:
  !cx v7 src_id_opt id kes.
    (!ks. ks = MAP FST kes ==> body_exprs_full_ok cx (MAP SND kes)) ==>
    body_expr_full_ok cx (StructLit v7 (src_id_opt,id) kes)
Proof
  rpt gen_tac >> strip_tac >>
  `body_exprs_full_ok cx (MAP SND kes)` by
    (first_assum (qspec_then `MAP FST kes` mp_tac) >> simp[]) >>
  simp[body_expr_full_ok_def] >> rpt gen_tac >> strip_tac >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty (StructLit v7 (src_id_opt,id) kes) es` by
    (irule structlit_vv_sim_full >> metis_tac[]) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  irule expr_sim_full_of_vv >> simp[post_value_type_def] >>
  conj_tac
  >- (rpt strip_tac >> drule_all exprSimHypsTheory.expr_body_pre_copy_ok >> simp[]) >>
  qpat_assum `expr_body_pre _ _ _ (StructLit _ _ _) _`
    (mp_tac o MATCH_MP expr_body_pre_type_evaluates) >>
  simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  qexists_tac `x` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env (StructLit v7 (src_id_opt,id) kes)
     (es with gas_obs := gs)` by simp[] >>
  drule_all exprSimSourceTheory.expr_body_pre_runtime_typed >>
  strip_tac >> gvs[] >> metis_tac[]
QED
