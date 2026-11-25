(* Finish only the store, keeping the allocation reserved before unwrap. *)
Theory bodyCopiedArraySnapshotStoreMods
Ancestors
  bodyCopiedArrayCutDefsMods bodyFullExtCallDefaultCopy bodyLocalSnapshotResourcesMods
  exprSimIfExpWidenedCounted typedCopyOriginPtrBase exprSimPtrLiteralBuffer
  assignTuplePtrCopyLen bodyFullMemoryFrames bodyFullAllocaFresh exprLoweringProps
  exprSimProps exprSimWordArgs bodyFullShadowBodyInv fragGasOriginPtrLoop
  bodyFullUnwrapSlotPost stateRelProj typedMemoryCopy ptrDiscipline venomMemDefs
  allocaHistory venomState venomInst loweringStateRelDefs finite_map
  vyperState vyperStorageFootprint memoryStoreCode bodyBinopFragMemory
  stmtReasonLitFragMemory context loweringPosts stmtSimDefs bodyMemoryDefs compileEnv

Theorem copied_store_history[local]:
  compile_copy_memory dst src n l = ((),sc) /\ fn_has_code l sc fn /\
  alloca_history fn t /\ t.vs_current_bb = l.cs_current_bb /\
  t.vs_inst_idx = LENGTH l.cs_current_insts /\
  u.vs_allocas = t.vs_allocas /\ u.vs_current_bb = t.vs_current_bb /\
  u.vs_inst_idx = LENGTH sc.cs_current_insts ==>
  alloca_history fn u
Proof
  strip_tac >> drule_then strip_assume_tac compile_copy_memory_code >>
  `sc.cs_current_bb = l.cs_current_bb` by fs[same_blocks_def] >>
  drule_all_then (qx_choose_then `bb` strip_assume_tac) fn_has_code_code >>
  `?rest. DROP t.vs_inst_idx bb.bb_instructions = emitted_insts l sc ++ rest` by
    fs[rich_listTheory.IS_PREFIX_APPEND] >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts l sc)` by
    (Cases_on `n = 0` >> simp[mk_inst_def]) >>
  `u.vs_inst_idx = t.vs_inst_idx + LENGTH (emitted_insts l sc)` by simp[] >>
  `alloca_history fn (u with vs_inst_idx := t.vs_inst_idx + LENGTH (emitted_insts l sc))`
    suffices_by
      (qpat_assum `u.vs_inst_idx = t.vs_inst_idx + LENGTH _`
         (fn th => pure_rewrite_tac [SYM th]) >>
       `u with vs_inst_idx := u.vs_inst_idx = u` by simp[venom_state_component_equality] >>
       asm_rewrite_tac[]) >>
  irule alloca_history_no_alloca_slice >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexistsl [`bb`,`rest`] >> conj_tac
  >- first_assum ACCEPT_TAC >> simp[]
QED

Theorem copied_array_finish_snapshot_mods:
  cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\ mid.gas_obs = [] /\
  sm.cs_next_var <= l.cs_next_var /\
  copied_store_cut_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
    (st0,es,sa,s0,G0,tn0) (obj,mid,raw,saved,et,bd,atv)
    (sm,s,G,tn) (l,t,Gl,tl) (src,sw,sc,cvv) (q,w) ==>
  ?u Gc tc.
    copied_saved_cut_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
      (st0,es,sa,s0,G0,tn0) (obj,mid,raw,saved,et,bd,atv)
      (sm,s,G,tn) (sc,u,Gc,tc) cvv (q,w)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then (map_every assume_tac o CONJUNCTS) copied_store_cut_copy_inputs_mods >>
  drule_all extcall_default_copy_capacity_joint >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shctx`,`PG`]
    (qx_choosel_then [`u`,`Gc`,`tc`] strip_assume_tac)) >>
  qpat_x_assum `copied_store_cut_mods _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [copied_store_cut_mods_def]) >>
  qpat_x_assum `copied_parent_frame_mods _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [copied_parent_frame_mods_def]) >>
  qpat_x_assum `copied_snapshot_dest_mods _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [copied_snapshot_dest_mods_def]) >>
  `ci_mono l sc` by
    (qpat_assum `compile_store_memory _ _ _ _ _ _ = _`
       (SUBST1_TAC o SYM o REWRITE_RULE [pairTheory.SND] o
        AP_TERM ``SND : unit # compile_state -> compile_state``) >>
     MATCH_ACCEPT_TAC ci_mono_compile_store_memory) >>
  suspend "machine"
QED

Resume copied_array_finish_snapshot_mods[machine]:
  markerLib.RESUME_TAC >>
  `l.cs_next_var <= sc.cs_next_var /\ l.cs_next_id <= sc.cs_next_id` by fs[ci_mono_def] >>
  `sa.cs_next_var <= l.cs_next_var` by decide_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at l x` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC freshWritesTheory.not_fresh_at_mono) >>
  `!x. not_fresh_at sm x ==> not_fresh_at l x` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC freshWritesTheory.not_fresh_at_mono) >>
  qhdtm_assum `typed_copy_state_frame`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [typed_copy_state_frame_def,venom_state_component_equality]) >>
  `!name b len. local_region ce mid.scopes u name b len <=>
      local_region ce mid.scopes t name b len` by
    (irule literal_ptr_local_region_frame >> qexists `l` >> simp[]) >>
  `!off len. off+len <= w2n w \/ w2n w+type_memory_size atv <= off ==>
    mem_bytes_at off len u.vs_memory = mem_bytes_at off len t.vs_memory` by
    (qhdtm_assum `typed_copy_frame`
       (strip_assume_tac o REWRITE_RULE [typed_copy_frame_def]) >>
     rpt gen_tac >> disch_tac >>
     qpat_assum `!a n. _ ==> mem_bytes_at a n u.vs_memory = _` irule >>
     first_assum ACCEPT_TAC) >>
  suspend "path_and_history"
QED

Resume copied_array_finish_snapshot_mods[path_and_history]:
  markerLib.RESUME_TAC >>
  `!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shctx,ctx,fn,PG)
       (s,G,tn) [] (OK u,Gc,tc)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl [`Gl`,`t`,`tl`] >>
     conj_tac
     >- (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK t,Gl,tl)`
          (qspec_then `D` ACCEPT_TAC)) >>
     qpat_assum `!D. gas_origin_ptr_path _ (t,Gl,tl) [] (OK u,Gc,tc)`
       (qspec_then `D` ACCEPT_TAC)) >>
  qhdtm_assum `copied_cursor_mods`
    (strip_assume_tac o REWRITE_RULE [copied_cursor_mods_def]) >>
  `compile_copy_memory (Var q) src (type_memory_size atv) l = ((),sc)` by
    fs[compile_store_memory_def] >>
  `alloca_history fn u` by
    (irule copied_store_history >> goal_assum (drule_at Any) >> simp[] >>
     qexists `t` >> simp[]) >>
  `allocas_from lo u` by
    (qpat_assum `u.vs_allocas = t.vs_allocas`
       (fn th => pure_rewrite_tac [allocas_from_def,th]) >>
     qpat_assum `allocas_from lo t` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (drule_then SUBST1_TAC typed_copy_state_frame_allocas_below_fmp >> simp[]) >>
  `not_fresh_at sc q` by drule_all_then ACCEPT_TAC freshWritesTheory.not_fresh_at_mono >>
  `ptr_covers Gc tc q u (type_memory_size atv)` by
    (irule ptr_covers_lookup_frame >> qexistsl [`Gl`,`t`,`tl`] >> simp[]) >>
  suspend "resources"
QED

Resume copied_array_finish_snapshot_mods[resources]:
  markerLib.RESUME_TAC >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `alloca_inv t` by
    (drule_at (Pat `stmt_state_rel _ _ _ _ _ mid t`) stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `!aid b len. aid < sa.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,len) ==>
       loweringStateRelDefs$regions_disjoint (w2n w) (type_memory_size atv) b len` by
    (rpt gen_tac >> strip_tac >>
     `sm.cs_next_id <> aid` by decide_tac >>
     qpat_assum `alloca_inv t`
       (strip_assume_tac o REWRITE_RULE [alloca_inv_def]) >>
     qpat_assum `allocas_non_overlapping t`
       (mp_tac o REWRITE_RULE [allocas_non_overlapping_def]) >>
     disch_then (qspecl_then [`sm.cs_next_id`,`aid`] mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  suspend "region_frames"
QED

Resume copied_array_finish_snapshot_mods[region_frames]:
  markerLib.RESUME_TAC >>
  qabbrev_tac `di = mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_size atv))] [q]` >>
  `MEM di (fn_insts fn) /\ di.inst_opcode = ALLOCA /\
   di.inst_id = sm.cs_next_id` by simp[Abbr `di`,mk_inst_def] >>
  `MEM di (fn_insts fn)` by simp[Abbr `di`] >>
  `FLOOKUP u.vs_allocas di.inst_id = SOME (w2n w,type_memory_size atv)` by simp[] >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x t /\
      FLOOKUP Gc x = FLOOKUP Gl x /\ op_taint tc (Var x) = op_taint tl (Var x)` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at l x` (drule_then assume_tac) >>
     qpat_assum `!x. not_fresh_at l x ==> _ /\ _ /\ _` (drule_then ACCEPT_TAC)) >>
  drule_at_then (Pat `stmt_state_rel _ _ _ _ _ _ _`)
    (drule_at_then (Pat `typed_copy_frame _ _ _ _`)
      (drule_at_then (Pat `FLOOKUP _ _.inst_id = SOME _`)
        (drule_at_then (Pat `_.t_stor = _.t_stor`)
          (drule_at_then (Pat `allocas_from _ _`)
            (qspecl_then [`sa`,`Gc`,`Gl`] mp_tac)))))
    local_snapshot_resources_mods >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[]])) >>
  strip_tac >> suspend "horizon"
QED

Resume copied_array_finish_snapshot_mods[horizon]:
  markerLib.RESUME_TAC >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx fn ce cx es s0 /\ stmt_state_rel H ctx fn ce cx mid u /\
     immutable_frame_mods fn ce cx mid u /\ storage_well_formed_on cx mid (FST H) /\
     ghost_inv_at_mods (DF H) lo d ce cx mid Gc tc u` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >>
     `stmt_state_rel H ctx fn ce cx mid u` by
       (irule typed_copy_semantic_frame >>
        goal_assum (drule_at (Pat `typed_copy_state_frame _ _ _ _ _`)) >>
        qexists `di` >> simp[] >>
        qpat_assum `!n b len. local_region ce mid.scopes t n b len ==> _`
          (mp_tac o REWRITE_RULE [loweringStateRelDefsTheory.regions_disjoint_def]) >> simp[]) >>
     `ghost_inv_at_mods (DF H) lo d ce cx mid Gc tc u` by
       (qpat_assum `!D d. ghost_inv_at_mods D lo d ce cx mid Gl tl t ==> _`
          (drule_then ACCEPT_TAC)) >>
     simp[]) >>
  `!name b len. local_region ce mid.scopes t name b len ==>
       mem_bytes_at b len u.vs_memory = mem_bytes_at b len t.vs_memory` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!off len. _ ==> mem_bytes_at off len u.vs_memory = _` irule >>
     qpat_assum `!n b len. local_region ce mid.scopes t n b len ==> _`
        (drule_then (ACCEPT_TAC o ONCE_REWRITE_RULE [DISJ_COMM] o
                       REWRITE_RULE [loweringStateRelDefsTheory.regions_disjoint_def]))) >>
  suspend "caller"
QED

Resume copied_array_finish_snapshot_mods[caller]:
  markerLib.RESUME_TAC >>
  `wb_frame ce mid mid sa t u` by
    (pure_rewrite_tac[wb_frame_def] >> rpt conj_tac
     >- (rpt gen_tac >> strip_tac >>
         qpat_assum `!x. not_fresh_at sa x ==> _ /\ _ /\ _` (drule_then strip_assume_tac) >> simp[])
     >- simp[]
     >- (rpt gen_tac >> strip_tac >>
         qpat_assum `alloca_frame ce mid sa t ce mid u`
           (drule_all_then (ACCEPT_TAC o CONJUNCT1) o REWRITE_RULE [alloca_frame_def])) >>
     irule locals_kept_regions >> first_assum ACCEPT_TAC) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (qpat_assum `wb_frame ce es mid sa s0 t`
       (strip_assume_tac o REWRITE_RULE [wb_frame_def,locals_kept_def]) >> simp[]) >>
  `wb_frame ce es mid sa s0 u` by
    (irule (INST_TYPE [alpha |-> ``:256``] wb_frame_trans) >> simp[] >> conj_tac
     >- (qexistsl [`mid`,`sa`,`t`] >> simp[]) >>
     qexistsl [`storage_trace_horizon mid.storage_trace`,`ctx`,`cx`,`fn`] >> simp[]) >>
  `!n b len. local_region ce es.scopes s0 n b len ==> local_region ce mid.scopes t n b len` by
    (rpt gen_tac >> disch_tac >> irule local_region_frame_fwd >>
     qexistsl [`s0`,`sa`,`es.scopes`] >> simp[] >>
     qpat_assum `wb_frame ce es mid sa s0 t`
       (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >> first_assum ACCEPT_TAC) >>
  suspend "ghost_and_pure"
QED

Resume copied_array_finish_snapshot_mods[ghost_and_pure]:
  markerLib.RESUME_TAC >>
  `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id ==>
       loweringStateRelDefs$regions_disjoint (w2n w) (type_memory_size atv) off sz` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `wb_frame ce es mid sa s0 t`
       (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
     qpat_assum `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> _` (drule_then assume_tac) >>
     qpat_assum `!aid b len. aid < sa.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,len) ==> _`
       (drule_all_then ACCEPT_TAC)) >>
  `!off sz i. loweringStateRelDefs$regions_disjoint (w2n w) (type_memory_size atv) off sz /\
      off <= i /\ i < off + sz /\ i IN tc.t_mem ==> i IN tl.t_mem` by
    (rpt gen_tac >> simp[loweringStateRelDefsTheory.regions_disjoint_def] >> strip_tac >>
     `~(w2n w <= i /\ i < w2n w + type_memory_size atv)` by decide_tac >>
     qpat_assum `!i. ~(w2n w <= i /\ _) ==> _` (drule_then (SUBST1_TAC o SYM)) >> simp[]) >>
  `ghost_kept_at lo ce es sa G0 tn0 s0 Gc tc` by
    (irule unwrap_slot_copy_ghost_kept_at >> qexistsl [`Gl`,`tl`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (rpt gen_tac >> strip_tac >>
         qpat_assum `!n b len. local_region ce es.scopes s0 n b len ==> _` (drule_then assume_tac) >>
         qpat_assum `!n b len. local_region ce mid.scopes t n b len ==> regions_disjoint _ _ _ _`
           (drule_then assume_tac) >>
         qpat_assum `!off sz i. regions_disjoint _ _ off sz /\ _ ==> _` (drule_all_then ACCEPT_TAC))
     >- (rpt gen_tac >> disch_tac >>
         qpat_assum `!x. not_fresh_at sa x ==> _ /\ _ /\ _` (drule_then strip_assume_tac) >> simp[])
     >- (rpt gen_tac >> strip_tac >>
         qpat_assum `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ _ ==> _`
           (drule_all_then assume_tac) >>
         qpat_assum `!off sz i. regions_disjoint _ _ off sz /\ _ ==> _` (drule_all_then ACCEPT_TAC)) >>
     rpt gen_tac >> strip_tac >>
     qpat_assum `!i. i < lo ==> (i IN tc.t_mem <=> i IN tl.t_mem)`
       (drule_then (SUBST1_TAC o SYM)) >> simp[]) >>
  `~expr_has_effect obj ==> pure_frame ce fn es sa s0 u` by
    (disch_tac >> irule pure_frame_trans >> simp[] >> qexistsl [`mid`,`sa`,`t`] >> simp[] >>
     conj_tac
     >- (qpat_assum `wb_frame ce es mid sa s0 t`
           (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >> first_assum ACCEPT_TAC) >>
     pure_rewrite_tac[pure_frame_def] >> conj_tac >- first_assum ACCEPT_TAC >>
     rpt gen_tac >> strip_tac >>
     qpat_assum `!off len. _ ==> mem_bytes_at off len u.vs_memory = _` irule >>
     qpat_assum `!inst b sz. _ ==> regions_disjoint _ _ _ _`
        (qspec_then `di` mp_tac) >> simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  suspend "finish"
QED

Resume copied_array_finish_snapshot_mods[finish]:
  markerLib.RESUME_TAC >>
  `return_buf_frame d ce sc u` by
    (irule return_buf_frame_frame >> qexistsl [`ce`,`t`,`l`] >> simp[] >>
     rpt gen_tac >> strip_tac >>
     qpat_assum `!x. not_fresh_at l x ==> lookup_var x u = _` (drule_then SUBST1_TAC) >> simp[]) >>
  `local_ptrs_reserved ce sc` by
    (irule local_ptrs_reserved_next_var >> qexists `l` >> simp[]) >>
  `cs_extends sm sc` by (irule cs_extends_trans >> qexists `l` >> simp[]) >>
  `sm.cs_next_id < sc.cs_next_id` by decide_tac >>
  `copied_base_frame_mods sm (s,G,tn) (u,Gc,tc)` by
    (qpat_assum `copied_base_frame_mods sm (s,G,tn) _`
       (strip_assume_tac o REWRITE_RULE [copied_base_frame_mods_def]) >>
     simp[copied_base_frame_mods_def] >> gen_tac >> disch_tac >>
     qpat_assum `!x. not_fresh_at sm x ==> not_fresh_at l x` (drule_then assume_tac) >>
     qpat_assum `!x. not_fresh_at sm x ==> lookup_var x t = _ /\ _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at l x ==> lookup_var x u = _ /\ _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `vv_own ce cx (ArrayT et bd) sm sc mid (Value saved) cvv u` by
    (simp[vv_own_def,mk_ptr_def,read_result_def,vyperStateTheory.return_def,eval_operand_def] >>
     disj1_tac >> qexists `sm.cs_next_id` >> simp[] >> conj_tac
     >- (drule val_footprint_le >> simp[]) >>
     rpt gen_tac >> disch_tac >>
     qpat_assum `!n b len. local_region ce mid.scopes t n b len ==> regions_disjoint _ _ _ _`
       (drule_then (mp_tac o REWRITE_RULE [loweringStateRelDefsTheory.regions_disjoint_def])) >>
     simp[arithmeticTheory.ADD_COMM]) >>
  qexistsl [`u`,`Gc`,`tc`] >>
  simp[copied_saved_cut_mods_def,copied_cursor_mods_def,copied_parent_frame_mods_def,
       copied_snapshot_dest_mods_def,Abbr `di`] >>
  conj_tac
  >- (qpat_assum `t.vs_current_bb = l.cs_current_bb` (SUBST1_TAC o SYM) >>
      qpat_assum `u.vs_current_bb = t.vs_current_bb` (SUBST1_TAC o SYM) >>
      first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED

Finalise copied_array_finish_snapshot_mods
