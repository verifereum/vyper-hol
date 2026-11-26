(* Rebase the registered proxy window and its linked landing to the call entry. *)
Theory bodyCreateProxyWindowRebaseMods
Ancestors
  bodyCreateProxyWindowMods bodyFullIfExpReach bodyFullShadowBodyInv
  stateRelProj abiEncodeOwnership instMemFrontier exprSimWordArgs
  exprLoweringProps loweringPosts loweringShapeDefs bodyMemoryDefs
  bodyPtrDefs ptrDiscipline reasonCopySourcePtr fragExec fragGasOriginPtr
  builtinCreate compileEnv vyperCreate vyperStorageFootprint
  venomState venomMemDefs venomExecSemantics venomInst words finite_map list

Theorem create_proxy_window_rebase_mods:
  compile_create_proxy_buf x b = (buf,c) /\
  fn_has_code b c func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= b.cs_next_var /\ sa.cs_next_id <= b.cs_next_id /\
  (!z n. cenv.ce_return_buf = SOME (PtrVar (Var z) n) ==> not_fresh_at b z) /\
  (!z n. cenv.ce_return_pc = SOME (PtrVar (Var z) n) ==> not_fresh_at b z) /\
  ~m.vs_halted /\ m.vs_current_bb = b.cs_current_bb /\
  m.vs_inst_idx = LENGTH b.cs_current_insts /\ alloca_history func m /\
  return_buf_frame d cenv b m /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!fn i z. frag_reachable ctx func m fn i z ==> dalloca_fmp_headroom i z) /\
  eval_operand x m = SOME tw /\ op_taint tm x = {} /\
  (!z. x = Var z ==> not_fresh_at b z) /\
  eval_operand y m = SOME aw /\ op_taint tm y = {} /\
  (!z. y = Var z ==> not_fresh_at b z) /\ (!l. y <> Label l) /\
  wb_frame cenv es ea sa s0 m /\ ghost_kept_at lo cenv es sa G0 tn0 s0 Gm tm /\
  s0.vs_alloca_next <= m.vs_alloca_next /\ storage_trace_domain cx st0 ea.storage_trace /\
  (!H. valid_horizon cx st0 H ea.storage_trace ==> valid_horizon cx st0 H es.storage_trace) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
  (!H. valid_horizon cx st0 H ea.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ea m /\ immutable_frame_mods func cenv cx ea m /\
    storage_well_formed_on cx ea (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ea Gm tm m) ==>
  ?p w u Gu tu.
    buf = Var p /\ not_fresh_at c p /\ b.cs_next_id < c.cs_next_id /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (m,Gm,tm) [] (OK u,Gu,tu)) /\
    ~u.vs_halted /\ u.vs_current_bb = c.cs_current_bb /\
    u.vs_inst_idx = LENGTH c.cs_current_insts /\ alloca_history func u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    s0.vs_alloca_next <= u.vs_alloca_next /\
    w2n w + 96 <= u.vs_alloca_next /\
    lookup_var p u = SOME w /\ ptr_covers Gu tu p u 96 /\ ptr_covers Gu tu p u 54 /\
    op_taint tu (Var p) = {} /\
    FLOOKUP u.vs_allocas b.cs_next_id = SOME (w2n w,96) /\
    (!name base n. local_region cenv ea.scopes u name base n ==>
                   regions_disjoint (w2n w) 96 base n) /\
    read_memory (w2n w) 54 u = minimal_proxy_initcode (w2w tw) /\
    (!i. w2n w <= i /\ i < w2n w + 54 ==> i NOTIN tu.t_mem) /\
    eval_operand y u = SOME aw /\ op_taint tu y = {} /\
    (!z. y = Var z ==> not_fresh_at c z) /\
    local_ptrs_reserved cenv c /\ sa.cs_next_var <= c.cs_next_var /\ sa.cs_next_id <= c.cs_next_id /\
    (!z n. cenv.ce_return_buf = SOME (PtrVar (Var z) n) ==> not_fresh_at c z) /\
    (!z n. cenv.ce_return_pc = SOME (PtrVar (Var z) n) ==> not_fresh_at c z) /\
    return_buf_frame d cenv c u /\
    (!fn i z. frag_reachable ctx func u fn i z ==> dalloca_fmp_headroom i z) /\
    wb_frame cenv es ea sa s0 u /\ ghost_kept_at lo cenv es sa G0 tn0 s0 Gu tu /\
    (!H. valid_horizon cx st0 H ea.storage_trace ==>
      stmt_state_rel H ctx func cenv cx ea u /\ immutable_frame_mods func cenv cx ea u /\
      storage_well_formed_on cx ea (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ea Gu tu u)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ea.storage_trace) ea.storage_trace` by
    fs[storage_trace_domain_def] >>
  `stmt_state_rel (storage_trace_horizon ea.storage_trace) ctx func cenv cx es s0` by
    (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _`
       irule >> first_assum (drule_then ACCEPT_TAC)) >>
  qpat_assum `!H. valid_horizon _ _ H ea.storage_trace ==> stmt_state_rel _ _ _ _ _ _ m /\ _`
    (drule_then strip_assume_tac) >>
  `allocas_from lo m /\ lo <= m.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `local_ptrs_reserved cenv b` by drule_all_then ACCEPT_TAC local_ptrs_reserved_next_var >>
  drule_all create_proxy_window_mods >>
  disch_then (qspecl_then [`explicit`,`PG`,`Gm`]
    (qx_choosel_then [`p`,`w`,`u`,`Gu`,`tu`] strip_assume_tac)) >>
  qexistsl_tac [`p`,`w`,`u`,`Gu`,`tu`] >>
  suspend "entry"
QED

Resume create_proxy_window_rebase_mods[entry]:
  `b.cs_next_var <= c.cs_next_var /\ b.cs_next_id <= c.cs_next_id` by
    (qspecl_then [`x`,`b`] mp_tac ci_mono_compile_create_proxy_buf >> simp[ci_mono_def]) >>
  `sa.cs_next_var <= c.cs_next_var /\ sa.cs_next_id <= c.cs_next_id` by decide_tac >>
  `local_ptrs_reserved cenv c` by drule_all_then ACCEPT_TAC local_ptrs_reserved_next_var >>
  `!z. not_fresh_at b z ==> not_fresh_at c z` by metis_tac[not_fresh_at_mono] >>
  `return_buf_frame d cenv c u` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`m`,`b`] >> simp[]) >>
  `eval_operand y u = SOME aw /\ op_taint tu y = {}` by
    (Cases_on `y` >> fs[eval_operand_def,op_taint_def]) >>
  `ptr_covers Gu tu p u 54` by (irule ptr_covers_mono >> qexists_tac `96` >> simp[]) >>
  `op_taint tu (Var p) = {}` by fs[ptr_covers_def] >>
  `!fn i z. frag_reachable ctx func u fn i z ==> dalloca_fmp_headroom i z` by
    (qpat_assum `!D. gas_origin_ptr_path _ (m,Gm,tm) [] (OK u,Gu,tu)`
       (qspec_then `DF (storage_trace_horizon ea.storage_trace)` assume_tac) >>
     rpt gen_tac >> disch_tac >>
     irule gas_origin_ptr_path_dalloca_fmp_headroom >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  suspend "root_frames"
QED

Resume create_proxy_window_rebase_mods[root_frames]:
  `MAP FDOM es.scopes = MAP FDOM ea.scopes` by fs[wb_frame_def,locals_kept_def] >>
  `wb_frame cenv es ea sa s0 u` by
    (irule (INST_TYPE [alpha |-> ``:256``] wb_frame_trans) >>
     asm_rewrite_tac[] >> conj_tac
     >- (qexistsl_tac [`ea`,`b`,`m`] >> asm_rewrite_tac[]) >>
     qexistsl_tac [`storage_trace_horizon ea.storage_trace`,`ctx`,`cx`,`func`] >>
     first_assum ACCEPT_TAC) >>
  `alloca_next_valid s0` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ es s0`
       (mp_then Any mp_tac stmt_state_rel_local_ptrs_alloca) >> simp[alloca_inv_def]) >>
  `!aid base n. FLOOKUP s0.vs_allocas aid = SOME (base,n) ==> base+n <= s0.vs_alloca_next` by
    (rpt gen_tac >> strip_tac >> irule alloca_region_below_frontier >>
     asm_rewrite_tac[] >> goal_assum (drule_at Any) >> simp[]) >>
  `!name base n. local_region cenv es.scopes s0 name base n ==> base+n <= s0.vs_alloca_next` by
    (rpt gen_tac >> strip_tac >> drule_all_then ACCEPT_TAC abi_encode_local_region_frontier) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gu tu` by
    (qpat_assum `!sk es0 G0 tn0 s0. _ ==> ghost_kept_at _ _ _ _ _ _ _ Gu tu` irule >>
     asm_rewrite_tac[] >> conj_tac >> rpt gen_tac >> strip_tac >>
     first_assum (drule_then assume_tac) >> decide_tac) >>
  suspend "finish"
QED

Resume create_proxy_window_rebase_mods[finish]:
  `!H. valid_horizon cx st0 H ea.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ea u /\ immutable_frame_mods func cenv cx ea u /\
    storage_well_formed_on cx ea (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ea Gu tu u` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H ea.storage_trace ==> stmt_state_rel _ _ _ _ _ _ m /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!D d. ghost_inv_at_mods D lo d cenv cx ea Gm tm m /\ _ ==> _`
       (drule_all_then strip_assume_tac) >> simp[]) >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by decide_tac >>
  asm_rewrite_tac[] >> rpt conj_tac >> rpt gen_tac >> disch_tac >>
  qpat_assum `!z. not_fresh_at b z ==> not_fresh_at c z` irule >>
  metis_tac[]
QED

Finalise create_proxy_window_rebase_mods
