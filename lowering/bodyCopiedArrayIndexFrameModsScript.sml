(* The destination of a forced snapshot is already old at the index cut. *)
Theory bodyCopiedArrayIndexFrameMods
Ancestors
  bodyCopiedArrayCutDefsMods bodyFullBuiltinConcatScratch
  bodyPtrBytestringBuiltinsWindowGhost wordArgsPtr exprSimWordArgs
  exprSimProps exprLoweringProps freshWrites vyperStorageFootprint
  vyperEvalExprPreservesScopesDom bodyPtrDefs bodyFullPostsMods loweringPosts
  compileEnv exprLowering bodyFullShadowBodyInv bodyMemoryDefs venomState
  vyperState vyperInterpreter vyperAST finite_map pair vyperStorageTrace

Theorem copied_index_dest_mods[local]:
  copied_snapshot_dest_mods fn ce lo mid sm (sc,u,Gc,tc) (q,w) (type_memory_size atv) /\
  expr_post H ctx fn ce cx idx mid sc si u fin key iop z /\
  ghost_kept_at lo ce mid sc Gc tc u Gi ti /\
  (!name b len. local_region ce mid.scopes u name b len <=>
                local_region ce fin.scopes z name b len) /\
  sc.cs_next_id <= si.cs_next_id /\ sc.cs_next_var <= si.cs_next_var /\
  u.vs_alloca_next <= z.vs_alloca_next /\ val_wf atv saved /\
  (!m. mem_agree_outside tc.t_mem u.vs_memory m ==> val_in_memory atv saved (w2n w) m) ==>
  copied_snapshot_dest_mods fn ce lo fin sm (si,z,Gi,ti) (q,w) (type_memory_size atv) /\
  (!m. mem_agree_outside ti.t_mem z.vs_memory m ==> val_in_memory atv saved (w2n w) m)
Proof
  simp[copied_snapshot_dest_mods_def] >> strip_tac >>
  drule_all_then strip_assume_tac (SRULE [GSYM loweringStateRelDefsTheory.regions_disjoint_def]
    concat_scratch_child_frame) >>
  `lookup_var q z = SOME w` by (first_assum irule >> simp[]) >>
  `ptr_covers Gi ti q z (type_memory_size atv)` by
    (qpat_x_assum `ptr_covers Gc _ _ _ _` mp_tac >>
     simp[ptr_covers_def]) >>
  `sm.cs_next_id < si.cs_next_id /\
   type_memory_size atv + w2n w <= z.vs_alloca_next` by decide_tac >>
  `not_fresh_at si q` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists `sc` >> simp[]) >>
  conj_tac
  >- (simp[] >>
      qpat_x_assum `!name b len. local_region ce mid.scopes u name b len <=> _`
        (pure_once_rewrite_tac o single o GSYM) >> first_assum ACCEPT_TAC) >>
  rpt strip_tac >> irule robust_val_in_memory_window_transport >>
  conj_tac >- first_assum ACCEPT_TAC >> qexistsl_tac [`tc.t_mem`,`ti.t_mem`,`type_memory_size atv`,`u.vs_memory`,`z.vs_memory`] >>
  simp[val_footprint_le]
QED

Theorem copied_index_dest_own_mods[local]:
  copied_snapshot_dest_mods fn ce lo fin sm (si,z,Gi,ti) (q,w) (type_memory_size atv) /\
  sm.cs_next_id < sc.cs_next_id /\ val_wf atv saved /\
  evaluate_type (get_tenv cx) ty = SOME atv ==>
  vv_own ce cx ty sm sc fin (Value saved) (LocatedValue ty (mk_ptr (Var q) LocMemory)) z
Proof
  simp[copied_snapshot_dest_mods_def, vv_own_def, contextTheory.mk_ptr_def,
       venomStateTheory.eval_operand_def, vyperStateTheory.read_result_def,
       vyperStateTheory.return_def, loweringStateRelDefsTheory.regions_disjoint_def] >>
  strip_tac >> disj1_tac >> qexistsl_tac [`sm.cs_next_id`,`w2n w`,`type_memory_size atv`] >>
  simp[val_footprint_le] >> first_assum ACCEPT_TAC
QED

Theorem copied_index_parent_mods[local]:
  copied_parent_frame_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
    (st0,es,sa,s0,G0,tn0) mid obj (sc,u,Gc,tc) /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id /\
  sc.cs_next_var <= si.cs_next_var /\ u.vs_alloca_next <= z.vs_alloca_next /\
  storage_trace_domain cx st0 fin.storage_trace /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==> valid_horizon cx st0 H mid.storage_trace) /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
    expr_post_mods H ctx fn ce cx idx mid sc si u fin key iop z /\
    ghost_inv_at_mods (DF H) lo d ce cx fin Gi ti z) /\
  ghost_kept_at lo ce mid sc Gc tc u Gi ti ==>
  copied_parent_frame_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
    (st0,es,sa,s0,G0,tn0) fin (Subscript ann obj idx) (si,z,Gi,ti)
Proof
  simp[copied_parent_frame_mods_def] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
    fs[storage_trace_domain_def] >>
  `valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) mid.storage_trace` by simp[] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then (strip_assume_tac o REWRITE_RULE [expr_post_mods_def])) >>
  drule_then assume_tac expr_post_frame >>
  drule_all_then assume_tac wb_frame_local_regions >>
  rpt conj_tac
  >- (gen_tac >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _` (drule_then strip_assume_tac) >>
      qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
        (drule_then (strip_assume_tac o REWRITE_RULE [expr_post_mods_def,expr_post_def])) >> simp[])
  >- (irule local_ptrs_reserved_next_var >> qexists `sc` >> simp[])
  >- (irule return_buf_frame_frame >> qexistsl_tac [`ce`,`u`,`sc`] >>
      simp[] >> rpt strip_tac >> irule wb_frame_vars >>
      rpt (goal_assum (drule_at Any)))
  >- (irule ghost_kept_at_trans >> qexistsl_tac [`Gc`,`mid`,`u`,`sc`,`tc`] >>
      fs[wb_frame_def])
  >- (irule (INST_TYPE [alpha |-> ``:256``] wb_frame_trans) >> simp[] >> conj_tac
      >- (qexistsl_tac [`mid`,`sc`,`u`] >> simp[]) >>
      qexistsl_tac [`storage_trace_horizon fin.storage_trace`,`ctx`,`cx`,`fn`] >> simp[]) >>
  simp[] >> strip_tac >> irule pure_frame_trans >> simp[] >>
  qexistsl_tac [`mid`,`sc`,`u`] >> simp[] >>
  drule_all_then assume_tac expr_post_pure_frame >> fs[wb_frame_def]
QED

Theorem copied_array_hold_index_mods:
  copied_saved_cut_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
    (st0,es,sa,s0,G0,tn0) (obj,mid,raw,saved,et,bd,atv)
    (sm,s,G,tn) (sc,u,Gc,tc) cvv (q,w) /\
  eval_expr cx obj (es with gas_obs := xs) = (INL raw,mid) /\
  bind (eval_expr cx idx) (read_result cx) (mid with gas_obs := ys) = (INL key,fin) /\
  compile_expr ce ty obj sa = (bvv,sm) /\
  compile_snapshot_vv ce T bvv sm = (cvv,sc) /\
  lower_value compile_expr ce ty idx sc = (iop,si) /\
  vv = LocatedValue ann (mk_ptr dst LocMemory) /\
  compile_array_subscript (Var q) iop
    (case bd of Fixed _ => F | Dynamic _ => T)
    (case bd of Fixed n => n | Dynamic _ => 0)
    (word_scale LocMemory) (elem_size_in_location ce LocMemory et)
    (is_signed_type (expr_type idx))
    (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca LocMemory) si = (dst,sb) /\
  cs_extends si sb /\ fn_has_code si sb fn /\ fn_inst_ids_distinct fn /\
  storage_trace_domain cx st0 fin.storage_trace /\ fin.gas_obs = [] /\ ~z.vs_halted /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
    expr_post_mods H ctx fn ce cx idx mid sc si u fin key iop z /\
    ghost_inv_at_mods (DF H) lo d ce cx fin Gi ti z /\
    ptr_val_ok cx (post_value_type ce idx) key iop Gi ti z /\
    z.vs_current_bb = si.cs_current_bb /\ z.vs_inst_idx = LENGTH si.cs_current_insts /\
    alloca_history fn z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    u.vs_alloca_next <= z.vs_alloca_next /\ ghost_kept_at lo ce mid sc Gc tc u Gi ti) ==>
  copied_select_cut_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
    (st0,es,sa,s0,G0,tn0) (obj,mid,raw,saved,et,bd,atv)
    (ann,idx,fin,key,iop,dst,vv) (sm,sc,cvv) (si,z,Gi,ti) sb (q,w)
Proof
  strip_tac >>
  qpat_assum `copied_saved_cut_mods _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [copied_saved_cut_mods_def]) >>
  drule_then strip_assume_tac (cj 1 compile_expr_grows) >>
  drule_then strip_assume_tac (cj 2 compile_expr_grows) >>
  `sm.cs_next_var <= sc.cs_next_var /\ sm.cs_next_id <= sc.cs_next_id` by
    (qspecl_then [`ce`,`T`,`bvv`,`sm`] mp_tac ci_mono_compile_snapshot_vv >> simp[ci_mono_def]) >>
  `sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id` by decide_tac >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >> simp[]) >>
  `MAP FDOM mid.scopes = MAP FDOM fin.scopes` by
    (drule (SRULE [SF ETA_ss] forced_eval_expr_preserves_scopes_dom) >> simp[]) >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==> valid_horizon cx st0 H mid.storage_trace` by
    (gen_tac >> strip_tac >>
     qpat_assum `bind (eval_expr _ idx) _ _ = _`
       (mp_then (Pat `_ = _`) mp_tac valid_horizon_frame) >>
     simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,storage_trace_frame_read_result]) >>
  qabbrev_tac `H0 = storage_trace_horizon fin.storage_trace` >>
  `valid_horizon cx st0 H0 fin.storage_trace` by fs[storage_trace_domain_def,Abbr `H0`] >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then (strip_assume_tac o REWRITE_RULE [expr_post_mods_def])) >>
  `copied_parent_frame_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
     (st0,es,sa,s0,G0,tn0) fin (Subscript ann obj idx) (si,z,Gi,ti)` by
    (irule copied_index_parent_mods >>
     rpt (goal_assum (drule_at Any)) >> simp[] >>
     qexistsl_tac [`iop`,`key`] >>
     gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  drule_then strip_assume_tac copied_saved_cut_index_entry_mods >>
  `stmt_state_rel H0 ctx fn ce cx mid u` by simp[] >>
  drule_then assume_tac expr_post_frame >>
  drule_all_then assume_tac wb_frame_local_regions >>
  qpat_assum `copied_array_type_mods _ _ _` (strip_assume_tac o REWRITE_RULE [copied_array_type_mods_def]) >>
  `copied_snapshot_dest_mods fn ce lo fin sm (si,z,Gi,ti) (q,w) (type_memory_size atv) /\
   (!m. mem_agree_outside ti.t_mem z.vs_memory m ==> val_in_memory atv saved (w2n w) m)` by
    (drule_all_then ACCEPT_TAC copied_index_dest_mods) >>
  `sm.cs_next_id < sc.cs_next_id` by fs[copied_snapshot_dest_mods_def] >>
  `vv_own ce cx (ArrayT et bd) sm sc fin (Value saved) cvv z` by
    (simp[] >> irule copied_index_dest_own_mods >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  simp[copied_select_cut_mods_def, copied_cursor_mods_def] >>
  fs[copied_parent_frame_mods_def, ghost_inv_at_mods_def]
QED
