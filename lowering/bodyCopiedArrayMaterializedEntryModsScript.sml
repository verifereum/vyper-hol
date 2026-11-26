(* Repackage the actual scratch copy without changing the snapshot destination. *)
Theory bodyCopiedArrayMaterializedEntryMods
Ancestors
  bodyCopiedArrayCutDefsMods bodyCopySlotRhsEndpointMods
  bodyCopyMaterializedRhsPostMods bodyFullPostsMods bodyMemoryDefs
  bodyFullHashKeccakFixed[qualified]
  stateRelProj freshWrites exprLoweringProps exprLowering compileEnv
  context exprSimStorageCopy exprSimCopy assignTuplePtrCopyLen
  bodyPtrDefs fragGasOriginPtr gasExplicitSites vyperStorageFootprint
  loweringPosts venomExecSemantics venomInst venomState words arithmetic

val slot_copy_physical =
  copy_slot_rhs_endpoint_mods
  |> Q.INST [`sm` |-> `k`, `sc` |-> `l`, `s` |-> `a`, `op` |-> `src`,
    `G` |-> `Ga`, `tn` |-> `ta`, `func` |-> `fn`, `rt` |-> `atv`,
    `ee` |-> `mid`, `v` |-> `saved`,
    `explicit` |-> `gas_explicit_sites ctx shctx`]
  |> concl |> dest_imp |> snd;

Theorem copied_array_materialized_store_entry_mods:
  copied_alloc_cut_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
    (st0,es,sa,s0,G0,tn0) (obj,mid,raw,saved,et,bd,atv)
    (sm,s,G,tn) (k,a,Ga,ta) (l,src,sc,cvv,bvv) (q,w) /\
  ci_mono sa sm /\ ci_mono sm k ==>
  ^slot_copy_physical ==>
  ?t Gl tl sw. copied_store_cut_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
    (st0,es,sa,s0,G0,tn0) (obj,mid,raw,saved,et,bd,atv)
    (sm,s,G,tn) (l,t,Gl,tl) (src,sw,sc,cvv) (q,w)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  disch_then (qx_choosel_then [`root`,`sw`,`inner`,`buf`,`u`,`t`,`Gl`,`tl`]
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `copied_alloc_cut_mods _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [copied_alloc_cut_mods_def]) >>
  qpat_assum `copied_array_type_mods _ _ _`
    (strip_assume_tac o REWRITE_RULE [copied_array_type_mods_def]) >>
  qpat_x_assum `copied_parent_frame_mods _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [copied_parent_frame_mods_def]) >>
  `sa.cs_next_id <= k.cs_next_id /\ sa.cs_next_var <= k.cs_next_var /\
   sm.cs_next_var <= k.cs_next_var` by
    (fs[ci_mono_def] >> decide_tac) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (qpat_assum `wb_frame _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [wb_frame_def,locals_kept_def]) >> simp[]) >>
  `~is_word_type (post_value_type ce obj) /\
   type_memory_size atv < dimword (:256)` by
    (simp[is_word_type_def] >> decide_tac) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post_mods H ctx fn ce cx obj es sa l s0 mid saved src t /\
    ghost_inv_at_mods (DF H) lo d ce cx mid Gl tl t /\
    ghost_kept_at lo ce es sa G0 tn0 s0 Gl tl /\
    ptr_val_ok cx (post_value_type ce obj) saved src Gl tl t /\
    ptr_buf_ok ce obj src Gl t /\ expr_store_bound cx (post_value_type ce obj) saved src t /\
    FLOOKUP t.vs_allocas k.cs_next_id = SOME (w2n sw,type_memory_size atv) /\
    lo <= w2n sw /\ w2n sw + type_memory_size atv <= t.vs_alloca_next /\
    not_fresh_at l root /\ wb_frame ce mid mid k a t /\
    ghost_kept_at lo ce mid k Ga ta a Gl tl /\
    (!x cap. not_fresh_at k x /\ ptr_covers Ga ta x a cap ==> ptr_covers Gl tl x t cap)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (drule_then assume_tac) >>
     qpat_x_assum `src = Var root` SUBST_ALL_TAC >>
     match_mp_tac (Q.INST [`sm` |-> `k`, `s` |-> `a`, `sb` |-> `l`, `z` |-> `t`,
       `vv` |-> `bvv`, `tv` |-> `raw`, `w` |-> `sw`, `nb` |-> `type_memory_size atv`,
       `u` |-> `u`, `rt` |-> `atv`, `G` |-> `Ga`, `tn` |-> `ta`]
       copy_materialized_rhs_post_mods) >> asm_rewrite_tac[LESS_EQ_REFL]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx fn ce cx mid t` by
    fs[expr_post_mods_def,expr_post_def] >>
  `copied_cursor_mods ctx fn l t` by
    (drule_then assume_tac bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >> simp[copied_cursor_mods_def]) >>
  `t.vs_alloca_next < dimword (:256)` by
    (drule_then (ACCEPT_TAC o MATCH_MP alloca_room_next_lt) stmt_state_rel_alloca_room) >>
  `lo <= t.vs_alloca_next /\ s0.vs_alloca_next <= t.vs_alloca_next /\
   k.cs_next_var <= l.cs_next_var` by
    (conj_tac >- (irule LESS_EQ_TRANS >> qexists `a.vs_alloca_next` >> simp[]) >>
     conj_tac >- (irule LESS_EQ_TRANS >> qexists `a.vs_alloca_next` >> simp[]) >>
     irule LESS_IMP_LESS_OR_EQ >> first_assum ACCEPT_TAC) >>
  `local_ptrs_reserved ce l` by
    (irule local_ptrs_reserved_next_var >> qexists `k` >> simp[]) >>
  `return_buf_frame d ce l t` by
    (irule return_buf_frame_frame >> qexistsl [`ce`,`a`,`k`] >> simp[]) >>
  suspend "parent"
QED

Resume copied_array_materialized_store_entry_mods[parent]:
  `copied_parent_frame_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
     (st0,es,sa,s0,G0,tn0) mid obj (l,t,Gl,tl)` by
    (simp[copied_parent_frame_mods_def] >> rpt conj_tac
     >- (gen_tac >> disch_tac >>
         qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
           (drule_then strip_assume_tac) >>
         qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
           (drule_then strip_assume_tac) >> fs[expr_post_mods_def,expr_post_def])
     >- (qpat_assum `expr_post_mods (storage_trace_horizon _) _ _ _ _ _ _ _ _ _ _ _ _ _`
           (strip_assume_tac o REWRITE_RULE [expr_post_mods_def,expr_post_def]) >>
         pure_rewrite_tac[wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     fs[expr_post_mods_def,expr_post_def]) >>
  suspend "physical_frames"
QED

Resume copied_array_materialized_store_entry_mods[physical_frames]:
  `t.vs_labels = a.vs_labels` by
    (drule_then strip_assume_tac copy_static_fields >>
     qpat_x_assum `exec_alloca _ _ _ = OK u` mp_tac >>
     simp[exec_alloca_def,mk_inst_def,AllCaseEqs()] >>
     strip_tac >> gvs[update_var_def]) >>
  `copied_base_frame_mods sm (s,G,tn) (t,Gl,tl)` by
    (qpat_x_assum `copied_base_frame_mods _ _ _`
       (strip_assume_tac o REWRITE_RULE [copied_base_frame_mods_def]) >>
     `s.vs_alloca_next <= t.vs_alloca_next` by
       (irule LESS_EQ_TRANS >> qexists `a.vs_alloca_next` >> simp[]) >>
     simp[copied_base_frame_mods_def] >> gen_tac >> disch_tac >>
     `not_fresh_at k x` by (irule not_fresh_at_mono >> qexists `sm` >> simp[]) >>
     qpat_assum `!x. not_fresh_at sm x ==> _` (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at k x ==> lookup_var x t = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `copied_snapshot_dest_mods fn ce lo mid sm (l,t,Gl,tl) (q,w) (type_memory_size atv)` by
    (qpat_x_assum `copied_snapshot_dest_mods _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [copied_snapshot_dest_mods_def]) >>
     qpat_assum `!x. not_fresh_at k x ==> lookup_var x t = _ /\ _`
       (drule_then strip_assume_tac) >>
     `not_fresh_at l q` by (irule not_fresh_at_mono >> qexists `k` >> simp[]) >>
     `sm.cs_next_id < l.cs_next_id /\ w2n w + type_memory_size atv <= t.vs_alloca_next` by
       (conj_tac >- (irule LESS_TRANS >> qexists `k.cs_next_id` >> simp[]) >>
        irule LESS_EQ_TRANS >> qexists `a.vs_alloca_next` >> simp[]) >>
     simp[copied_snapshot_dest_mods_def] >>
     `!name b len. local_region ce mid.scopes t name b len <=> local_region ce mid.scopes a name b len` by
       (rpt gen_tac >> irule copy_buffer_local_region_frame >> qexists `k` >> simp[]) >>
     simp[] >> first_assum ACCEPT_TAC) >>
  suspend "package"
QED

Resume copied_array_materialized_store_entry_mods[package]:
  `!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shctx,ctx,fn,PG)
      (s,G,tn) [] (OK t,Gl,tl)` by
    (gen_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _`
       (qspec_then `D` (mp_tac o MATCH_MP gas_origin_ptr_path_append)) >> simp[]) >>
  `cs_extends sm l` by (irule cs_extends_trans >> qexists `k` >> simp[]) >>
  `ptr_mem_ok cx (ArrayT et bd) saved src Gl tl t` by
    (qpat_assum `ptr_val_ok cx (post_value_type ce obj) saved src Gl tl t`
       (mp_tac o REWRITE_RULE [ptr_val_ok_def]) >> asm_rewrite_tac[] >>
     disch_then (ACCEPT_TAC o CONJUNCT2)) >>
  qpat_x_assum `root = STRING _ _` kall_tac >>
  `!x. src = Var x ==> not_fresh_at l x` by simp[] >>
  `type_memory_size atv <> 0 ==>
      (?x. src = Var x /\ ptr_covers Gl tl x t (type_memory_size atv)) /\
      w2n sw + type_memory_size atv <= t.vs_alloca_next /\ t.vs_alloca_next < dimword (:256)` by
    simp[] >>
  qexistsl [`t`,`Gl`,`tl`,`sw`] >> pure_rewrite_tac[copied_store_cut_mods_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise copied_array_materialized_store_entry_mods
