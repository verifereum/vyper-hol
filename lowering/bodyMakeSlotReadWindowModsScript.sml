(* A successful MakeArray operand read leaves the held output window intact. *)
Theory bodyMakeSlotReadWindowMods
Ancestors
  bodyMakeElementsContractMods bodyFullIfExpReach bodyMemoryDefs
  exprSimWordArgs exprSimProps stateRelProj wordArgsPtr freshWrites
  vyperStorageTrace vyperStorageFootprint gasOutcomeFull
  valueEncodingProps logValueFramePtr
  bodyFullPostsMods loweringPosts loweringStateRelDefs
  bodyPtrDefs finite_map list pair arithmetic words

val _ = Parse.hide "base";

Theorem slot_read_window_prefix[local]:
  make_elements_prefix_mods base ps off s tn /\ off <= cap /\
  mem_bytes_at base cap z.vs_memory = mem_bytes_at base cap s.vs_memory /\
  (!i. base <= i /\ i < base+cap /\ i IN tz.t_mem ==> i IN tn.t_mem) ==>
  make_elements_prefix_mods base ps off z tz
Proof
  simp[make_elements_prefix_mods_def,EVERY_MEM,FORALL_PROD] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!a b p n. MEM (a,b,p,n) ps ==> _`
    (drule_then strip_assume_tac) >> simp[] >>
  rename1 `val_wf rt pv` >> rename1 `val_footprint rt pv <= n` >>
  rename1 `MEM (rt,pv,p,n) ps` >>
  `base + (p-base) = p /\ p-base + val_footprint rt pv <= cap /\
   p + val_footprint rt pv <= base+cap` by decide_tac >>
  `mem_bytes_at p (val_footprint rt pv) z.vs_memory =
   mem_bytes_at p (val_footprint rt pv) s.vs_memory` by
    (drule mem_bytes_at_translated_window >>
     disch_then (qspecl_then [`p-base`,`val_footprint rt pv`] mp_tac) >> simp[]) >>
  `!i. p <= i /\ i < p + val_footprint rt pv /\ i IN tz.t_mem ==> i IN tn.t_mem` by
    (rpt strip_tac >> first_x_assum irule >> simp[] >> decide_tac) >>
  qpat_assum `mem_bytes_at p _ _ = _`
    (mp_then Any mp_tac robust_val_in_memory_footprint_frame) >>
  disch_then (qspecl_then [`tn.t_mem`,`tz.t_mem`] mp_tac) >> simp[]
QED

Theorem slot_read_window_trace[local]:
  (!tail. eval_expr cx h (es with gas_obs := gs ++ tail) =
     (INL raw,mid with gas_obs := tail)) ==>
  ?events. mid.storage_trace = es.storage_trace ++ events
Proof
  disch_then (qspec_then `[]` assume_tac) >>
  `storage_trace_frame (eval_expr cx h)` by simp[cj 5 evaluate_storage_trace_frame] >>
  drule_all storage_trace_frame_prefix >> simp[]
QED

Theorem make_slot_read_window_mods:
  make_slot_entry_mods mods exps src tops cenv cx env
    (DF,lo,d,ctx,shadow_ctx,func,shadow_func) st0
    (csbase,ebase,sbase,Gbase,tnbase) (aid,base,cap,q)
    h xs dty dtv ps off sa sb sha shb (es,s,G,tn) /\
  (!tail. eval_expr cx h
      (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL raw,mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post_mods H ctx func cenv cx h es sa sc s mid v op z /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid gz tz z /\
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s,G,tn) marks (OK z,gz,tz)) /\
  ghost_kept_at lo cenv es sa G tn s gz tz /\
  alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
  ~z.vs_halted /\ z.vs_current_bb = sc.cs_current_bb /\
  z.vs_inst_idx = LENGTH sc.cs_current_insts /\
  sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id ==>
  make_elements_cut_mods DF lo d ctx func cenv cx st0
    (csbase,ebase,sbase,Gbase,tnbase) (aid,base,cap,q) sc mid z gz tz /\
  make_elements_save_mods s z /\ make_elements_prefix_mods base ps off z tz /\
  mem_bytes_at base cap z.vs_memory = mem_bytes_at base cap s.vs_memory /\
  (~expr_has_effect h ==> make_elements_frame_mods cenv func base cap sa es s z)
Proof
  strip_tac >> drule slot_read_window_trace >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qhdtm_x_assum `make_slot_entry_mods`
    (strip_assume_tac o REWRITE_RULE[make_slot_entry_mods_def,make_elements_entry_mods_def]) >>
  qhdtm_x_assum `make_elements_static_mods`
    (strip_assume_tac o REWRITE_RULE[make_elements_static_mods_def]) >>
  qhdtm_x_assum `make_elements_cut_mods`
    (strip_assume_tac o REWRITE_RULE[make_elements_cut_mods_def]) >>
  qhdtm_x_assum `expr_post_mods` (strip_assume_tac o REWRITE_RULE[expr_post_mods_def]) >>
  drule_then assume_tac expr_post_frame >>
  qhdtm_x_assum `expr_post` (strip_assume_tac o REWRITE_RULE[expr_post_def]) >>
  `?evs. mid.storage_trace = ebase.storage_trace ++ evs` by
    (qpat_assum `mid.storage_trace = es.storage_trace ++ _` mp_tac >>
     qpat_assum `es.storage_trace = ebase.storage_trace ++ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[APPEND_ASSOC]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) es.storage_trace /\
   valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) ebase.storage_trace` by
    (conj_tac
     >- (irule valid_horizon_append >> qexists_tac `events` >>
         qpat_assum `mid.storage_trace = es.storage_trace ++ events`
           (fn th => pure_once_rewrite_tac[GSYM th]) >> first_assum ACCEPT_TAC) >>
     irule valid_horizon_append >> qexists_tac `evs` >>
     qpat_assum `mid.storage_trace = ebase.storage_trace ++ evs`
       (fn th => pure_once_rewrite_tac[GSYM th]) >> first_assum ACCEPT_TAC) >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx es s /\
   stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx ebase sbase` by simp[] >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by fs[locals_kept_def] >>
  `lo <= base /\ off <= cap /\ aid < sc.cs_next_id /\
   base+cap <= z.vs_alloca_next /\ sbase.vs_alloca_next <= z.vs_alloca_next` by decide_tac >>
  `lookup_var q z = SOME (n2w base : 256 word) /\ not_fresh_at sc q` by
    (conj_tac >- simp[] >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `ptr_covers gz tz q z cap` by
    (qpat_assum `ghost_kept_at lo cenv es sa G tn s gz tz`
       (strip_assume_tac o REWRITE_RULE[ghost_kept_at_def]) >>
     qpat_assum `!x. not_fresh_at sa x ==> _`
       (drule_then strip_assume_tac) >>
     qpat_assum `ptr_covers G tn q s cap`
       (mp_tac o REWRITE_RULE[ptr_covers_def]) >> simp[ptr_covers_def]) >>
  `!name b n. local_region cenv mid.scopes z name b n ==>
              loweringStateRelDefs$regions_disjoint base cap b n` by
    (rpt strip_tac >> first_x_assum irule >> qexists_tac `name` >>
     irule local_region_frame >>
     conj_tac
     >- (qexists_tac `func` >>
         qpat_assum `stmt_state_rel _ ctx func cenv cx es s`
           (strip_assume_tac o MATCH_MP stmt_state_rel_local_ptrs_alloca) >> simp[]) >>
     qexistsl_tac [`sa`,`mid.scopes`,`z`] >> simp[]) >>
  `!name b n. local_region cenv es.scopes s name b n ==>
              base+cap <= b \/ b+n <= base` by fs[regions_disjoint_def] >>
  `mem_bytes_at base cap z.vs_memory = mem_bytes_at base cap s.vs_memory` by
    (first_x_assum irule >> conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `aid` >> simp[]) >>
  `make_elements_prefix_mods base ps off z tz` by
    (irule slot_read_window_prefix >> qexistsl_tac [`cap`,`s`,`tn`] >> simp[] >>
     qpat_assum `ghost_kept_at lo cenv es sa G tn s gz tz`
       (strip_assume_tac o REWRITE_RULE[ghost_kept_at_def]) >>
     rpt strip_tac >>
     qpat_assum `!id b n i. FLOOKUP s.vs_allocas id = SOME (b,n) /\ _ ==> _`
       (qspecl_then [`aid`,`base`,`cap`,`i`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
  suspend "restore_cut"
QED

Resume make_slot_read_window_mods[restore_cut]:
  markerLib.RESUME_TAC >>
  `wb_frame cenv ebase mid csbase sbase z` by
    (qpat_assum `stmt_state_rel _ ctx func cenv cx ebase sbase`
       (mp_then Any irule wb_frame_trans) >>
     simp[] >> qexistsl_tac [`es`,`sa`,`s`] >> simp[]) >>
  `ghost_kept_at lo cenv ebase csbase Gbase tnbase sbase gz tz` by
    (qpat_assum `stmt_state_rel _ ctx func cenv cx ebase sbase`
       (mp_then Any irule ghost_kept_at_wb_trans) >>
     simp[] >> qexistsl_tac [`G`,`es`,`es`,`s`,`sa`,`tn`] >> simp[]) >>
  `return_buf_frame d cenv sc z` by
    (qpat_assum `return_buf_frame d cenv sa s`
       (mp_then Any irule return_buf_frame_frame) >> simp[]) >>
  `!fn i u. frag_reachable ctx func z fn i u ==> dalloca_fmp_headroom i u` by
    (rpt gen_tac >> strip_tac >>
     drule_all gas_origin_ptr_path_dalloca_fmp_headroom >> simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       stmt_state_rel H ctx func cenv cx mid z /\
       immutable_frame_mods func cenv cx mid z /\
       storage_well_formed_on cx mid (FST H) /\
       ghost_inv_at_mods (DF H) lo d cenv cx mid gz tz z` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ _`
       (drule_then strip_assume_tac) >> fs[expr_post_mods_def,expr_post_def]) >>
  `MAP FDOM ebase.scopes = MAP FDOM mid.scopes` by
    (qpat_assum `MAP FDOM ebase.scopes = _` (fn th => pure_once_rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `make_elements_save_mods s z` by simp[make_elements_save_mods_def] >>
  `make_elements_save_mods sbase z` by
    (qpat_assum `make_elements_save_mods sbase s`
       (strip_assume_tac o REWRITE_RULE[make_elements_save_mods_def]) >>
     simp[make_elements_save_mods_def] >> rpt strip_tac >>
     qpat_assum `!a b. FLOOKUP sbase.vs_allocas a = SOME b ==> _`
       (drule_then assume_tac) >> simp[]) >>
  conj_tac
  >- (simp[make_elements_cut_mods_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[] >> strip_tac >>
  qpat_assum `~expr_has_effect h ==> pure_frame _ _ _ _ _ _`
    (drule_then (strip_assume_tac o REWRITE_RULE[pure_frame_def])) >>
  rewrite_tac[make_elements_frame_mods_def] >> conj_tac
  >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!off len. (!i b sz. _ ==> _) ==> mem_bytes_at off len _ = _`
    (qspecl_then [`p`,`n`] irule) >> first_assum ACCEPT_TAC
QED

Finalise make_slot_read_window_mods
