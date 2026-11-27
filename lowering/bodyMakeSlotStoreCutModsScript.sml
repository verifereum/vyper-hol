(* Restore the anchored MakeArray traversal cut after writing one slot. *)
Theory bodyMakeSlotStoreCutMods
Ancestors
  bodyMakeElementsContractMods bodyStructFieldCutsMods
  bodyMakeSlotRegisteredImmMods bodyMakeSlotRegisteredStateMods
  bodyFullIfExpReach bodyInvCodeProps
  bodyMemoryDefs wordArgsPtr exprSimCopy exprSimProps exprSimFullBundleProps
  typedMemoryCopy stateRelProj assignTuplePtrCopyLen exprLoweringProps freshWrites
  bodyPtrDefs loweringPosts loweringStateRelDefs venomMemDefs venomState
  vyperStorageFootprint gasOutcomeFull finite_map list arithmetic

val _ = Parse.hide "base";

Triviality slot_anchor_writeback:
  wb_frame ce es ee sa s z /\ z.vs_allocas = t.vs_allocas /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x z) /\
  (!p n. p+n <= dst \/ dst+k <= p ==>
    mem_bytes_at p n t.vs_memory = mem_bytes_at p n z.vs_memory) /\
  (!name p n. local_region ce es.scopes s name p n ==> p+n <= dst \/ dst+k <= p) /\
  (!a p n. FLOOKUP s.vs_allocas a = SOME (p,n) /\ a < sa.cs_next_id ==>
    p+n <= dst \/ dst+k <= p) ==>
  wb_frame ce es ee sa s t
Proof
  simp_tac bool_ss [wb_frame_def] >> strip_tac >> rpt conj_tac
  >- (rpt strip_tac >> metis_tac[])
  >- (rpt strip_tac >> rename1 `FLOOKUP s.vs_allocas a = SOME (p,n)` >>
      `p+n <= dst \/ dst+k <= p` by metis_tac[] >>
      `mem_bytes_at p n t.vs_memory = mem_bytes_at p n z.vs_memory` by simp[] >>
      metis_tac[]) >>
  irule locals_kept_regions_tail >> qexists_tac `z` >>
  simp[] >> metis_tac[]
QED

Triviality slot_anchor_ghost:
  ghost_kept_at lo ce es sa G0 tn0 s gz tz /\
  (!x. not_fresh_at sa x ==>
    FLOOKUP gf x = FLOOKUP gz x /\ op_taint tf (Var x) = op_taint tz (Var x)) /\
  (!i. ~(dst <= i /\ i < dst+k) ==> (i IN tf.t_mem <=> i IN tz.t_mem)) /\
  (!name p n. local_region ce es.scopes s name p n ==> p+n <= dst \/ dst+k <= p) /\
  (!a p n. FLOOKUP s.vs_allocas a = SOME (p,n) /\ a < sa.cs_next_id ==>
    p+n <= dst \/ dst+k <= p) ==>
  ghost_kept_at lo ce es sa G0 tn0 s gf tf
Proof
  simp_tac bool_ss [ghost_kept_at_def] >> strip_tac >> rpt conj_tac
  >- (rpt strip_tac >> rename1 `FLOOKUP s.vs_allocas a = SOME (p,n)` >>
      `p+n <= dst \/ dst+k <= p` by metis_tac[] >>
      `~(dst <= i) \/ ~(i < dst+k)` by decide_tac >> metis_tac[]) >>
  qx_genl_tac [`name`,`p`,`n`,`i`] >> strip_tac >>
  `p+n <= dst \/ dst+k <= p` by metis_tac[] >>
  `~(dst <= i) \/ ~(i < dst+k)` by decide_tac >> metis_tac[]
QED

Theorem make_slot_store_cut_mods:
  make_elements_static_mods mods exps src tops cenv cx env
    (DF,lo,ctx,shadow_ctx,func,shadow_func) st0 csbase ebase sbase aid sc /\
  make_elements_cut_mods DF lo d ctx func cenv cx st0
    (csbase,ebase,sbase,Gbase,tnbase) (aid,base,cap,q) sc mid z gz tz /\
  storage_trace_domain cx st0 mid.storage_trace /\ env_consistent env cx mid /\
  off + type_memory_size dtv <= cap /\ ci_mono sc sb /\
  struct_store_effects func (sc,gz,tz,z) (sb,gf,tf,t) (base+off,dtv,v) /\
  (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (z,gz,tz) [] (OK t,gf,tf)) ==>
  make_elements_cut_mods DF lo d ctx func cenv cx st0
    (csbase,ebase,sbase,Gbase,tnbase) (aid,base,cap,q) sb mid t gf tf
Proof
  simp_tac bool_ss [make_elements_static_mods_def, make_elements_cut_mods_def,
    ci_mono_def] >> strip_tac >>
  qpat_assum `struct_store_effects _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[struct_store_effects_def, expr_sim_full_endpoint_def]) >>
  qabbrev_tac `n = type_memory_size dtv` >>
  `typed_copy_state_frame sc base cap z t` by
    (irule typed_copy_state_frame_subinterval >>
     qpat_assum `typed_copy_state_frame sc (base+off) n z t` (irule_at Any) >>
     decide_tac) >>
  `t.vs_allocas = z.vs_allocas /\ t.vs_alloca_next = z.vs_alloca_next` by
    fs[typed_copy_state_frame_def, venom_state_component_equality] >>
  `!x. not_fresh_at sc x ==> lookup_var x t = lookup_var x z` by
    fs[typed_copy_state_frame_def] >>
  `!p k. p+k <= base+off \/ base+off+n <= p ==>
    mem_bytes_at p k t.vs_memory = mem_bytes_at p k z.vs_memory` by
    (qpat_assum `typed_copy_state_frame sc (base+off) n z t` mp_tac >>
     simp_tac bool_ss [typed_copy_state_frame_def, typed_copy_frame_def] >> metis_tac[]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  `alloca_inv z` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> stmt_state_rel H _ _ _ _ mid z /\ _`
       (drule_then strip_assume_tac) >>
     drule stmt_state_rel_local_ptrs_alloca >> metis_tac[]) >>
  `!name p k. local_region cenv mid.scopes t name p k <=>
    local_region cenv mid.scopes z name p k` by
    (rpt gen_tac >> irule copy_buffer_local_region_frame >>
     qexists_tac `sc` >> simp[]) >>
  `!name p k. local_region cenv mid.scopes z name p k ==>
    loweringStateRelDefs$regions_disjoint (base+off) n p k` by suspend "local_slot" >>
  `wb_frame cenv ebase mid csbase sbase t /\
   ghost_kept_at lo cenv ebase csbase Gbase tnbase sbase gf tf` by suspend "anchor" >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid t /\ immutable_frame_mods func cenv cx mid t /\
    storage_well_formed_on cx mid (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx mid gf tf t`
    by suspend "horizon" >>
  suspend "finish"
QED

Resume make_slot_store_cut_mods[local_slot]:
  rpt strip_tac >> simp[loweringStateRelDefsTheory.regions_disjoint_def] >>
  qpat_assum `!name b k. local_region cenv mid.scopes z name b k ==> _`
    (drule_then mp_tac) >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Resume make_slot_store_cut_mods[anchor]:
  `!x. not_fresh_at csbase x ==> not_fresh_at sc x` by
    metis_tac[not_fresh_at_mono] >>
  `!name p k. local_region cenv ebase.scopes sbase name p k ==> p+k <= base+off \/ base+off+n <= p` by
    (rpt strip_tac >>
     `local_region cenv mid.scopes z name p k` by
       (irule local_region_frame_fwd >> qexistsl_tac [`sbase`,`csbase`,`ebase.scopes`] >>
        simp[] >> metis_tac[exprSimWordArgsTheory.wb_frame_vars]) >>
     qpat_assum `!name p k. local_region cenv mid.scopes z name p k ==>
       loweringStateRelDefs$regions_disjoint (base+off) n p k` (drule_then mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `!a p k. FLOOKUP sbase.vs_allocas a = SOME (p,k) /\ a < csbase.cs_next_id ==>
    p+k <= base+off \/ base+off+n <= p` by
    (rpt strip_tac >>
     `a <> aid` by decide_tac >>
     `FLOOKUP z.vs_allocas a = SOME (p,k)` by
       (qpat_assum `make_elements_save_mods sbase z`
          (irule o REWRITE_RULE[make_elements_save_mods_def]) >> simp[]) >>
     qpat_assum `alloca_inv z` (mp_tac o REWRITE_RULE[alloca_inv_def,allocas_non_overlapping_def]) >>
     disch_then strip_assume_tac >>
     first_x_assum (qspecl_then [`a`,`aid`,`p`,`k`,`base`,`cap`] mp_tac) >> simp[] >> decide_tac) >>
  conj_tac
  >- (irule slot_anchor_writeback >> qexistsl_tac [`base+off`,`n`,`z`] >>
      asm_simp_tac bool_ss [] >> metis_tac[]) >>
  irule slot_anchor_ghost >> qexistsl_tac [`base+off`,`gz`,`n`,`tz`] >>
  asm_simp_tac bool_ss [] >> metis_tac[]
QED

Resume make_slot_store_cut_mods[horizon]:
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> stmt_state_rel H _ _ _ _ mid z /\ _`
     (drule_then strip_assume_tac) >>
  `immutable_frame_mods func cenv cx mid t` by
    (irule make_slot_registered_immutable_frame_mods >>
     qpat_assum `typed_copy_state_frame sc (base+off) n z t` (irule_at Any) >>
     qpat_assum `contract_inv mods exps ctx cenv cx` (irule_at Any) >>
     qpat_assum `expr_sim_inv_mods mods cenv cx env ebase` (irule_at Any) >>
     qpat_assum `FLOOKUP z.vs_allocas aid = SOME (base,cap)` (irule_at Any) >>
     asm_simp_tac bool_ss []) >>
  `ALOOKUP cenv.ce_modules cenv.ce_module = SOME tops` by
    (drule_then SUBST1_TAC contract_inv_cenv_modules >> fs[bodyInvSplitTheory.module_body_inv_def]) >>
  `stmt_state_rel H ctx func cenv cx mid t /\ ghost_inv_at_mods (DF H) lo d cenv cx mid gf tf t` by
    (irule make_slot_registered_state_ghost_mods >>
     qpat_assum `struct_store_effects func _ _ _` (irule_at Any) >>
     qpat_assum `FLOOKUP z.vs_allocas aid = SOME (base,cap)` (irule_at Any) >>
     qpat_assum `ALOOKUP cenv.ce_modules cenv.ce_module = SOME tops` (irule_at Any) >>
     qpat_assum `stmt_state_rel H ctx func cenv cx mid z` (irule_at Any) >>
     qpat_assum `ghost_inv_at_mods (DF H) lo d cenv cx mid gz tz z` (irule_at Any) >>
     asm_simp_tac bool_ss [GSYM (Abbr `n`)] >>
     conj_tac >- (qpat_assum `!name b k. local_region cenv mid.scopes z name b k ==> _ base cap b k` ACCEPT_TAC) >>
     conj_tac >> rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `csbase` >> metis_tac[]) >>
  asm_rewrite_tac[]
QED

Resume make_slot_store_cut_mods[finish]:
  `lookup_var q t = SOME (n2w base) /\ ptr_covers gf tf q t cap` by
    (simp[] >> irule ptr_covers_lookup_frame >>
     qpat_assum `ptr_covers gz tz q z cap` (irule_at Any) >> simp[]) >>
  `not_fresh_at sb q` by metis_tac[not_fresh_at_mono] >>
  `make_elements_save_mods sbase t` by fs[make_elements_save_mods_def] >>
  `return_buf_frame d cenv sb t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`z`,`sc`] >> simp[]) >>
  `!fn i u. frag_reachable ctx func t fn i u ==> dalloca_fmp_headroom i u` by
    (qpat_assum `!D. gas_origin_ptr_path _ (z,gz,tz) [] (OK t,gf,tf)`
       (qspec_then `ARB` mp_tac) >>
     disch_then (fn th => mp_tac (MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO]
       gas_origin_ptr_path_dalloca_fmp_headroom) th)) >>
     asm_simp_tac bool_ss [] >> metis_tac[]) >>
  `aid < sb.cs_next_id` by decide_tac >>
  asm_simp_tac bool_ss [] >>
  conj_tac >- (rpt strip_tac >> qpat_assum `!name b k. local_region cenv mid.scopes z name b k ==> _ base cap b k` (drule_then ACCEPT_TAC)) >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      `valid_horizon cx st0 H mid.storage_trace` by asm_rewrite_tac[] >>
      qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> stmt_state_rel H _ _ _ _ mid t /\ _`
        (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED

Finalise make_slot_store_cut_mods
