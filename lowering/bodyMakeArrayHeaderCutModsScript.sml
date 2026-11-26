(* Execution and the cut after the optional homogeneous array length word. *)
Theory bodyMakeArrayHeaderCutMods
Ancestors
  bodyMakeElementsContractMods calldataOverwritePtr bodyPtrMakeArrayWordStore
  bodyPtrMakeArrayCopyStep bodyFullHashKeccakFixed bodyFullIfExpReach
  bodyFullPathHistory exprSimRawLog exprSimRawCallCalldata ghostPcTransportPtr
  emitHelperProps stateRelProj venomMemDefs valueEncodingProps vyperStorageTrace
  bodyPtrDefs venomState ptrDiscipline exprLoweringProps compileEnv fragGasOriginPtr
  bodyFullShadowBodyInv valueEncoding vyperState

val _ = Parse.hide "base";

Theorem header_store_path[local]:
  emit_void MSTORE [Var q; Lit (n2w k)] sm = ((),sh) /\
  lookup_var q s = SOME (n2w base) /\ base + cap < dimword (:256) /\
  32 <= cap /\ base + cap <= s.vs_alloca_next /\
  ptr_covers G tn q s cap /\ allocas_from lo s /\
  fn_has_code sm sh func /\ fn_inst_ids_distinct func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  let raw = mstore base (n2w k) s in
  let i = mk_inst sm.cs_next_id MSTORE [Var q; Lit (n2w k)] [] in
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (raw with vs_inst_idx := LENGTH sh.cs_current_insts),
       step_prov PG G i raw,step_taint i s raw tn)
Proof
  strip_tac >> simp[] >>
  `base < dimword (:256)` by decide_tac >>
  `ptr_covers G tn q s 32` by
    (fs[ptr_covers_def] >> qexistsl_tac [`b`,`sz'`] >> decide_tac) >>
  `eval_operand (Var q) s = SOME (n2w base) /\
   eval_operand (Lit (n2w k)) s = SOME (n2w k) /\
   op_taint tn (Lit (n2w k)) = {}` by simp[eval_operand_def,op_taint_def] >>
  drule_all clean_mstore_overwrite_prefix_uniform_origin_joint >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `emitted_insts sm sh = [mk_inst sm.cs_next_id MSTORE [Var q; Lit (n2w k)] []]` by
    metis_tac[emitted_insts_emit_void] >>
  `step_inst_base (mk_inst sm.cs_next_id MSTORE [Var q; Lit (n2w k)] []) s =
     OK (mstore base (n2w k) s)` by
    (qspecl_then [`Var q`,`Lit (n2w k)`] mp_tac step_MSTORE >>
     simp[eval_operand_def] >>
     disch_then (qspecl_then [`n2w base`,`sm.cs_next_id`,`s`] mp_tac) >>
     simp[wordsTheory.w2n_n2w]) >>
  qpat_x_assum `!D. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _` (qspec_then `ARB` mp_tac) >>
  simp[fragGasSeqPtrTheory.inst_seq_ptr_def] >> strip_tac >>
  `t = mstore base (n2w k) s with vs_inst_idx := LENGTH sh.cs_current_insts` by
    (qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
     simp[run_inst_seq_def] >> strip_tac >> simp[venom_state_component_equality]) >>
  fs[wordsTheory.w2n_n2w] >> decide_tac
QED

Theorem header_store_wb[local]:
  wb_frame cenv ebase es csbase sbase s /\ local_ptrs_reserved cenv csbase /\
  MAP FDOM ebase.scopes = MAP FDOM es.scopes /\
  FLOOKUP s.vs_allocas aid = SOME (base,cap) /\ csbase.cs_next_id <= aid /\
  alloca_inv s /\ 32 <= cap /\
  (!name b n. local_region cenv es.scopes s name b n ==>
    loweringStateRelDefs$regions_disjoint base cap b n) ==>
  wb_frame cenv ebase es csbase sbase
    (mstore base (n2w k) s with vs_inst_idx := pc)
Proof
  strip_tac >> simp[raw_call_wb_frame_inst_idx] >>
  irule raw_log_mstore_frame >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      rename1 `other < csbase.cs_next_id` >>
      `aid <> other` by decide_tac >>
      `base + cap <= b \/ b + sz <= base` by
        (fs[alloca_inv_def,allocas_non_overlapping_def] >> metis_tac[]) >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  qexists_tac `es` >> simp[] >> rpt strip_tac >>
  `loweringStateRelDefs$regions_disjoint base cap b sz` by
    (first_x_assum irule >> qexists_tac `n` >> simp[]) >>
  fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem header_word_prefix[local]:
  lookup_var q s = SOME (n2w base) /\ base < dimword (:256) /\ k < dimword (:256) ==>
  make_elements_prefix_mods base [(BaseTV (UintT 256),IntV (&k),base,32)] 32
    (mstore base (n2w k) s with vs_inst_idx := pc)
    (step_taint (mk_inst id MSTORE [Var q; Lit (n2w k)] []) s (mstore base (n2w k) s) tn)
Proof
  strip_tac >>
  simp[make_elements_prefix_mods_def,valueEncodingDefsTheory.val_wf_def,
       loweringPostsTheory.val_footprint_def,type_memory_size_def,valueEncodingDefsTheory.val_in_memory_def,
       val_to_w256_def,integer_wordTheory.i2w_def] >>
  rpt strip_tac >>
  `mem_word_at (w2n (n2w base : bytes32)) m = n2w k` suffices_by simp[wordsTheory.w2n_n2w] >>
  irule mstore_raw_robust_word >>
  qexistsl_tac [`q`,`id`,`s`,`tn`] >> simp[] >>
  qexists_tac `Lit (n2w k)` >> simp[eval_operand_def,op_taint_def]
QED

Theorem make_array_header_cut_from_frame_mods:
  make_elements_cut_mods DF lo d ctx func cenv cx st0
    (csbase,ebase,sbase,Gbase,tnbase) (aid,base,cap,q) sm es s G tn /\
  (if h then emit_void MSTORE [Var q; Lit (n2w k)] else return ()) sm = ((),sh) /\
  fn_has_code sm sh func /\ fn_inst_ids_distinct func /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  csbase.cs_next_id <= aid /\ local_ptrs_reserved cenv csbase /\ local_ptrs_reserved cenv sm /\
  MEM ai (fn_insts func) /\ ai.inst_opcode = ALLOCA /\ ai.inst_id = aid /\
  (h ==> 32 <= cap /\ k < dimword (:256)) /\
  (h ==> !H.
    let raw = mstore base (n2w k) s in
    let i = mk_inst sm.cs_next_id MSTORE [Var q; Lit (n2w k)] [] in
    let t = raw with vs_inst_idx := LENGTH sh.cs_current_insts in
    valid_horizon cx st0 H es.storage_trace /\
    stmt_state_rel H ctx func cenv cx es s /\
    immutable_frame_mods func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx es G tn s ==>
    stmt_state_rel H ctx func cenv cx es t /\
    immutable_frame_mods func cenv cx es t /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx es (step_prov PG G i raw) (step_taint i s raw tn) t) ==>
  ?t g tt.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,g,tt)) /\
    ci_mono sm sh /\ local_ptrs_reserved cenv sh /\
    make_elements_cut_mods DF lo d ctx func cenv cx st0
      (csbase,ebase,sbase,Gbase,tnbase) (aid,base,cap,q) sh es t g tt /\
    make_elements_prefix_mods base
      (if h then [(BaseTV (UintT 256),IntV (&k),base,32)] else [])
      (if h then 32 else 0) t tt /\
    (!name b n. local_region cenv es.scopes t name b n = local_region cenv es.scopes s name b n) /\
    (!name b n. local_region cenv es.scopes s name b n ==>
      mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory) /\
    (!p n. p+n <= base \/ base+(if h then 32 else 0) <= p ==>
      mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory)
Proof
  strip_tac >> reverse (Cases_on `h`)
  >- (gvs[compileEnvTheory.comp_return_def] >> qexistsl_tac [`s`,`G`,`tn`] >>
      simp[ci_mono_def,compileEnvTheory.cs_extends_refl,make_elements_prefix_mods_def] >>
      rpt gen_tac >> irule (cj 1 gas_origin_ptr_path_rules) >>
      fs[make_elements_cut_mods_def]) >>
  qabbrev_tac `H0 = storage_trace_horizon es.storage_trace` >>
  `valid_horizon cx st0 H0 es.storage_trace` by
    fs[Abbr `H0`,vyperStorageFootprintTheory.storage_trace_domain_def] >>
  gvs[make_elements_cut_mods_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ _ /\ _`
    (qspec_then `H0` mp_tac) >>
  (impl_tac >- (first_assum ACCEPT_TAC)) >> strip_tac >>
  `alloca_inv s` by (drule (cj 2 stmt_state_rel_local_ptrs_alloca) >> simp[]) >>
  `allocas_from lo s` by fs[ghost_inv_at_mods_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
  drule_all header_store_path >> disch_then (qspec_then `PG` assume_tac) >>
  `ci_mono sm sh` by metis_tac[ci_mono_emit_void,pairTheory.SND] >>
  `local_ptrs_reserved cenv sh` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sm` >> fs[ci_mono_def]) >>
  `sm.cs_next_id <= sh.cs_next_id /\ sm.cs_next_var <= sh.cs_next_var` by fs[ci_mono_def] >>
  `sm.cs_current_bb = sh.cs_current_bb` by
    (drule emit_void_same_blocks >> simp[same_blocks_def]) >>
  `base < dimword (:256)` by decide_tac >>
  qabbrev_tac `raw = mstore base (n2w k) s` >>
  qabbrev_tac `i = mk_inst sm.cs_next_id MSTORE [Var q; Lit (n2w k)] []` >>
  qabbrev_tac `t = raw with vs_inst_idx := LENGTH sh.cs_current_insts` >>
  qabbrev_tac `g = step_prov PG G i raw` >>
  qabbrev_tac `tt = step_taint i s raw tn` >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,g,tt)` by
    fs[Abbr `t`,Abbr `g`,Abbr `tt`] >>
  `eval_operand (Lit (n2w k)) s = SOME (n2w k)` by simp[eval_operand_def] >>
  `g = G /\ tt.t_var = tn.t_var /\ tt.t_mem = tn.t_mem DIFF {j | base <= j /\ j < base+32}` by
    (drule_all mstore_raw_ghost_frame >>
     disch_then (qspecl_then [`tn`,`sm.cs_next_id`,`PG`,`G`] mp_tac) >>
     simp[Abbr `g`,Abbr `tt`,Abbr `i`,Abbr `raw`,wordsTheory.w2n_n2w,op_taint_def]) >>
  qexistsl_tac [`t`,`g`,`tt`] >>
  `!name b n. local_region cenv es.scopes t name b n = local_region cenv es.scopes s name b n` by
    simp[Abbr `t`,Abbr `raw`,loweringStateRelDefsTheory.local_region_def,lookup_var_def,mstore_def] >>
  `FLOOKUP t.vs_allocas ai.inst_id = SOME (base,cap) /\
   lookup_var q t = SOME (n2w base) /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_allocas = s.vs_allocas /\ ~t.vs_halted /\ t.vs_current_bb = sh.cs_current_bb /\
   t.vs_inst_idx = LENGTH sh.cs_current_insts` by
    fs[Abbr `t`,Abbr `raw`,lookup_var_def,mstore_def] >>
  `ptr_covers g tt q t cap` by
    (gvs[ptr_covers_def,op_taint_def,wordsTheory.w2n_n2w] >> decide_tac) >>
  `not_fresh_at sh q /\ ai.inst_id < sh.cs_next_id` by
    (fs[loweringStateRelDefsTheory.not_fresh_at_def] >> decide_tac) >>
  `make_elements_save_mods sbase t` by fs[make_elements_save_mods_def] >>
  simp[] >> conj_tac >- suspend "cut_fields" >>
  conj_tac >-
    (simp[Abbr `t`,Abbr `tt`,Abbr `i`,Abbr `raw`] >> irule header_word_prefix >> simp[]) >>
  `!p n. p+n <= base \/ base+32 <= p ==>
       mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory` by
    (simp[Abbr `t`,Abbr `raw`] >> rpt strip_tac >>
     irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!name b n. local_region _ _ _ name b n ==> loweringStateRelDefs$regions_disjoint _ _ b n`
        (qspecl_then [`name`,`b`,`n`] mp_tac) >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def] >>
      strip_tac >> first_x_assum irule >> decide_tac) >>
  fs[arithmeticTheory.ADD_COMM]
QED

Resume make_array_header_cut_from_frame_mods[cut_fields]:
  qpat_assum `!D explicit. gas_origin_ptr_path _ _ _ _`
    (qspecl_then [`ARB`,`ARB`] assume_tac) >>
  `alloca_history func t` by (drule_all body_full_path_alloca_history >> simp[]) >>
  `wb_frame cenv ebase es csbase sbase t` by
    (simp[Abbr `t`,Abbr `raw`] >> irule header_store_wb >> simp[] >>
     qexistsl_tac [`ai.inst_id`,`cap`] >> simp[] >> first_assum ACCEPT_TAC) >>
  `ghost_kept_at lo cenv ebase csbase Gbase tnbase sbase G tt` by
    (qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[ghost_kept_at_def,op_taint_def] >> rpt (pop_assum kall_tac) >> metis_tac[]) >>
  `return_buf_frame d cenv sh t` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`,`s`,`sm`] >> simp[Abbr `t`,Abbr `raw`,lookup_var_def,mstore_def]) >>
  simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     qpat_assum `!H. _ /\ _ ==> stmt_state_rel H _ _ _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  map_every qx_gen_tac [`fn`,`i`,`u`] >> disch_tac >>
  drule gas_origin_ptr_path_dalloca_fmp_headroom >>
  disch_then (qspecl_then [`fn`,`i`,`u`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]
QED

Finalise make_array_header_cut_from_frame_mods
