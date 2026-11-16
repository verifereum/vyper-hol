(* Optional length-word initialization for the joint MakeArray loop. *)
Theory bodyFullMakeArrayHeader
Ancestors
  bodyFullHashCleanFrame bodyPtrMakeArrayWordStore calldataOverwritePtr
  exprSimAlloc bodyFullMakeArrayInit ghostPcTransportPtr gasOutcomeFull
  exprSimRawLog exprLoweringProps emitHelperProps fragExecPtr
  venomState venomMemDefs valueEncoding valueEncodingProps
  bodyFullPathHistory loweringPosts bodyPtrMakeArrayCopyStep
  vyperStorageTrace freshWrites

val _ = Parse.hide "base";

Theorem make_array_header_joint[local]:
  emit_void MSTORE [Var q; Lit (n2w len)] sm = ((),sh) /\
  lookup_var q s = SOME (n2w base) /\ base + cap < dimword (:256) /\
  32 <= cap /\ base + cap <= s.vs_alloca_next /\
  ptr_covers G tn q s cap /\ allocas_from lo s /\
  fn_has_code sm sh func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t Gf tnf.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK t,Gf,tnf)) /\
    t = (mstore base (n2w len) s with vs_inst_idx := LENGTH sh.cs_current_insts) /\
    Gf = step_prov PG G (mk_inst sm.cs_next_id MSTORE [Var q; Lit (n2w len)] [])
      (mstore base (n2w len) s) /\
    tnf = step_taint (mk_inst sm.cs_next_id MSTORE [Var q; Lit (n2w len)] []) s
      (mstore base (n2w len) s) tn /\
    ci_mono sm sh /\ sh.cs_next_var = sm.cs_next_var /\
    sh.cs_current_bb = sm.cs_current_bb
Proof
  strip_tac >>
  `base < dimword (:256)` by decide_tac >>
  `ptr_covers G tn q s 32` by
    (fs[bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `eval_operand (Var q) s = SOME (n2w base) /\
   eval_operand (Lit (n2w len)) s = SOME (n2w len) /\
   ptrDiscipline$op_taint tn (Lit (n2w len)) = {}` by
    simp[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_taint_def] >>
  drule_all clean_mstore_overwrite_prefix_uniform_origin_joint >>
  disch_then (qspec_then `PG` mp_tac) >>
  strip_tac >>
  `emitted_insts sm sh =
    [mk_inst sm.cs_next_id MSTORE [Var q; Lit (n2w len)] []]` by
    metis_tac[emitted_insts_emit_void] >>
  `step_inst_base (mk_inst sm.cs_next_id MSTORE [Var q; Lit (n2w len)] []) s =
     OK (mstore base (n2w len) s)` by
    (qspecl_then [`Var q`,`Lit (n2w len)`] mp_tac emitHelperPropsTheory.step_MSTORE >>
     simp[venomStateTheory.eval_operand_def] >>
     disch_then (qspecl_then [`n2w base`,`sm.cs_next_id`,`s`] mp_tac) >>
     simp[wordsTheory.w2n_n2w]) >>
  qpat_x_assum `!D. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _` (qspec_then `ARB` mp_tac) >>
  simp[fragGasSeqPtrTheory.inst_seq_ptr_def] >> strip_tac >>
  `t = mstore base (n2w len) s with vs_inst_idx := LENGTH sh.cs_current_insts` by
    (qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
     simp[exprLoweringPropsTheory.run_inst_seq_def] >>
     strip_tac >>
     simp[venomStateTheory.venom_state_component_equality]) >>
  `ci_mono sm sh` by metis_tac[ci_mono_emit_void, pairTheory.SND] >>
  drule emit_void_same_blocks >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  fs[exprLoweringPropsTheory.same_blocks_def, wordsTheory.w2n_n2w]
QED

Theorem make_array_header_full:
  (if header then emit_void MSTORE [Var q; Lit (n2w len)] else return ()) sm = ((),sh) /\
  fn_has_code sm sh func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ storage_trace_domain cx st0 es.storage_trace /\
  csbase.cs_next_id <= aid /\ local_ptrs_reserved cenv csbase /\
  local_ptrs_reserved cenv sm /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sm x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sm x) /\
  MEM ai (fn_insts func) /\ ai.inst_opcode = ALLOCA /\ ai.inst_id = aid /\
  (header ==> 32 <= cap /\ len < dimword (:256)) /\
  (?events. es.storage_trace = ebase.storage_trace ++ events) /\
  FLOOKUP s.vs_allocas aid = SOME (base,cap) /\
  lookup_var q s = SOME (n2w base) /\
  ptr_covers G tn q s cap /\ not_fresh_at sm q /\
  aid < sm.cs_next_id /\ base+cap < dimword (:256) /\
  base+cap <= s.vs_alloca_next /\
  (!name b n. local_region cenv es.scopes s name b n ==>
    loweringStateRelDefs$regions_disjoint base cap b n) /\
  alloca_history func s /\ sbase.vs_alloca_next <= s.vs_alloca_next /\
  (!a b. FLOOKUP sbase.vs_allocas a = SOME b ==> FLOOKUP s.vs_allocas a = SOME b) /\
  MAP FDOM ebase.scopes = MAP FDOM es.scopes /\
  wb_frame cenv ebase es csbase sbase s /\
  ghost_kept_at lo cenv ebase csbase Gbase tnbase sbase G tn /\
  return_buf_frame d cenv sm s /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) ==>
  ?t Gf tnf ps.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tnf)) /\
    ci_mono sm sh /\ local_ptrs_reserved cenv sh /\
    ps = (if header then [(BaseTV (UintT 256),IntV (&len),base,32)] else []) /\
    (?events. es.storage_trace = ebase.storage_trace ++ events) /\
    FLOOKUP t.vs_allocas aid = SOME (base,cap) /\
    lookup_var q t = SOME (n2w base) /\
    ptr_covers Gf tnf q t cap /\ not_fresh_at sh q /\
    aid < sh.cs_next_id /\ base+cap < dimword (:256) /\
    base+cap <= t.vs_alloca_next /\
    (!name b n. local_region cenv es.scopes t name b n ==>
      loweringStateRelDefs$regions_disjoint base cap b n) /\
    alloca_history func t /\ sbase.vs_alloca_next <= t.vs_alloca_next /\
    (!a b. FLOOKUP sbase.vs_allocas a = SOME b ==> FLOOKUP t.vs_allocas a = SOME b) /\
    MAP FDOM ebase.scopes = MAP FDOM es.scopes /\
    wb_frame cenv ebase es csbase sbase t /\
    ghost_kept_at lo cenv ebase csbase Gbase tnbase sbase Gf tnf /\
    return_buf_frame d cenv sh t /\ ~t.vs_halted /\
    t.vs_current_bb = sh.cs_current_bb /\
    t.vs_inst_idx = LENGTH sh.cs_current_insts /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es t /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx es Gf tnf t) /\
    EVERY (\(rt,v,p,n). val_wf rt v /\ val_footprint rt v <= n /\
      base <= p /\ p+n <= base+(if header then 32 else 0) /\
      (!m. mem_agree_outside tnf.t_mem t.vs_memory m ==> val_in_memory rt v p m)) ps /\
    (header ==> !m. mem_agree_outside tnf.t_mem t.vs_memory m ==>
      mem_word_at base m = n2w len) /\
    (!p n. p+n <= base \/ base+(if header then 32 else 0) <= p ==>
      mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory) /\
    (!name b n. local_region cenv es.scopes s name b n ==>
      mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory)
Proof
  strip_tac >> reverse (Cases_on `header`)
  >- (gvs[compileEnvTheory.comp_return_def] >>
      qexistsl_tac [`s`,`G`,`tn`] >>
      simp[ci_mono_def, compileEnvTheory.cs_extends_refl,
           fragGasOriginPtrTheory.gas_origin_ptr_path_rules] >> metis_tac[]) >>
  gvs[] >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es s /\
   ghost_inv_at (DF (storage_trace_horizon es.storage_trace)) lo d cenv cx es G tn s` by
    metis_tac[] >>
  `allocas_from lo s /\ lo <= base /\ alloca_inv s` by
    (fs[bodyPtrDefsTheory.ghost_inv_at_def, ptrDisciplineTheory.allocas_from_def,
        stmt_state_rel_def] >> metis_tac[]) >>
  drule_all make_array_header_joint >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >>
  simp[] >> suspend "packet"
QED

Resume make_array_header_full[packet]:
  `base < dimword (:256)` by decide_tac >>
  `eval_operand (Lit (n2w len)) s = SOME (n2w len)` by
    simp[eval_operand_def] >>
  drule_all mstore_raw_ghost_frame >>
  disch_then (qspecl_then [`tn`,`sm.cs_next_id`,`PG`,`G`] strip_assume_tac) >>
  gvs[wordsTheory.w2n_n2w, ptrDisciplineTheory.op_taint_def] >>
  `sm.cs_next_id <= sh.cs_next_id` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv sh` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sm` >> simp[]) >>
  `not_fresh_at sh q` by fs[loweringStateRelDefsTheory.not_fresh_at_def] >>
  `ai.inst_id < sh.cs_next_id` by decide_tac >>
  `lookup_var q (mstore base (n2w len) s with vs_inst_idx := LENGTH sh.cs_current_insts) = SOME (n2w base)` by
    fs[lookup_var_def,mstore_def] >>
  `!name b n. local_region cenv es.scopes
    (mstore base (n2w len) s with vs_inst_idx := LENGTH sh.cs_current_insts) name b n =
    local_region cenv es.scopes s name b n` by
    simp[loweringStateRelDefsTheory.local_region_def,lookup_var_def,mstore_def] >>
  `ptr_covers G
    (step_taint (mk_inst sm.cs_next_id MSTORE [Var q;Lit (n2w len)] []) s
      (mstore base (n2w len) s) tn) q (mstore base (n2w len) s) cap` by
    fs[bodyPtrDefsTheory.ptr_covers_def,ptrDisciplineTheory.op_taint_def,lookup_var_def,mstore_def] >>
  `return_buf_frame d cenv sh (mstore base (n2w len) s with vs_inst_idx := LENGTH sh.cs_current_insts)` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`,`s`,`sm`] >> simp[lookup_var_def,mstore_def]) >>
  `!b w. (mstore b w s).vs_current_bb = s.vs_current_bb` by simp[mstore_def] >>
  simp[] >>
  conj_tac >- (rpt strip_tac >> first_x_assum irule >> qexists_tac `name` >> simp[]) >>
  conj_tac >- suspend "history" >>
  conj_tac >- suspend "wb" >>
  conj_tac >- suspend "kept" >>
  conj_tac >- suspend "horizons" >>
  conj_tac >- suspend "word" >>
  conj_tac >- suspend "decode" >>
  conj_tac >- suspend "exterior" >>
  suspend "locals"
QED

Resume make_array_header_full[history]:
  qpat_x_assum `!D explicit. gas_origin_ptr_path _ _ _ _`
    (qspecl_then [`ARB`,`ARB`] assume_tac) >>
  drule_all body_full_path_alloca_history >> simp[]
QED
Resume make_array_header_full[wb]:
  `wb_frame cenv ebase es csbase sbase (mstore base (n2w len) s)` suffices_by
    (strip_tac >> fs[loweringPostsTheory.wb_frame_def,
      loweringPostsTheory.locals_kept_def, loweringPostsTheory.popped_kept_def,
      loweringStateRelDefsTheory.local_region_def, lookup_var_def] >>
     rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  irule raw_log_mstore_frame >> conj_tac
  >- (rpt strip_tac >>
      `aid <> ai.inst_id` by decide_tac >>
      `base + cap <= b \/ b + sz <= base` by
        (fs[alloca_inv_def, allocas_non_overlapping_def] >> metis_tac[]) >>
      fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  simp[] >> qexists_tac `es` >> simp[] >> rpt strip_tac >>
  `loweringStateRelDefs$regions_disjoint base cap b sz` by
    (first_x_assum irule >> qexists_tac `n` >> simp[]) >>
  fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED
Resume make_array_header_full[kept]:
  qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[bodyPtrDefsTheory.ghost_kept_at_def, ptrDisciplineTheory.op_taint_def] >>
  rpt (pop_assum kall_tac) >> metis_tac[]
QED
Resume make_array_header_full[horizons]:
  gen_tac >> disch_tac >>
  `stmt_state_rel H ctx func cenv cx es s /\
   ghost_inv_at (DF H) lo d cenv cx es G tn s` by metis_tac[] >>
  simp[stmt_state_rel_inst_idx,ghost_inv_at_inst_idx] >>
  conj_tac
  >- (irule literal_mstore_state_rel >> simp[] >>
      qexistsl_tac [`base`,`ai`,`cap`] >> simp[] >>
      rpt strip_tac >>
      `loweringStateRelDefs$regions_disjoint base cap lb lsz` by
        (first_x_assum irule >> qexists_tac `name` >> simp[]) >>
      fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  irule wordLoadStorePtrTheory.ghost_inv_at_mstore_clean >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      `loweringStateRelDefs$regions_disjoint base cap b sz` by
        (first_x_assum irule >> qexists_tac `name` >> simp[]) >>
      fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  conj_tac >- (qexists_tac `func` >> fs[stmt_state_rel_def,loweringStateRelDefsTheory.state_rel_def]) >>
  qexists_tac `tn` >> simp[]
QED
Resume make_array_header_full[word]:
  simp[valueEncodingDefsTheory.val_wf_def,loweringPostsTheory.val_footprint_def,
       type_memory_size_def,valueEncodingDefsTheory.val_in_memory_def,
       val_to_w256_def,integer_wordTheory.i2w_def] >>
  rpt strip_tac >>
  `base < dimword (:256)` by decide_tac >>
  `mem_word_at (w2n (n2w base : bytes32)) m = n2w len` suffices_by
    simp[wordsTheory.w2n_n2w] >>
  irule mstore_raw_robust_word >>
  qexistsl_tac [`q`,`sm.cs_next_id`,`s`,`tn`] >> simp[] >>
  qexists_tac `Lit (n2w len)` >> simp[ptrDisciplineTheory.op_taint_def]
QED
Resume make_array_header_full[decode]:
  rpt strip_tac >>
  `base < dimword (:256)` by decide_tac >>
  `mem_word_at (w2n (n2w base : bytes32)) m = n2w len` suffices_by
    simp[wordsTheory.w2n_n2w] >>
  irule mstore_raw_robust_word >>
  qexistsl_tac [`q`,`sm.cs_next_id`,`s`,`tn`] >> simp[] >>
  qexists_tac `Lit (n2w len)` >> simp[ptrDisciplineTheory.op_taint_def]
QED
Resume make_array_header_full[exterior]:
  rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> decide_tac
QED
Resume make_array_header_full[locals]:
  rpt strip_tac >>
  `loweringStateRelDefs$regions_disjoint base cap b n` by
    (first_x_assum irule >> qexists_tac `name` >> simp[]) >>
  irule mstore_mem_bytes_at_disjoint >>
  fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Finalise make_array_header_full
