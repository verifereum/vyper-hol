(*
 * Dynamic-array append over the finite-horizon joint judgment.
 * Stated over the finite-horizon full family (bodySimFull), one sub-shape
 * per S1 dispatch arm of bodySimStmtCases/bodySimDeclCases, so the case in
 * bodyFullCases closes by the same case split.
 *
 * TOP-LEVEL: the body_*_full sub-shape theorems below.
 *)
Theory bodyFullAppend
Ancestors
  bodyFullShadowBodyInv bodyFullMemoryStore bodyFullMemorySameTypeStore
  bodySimStmtFacts[qualified,ignore_grammar]
  bodyInvCodeProps[qualified,ignore_grammar] exprBodyPreProps[qualified,ignore_grammar]
  bodyTypedTargetScope[qualified,ignore_grammar]
  exprBodyPreCallSafetyProps[qualified,ignore_grammar]
  bodyFullStructLitPhysical immutableDeployAssignRanges
  placeMemoryTypeInterfaces
  bodyFullStoreSlotsPath bodyFullStoreSlotsStatic
  memoryPlaceStorePost stmtSimAugAssignPlaceMemory
  stateRelProj bodyFullAppendLocalFrames bodyFullAppendNestedFrames
  bodyFullMemoryFrames bodyFullMemoryCopy typedCopyOriginPtrBase
  robustCopyTransportPtr typedMemoryCopy loweringStateRelDefs
  bodyPtrMakeArrayCopyStateFrame bodyMemAggregatePath
  stmtSimAppendStorageCompose bodyFullMemoryStage bodyFullPathHistory
  bodyFullTarget bodyAppendResolvedPre gasOutcomeFullCompose stmtLoweringMono
  loweringPosts supportedTypes exprSimSource gasShadowCompileStmtHelpers
  exprLoweringProps
  bodyFullAppendResolved placeStore bodyPtrDefs valueEncodingDefs
  assignTuplePtrStoreWord rawCallBufferPtr vyperPlaceWriteSoundness vyperTyping
  tuplePlaceSourceHead exprSimPrecompiles stmtSimForArrayFrame vyperScopePreservation
  appendStorageStageTransportPtr appendStorageStaticPtr fragGasCopyLoop instSeqPtrLo appendResolvedStorageRel
  fragGasCopySeqLiftProps
  vyperFiniteStoragePreservation assignTuplePtrLoadStep targetSubscriptStorage appendStorageGhostPtr
  bodyFullPreds bodySimFull gasShadow bodySim exprSimHypsDefs supportedStmts
  compileEnv exprLowering stmtLowering vyperTypeSystem vyperContext
  vyperInterpreter vyperState vyperValue vyperAST list finite_map
  targetPlaceSimCases vyperExprNoControl vyperTypeCallGraph
  vyperTypeCallStackSoundness bodyFullShared vyperStorageTrace vyperStorageFootprint
  vyperEvalExprPreservesScopesDom immutableDeployPhysicalSource

val _ = Parse.hide "body";

Theorem append_staged_store_path[local]:
  compile_store_memory cenv (Var xs) (Var xd) dty sty sa = ((),sb) /\
  ~is_word_type dty /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  0 < type_memory_size stv /\ type_memory_size dtv + 64 < dimword (:256) /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  not_fresh_at sa xs /\ not_fresh_at sa xd /\
  lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory stv v (w2n sw) mem) /\
  ptr_covers G tn xs s (type_memory_size stv) /\
  ptr_covers G tn xd s (type_memory_size dtv) /\
  w2n sw + val_store_size stv v < dimword (:256) /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  w2n sw + val_store_size stv v <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv <= s.vs_alloca_next /\
  (~is_bytestring_type sty ==> w2n sw + type_memory_size stv <= w2n dw \/
    w2n dw + type_memory_size dtv <= w2n sw) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
      val_in_memory dtv v (w2n dw) mem) /\
    typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!i. ~(w2n dw <= i /\ i < w2n dw+type_memory_size dtv) ==>
      (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `is_bytestring_type sty`
  >- suspend "bytestring" >>
  `val_store_size stv v = type_memory_size stv` by
    metis_tac[bodyDeclMemoryCoreTheory.val_store_size_non_bytestring] >>
  mp_tac (SPEC_ALL bodyFullMemoryStoreTheory.body_full_memory_store_path) >>
  fs[] >> disch_then irule >> first_assum ACCEPT_TAC
QED

Resume append_staged_store_path[bytestring]:
  `is_bytestring_type dty` by
    metis_tac[typedMemoryCopyTheory.type_widens_from_bytestring] >>
  `~is_word_type sty` by metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
  `compile_store_memory cenv (Var xs) (Var xd) sty sty sa = ((),sb)` by
    fs[contextTheory.compile_store_memory_def] >>
  `arg_type_fits sty dty` by fs[vyperTypeSystemTheory.type_widens_to_def] >>
  `type_memory_bytes cenv sty <= type_memory_bytes cenv dty` by
    simp[memoryLocalRhsPropsTheory.arg_type_fits_bytestring_memory_bytes] >>
  `type_memory_size stv <= type_memory_size dtv` by fs[] >>
  `type_memory_size stv + 64 < dimword (:256)` by decide_tac >>
  `ptr_covers G tn xd s (type_memory_size stv)` by
    metis_tac[reasonCopySourcePtrTheory.ptr_covers_mono] >>
  `w2n dw + type_memory_size stv < dimword (:256) /\
    w2n dw + type_memory_size stv <= s.vs_alloca_next` by decide_tac >>
  drule_all bodyFullMemorySameTypeStoreTheory.body_full_memory_same_type_store_path >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t` by
    (irule typedMemoryCopyTheory.typed_copy_state_frame_subinterval >>
     qexistsl_tac [`w2n dw`,`type_memory_size stv`] >> simp[]) >>
  qexistsl_tac [`t`,`Gf`,`tf`] >> simp[] >>
  conj_tac >- metis_tac[valueCopyBytesTheory.bytestring_val_in_memory_transfer] >>
  rpt strip_tac >> metis_tac[valueCopyBytesTheory.bytestring_val_in_memory_transfer]
QED

Finalise append_staged_store_path[local]

(* Staging ends before the storage guard; it needs no static/no-dalloca
   restriction.  The allocation/copy compiler cut is kept explicit. *)
Theorem append_storage_aggregate_stage_ready[local]:
  stmt_state_rel H0 ctx func cenv cx es s /\
  compile_alloc_buffer n sa = (buf,sm) /\
  compile_store_memory cenv (Var xs) buf.buf_operand dty sty sm = ((),sb) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !rt. evaluate_type (get_tenv cx) fty = SOME rt ==>
      sz = type_memory_size rt) fields) /\
  type_widens_to (get_tenv cx) sty dty /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  local_ptrs_reserved cenv sa /\ fn_inst_ids_distinct func /\
  n + 64 < dimword (:256) /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  alloca_history func s /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  not_fresh_at sa xs /\ lookup_var xs s = SOME sw /\
  evaluate_type (get_tenv cx) sty = SOME tv /\ ~is_word_type sty /\
  ~is_word_type dty /\ type_memory_bytes cenv sty = type_memory_size tv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\ type_memory_size dtv = n /\
  type_memory_bytes cenv dty = n /\ 0 < type_memory_size tv /\
  value_has_type tv v /\ value_has_type dtv v /\ val_wf tv v /\ val_wf dtv v /\
  expr_val_at cenv cx sty start sa es v (Var xs) s /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv v (w2n sw) mem) /\
  ptr_covers G tn xs s (type_memory_size tv) /\
  w2n sw + val_store_size tv v < dimword (:256) /\
  w2n sw + val_store_size tv v <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t root b Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    (!H. stmt_state_rel H ctx func cenv cx es s ==>
      stmt_state_rel H ctx func cenv cx es t) /\
    (!D d. ghost_inv_at D lo d cenv cx es G tn s ==>
      ghost_inv_at D lo d cenv cx es Gf tf t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    buf.buf_operand = Var root /\ not_fresh_at sb root /\
    lookup_var root t = SOME (n2w b) /\ ptr_covers Gf tf root t n /\
    op_taint tf buf.buf_operand = {} /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b,n) /\
    lo <= b /\ b+n < dimword (:256) /\ b+n <= t.vs_alloca_next /\
    (!name a len. local_region cenv es.scopes t name a len ==>
      regions_disjoint b n a len) /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
      val_in_memory dtv v b mem) /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==>
      FLOOKUP t.vs_allocas aid = SOME ent) /\
    (!x. not_fresh_at sa x ==>
      not_fresh_at sb x /\ lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    alloca_history func t /\ alloca_frame cenv es sa s cenv es t /\
    (!aid off sz. aid < sa.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (off,sz) ==>
      !i. off <= i /\ i < off+sz ==> (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    (!i. ~(b <= i /\ i < b+n) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tf.t_mem <=> i IN tn.t_mem))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `n < dimword (:256)` by decide_tac >>
  drule_all bodyFullMemoryFramesTheory.body_full_alloc_buffer_path >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`] strip_assume_tac) >>
  `b < dimword (:256)` by decide_tac >>
  `not_fresh_at sm xs /\ lookup_var xs u = SOME sw` by metis_tac[] >>
  `!name a len. local_region cenv es.scopes u name a len <=>
    local_region cenv es.scopes s name a len` by
    (rw[loweringStateRelDefsTheory.local_region_def] >>
     metis_tac[loweringStateRelDefsTheory.local_ptrs_reserved_def]) >>
  `!mem. mem_agree_outside tn1.t_mem u.vs_memory mem ==>
    val_in_memory tv v (w2n sw) mem` by suspend "source" >>
  `s.vs_alloca_next <= u.vs_alloca_next` by suspend "frontier" >>
  `w2n sw + val_store_size tv v <= u.vs_alloca_next` by decide_tac >>
  `b+n <= u.vs_alloca_next` by suspend "end_bound" >>
  `compile_store_memory cenv (Var xs) (Var root) dty sty sm = ((),sb)` by metis_tac[] >>
  `ptr_covers G1 tn1 xs u (type_memory_size tv)` by metis_tac[] >>
  `w2n ((n2w b):bytes32) = b` by simp[] >>
  SUBGOAL_THEN
    ``~is_bytestring_type sty ==>
      w2n (sw:bytes32) + type_memory_size tv <= b \/ b+n <= w2n sw``
    ASSUME_TAC >- suspend "separation" >>
  mp_tac (Q.INST [`sa` |-> `sm`, `s` |-> `u`, `tn` |-> `tn1`,
    `G` |-> `G1`, `xd` |-> `root`, `dw` |-> `(n2w b):bytes32`,
    `tenv` |-> `get_tenv cx`, `stv` |-> `tv`]
    (SPEC_ALL append_staged_store_path)) >>
  (impl_tac >-
    (simp[] >> conj_tac
     >- (rpt gen_tac >> strip_tac >> res_tac >> simp[]) >>
     strip_tac >> res_tac >> decide_tac)) >>
  strip_tac >>
  qpat_assum `w2n ((n2w b):bytes32) = b` (fn addr =>
    qpat_assum `type_memory_size dtv = n` (fn size =>
      RULE_ASSUM_TAC (PURE_REWRITE_RULE [addr,size]))) >>
  `t.vs_allocas = u.vs_allocas /\ t.vs_alloca_next = u.vs_alloca_next` by
    (fs[typed_copy_state_frame_def,venomStateTheory.venom_state_component_equality]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    metis_tac[typed_copy_state_frame_allocas_below_fmp] >>
  `ci_mono sm sb` by metis_tac[exprLoweringPropsTheory.ci_mono_compile_store_memory,pairTheory.SND] >>
  `!x. not_fresh_at sm x ==> not_fresh_at sb x` by
    (fs[exprLoweringPropsTheory.ci_mono_def] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `lookup_var root t = SOME (n2w b) /\
    FLOOKUP Gf root = FLOOKUP G1 root /\
    op_taint tf (Var root) = op_taint tn1 (Var root)` by metis_tac[] >>
  `ptr_covers Gf tf root t n` by metis_tac[assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame] >>
  `op_taint tf buf.buf_operand = {}` by fs[ptr_covers_def] >>
  `!name a len. local_region cenv es.scopes t name a len <=>
    local_region cenv es.scopes u name a len` by
    (rw[local_region_def] >> metis_tac[local_ptrs_reserved_def]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sb x /\
    lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tf (Var x) = op_taint tn (Var x)` by metis_tac[] >>
  `allocas_from lo t` by (fs[ptrDisciplineTheory.allocas_from_def] >> metis_tac[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK t,Gf,tf)` by
    (gen_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _`
       (qspec_then `D` (mp_tac o MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_append)) >>
     disch_then (qspecl_then [`u`,`G1`,`tn1`,`[]`,`OK t`,`Gf`,`tf`] mp_tac) >>
     simp[]) >>
  `alloca_history func t` by
    (irule bodyFullPathHistoryTheory.body_full_path_alloca_history >>
     goal_assum (drule_at Any) >>
     metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca]) >>
  qexistsl_tac [`t`,`root`,`b`,`Gf`,`tf`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "state" >>
  conj_tac >- suspend "ghost" >>
  simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- suspend "frame" >>
  conj_tac >- suspend "older_taint" >> suspend "exterior"
QED

Resume append_storage_aggregate_stage_ready[source]:
  mp_tac (Q.SPECL [`tn.t_mem`,`tn1.t_mem`,`s.vs_memory`,`u.vs_memory`,
    `{i | b <= i /\ i < b+n}`,`tv`,`v`,`w2n (sw:bytes32)`]
    robust_val_in_memory_exterior_frame) >>
  (impl_tac >-
    (simp[] >> rpt strip_tac >>
     qpat_assum `expr_val_at _ _ _ _ _ _ _ _ _`
       (mp_tac o Q.SPEC `tv` o REWRITE_RULE [loweringPostsTheory.expr_val_at_def]) >>
     simp[venomStateTheory.eval_operand_def] >> strip_tac >>
     gvs[regions_disjoint_def] >> res_tac >> decide_tac)) >> simp[]
QED

Resume append_storage_aggregate_stage_ready[separation]:
  strip_tac >>
  `eval_operand (Var xs) s = SOME sw` by simp[venomStateTheory.eval_operand_def] >>
  drule_all immutableDeployAssignRangesTheory.immutable_assign_nonbytes_source_owned >>
  strip_tac
  >- fs[]
  >- (`regions_disjoint b n b' sz` by metis_tac[] >>
      fs[regions_disjoint_def] >> decide_tac) >>
  `regions_disjoint b n b' sz` by metis_tac[] >>
  fs[regions_disjoint_def] >> decide_tac
QED

Resume append_storage_aggregate_stage_ready[frontier]:
  qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _`
    (qspec_then `cx_dead H0 cx` mp_tac) >>
  disch_then (strip_assume_tac o MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_projections) >>
  drule fragGasOriginTheory.gas_origin_path_erase >> strip_tac >>
  drule fragGasModeTheory.gas_marked_path_exec >> strip_tac >>
  drule bodyMemBopRestWordPathTheory.rest_word_path_frontier >> simp[]
QED

Resume append_storage_aggregate_stage_ready[end_bound]:
  `alloca_inv s` by
    metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca] >>
  qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _`
    (qspec_then `cx_dead H0 cx` mp_tac) >>
  disch_then (strip_assume_tac o MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_projections) >>
  `gas_path_mem ctx func s 0 (OK u)` by
    (drule fragGasOriginTheory.gas_origin_path_erase >>
     simp[fragGasModeTheory.gas_marked_path_def]) >>
  `alloca_inv u` by metis_tac[bodyMemAggregatePathTheory.aggregate_mem_path_alloca_inv] >>
  fs[venomMemDefsTheory.alloca_inv_def,venomMemDefsTheory.alloca_next_valid_def] >>
  qpat_x_assum `!aid base sz. FLOOKUP u.vs_allocas aid = SOME (base,sz) ==> _`
    (qspecl_then [`sa.cs_next_id`,`b`,`n`] mp_tac) >> simp[]
QED

Resume append_storage_aggregate_stage_ready[state]:
  rpt strip_tac >>
  `copy_static t = copy_static u` by
    (qpat_assum `typed_copy_state_frame _ _ _ _ _`
       (mp_tac o AP_TERM ``copy_static`` o CONJUNCT1 o
        REWRITE_RULE [typed_copy_state_frame_def]) >> simp[exprSimStorageCopyTheory.copy_static_def]) >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    metis_tac[exprSimAllocTheory.buffer_alloc_code] >>
  qpat_assum `typed_copy_state_frame _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE
      [typed_copy_state_frame_def,typed_copy_frame_def]) >>
  irule literal_copy_window_stmt_state_rel >>
  qexistsl_tac [`sa.cs_next_id`,`b`,`n`,
    `STRING #"%" (toString sa.cs_next_var)`,`sa`,`sm`,`u`] >>
  rpt conj_tac >> rpt strip_tac >> simp[] >> metis_tac[]
QED

Resume append_storage_aggregate_stage_ready[ghost]:
  rpt strip_tac >>
  `ghost_inv_at D lo d cenv cx es G1 tn1 u` by metis_tac[] >>
  `t.vs_call_ctx = u.vs_call_ctx /\ t.vs_immutables = u.vs_immutables /\
   t.vs_accounts = u.vs_accounts /\ t.vs_transient = u.vs_transient /\
   t.vs_allocas = u.vs_allocas /\ t.vs_alloca_next = u.vs_alloca_next` by
    (qpat_assum `typed_copy_state_frame _ _ _ _ _`
       (mp_tac o AP_TERM ``\z. (z.vs_call_ctx,z.vs_immutables,z.vs_accounts,
          z.vs_transient,z.vs_allocas,z.vs_alloca_next)`` o CONJUNCT1 o
        REWRITE_RULE [typed_copy_state_frame_def]) >> simp[]) >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (fs[ptrDisciplineTheory.allocas_from_def] >> metis_tac[]) >>
  `!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==>
    not_fresh_at sm x` by metis_tac[] >>
  `!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==>
    not_fresh_at sm x` by metis_tac[] >>
  irule bodyFullMemoryFramesTheory.body_full_memory_ghost_frame >>
  simp[] >> qexistsl_tac [`G1`,`u`,`sm`,`tn1`,`{i | b <= i /\ i < b+n}`] >>
  simp[] >> rpt conj_tac
  >- (qx_genl_tac [`name`,`entry`,`p`,`cap`,`w`] >> strip_tac >>
      `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
      `lookup_var p s = SOME w` by metis_tac[] >>
      `!name a len. local_region cenv es.scopes s name a len ==>
        regions_disjoint b n a len` by
        (qpat_assum `!name a len. local_region cenv es.scopes u name a len ==> _` mp_tac >>
         simp[]) >>
      drule_all exprSimPtrLiteralBufferTheory.literal_ptr_local_footprint_exterior >> simp[])
  >- (qx_gen_tac `i` >> strip_tac >>
      qpat_assum `typed_copy_state_frame _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE
          [typed_copy_state_frame_def,typed_copy_frame_def]) >>
      qpat_assum `!a len. a+len <= b \/ b+n <= a ==> _`
        (qspecl_then [`i`,`1`] mp_tac) >>
      (impl_tac >-
        (irule (DECIDE ``!b i n:num.
          ~(b <= i /\ i < b+n) ==> i+1 <= b \/ b+n <= i``) >> simp[])) >> simp[])
  >- (qx_gen_tac `i` >> strip_tac >>
      `~(b <= i /\ i < b+n)` by
        (irule (DECIDE ``!i lo b n:num.
          i < lo /\ lo <= b ==> ~(b <= i /\ i < b+n)``) >>
         qexists_tac `lo` >> simp[]) >>
      qpat_assum `!i. _ ==> (i IN tf.t_mem <=> i IN tn1.t_mem)`
        (qspec_then `i` mp_tac) >>
      qpat_assum `!i. _ ==> (i IN tn1.t_mem <=> i IN tn.t_mem)`
        (qspec_then `i` mp_tac) >> simp[])
  >- (qpat_assum `typed_copy_state_frame _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE
          [typed_copy_state_frame_def,typed_copy_frame_def]) >>
      qpat_assum `!a len. a+len <= b \/ b+n <= a ==> _`
        (qspecl_then [`0`,`lo`] mp_tac) >>
      (impl_tac >- simp[]) >> simp[]) >>
  fs[typed_copy_state_frame_def,venomStateTheory.venom_state_component_equality,
    ptrDisciplineTheory.allocas_from_def] >> metis_tac[]
QED

Resume append_storage_aggregate_stage_ready[frame]:
  irule stmtSimDefsTheory.alloca_frame_of_mem_frame >>
  simp[] >> reverse conj_tac
  >- (qexistsl_tac [`H0`,`ctx`,`cx`,`func`] >> first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  `regions_disjoint b n off sz` by metis_tac[] >>
  fs[typed_copy_state_frame_def,typed_copy_frame_def,regions_disjoint_def] >>
  metis_tac[]
QED

Resume append_storage_aggregate_stage_ready[older_taint]:
  rpt strip_tac >>
  `regions_disjoint b n off sz` by metis_tac[] >>
  `~(b <= i /\ i < b+n)` by (fs[regions_disjoint_def] >> decide_tac) >>
  metis_tac[]
QED

Resume append_storage_aggregate_stage_ready[exterior]:
  qx_gen_tac `i` >> strip_tac >>
  `i+1 <= b \/ b+n <= i` by decide_tac >>
  qpat_assum `typed_copy_state_frame sm b n u t`
    (qspecl_then [`i`,`1`] mp_tac o cj 3 o
      PURE_REWRITE_RULE [typed_copy_state_frame_def,typed_copy_frame_def]) >>
  simp[]
QED

Finalise append_storage_aggregate_stage_ready[local]

(* Retain the primitive's exact endpoint while varying only the horizon. *)
Theorem append_storage_address_binop_uniform[local]:
  emit_op opc [left;right] a = (op,b) /\ fn_has_code a b func /\
  (opc = MUL /\ w = x*y \/ opc = ADD /\ w = x+y) /\
  eval_operand left s = SOME x /\ eval_operand right s = SOME y /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?out t Gf tf.
    op = Var out /\ not_fresh_at b out /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    eval_operand op t = SOME w /\ op_taint tf op = {} /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    typed_copy_state_frame a 0 0 s t /\ t.vs_memory = s.vs_memory /\
    t.vs_labels = s.vs_labels /\ tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\
    (!p. not_fresh_at a p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all typed_copy_origin_ptr_binop_path >>
  disch_then (qspecl_then [`0`,`0`,`explicit`,`PG`,`G`,`ARB`] strip_assume_tac) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK t,G',tn')` by
    (gen_tac >> drule_all typed_copy_origin_ptr_binop_path >>
     disch_then (qspecl_then [`0`,`0`,`explicit`,`PG`,`G`,`D`] strip_assume_tac) >>
     gvs[]) >>
  `!p. not_fresh_at a p ==> p <> out` by
    (drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
     gvs[not_fresh_at_def] >> metis_tac[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    metis_tac[typed_copy_state_frame_allocas_below_fmp] >>
  qexistsl_tac [`out`,`t`,`G'`,`tn'`] >>
  gvs[] >>
  simp[typed_copy_origin_ptr_binop_ghost_frame] >>
  rpt strip_tac >> `p <> out` by metis_tac[] >>
  simp[typed_copy_origin_ptr_binop_ghost_frame,
    venomStateTheory.update_var_def,venomStateTheory.lookup_var_def,
    finite_mapTheory.FLOOKUP_UPDATE]
QED

(* The cursor here is the successful guard endpoint, not its input. *)
Theorem append_storage_aggregate_address_ready[local]:
  emit_op ADD [bop; Lit 1w] a = (dop,b) /\
  emit_op MUL [lop; Lit (n2w (type_slot_size tv))] b = (off,c) /\
  emit_op ADD [dop;off] c = (addr,d) /\ fn_has_code a d func /\
  (!x. bop = Var x \/ lop = Var x ==> not_fresh_at a x) /\
  eval_operand bop s = SOME slot /\ eval_operand lop s = SOME (n2w len) /\
  op_taint tn bop = {} /\ op_taint tn lop = {} /\
  0 < type_slot_size tv /\ len < cap /\
  w2n slot + (1+cap*type_slot_size tv) <= dimword (:256) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?out t Gf tf.
    addr = Var out /\ not_fresh_at d out /\
    eval_operand addr t = SOME (slot+n2w (1+len*type_slot_size tv)) /\
    op_taint tf addr = {} /\
    w2n (slot+n2w (1+len*type_slot_size tv)) + type_slot_size tv <= dimword (:256) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    typed_copy_state_frame a 0 0 s t /\ t.vs_memory = s.vs_memory /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    ~t.vs_halted /\ t.vs_current_bb = d.cs_current_bb /\
    t.vs_inst_idx = LENGTH d.cs_current_insts /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at a x ==> not_fresh_at d x /\
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d` by
    metis_tac[typed_copy_emit_op_mono] >>
  `cs_extends a b /\ cs_extends b c /\ cs_extends c d` by fs[ci_mono_def] >>
  `fn_has_code a b func /\ fn_has_code b c func /\ fn_has_code c d func` by
    metis_tac[fragExecTheory.fn_has_code_split,compileEnvTheory.cs_extends_trans] >>
  `!x. not_fresh_at a x ==> not_fresh_at b x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono,ci_mono_def] >>
  `!x. not_fresh_at b x ==> not_fresh_at c x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono,ci_mono_def] >>
  `!x. not_fresh_at c x ==> not_fresh_at d x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono,ci_mono_def] >>
  `eval_operand (Lit 1w) s = SOME 1w /\ op_taint tn (Lit 1w) = {}` by
    simp[venomStateTheory.eval_operand_def,ptrDisciplineTheory.op_taint_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`, `w` |-> `x+y`]
    append_storage_address_binop_uniform)) >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`] strip_assume_tac) >>
  rename1 `dop = Var vdata` >>
  rename1 `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK q1,G1,tn1)` >>
  `eval_operand lop q1 = SOME (n2w len) /\ op_taint tn1 lop = {}` by
    (Cases_on `lop` >> fs[venomStateTheory.eval_operand_def,ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
  `eval_operand (Lit (n2w (type_slot_size tv))) q1 = SOME (n2w (type_slot_size tv)) /\
    op_taint tn1 (Lit (n2w (type_slot_size tv))) = {}` by
    simp[venomStateTheory.eval_operand_def,ptrDisciplineTheory.op_taint_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `MUL`, `w` |-> `x*y`]
    append_storage_address_binop_uniform)) >>
  disch_then (qspecl_then [`explicit`,`PG`,`G1`] strip_assume_tac) >>
  rename1 `off = Var vscale` >>
  rename1 `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (q1,G1,tn1) [] (OK q2,G2,tn2)` >>
  `eval_operand dop q2 = SOME (slot+1w) /\ op_taint tn2 dop = {}` by
    (gvs[venomStateTheory.eval_operand_def,ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`, `w` |-> `x+y`]
    append_storage_address_binop_uniform)) >>
  disch_then (qspecl_then [`explicit`,`PG`,`G2`] strip_assume_tac) >>
  rename1 `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (q2,G2,tn2) [] (OK t,Gf,tf)` >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK t,Gf,tf)` by suspend "paths" >>
  `typed_copy_state_frame a 0 0 s t` by suspend "frame" >>
  `w2n (slot+n2w (1+len*type_slot_size tv)) + type_slot_size tv <= dimword (:256)`
    by suspend "bound" >>
  `slot+1w+n2w len*n2w (type_slot_size tv) =
    slot+n2w (1+len*type_slot_size tv)` by
    (pure_rewrite_tac[wordsTheory.word_mul_n2w,
       GSYM wordsTheory.word_add_n2w,wordsTheory.WORD_ADD_ASSOC] >> REFL_TAC) >>
  qexistsl_tac [`out`,`t`,`Gf`,`tf`] >> simp[] >>
  metis_tac[]
QED

Resume append_storage_aggregate_address_ready[paths]:
  gen_tac >> metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans]
QED

Resume append_storage_aggregate_address_ready[frame]:
  `ci_mono a c` by metis_tac[exprLoweringPropsTheory.ci_mono_trans] >>
  `typed_copy_state_frame a 0 0 q1 q2 /\
   typed_copy_state_frame a 0 0 q2 t` by
    metis_tac[typed_copy_state_frame_mono] >>
  metis_tac[typed_copy_state_frame_trans]
QED

Resume append_storage_aggregate_address_ready[bound]:
  `len * type_slot_size tv + type_slot_size tv <= cap * type_slot_size tv` by
    (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
  `w2n slot + (1 + len * type_slot_size tv) < dimword (:256)` by decide_tac >>
  simp[wordsTheory.word_add_def,wordsTheory.w2n_n2w,arithmeticTheory.LESS_MOD] >>
  decide_tac
QED

Finalise append_storage_aggregate_address_ready[local]

(* Unpack the observed storage place once, with a natural (non-wrapping)
   slot address and a range bound for the whole array. *)
Theorem append_observed_array_bounds[local]:
  storage_place_observed H (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) /\
  regions_consistent (FST H) ==>
  ?rootk root path delta.
    MEM (tr,rootk,root) (FST H) /\
    storage_subregion root path delta (ArrayTV tv (Dynamic cap)) /\
    w2n slot = w2n rootk + delta /\
    w2n rootk + type_slot_size root <= dimword (:256) /\
    w2n slot + (1+cap*type_slot_size tv) <= dimword (:256)
Proof
  strip_tac >>
  qpat_x_assum `storage_place_observed _ _`
    (qx_choosel_then [`rootk`,`root`,`path`,`delta`] strip_assume_tac o
     PURE_REWRITE_RULE [vyperStoragePlaceObservedTheory.storage_place_observed_def]) >>
  drule_then assume_tac vyperStoragePlaceRegionTheory.storage_subregion_bounds >>
  `w2n rootk + type_slot_size root <= dimword (:256)` by
    metis_tac[vyperStorageFootprintTheory.regions_consistent_def] >>
  `w2n rootk + delta < dimword (:256) /\ delta < dimword (:256)` by
    (fs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
  `w2n slot = w2n rootk+delta` by
    simp[wordsTheory.word_add_def,wordsTheory.w2n_n2w] >>
  qexistsl_tac [`rootk`,`root`,`path`,`delta`] >>
  simp[] >> fs[vyperValueTheory.type_slot_size_def] >> decide_tac
QED

Theorem append_subregion_sparse_state[local]:
  stmt_state_rel H ctx func cenv cx es s /\
  MEM (tr,rootk,root) (FST H) /\ regions_consistent (FST H) /\
  storage_locks_separated (FST H) (SND H) /\
  storage_subregion root path delta (ArrayTV tv (Dynamic cap)) /\
  w2n slot = w2n rootk + delta /\ w2n rootk + type_slot_size root <= dimword (:256) /\
  0 < type_slot_size tv /\ len < cap /\
  k = slot + n2w (1+len*type_slot_size tv) /\
  encode_value tv v = SOME writes /\ value_has_type tv v /\
  (!i. MEM i ks <=> MEM i (MAP FST writes)) /\
  (!i b. i < type_slot_size tv /\ b < 32 /\ MEM i (MAP FST writes) /\
    ~dead_bytes (apply_writes k writes (get_storage cx es tr)) (w2n k) tv (w2n k+i) b ==>
    EL b (word_to_bytes (lookup_storage (k+n2w i)
       (apply_writes k writes (get_storage cx es tr))) T) = EL b (word_to_bytes (rd i) T)) ==>
  stmt_state_rel H ctx func cenv cx
    (set_storage cx es tr (update_storage slot h (apply_writes k writes (get_storage cx es tr))))
    ((if tr then tstore else sstore) slot h
      (FOLDL (\q i. (if tr then tstore else sstore) (k+n2w i) (rd i) q) s ks))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac append_observed_child >>
  drule_all_then strip_assume_tac placeStoreStorageTheory.place_store_root_layout >>
  drule_then (qspec_then `tr` assume_tac) stmtSimAssignStorageCopyTheory.storage_copy_initial_agree >>
  qabbrev_tac `raw = apply_writes k writes (get_storage cx es tr)` >>
  qabbrev_tac `low = FOLDL (\st i. update_storage (k+n2w i) (rd i) st)
    (if tr then contract_transient s else contract_storage s) ks` >>
  `storage_agree (storage_dead H tr raw) raw low` by suspend "leaf" >>
  `storage_agree (storage_dead H tr (update_storage slot h raw))
     (update_storage slot h raw) (update_storage slot h low)` by suspend "header" >>
  mp_tac (Q.SPECL [`ctx`,`func`,`cenv`,`cx`,`es`,`s`,`tr`,
    `update_storage slot h raw`,`update_storage slot h low`]
      (INST_TYPE [alpha |-> ``:256``]
        placeStoreStorageTheory.place_store_storage_replace)) >>
  impl_tac >- simp[] >>
  Cases_on `tr` >>
  simp[Abbr `low`,stmtSimAssignStorageCopyTheory.storage_copy_backend_fold,
    venomStateTheory.sstore_def,venomStateTheory.tstore_def,venomStateTheory.contract_storage_def,
    vfmStateTheory.lookup_account_def,venomStateTheory.contract_transient_def,
    combinTheory.APPLY_UPDATE_THM,combinTheory.UPDATE_EQ]
QED

Resume append_subregion_sparse_state[leaf]:
  mp_tac (Q.SPECL [`H`,`tr`,`rootk`,`root`,
    `path ++ [ValueSubscript (IntV (&len))]`,
    `delta + (1+len*type_slot_size tv)`,`tv`,`w2n (k:bytes32)`,
    `writes`,`v`,`ks`,`rd`,`get_storage cx es tr`,
    `if tr then contract_transient s else contract_storage s`]
      placeStoreSlotsTheory.place_store_encoded_copy_agree_sparse) >>
  simp_tac std_ss [GSYM wordsTheory.word_add_n2w,wordsTheory.n2w_w2n] >>
  simp[Abbr `raw`,Abbr `low`]
QED

Resume append_subregion_sparse_state[header]:
  `!j b. storage_dead H tr (update_storage slot h raw) j b <=> storage_dead H tr raw j b` by
    (rpt gen_tac >>
     mp_tac (Q.INST [`H` |-> `H`,`tr` |-> `tr`,`rootk` |-> `(rootk:bytes32)`,
       `root` |-> `root`,`path` |-> `path`,`delta` |-> `delta`,`tv` |-> `tv`,
       `cap` |-> `cap`,`slot` |-> `(slot:bytes32)`,`st` |-> `raw`,`h` |-> `h`]
       append_subregion_header_storage_dead) >> simp[]) >>
  fs[storage_agree_def] >> rpt strip_tac >>
  rename1 `EL b (word_to_bytes (lookup_storage q _) T)` >>
  Cases_on `q = slot` >>
  gvs[vfmStateTheory.lookup_storage_def,vfmStateTheory.update_storage_def,combinTheory.APPLY_UPDATE_THM]
QED

Finalise append_subregion_sparse_state[local]

Theorem append_operand_frame[local]:
  (!label. op <> Label label) /\ (!x. op = Var x ==> not_fresh_at a x) /\
  (!x. not_fresh_at a x ==> lookup_var x t = lookup_var x s /\
    op_taint tf (Var x) = op_taint tn (Var x)) /\
  eval_operand op s = SOME w /\ op_taint tn op = {} ==>
  eval_operand op t = SOME w /\ op_taint tf op = {}
Proof
  Cases_on `op` >> simp[venomStateTheory.eval_operand_def,
    ptrDisciplineTheory.op_taint_def] >> metis_tac[]
QED

(* The sparse endpoint bridge is independent of the implementation of the
   slots path.  In particular, it assumes neither nonstatic execution nor a
   no-dalloca context for that path. *)
Theorem append_storage_aggregate_endpoint_post[local]:
  ~cx.txn.is_static /\
  stmt_state_rel H ctx func cenv cx es s /\
  storage_well_formed_on cx es (FST H) /\
  ghost_inv_at D lo d cenv cx es G tn s /\ dead_lo_ok H D lo cenv cx /\
  return_buf_frame d cenv sa s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. lo <> 0 /\ cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> not_fresh_at sb x) /\
  storage_place_observed H (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) /\
  regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
  0 < type_slot_size tv /\ well_formed_type_value tv /\ value_has_type tv v /\
  encode_value tv v = SOME writes /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv v (w2n b) mem) /\
  w2n b + 32 * type_slot_size tv <= dimword (:256) /\
  len = w2n (lookup_storage slot (get_storage cx es tr)) /\ len < cap /\
  k = slot+n2w (1+len*type_slot_size tv) /\
  (!i. MEM i ks <=> MEM i (MAP FST writes)) /\
  store_copy_normalize s u =
    (if tr then tstore else sstore) slot (n2w (len+1))
      (FOLDL (\q i. (if tr then tstore else sstore) (k+n2w i)
        (mem_word_at (w2n b+32*i) s.vs_memory) q) s ks) /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
  u.vs_alloca_next = s.vs_alloca_next /\ u.vs_call_ctx = s.vs_call_ctx /\
  u.vs_immutables = s.vs_immutables /\ tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
  (if tr then contract_storage u = contract_storage s /\ tf.t_stor = tn.t_stor
   else contract_transient u = contract_transient s /\ tf.t_trans = tn.t_trans) /\
  (if tr then tf.t_trans else tf.t_stor) SUBSET
    key_update
      (FOLDL (\X j. key_update X (k+n2w j)
        (mem_word_taint tn.t_mem (w2n b+32*j)))
        (if tr then tn.t_trans else tn.t_stor) ks) slot {} /\
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gf,tf) /\
  fn_inst_ids_distinct func /\ alloca_history func s /\
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v es = (res,ee) /\
  ee = set_storage cx es tr
    (update_storage slot (n2w (len+1)) (apply_writes k writes (get_storage cx es tr))) ==>
  res = INL () /\ stmt_state_rel H ctx func cenv cx ee u /\
  storage_well_formed_on cx ee (FST H) /\
  ghost_inv_at D lo d cenv cx ee Gf tf u /\ return_buf_frame d cenv sb u /\
  alloca_history func u /\ alloca_frame cenv es sa s cenv ee u /\
  tf.t_mem = tn.t_mem /\ u.vs_alloca_next = s.vs_alloca_next /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (qx_choosel_then [`rootk`,`root`,`path`,`delta`] strip_assume_tac)
    append_observed_array_bounds >>
  drule_all_then strip_assume_tac append_observed_child >>
  `val_in_memory tv v (w2n b) s.vs_memory` by
    metis_tac[bodyPtrDefsTheory.mem_agree_outside_def] >>
  `(!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s)` by metis_tac[] >>
  `res = INL ()` by suspend "result" >>
  `stmt_state_rel H ctx func cenv cx ee u` by suspend "relation" >>
  `storage_well_formed_on cx ee (FST H)` by suspend "well_formed" >>
  simp[] >>
  conj_tac >- suspend "ghost" >>
  conj_tac >- suspend "return" >>
  conj_tac >- (irule bodyFullPathHistoryTheory.body_full_path_alloca_history >>
    goal_assum (drule_at Any) >>
    metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca]) >>
  suspend "frame"
QED

Resume append_storage_aggregate_endpoint_post[result]:
  qpat_x_assum `append_place _ _ _ _ = _` mp_tac >>
  qpat_assum `len = w2n (lookup_storage slot _)` SUBST_ALL_TAC >>
  simp[stmtSimAppendStorageTheory.append_storage_writes, ignore_bind_def, bind_def,
    vyperStorageBackendTheory.write_storage_slot_eq,
    vyperStorageBackendTheory.get_storage_after_set, vyperStorageTheory.encode_value_def,
    vyperStorageTheory.encode_base_to_slot_def, vyperStorageTheory.apply_writes_def,
    integer_wordTheory.i2w_def] >>
  Cases_on `tr` >>
  simp[vyperStorageBackendTheory.set_storage_def, combinTheory.APPLY_UPDATE_THM]
QED

Resume append_storage_aggregate_endpoint_post[relation]:
  irule placeStoreStorageTheory.place_store_normalized_stmt_state >>
  qexistsl_tac [`s`,`sa`] >> simp[] >>
  qpat_assum `store_copy_normalize s u = _` SUBST1_TAC >>
  qpat_assum `ee = _` SUBST1_TAC >>
  mp_tac (Q.INST [`H` |-> `H`,`ctx` |-> `ctx`,`func` |-> `func`,`cenv` |-> `cenv`,
    `cx` |-> `cx`,`es` |-> `es`,`s` |-> `s`,`tr` |-> `tr`,`rootk` |-> `(rootk:bytes32)`,
    `root` |-> `root`,`path` |-> `path`,`delta` |-> `delta`,`tv` |-> `tv`,
    `cap` |-> `cap`,`slot` |-> `(slot:bytes32)`,`k` |-> `(k:bytes32)`,`len` |-> `len`,
    `v` |-> `v`,`writes` |-> `writes`,`ks` |-> `ks`,`h` |-> `(n2w (len+1):bytes32)`,
    `rd` |-> `\i. mem_word_at (w2n b+32*i) s.vs_memory`]
      append_subregion_sparse_state) >>
  BETA_TAC >> impl_tac >- suspend "memory_live" >>
  simp[]
QED

Resume append_storage_aggregate_endpoint_post[memory_live]:
  rename1 `val_in_memory tv v (w2n buf_word) s.vs_memory` >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  qx_genl_tac [`i`,`byidx`] >> strip_tac >>
  `w2n k < dimword (:256)` by simp[wordsTheory.w2n_lt] >>
  `EL byidx (word_to_bytes (lookup_storage (n2w (w2n k+i))
     (apply_writes (n2w (w2n k)) writes (get_storage cx es tr))) T) =
   EL byidx (word_to_bytes (mload (w2n buf_word+32*i) s) T)` suffices_by
    simp[GSYM wordsTheory.word_add_n2w,valueEncodingPropsTheory.mem_word_at_eq_mload] >>
  mp_tac (Q.INST [`tv` |-> `tv`,`v` |-> `v`,`off` |-> `w2n buf_word`,
    `s` |-> `s`,`start` |-> `w2n (k:bytes32)`,`writes` |-> `writes`,
    `i` |-> `i`,`b` |-> `byidx`,`st` |-> `get_storage cx es tr`]
      placeStoreStorageTheory.place_store_memory_live_at) >>
  impl_tac >-
    (pure_rewrite_tac[wordsTheory.n2w_w2n] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp_tac std_ss []
QED

Resume append_storage_aggregate_endpoint_post[well_formed]:
  `well_formed_type_value (ArrayTV tv (Dynamic cap))` by
    (`cap <= cap * type_slot_size tv` by
       (Cases_on `type_slot_size tv` >> gvs[arithmeticTheory.MULT_CLAUSES]) >>
     qpat_assum `w2n slot + (1 + cap * type_slot_size tv) <= _` mp_tac >>
     simp[vyperTypingTheory.well_formed_type_value_def,vyperValueTheory.type_slot_size_def] >>
     fs[wordsTheory.dimword_def] >> decide_tac) >>
  irule vyperFiniteStoragePreservationTheory.append_subregion_preserves_storage_well_formed_on >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`tr`,`delta`,`tv`,`cap`,`path`,`res`,`rootk`,`slot`,`es`,`root`,`v`] >>
  asm_rewrite_tac[]
QED

Resume append_storage_aggregate_endpoint_post[ghost]:
  `stor_taint_ok_at D tf u` by suspend "storage_taint" >>
  `!p sz. not_fresh_at sa p /\ ptr_covers G tn p s sz ==>
    ptr_covers Gf tf p u sz` by
    (rw[bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[]) >>
  gvs[bodyPtrDefsTheory.ghost_inv_at_def, vyperStorageBackendTheory.set_storage_def] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sa p` by
        metis_tac[loweringStateRelDefsTheory.local_ptrs_reserved_def] >>
      metis_tac[]) >>
  conj_tac
  >- (Cases_on `d` >> gvs[bodyPtrDefsTheory.return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME rb)` >> PairCases_on `rb` >>
      gvs[bodyPtrDefsTheory.return_buf_ptr_def] >> metis_tac[]) >>
  gvs[ptrDisciplineTheory.allocas_from_def] >> metis_tac[]
QED

Resume append_storage_aggregate_endpoint_post[storage_taint]:
  `s.vs_call_ctx.cc_address = cx.txn.target` by
    (drule stateRelProjTheory.stmt_state_rel_state_rel >>
     disch_then (mp_tac o MATCH_MP stateRelProjTheory.state_rel_call_ctx_rel) >>
     simp[loweringStateRelDefsTheory.call_ctx_rel_def]) >>
  `storage_dead H tr (if tr then contract_transient s else contract_storage s) =
    storage_dead H tr (get_storage cx es tr)` by
    metis_tac[stmtSimAssignStorageCopyTheory.storage_copy_initial_agree,
      accountsRelPropsTheory.storage_agree_storage_dead] >>
  `storage_dead H tr (if tr then contract_transient u else contract_storage u) =
    storage_dead H tr (get_storage cx ee tr)` by
    metis_tac[stmtSimAssignStorageCopyTheory.storage_copy_initial_agree,
      accountsRelPropsTheory.storage_agree_storage_dead] >>
  `(if tr then tn.t_trans else tn.t_stor) SUBSET
    {(q,by) | storage_dead H tr (get_storage cx es tr) (w2n q) by}` by
    suspend "initial_bank" >>
  `!j by. j < type_slot_size tv /\ by < 32 /\ MEM j (MAP FST writes) /\
    ~dead_bytes (apply_writes k writes (get_storage cx es tr)) (w2n k) tv (w2n k+j) by
    ==> w2n b+32*j+by NOTIN tn.t_mem` by
    (rpt strip_tac >> (metis_tac[bodyFullAppendLocalFramesTheory.append_encoded_live_byte_clean])) >>
  `key_update
    (FOLDL (\X j. key_update X (k+n2w j)
      (mem_word_taint tn.t_mem (w2n b+32*j)))
      (if tr then tn.t_trans else tn.t_stor) ks) slot {} SUBSET
    {(q,by) | storage_dead H tr
      (update_storage slot (n2w (len+1)) (apply_writes k writes (get_storage cx es tr)))
      (w2n q) by}` by
    (irule append_subregion_sparse_keys_dead >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  suspend "final_banks"
QED

Resume append_storage_aggregate_endpoint_post[initial_bank]:
  qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  Cases_on `tr` >>
  gvs[bodyPtrDefsTheory.ghost_inv_at_def, bodyPtrDefsTheory.stor_taint_ok_at_def,
    bodyPtrDefsTheory.dead_lo_ok_def, sourceUnitExecutionTheory.cx_dead_def,
    venomStateTheory.contract_storage_def,
    venomStateTheory.contract_transient_def, vfmStateTheory.lookup_account_def]
QED

Resume append_storage_aggregate_endpoint_post[final_banks]:
  `stor_taint_ok_at D tn s` by fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  Cases_on `tr` >>
  gvs[bodyPtrDefsTheory.stor_taint_ok_at_def, bodyPtrDefsTheory.dead_lo_ok_def,
    sourceUnitExecutionTheory.cx_dead_def, venomStateTheory.contract_storage_def,
    venomStateTheory.contract_transient_def, vfmStateTheory.lookup_account_def,
    vyperStorageBackendTheory.set_storage_def, vyperStorageBackendTheory.get_storage_def] >>
  metis_tac[pred_setTheory.SUBSET_TRANS]
QED

Resume append_storage_aggregate_endpoint_post[return]:
  Cases_on `d` >> gvs[loweringPostsTheory.return_buf_frame_def] >>
  rename1 `return_buf_frame (SOME rb)` >> PairCases_on `rb` >>
  gvs[loweringPostsTheory.return_buf_frame_def] >> metis_tac[]
QED

Resume append_storage_aggregate_endpoint_post[frame]:
  irule (INST_TYPE [alpha |-> ``:256``] stmtSimDefsTheory.alloca_frame_of_mem_frame) >>
  goal_assum (drule_at Any) >>
  gvs[vyperStorageBackendTheory.set_storage_def] >> metis_tac[]
QED

Finalise append_storage_aggregate_endpoint_post[local]

Theorem append_storage_aggregate_cont_full[local]:
 !DF lo d ctx shadow_ctx PG func cx st0 lctx RetQ cenv sa sc sd sf
   mid s G tn tr slot tv stv v xs sw elem sty cap buf writes bop.
  evaluate_type (get_tenv cx) elem = SOME tv /\ ~is_word_type elem /\
  ~is_word_type sty /\ type_memory_bytes cenv sty = type_memory_size stv /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  type_widens_to (get_tenv cx) sty elem /\
  type_memory_bytes cenv elem = type_memory_size tv /\
  value_has_type stv v /\ val_wf stv v /\ 0 < type_memory_size stv /\
  0 < type_slot_size tv /\ well_formed_type_value tv /\
  type_memory_size tv + 64 < dimword (:256) /\ cap < dimword (:256) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !rt. evaluate_type (get_tenv cx) fty = SOME rt ==>
      sz = type_memory_size rt) fields) /\
  value_has_type tv v /\ val_wf tv v /\ encode_value tv v = SOME writes /\
  compile_alloc_buffer (type_memory_size tv) sa = (buf,sc) /\
  compile_store_memory cenv (Var xs) buf.buf_operand elem sty sc = ((),sd) /\
  compile_dynarray_append cenv bop buf.buf_operand 1 (type_slot_size tv)
    elem elem cap F (if tr then LocTransient else LocStorage) sd = ((),sf) /\
  fn_has_code sa sf func /\ fn_inst_ids_distinct func /\
  eval_operand bop s = SOME slot /\ op_taint tn bop = {} /\
  (!label. bop <> Label label) /\ (!x. bop = Var x ==> not_fresh_at sa x) /\
  not_fresh_at sa xs /\ lookup_var xs s = SOME sw /\
  (?start. expr_val_at cenv cx sty start sa mid v (Var xs) s) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory stv v (w2n sw) mem) /\
  ptr_covers G tn xs s (type_memory_size stv) /\
  w2n sw + val_store_size stv v < dimword (:256) /\
  w2n sw + val_store_size stv v <= s.vs_alloca_next /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid s /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx mid G tn s /\
    storage_place_observed H (StoragePlace tr slot (ArrayTV tv (Dynamic cap)))) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  local_ptrs_reserved cenv sa /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0
    (append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v) (mid,s,G,tn)
    (\H res ee Gf tf u. ?cenv''.
      stmt_lands lctx sf res u /\ ~u.vs_halted /\
      (res = INL () ==> ~block_is_terminated sf /\ cenv'' = cenv) /\
      cenv_top_ext cenv cenv'' ee.scopes /\
      stmt_state_rel H ctx func cenv'' cx ee u /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv'' sf u /\ alloca_history func u /\
      s.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv'' cx ee Gf tf u /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
      alloca_frame cenv mid sa s cenv'' ee u /\
      (!aid off sz. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (off,sz) ==>
        !i. off <= i /\ i < off+sz ==> (i IN tf.t_mem <=> i IN tn.t_mem)))
    (\H res ee gt r. (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
      halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !t. (r = Halt t \/ ?ir. r = IntRet ir t) ==>
        allocas_below_fmp t))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?start. expr_val_at _ _ _ start _ _ _ _ _` strip_assume_tac >>
  `ci_mono sa sc /\ ci_mono sc sd /\ ci_mono sd sf` by
    metis_tac[exprLoweringPropsTheory.ci_mono_compile_alloc_buffer,
      exprLoweringPropsTheory.ci_mono_compile_store_memory,
      stmtLoweringMonoTheory.ci_mono_compile_dynarray_append,pairTheory.SND] >>
  `cs_extends sa sc /\ cs_extends sc sd /\ cs_extends sd sf` by fs[ci_mono_def] >>
  `fn_has_code sa sc func /\ fn_has_code sc sd func /\ fn_has_code sd sf func` by
    metis_tac[fragExecTheory.fn_has_code_split,compileEnvTheory.cs_extends_trans] >>
  qabbrev_tac `H0 = storage_trace_horizon mid.storage_trace` >>
  `valid_horizon cx st0 H0 mid.storage_trace` by
    fs[Abbr `H0`,vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `H0` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  drule_all (SRULE [] (Q.INST [`n` |-> `type_memory_size dtv`]
    (INST_TYPE [beta |-> ``:256``] append_storage_aggregate_stage_ready))) >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (qx_choose_then `staged` (qx_choose_then `root` (qx_choose_then `baseN`
      (qx_choose_then `Gs` (qx_choose_then `ts` strip_assume_tac)))))) >>
  qpat_assum `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ = _`
    (strip_assume_tac o REWRITE_RULE [stmtSimAppendStorageComposeTheory.append_storage_copy_suffix_parts]) >>
  suspend "guard_ready"
QED

Resume append_storage_aggregate_cont_full[guard_ready]:
  `stmt_state_rel H0 ctx func cenv cx mid staged /\
   ghost_inv_at (DF H0) lo d cenv cx mid Gs ts staged` by
    (conj_tac >- (first_assum MATCH_MP_TAC >> first_assum ACCEPT_TAC) >>
     first_assum MATCH_MP_TAC >> first_assum ACCEPT_TAC) >>
  `regions_consistent (FST H0)` by
    fs[vyperStorageFootprintTheory.valid_horizon_def] >>
  `w2n slot + (1+cap*type_slot_size tv) <= dimword (:256)` by
    metis_tac[append_observed_array_bounds] >>
  `storage_read_live H0 tr (get_storage cx mid tr) slot (ArrayTV tv (Dynamic cap))` by
    (irule accountsRelPropsTheory.storage_place_observed_read_live >>
     simp[type_slot_size_def]) >>
  `eval_operand bop staged = SOME slot /\ op_taint ts bop = {} /\
   (!x. bop = Var x ==> not_fresh_at sd x)` by
    (mp_tac (Q.INST [`op` |-> `bop`,`a` |-> `sa`,`s` |-> `s`,
       `t` |-> `staged`,`tn` |-> `tn`,`tf` |-> `ts`,`w` |-> `(slot:bytes32)`]
       append_operand_frame) >>
     impl_tac >-
       (asm_rewrite_tac[] >> gen_tac >> strip_tac >>
        qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sd x /\ _`
          (qspec_then `x` (drule_then strip_assume_tac)) >> simp[]) >>
     strip_tac >> asm_rewrite_tac[] >>
     rpt strip_tac >>
     qpat_assum `!x. bop = Var x ==> not_fresh_at sa x` (qspec_then `x` (drule_then assume_tac)) >>
     qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sd x /\ _`
       (qspec_then `x` (drule_then strip_assume_tac)) >> first_assum ACCEPT_TAC) >>
  `(if tr then tload slot staged else sload slot staged) =
   lookup_storage slot (get_storage cx mid tr)` by
    (irule (INST_TYPE [alpha |-> ``:256``]
       (cj 2 targetSubscriptStorageTheory.target_storage_array_len_ok)) >>
     conj_tac >- (qexists_tac `bop` >> simp[]) >>
     qexistsl_tac [`H0`,`cenv`,`ctx`,`func`,`cap`,`tv`] >>
     simp[type_slot_size_def,Once arithmeticTheory.ADD_COMM]) >>
  `key_taint (if tr then ts.t_trans else ts.t_stor) slot = {}` by
    suspend "header_clean" >>
  `ci_mono sd s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\
   ci_mono s3 s4 /\ ci_mono s4 s5 /\ ci_mono s5 s6 /\
   ci_mono s6 s7 /\ ci_mono s7 s8 /\ ci_mono s8 sf` by
    suspend "suffix_mono" >>
  `fn_has_code sd s3 func /\ fn_has_code s3 s6 func /\
   fn_has_code s6 s7 func /\ fn_has_code s7 s8 func /\ fn_has_code s8 sf func` by
    suspend "suffix_code" >>
  qabbrev_tac `len = w2n (lookup_storage slot (get_storage cx mid tr))` >>
  Cases_on `len < cap` >- suspend "guard_pass" >> suspend "capacity"
QED

Resume append_storage_aggregate_cont_full[header_clean]:
  `staged.vs_call_ctx.cc_address = cx.txn.target` by
    (qpat_assum `stmt_state_rel H0 ctx func cenv cx mid staged`
       (mp_tac o MATCH_MP stateRelProjTheory.stmt_state_rel_state_rel) >>
     disch_then (mp_tac o MATCH_MP stateRelProjTheory.state_rel_call_ctx_rel) >>
     simp[loweringStateRelDefsTheory.call_ctx_rel_def]) >>
  `storage_dead H0 tr (if tr then contract_transient staged else contract_storage staged) =
    storage_dead H0 tr (get_storage cx mid tr)` by
    (qpat_assum `stmt_state_rel H0 ctx func cenv cx mid staged`
       (qspec_then `tr` mp_tac o MATCH_MP stmtSimAssignStorageCopyTheory.storage_copy_initial_agree) >>
     metis_tac[accountsRelPropsTheory.storage_agree_storage_dead]) >>
  `(if tr then ts.t_trans else ts.t_stor) SUBSET
    {(q,by) | storage_dead H0 tr (get_storage cx mid tr) (w2n q) by}` by
    (qpat_assum `ghost_inv_at (DF H0) lo d cenv cx mid Gs ts staged` mp_tac >>
     qpat_assum `!H. dead_lo_ok H (DF H) lo cenv cx` (qspec_then `H0` mp_tac) >>
     qpat_assum `storage_dead H0 tr _ = _` (mp_tac o SYM) >>
     qpat_assum `staged.vs_call_ctx.cc_address = cx.txn.target` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `tr` >>
     simp[bodyPtrDefsTheory.ghost_inv_at_def,bodyPtrDefsTheory.stor_taint_ok_at_def,
       bodyPtrDefsTheory.dead_lo_ok_def,sourceUnitExecutionTheory.cx_dead_def,
       venomStateTheory.contract_storage_def,venomStateTheory.contract_transient_def,
       vfmStateTheory.lookup_account_def, SF CONJ_ss]) >>
  irule (INST_TYPE [alpha |-> ``:256``] storage_dead_key_taint_empty) >>
  qexistsl_tac [`H0`,`get_storage cx mid tr`,`tr`,`ArrayTV tv (Dynamic cap)`] >>
  simp[type_slot_size_def]
QED

Resume append_storage_aggregate_cont_full[suffix_mono]:
  rpt conj_tac >>
  metis_tac[typed_copy_emit_op_mono,exprLoweringPropsTheory.ci_mono_emit_void,
    stmtLoweringMonoTheory.ci_mono_compile_store_slots,pairTheory.SND]
QED

Resume append_storage_aggregate_cont_full[suffix_code]:
  `ci_mono sd s3 /\ ci_mono s3 s6 /\ ci_mono s6 sf /\
   ci_mono s7 sf /\ ci_mono s3 sf` by
    metis_tac[exprLoweringPropsTheory.ci_mono_trans] >>
  `cs_extends sd s3 /\ cs_extends s3 s6 /\ cs_extends s6 s7 /\
   cs_extends s7 s8 /\ cs_extends s8 sf /\ cs_extends s3 sf /\
   cs_extends s6 sf /\ cs_extends s7 sf` by
    (rpt conj_tac >> irule (cj 1 (iffLR ci_mono_def)) >> first_assum ACCEPT_TAC) >>
  mp_tac (Q.SPECL [`sd`,`s3`,`sf`,`func`] fragExecTheory.fn_has_code_split) >>
  simp[] >> strip_tac >>
  mp_tac (Q.SPECL [`s3`,`s6`,`sf`,`func`] fragExecTheory.fn_has_code_split) >>
  simp[] >> strip_tac >>
  mp_tac (Q.SPECL [`s6`,`s7`,`sf`,`func`] fragExecTheory.fn_has_code_split) >>
  simp[] >> strip_tac >>
  mp_tac (Q.SPECL [`s7`,`s8`,`sf`,`func`] fragExecTheory.fn_has_code_split) >> simp[]
QED

Resume append_storage_aggregate_cont_full[capacity]:
  `~(w2n (if tr then tload slot staged else sload slot staged) < cap)` by
    fs[Abbr `len`] >>
  drule_all append_storage_guard_abort_conditional_uniform >>
  disch_then (qspecl_then [`PG`,`Gs`]
    (qx_choose_then `r` (qx_choose_then `j` (qx_choose_then `Gr`
      (qx_choose_then `tR` strip_assume_tac))))) >>
  `!tail. append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v
        (mid with gas_obs := tail) =
        (INR (Error (RuntimeError "append full storage array")),mid with gas_obs := tail)` by
    (gen_tac >> irule vyperStorageBackendTheory.append_storage_full >>
     Cases_on `tr` >> fs[Abbr `len`,vyperStorageBackendTheory.get_storage_def]) >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_exit >>
  conj_tac >- (qexistsl_tac [`Gr`, `mid`, `Abort Revert_abort (r with vs_inst_idx := j)`,
    `INR (Error (RuntimeError "append full storage array"))`, `tR`] >>
    simp[fragExecTheory.exit_result_def,bodyPtrDefsTheory.stmt_exit_ptr_def,
      exprSimDefsTheory.expr_exit_def,exprSimDefsTheory.halt_exit_def] >>
    metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans]) >> simp[]
QED

Resume append_storage_aggregate_cont_full[guard_pass]:
  `w2n (if tr then tload slot staged else sload slot staged) < cap` by
    fs[Abbr `len`] >>
  drule_all append_storage_guard_conditional_uniform >>
  disch_then (qspecl_then [`PG`,`Gs`]
    (qx_choose_then `graw` (qx_choose_then `Gg` (qx_choose_then `tg` strip_assume_tac)))) >>
  qabbrev_tac `guarded = graw with vs_inst_idx := LENGTH s3.cs_current_insts` >>
  `guarded.vs_current_bb = s3.cs_current_bb /\ ~guarded.vs_halted /\
   guarded.vs_inst_idx = LENGTH s3.cs_current_insts /\
   allocas_from lo guarded /\ (ctx_has_dalloca ctx ==> allocas_below_fmp guarded)` by
    suspend "guard_fields" >>
  `eval_operand bop graw = SOME slot /\ op_taint tg bop = {}` by
    (match_mp_tac (Q.INST [`a` |-> `sd`,`s` |-> `staged`,`tn` |-> `ts`]
        append_operand_frame) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     gen_tac >> strip_tac >>
     qpat_assum `!x. not_fresh_at sd x ==> _`
       (qspec_then `x` (drule_then strip_assume_tac)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `eval_operand bop guarded = SOME slot /\ op_taint tg bop = {} /\
   eval_operand lop guarded = SOME (n2w len)` by
    (fs[Abbr `guarded`,Abbr `len`,venomStateTheory.eval_operand_def,
      venomStateTheory.lookup_var_def, CaseEq "operand"]) >>
  `!x. bop = Var x \/ lop = Var x ==> not_fresh_at s3 x` by
    metis_tac[typed_copy_emit_op_fresh,exprOperandVarTheory.compiler_ci_mono_not_fresh,
      venomStateTheory.operand_distinct] >>
  drule_all append_storage_aggregate_address_ready >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`,`Gg`]
    (qx_choose_then `out` (qx_choose_then `placed` (qx_choose_then `Gp`
      (qx_choose_then `tp` strip_assume_tac))))) >>
  suspend "slots_inputs"
QED

Resume append_storage_aggregate_cont_full[guard_fields]:
  `s3.cs_current_bb = sd.cs_current_bb` by
    (qpat_assum `emit_op _ _ sd = (_,s1)`
       (mp_tac o MATCH_MP exprLoweringPropsTheory.emit_op_same_blocks) >>
     qpat_assum `emit_op LT _ s1 = (_,s2)`
       (mp_tac o MATCH_MP exprLoweringPropsTheory.emit_op_same_blocks) >>
     qpat_assum `emit_void ASSERT _ s2 = ((),s3)`
       (mp_tac o MATCH_MP exprLoweringPropsTheory.emit_void_same_blocks) >>
     simp[exprLoweringPropsTheory.same_blocks_def] >> rpt strip_tac >> simp[]) >>
  qpat_assum `allocas_from lo staged`
    (assume_tac o SRULE [ptrDisciplineTheory.allocas_from_def]) >>
  qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp staged`
    (assume_tac o SRULE [ptrDisciplineTheory.allocas_below_fmp_def]) >>
  qpat_assum `state_frame graw = state_frame staged` (strip_assume_tac o
    SRULE [stateFrameTheory.state_frame_def,venomStateTheory.venom_state_component_equality]) >>
  simp[Abbr `guarded`,ptrDisciplineTheory.allocas_from_def,
    ptrDisciplineTheory.allocas_below_fmp_def] >>
  metis_tac[]
QED

Resume append_storage_aggregate_cont_full[slots_inputs]:
  `placed.vs_memory = staged.vs_memory /\ placed.vs_allocas = staged.vs_allocas /\
   placed.vs_alloca_next = staged.vs_alloca_next /\
   placed.vs_call_ctx = staged.vs_call_ctx /\ placed.vs_labels = staged.vs_labels /\
   placed.vs_immutables = staged.vs_immutables` by suspend "placed_fields" >>
  `!x. not_fresh_at sd x ==> not_fresh_at s6 x /\
    lookup_var x placed = lookup_var x staged /\ FLOOKUP Gp x = FLOOKUP Gs x /\
    op_taint tp (Var x) = op_taint ts (Var x)` by suspend "placed_old" >>
  `w2n (n2w baseN : bytes32) = baseN` by
    simp[wordsTheory.w2n_n2w,arithmeticTheory.LESS_MOD] >>
  `eval_operand buf.buf_operand placed = SOME (n2w baseN) /\
   op_taint tp buf.buf_operand = {} /\ ptr_covers Gp tp root placed (type_memory_size tv) /\
   (!mem. mem_agree_outside tp.t_mem placed.vs_memory mem ==>
      val_in_memory tv v (w2n (n2w baseN : bytes32)) mem) /\
   (!x. buf.buf_operand = Var x \/ pop = Var x ==> not_fresh_at s6 x)` by
    suspend "placed_operand" >>
  `!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (s,G,tn) [] (OK placed,Gp,tp)` by suspend "placed_path" >>
  `placed.vs_call_ctx.cc_static = cx.txn.is_static` by
    (qpat_assum `stmt_state_rel H0 ctx func cenv cx mid staged`
       (mp_tac o MATCH_MP stateRelProjTheory.stmt_state_rel_state_rel) >>
     disch_then (mp_tac o MATCH_MP stateRelProjTheory.state_rel_call_ctx_rel) >>
     simp[loweringStateRelDefsTheory.call_ctx_rel_def]) >>
  `type_memory_size tv <> 0 ==>
   ?x. buf.buf_operand = Var x /\ ptr_covers Gp tp x placed (type_memory_size tv)` by
    (strip_tac >> qexists_tac `root` >> simp[]) >>
  `w2n (n2w baseN : bytes32) + type_memory_size tv < dimword (:256) /\
   lo <= placed.vs_alloca_next` by simp[] >>
  `type_memory_size tv = 0 \/
    w2n (n2w baseN : bytes32) + type_memory_size tv <= placed.vs_alloca_next`
    suffices_by (disch_tac >> Cases_on `placed.vs_call_ctx.cc_static` >-
      suspend "slots_static" >> suspend "slots_nonstatic") >> simp[]
QED

Resume append_storage_aggregate_cont_full[placed_fields]:
  qpat_assum `state_frame graw = state_frame staged` (strip_assume_tac o
    SRULE [stateFrameTheory.state_frame_def,venomStateTheory.venom_state_component_equality]) >>
  qpat_assum `typed_copy_state_frame s3 0 0 guarded placed` (strip_assume_tac o
    SRULE [typedMemoryCopyTheory.typed_copy_state_frame_def,
      venomStateTheory.venom_state_component_equality]) >>
  simp[Abbr `guarded`]
QED

Resume append_storage_aggregate_cont_full[placed_old]:
  `ci_mono sd s3` by metis_tac[exprLoweringPropsTheory.ci_mono_trans] >>
  gen_tac >> disch_tac >>
  `not_fresh_at s3 x` by metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh] >>
  qpat_assum `!x. not_fresh_at s3 x ==> _` (qspec_then `x` mp_tac) >>
  qpat_assum `!x. not_fresh_at sd x ==> _` (qspec_then `x` mp_tac) >>
  qpat_assum `Abbrev (guarded = _)` mp_tac >>
  qpat_assum `not_fresh_at s3 x` mp_tac >>
  qpat_assum `not_fresh_at sd x` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp[markerTheory.Abbrev_def,venomStateTheory.lookup_var_def, SF CONJ_ss]
QED

Resume append_storage_aggregate_cont_full[placed_operand]:
  qpat_assum `!x. not_fresh_at sd x ==> not_fresh_at s6 x /\ _`
    (qspec_then `root` mp_tac) >>
  simp[venomStateTheory.eval_operand_def,bodyPtrDefsTheory.ptr_covers_def] >>
  qpat_assum `ptr_covers Gs ts root staged (type_memory_size tv)`
    (mp_tac o SRULE [bodyPtrDefsTheory.ptr_covers_def]) >>
  qpat_assum `op_taint ts buf.buf_operand = {}` mp_tac >>
  qpat_assum `buf.buf_operand = Var root` mp_tac >>
  qpat_assum `not_fresh_at s6 out` mp_tac >>
  qpat_assum `!x. not_fresh_at sd x ==> not_fresh_at s6 x /\ _`
    (qspec_then `root` (mp_tac o cj 1)) >>
  qpat_assum `not_fresh_at sd root` mp_tac >>
  qpat_assum `lookup_var root staged = SOME _` mp_tac >>
  qpat_assum `w2n (n2w baseN : bytes32) = baseN` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp[] >> metis_tac[]
QED

Resume append_storage_aggregate_cont_full[placed_path]:
  gen_tac >>
  irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
  qexistsl_tac [`Gg`,`guarded`,`tg`] >> simp[] >>
  irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
  qexistsl_tac [`Gs`,`staged`,`ts`] >> simp[]
QED

Resume append_storage_aggregate_cont_full[slots_static]:
  drule_all bodyFullStoreSlotsStaticTheory.compile_store_slots_static_origin_ptr_path >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (qx_choose_then `blocked` (qx_choose_then `Gb` (qx_choose_then `tb` strip_assume_tac)))) >>
  `type_slot_size tv <> 0` by decide_tac >>
  qpat_x_assum `!D. gas_origin_ptr_path _ (placed,Gp,tp) [] ((if _ then _ else _),Gb,tb)`
    (mp_tac) >>
  simp[] >> disch_tac >>
  `!tail. append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v
    (mid with gas_obs := tail) =
    (INR (Error (RuntimeError "write in static context")),mid with gas_obs := tail)` by
    (gen_tac >> irule stmtSimAppendStorageTheory.append_storage_static >>
     qpat_assum `placed.vs_call_ctx.cc_static <=> cx.txn.is_static` mp_tac >>
     simp[stmtSimAppendStorageComposeTheory.get_storage_gas_obs] >>
     fs[Abbr `len`]) >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_exit >>
  conj_tac >- (qexistsl_tac [`Gb`,`mid`,`Abort ExHalt_abort (halt_state (set_returndata [] blocked))`,
    `INR (Error (RuntimeError "write in static context"))`,`tb`] >>
    simp[fragExecTheory.exit_result_def,bodyPtrDefsTheory.stmt_exit_ptr_def,
      exprSimDefsTheory.expr_exit_def,exprSimDefsTheory.halt_exit_def] >>
    rpt strip_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
    qexistsl_tac [`Gp`,`placed`,`tp`] >> simp[]) >> simp[]
QED

Resume append_storage_aggregate_cont_full[slots_nonstatic]:
  drule_all bodyFullStoreSlotsPathTheory.compile_store_slots_origin_ptr_path >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (qx_choose_then `stored` (qx_choose_then `ks` (qx_choose_then `Gk`
      (qx_choose_then `tk` strip_assume_tac))))) >>
  suspend "header_path"
QED

Resume append_storage_aggregate_cont_full[header_path]:
  `eval_operand lop stored = SOME (n2w len) /\ op_taint tk lop = {}` by
    (qpat_assum `emit_op _ [bop] sd = (lop,s1)`
       (mp_tac o cj 2 o MATCH_MP emitHelperPropsTheory.emitted_insts_emit_op) >>
     disch_then SUBST_ALL_TAC >>
     qpat_assum `!x. bop = Var x \/ _ ==> _`
       (qspec_then `STRING #"%" (toString sd.cs_next_var)` (assume_tac o SRULE [])) >>
     qpat_assum `!x. not_fresh_at s3 x ==> _` (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at s6 x ==> _` (drule_then strip_assume_tac) >>
     qpat_assum `eval_operand (Var _) guarded = _`
       (assume_tac o REWRITE_RULE [venomStateTheory.eval_operand_def]) >>
     pure_rewrite_tac[venomStateTheory.eval_operand_def] >>
     map_every (fn q => qpat_assum q (fn th => pure_rewrite_tac[th]))
       [`lookup_var _ stored = lookup_var _ placed`,
        `lookup_var _ placed = lookup_var _ guarded`,
        `lookup_var _ guarded = SOME (n2w len)`,
        `op_taint tk (Var _) = op_taint tp (Var _)`,
        `op_taint tp (Var _) = op_taint tg (Var _)`, `op_taint tg (Var _) = {}`] >>
     simp[]) >>
  `allocas_from lo stored` by
    (qpat_assum `allocas_from lo placed` mp_tac >>
     qpat_assum `stored.vs_allocas = placed.vs_allocas`
       (fn th => rewrite_tac[ptrDisciplineTheory.allocas_from_def,th])) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp stored` by
    (qpat_assum `store_copy_normalize placed stored = _`
       (mp_tac o MATCH_MP bodyFullStoreSlotsFrameTheory.store_slots_normalize_allocas_below_fmp) >>
     simp[bodyFullStoreSlotsFrameTheory.store_slots_fold_allocas_below_fmp, SF CONJ_ss]) >>
  `eval_operand (Lit 1w) stored = SOME 1w /\ op_taint tk (Lit 1w) = {}` by
    simp[venomStateTheory.eval_operand_def,ptrDisciplineTheory.op_taint_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`, `w` |-> `x+y`]
    append_storage_address_binop_uniform)) >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`,`Gk`]
    (qx_choose_then `nvar` (qx_choose_then `counted` (qx_choose_then `Gc`
      (qx_choose_then `tc` strip_assume_tac))))) >>
  `counted.vs_call_ctx = stored.vs_call_ctx` by
    (qpat_assum `typed_copy_state_frame s7 0 0 stored counted`
       (mp_tac o Q.AP_TERM `\z. z.vs_call_ctx` o cj 1 o
        SRULE [typed_copy_state_frame_def]) >> simp[]) >>
  `~cx.txn.is_static /\ ~counted.vs_call_ctx.cc_static` by
    (qpat_assum `~placed.vs_call_ctx.cc_static` mp_tac >>
     qpat_assum `placed.vs_call_ctx.cc_static <=> cx.txn.is_static` mp_tac >>
     pure_asm_rewrite_tac[] >> metis_tac[]) >>
  `eval_operand bop guarded = SOME slot /\ op_taint tg bop = {}` by simp[] >>
  `!x. bop = Var x ==> not_fresh_at s3 x` by
    (gen_tac >> strip_tac >>
     qpat_assum `!x. bop = Var x \/ lop = Var x ==> not_fresh_at s3 x`
       (qspec_then `x` mp_tac) >> simp[]) >>
  `!x. bop = Var x ==> not_fresh_at s6 x` by
    (gen_tac >> strip_tac >>
     qpat_assum `!x. bop = Var x ==> not_fresh_at s3 x` (qspec_then `x` (drule_then assume_tac)) >>
     qpat_assum `!x. not_fresh_at s3 x ==> not_fresh_at s6 x /\ _`
       (qspec_then `x` (drule_then strip_assume_tac)) >> first_assum ACCEPT_TAC) >>
  `!x. bop = Var x ==> not_fresh_at s7 x` by
    (`ci_mono s6 s7` by
      (mp_tac (Q.SPECL [`cenv`,`buf.buf_operand`,`pop`,`elem`,`tr`,`s6`]
         (cj 1 stmtLoweringMonoTheory.ci_mono_compile_store_slots)) >> simp[]) >>
     gen_tac >> strip_tac >>
     qpat_assum `!x. bop = Var x ==> not_fresh_at s6 x` (qspec_then `x` (drule_then assume_tac)) >>
     irule exprOperandVarTheory.compiler_ci_mono_not_fresh >> qexists_tac `s6` >> simp[]) >>
  `eval_operand bop placed = SOME slot /\ op_taint tp bop = {}` by
    (match_mp_tac (Q.INST [`a` |-> `s3`,`s` |-> `guarded`,`tn` |-> `tg`]
        append_operand_frame) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     gen_tac >> strip_tac >>
     qpat_assum `!x. not_fresh_at s3 x ==> not_fresh_at s6 x /\ lookup_var x placed = lookup_var x guarded /\ _`
       (qspec_then `x` (drule_then strip_assume_tac)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `eval_operand bop stored = SOME slot /\ op_taint tk bop = {}` by
    (match_mp_tac (Q.INST [`a` |-> `s6`,`s` |-> `placed`,`tn` |-> `tp`]
        append_operand_frame) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     gen_tac >> strip_tac >>
     qpat_assum `!x. not_fresh_at s6 x ==> lookup_var x stored = lookup_var x placed /\ _`
       (qspec_then `x` (drule_then strip_assume_tac)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `eval_operand bop counted = SOME slot /\ op_taint tc bop = {}` by
    (match_mp_tac (Q.INST [`a` |-> `s7`,`s` |-> `stored`,`tn` |-> `tk`]
        append_operand_frame) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     gen_tac >> strip_tac >>
     qpat_assum `!x. not_fresh_at s7 x ==> lookup_var x counted = lookup_var x stored /\ _`
       (qspec_then `x` (drule_then strip_assume_tac)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `eval_operand nop counted = SOME (n2w (len+1))` by
    simp[GSYM wordsTheory.word_add_n2w] >>
  drule_all bodyFullStoreSlotsTaintStoreTheory.storage_tainted_word_store_origin_ptr >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`,`Gc`] assume_tac) >>
  qabbrev_tac `u = ((if tr then tstore else sstore) slot (n2w (len+1)) counted)
    with vs_inst_idx := LENGTH sf.cs_current_insts` >>
  qabbrev_tac `tf = if tr then tc with t_trans := key_update tc.t_trans slot {}
    else tc with t_stor := key_update tc.t_stor slot {}` >>
  `!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (counted,Gc,tc) [] (OK u,Gc,tf)` by
    (qpat_assum `!D. gas_origin_ptr_path _ (counted,Gc,tc) [] _` mp_tac >>
     simp[Abbr `u`,Abbr `tf`] >> metis_tac[]) >>
  `!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (staged,Gs,ts) [] (OK u,Gc,tf)` by suspend "store_paths" >>
  suspend "store_normalize"
QED

Resume append_storage_aggregate_cont_full[store_paths]:
  gen_tac >>
  irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
  qexistsl_tac [`Gc`,`counted`,`tc`] >> simp[] >>
  irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
  qexistsl_tac [`Gk`,`stored`,`tk`] >> simp[] >>
  irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
  qexistsl_tac [`Gp`,`placed`,`tp`] >> simp[] >>
  irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
  qexistsl_tac [`Gg`,`guarded`,`tg`] >> simp[]
QED

Resume append_storage_aggregate_cont_full[store_normalize]:
  `store_copy_normalize staged placed = staged` by
    (qpat_assum `typed_copy_state_frame s3 0 0 guarded placed`
       (mp_tac o Q.AP_TERM `(\z. (store_copy_normalize staged z) with
          vs_memory := staged.vs_memory)` o cj 1 o SRULE [typed_copy_state_frame_def]) >>
     qpat_assum `state_frame graw = state_frame staged`
       (mp_tac o Q.AP_TERM `store_copy_normalize staged`) >>
     qpat_assum `placed.vs_memory = staged.vs_memory` mp_tac >>
     qpat_assum `Abbrev (guarded = _)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[markerTheory.Abbrev_def,stateFrameTheory.state_frame_def,
       stmtSimStoreCopyTheory.store_copy_normalize_def,venomStateTheory.venom_state_component_equality]) >>
  `store_copy_normalize placed counted = store_copy_normalize placed stored` by
    (qpat_assum `typed_copy_state_frame s7 0 0 stored counted`
       (mp_tac o Q.AP_TERM `store_copy_normalize placed` o cj 1 o
        SRULE [typed_copy_state_frame_def]) >>
     qpat_assum `counted.vs_memory = stored.vs_memory` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[stmtSimStoreCopyTheory.store_copy_normalize_def,
       venomStateTheory.venom_state_component_equality]) >>
  `store_copy_normalize staged u =
    (if tr then tstore else sstore) slot (n2w (len+1))
      (FOLDL (\q i. (if tr then tstore else sstore)
        (slot+n2w (1+len*type_slot_size tv)+n2w i)
        (mem_word_at (w2n (n2w baseN : bytes32)+32*i) staged.vs_memory) q) staged ks)` by
    (simp[Abbr `u`,placeStoreSlotsTheory.store_slots_normalize_store] >>
     once_rewrite_tac[GSYM (Q.INST [`a` |-> `staged`, `b` |-> `placed`,
       `t` |-> `counted`] placeStoreSlotsTheory.store_slots_normalize_compose)] >>
     simp[placeStoreSlotsTheory.store_slots_normalize_fold,
       valueEncodingPropsTheory.mem_word_at_eq_mload,venomStateTheory.mload_def]) >>
  suspend "endpoint_fields"
QED

Resume append_storage_aggregate_cont_full[endpoint_fields]:
  `u.vs_memory = staged.vs_memory /\ u.vs_allocas = staged.vs_allocas /\
   u.vs_alloca_next = staged.vs_alloca_next /\ u.vs_call_ctx = staged.vs_call_ctx /\
   ~u.vs_halted` by
    (qpat_assum `typed_copy_state_frame s7 0 0 stored counted`
       (mp_tac o Q.AP_TERM `\z. (z.vs_allocas,z.vs_alloca_next)` o cj 1 o
        SRULE [typed_copy_state_frame_def]) >>
     Cases_on `tr` >>
     simp[Abbr `u`,venomStateTheory.sstore_def,venomStateTheory.tstore_def]) >>
  qabbrev_tac `payload = FOLDL (\q i. (if tr then tstore else sstore)
    (slot+n2w (1+len*type_slot_size tv)+n2w i)
    (mem_word_at (w2n (n2w baseN : bytes32)+32*i) staged.vs_memory) q) staged ks` >>
  `payload = if tr then staged with vs_transient :=
     (staged.vs_call_ctx.cc_address =+
       FOLDL (\q i. update_storage (slot+n2w (1+len*type_slot_size tv)+n2w i)
          (mem_word_at (w2n (n2w baseN : bytes32)+32*i) staged.vs_memory) q)
         (contract_transient staged) ks) staged.vs_transient
    else staged with vs_accounts :=
     (staged.vs_call_ctx.cc_address =+
       (lookup_account staged.vs_call_ctx.cc_address staged.vs_accounts with storage :=
          FOLDL (\q i. update_storage (slot+n2w (1+len*type_slot_size tv)+n2w i)
            (mem_word_at (w2n (n2w baseN : bytes32)+32*i) staged.vs_memory) q)
            (contract_storage staged) ks)) staged.vs_accounts` by
    (qpat_assum `Abbrev (payload = _)`
       (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     ACCEPT_TAC (BETA_RULE (Q.SPECL [`ks`, `(slot+n2w (1+len*type_slot_size tv)) : bytes32`,
       `\i. mem_word_at (w2n (n2w baseN : bytes32)+32*i) staged.vs_memory`, `staged`, `tr`]
       stmtSimAssignStorageCopyTheory.storage_copy_backend_fold))) >>
  `u.vs_immutables = staged.vs_immutables /\
   (if tr then contract_storage u = contract_storage staged
    else contract_transient u = contract_transient staged)` by
    (qpat_assum `store_copy_normalize staged u = _`
       (mp_tac o BETA_RULE o Q.AP_TERM `\z. (z.vs_immutables,
          if tr then contract_storage z else contract_transient z)`) >>
     qpat_assum `payload = _` SUBST1_TAC >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `tr` >>
     simp[stmtSimStoreCopyTheory.store_copy_normalize_def,
       venomStateTheory.sstore_def,venomStateTheory.tstore_def,
       venomStateTheory.contract_storage_def,venomStateTheory.contract_transient_def]) >>
  `tf.t_mem = ts.t_mem /\ tf.t_imm = ts.t_imm /\
   (if tr then tf.t_stor = ts.t_stor else tf.t_trans = ts.t_trans)` by
    (qpat_assum `if tr then tk.t_stor = _ else tk.t_trans = _` mp_tac >>
     Cases_on `tr` >> simp[Abbr `tf`] >> metis_tac[]) >>
  `(if tr then tf.t_trans else tf.t_stor) SUBSET
   key_update
     (FOLDL (\X j. key_update X (slot+n2w (1+len*type_slot_size tv)+n2w j)
       (mem_word_taint ts.t_mem (w2n (n2w baseN : bytes32)+32*j)))
       (if tr then ts.t_trans else ts.t_stor) ks) slot {}` by
    (Cases_on `tr` >> simp[Abbr `tf`] >>
     irule lowerDloadMaskedStorageTheory.ld_key_update_mono >> simp[] >>
     qpat_x_assum `(if _ then tk.t_trans else tk.t_stor) SUBSET _` mp_tac >>
     qpat_assum `w2n (n2w baseN : bytes32) = baseN` mp_tac >>
     qpat_assum `tp.t_mem = tg.t_mem` mp_tac >>
     qpat_assum `tg.t_mem = ts.t_mem` mp_tac >>
     qpat_assum `tp.t_trans = tg.t_trans` mp_tac >>
     qpat_assum `tg.t_trans = ts.t_trans` mp_tac >>
     qpat_assum `tp.t_stor = tg.t_stor` mp_tac >>
     qpat_assum `tg.t_stor = ts.t_stor` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> ntac 7 disch_tac >> simp[]) >>
  suspend "endpoint_old"
QED

Resume append_storage_aggregate_cont_full[endpoint_old]:
  `ci_mono sa sd /\ ci_mono sd s6 /\ ci_mono s6 s7 /\ ci_mono sd sf` by
    metis_tac[exprLoweringPropsTheory.ci_mono_trans] >>
  `!x. not_fresh_at sd x ==> not_fresh_at sf x /\
    lookup_var x u = lookup_var x staged /\ FLOOKUP Gc x = FLOOKUP Gs x /\
    op_taint tf (Var x) = op_taint ts (Var x)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!x. not_fresh_at sd x ==> not_fresh_at s6 x /\ _`
       (qspec_then `x` (strip_assume_tac o SRULE [])) >>
     `not_fresh_at s7 x /\ not_fresh_at sf x` by
       metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh] >>
     qpat_assum `!x. not_fresh_at s6 x ==> lookup_var x stored = _ /\ _`
       (qspec_then `x` (strip_assume_tac o SRULE [])) >>
     qpat_assum `!x. not_fresh_at s7 x ==> lookup_var x counted = _ /\ _`
       (qspec_then `x` (strip_assume_tac o SRULE [])) >>
     `lookup_var x u = lookup_var x counted /\
      op_taint tf (Var x) = op_taint tc (Var x)` by
       (qpat_assum `Abbrev (u = _)`
          (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
        qpat_assum `Abbrev (tf = _)`
          (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
        Cases_on `tr` >>
        simp[NoAsms,venomStateTheory.sstore_def,venomStateTheory.tstore_def,
          venomStateTheory.lookup_var_def,ptrDisciplineTheory.op_taint_def]) >>
     simp[]) >>
  `!x. not_fresh_at sd x ==> not_fresh_at sf x` by simp[] >>
  `local_ptrs_reserved cenv sd` by
    (irule exprOperandVarTheory.compiler_ci_mono_reserved >> qexists_tac `sa` >> simp[]) >>
  `!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sd x` by
    (rpt strip_tac >> irule exprOperandVarTheory.compiler_ci_mono_not_fresh >>
     qexists_tac `sa` >> simp[]) >>
  `!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sd x` by
    (rpt strip_tac >> irule exprOperandVarTheory.compiler_ci_mono_not_fresh >>
     qexists_tac `sa` >> simp[]) >>
  `!x. lo <> 0 /\ cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sd x` by
    (rpt strip_tac >>
     irule exprLoweringPropsTheory.local_ptrs_reserved_imm_base >>
     qexists_tac `cenv` >> simp[]) >>
  `sa.cs_next_var <= sd.cs_next_var` by
    (qpat_assum `ci_mono sa sd`
       (ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [ci_mono_def])) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
     lookup_var x staged = SOME w` by
    (rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sd x /\ _`
       (qspec_then `x` (strip_assume_tac o SRULE [])) >> simp[]) >>
  `return_buf_frame d cenv sd staged` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`,`s`,`sa`] >> simp[]) >>
  suspend "source_success"
QED

Resume append_storage_aggregate_cont_full[source_success]:
  qabbrev_tac `ee = set_storage cx mid tr (update_storage slot (n2w (len+1))
     (apply_writes (slot+n2w (1+len*type_slot_size tv)) writes (get_storage cx mid tr)))` >>
  `append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v mid = (INL (),ee)` by
    (qpat_assum `Abbrev (ee = _)` (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qpat_assum `Abbrev (len = _)` (mp_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qpat_assum `len < cap` mp_tac >>
     qpat_assum `encode_value tv v = SOME writes` mp_tac >>
     qpat_assum `~cx.txn.is_static` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> ntac 3 disch_tac >> disch_then SUBST_ALL_TAC >>
     simp[stmtSimAppendStorageTheory.append_storage_writes, ignore_bind_def, bind_def,
          vyperStorageBackendTheory.write_storage_slot_eq,
          vyperStorageBackendTheory.get_storage_after_set, vyperStorageTheory.encode_value_def,
          vyperStorageTheory.encode_base_to_slot_def, vyperStorageTheory.apply_writes_def,
          integer_wordTheory.i2w_def] >>
     Cases_on `tr` >>
     simp[vyperStorageBackendTheory.set_storage_def, combinTheory.APPLY_UPDATE_THM]) >>
  suspend "outcome_success"
QED

Resume append_storage_aggregate_cont_full[outcome_success]:
  `ee.storage_trace = mid.storage_trace` by
    (Cases_on `tr` >> simp[NoAsms,Abbr `ee`,vyperStorageBackendTheory.set_storage_def]) >>
  `!tail. append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v
      (mid with gas_obs := tail) = (INL (),ee with gas_obs := tail)` by
    (gen_tac >> irule stmtSimAppendStorageComposeTheory.append_storage_place_gas_obs >>
     first_assum ACCEPT_TAC) >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_pure >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`Gc`,`ee`,`INL ()`,`u`,`tf`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  gen_tac >> disch_tac >>
  conj_tac
  >- (irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
      qexistsl_tac [`Gs`,`staged`,`ts`] >> simp[]) >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (qpat_assum `ee.storage_trace = mid.storage_trace` (fn th =>
       qpat_assum `valid_horizon cx st0 H ee.storage_trace`
         (ACCEPT_TAC o PURE_REWRITE_RULE [th]))) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H)` by
    (qpat_assum `valid_horizon cx st0 H mid.storage_trace`
       (strip_assume_tac o REWRITE_RULE [vyperStorageFootprintTheory.valid_horizon_def]) >>
     simp[]) >>
  `stmt_state_rel H ctx func cenv cx mid staged /\
    ghost_inv_at (DF H) lo d cenv cx mid Gs ts staged /\
    dead_lo_ok H (DF H) lo cenv cx` by simp[] >>
  suspend "outcome_endpoint"
QED

Resume append_storage_aggregate_cont_full[outcome_endpoint]:
  `w2n (n2w baseN : bytes32) + 32 * type_slot_size tv <= dimword (:256)` by
    (irule arithmeticTheory.LESS_IMP_LESS_OR_EQ >>
     qpat_assum `w2n (n2w baseN : bytes32) + type_memory_size tv < dimword (:256)`
       (ACCEPT_TAC o PURE_REWRITE_RULE [valueEncodingPropsTheory.type_memory_size_slots])) >>
  `!mem. mem_agree_outside ts.t_mem staged.vs_memory mem ==>
     val_in_memory tv v (w2n (n2w baseN : bytes32)) mem` by simp[] >>
  `len = w2n (lookup_storage slot (get_storage cx mid tr))` by simp[Abbr `len`] >>
  `ee = set_storage cx mid tr (update_storage slot (n2w (len+1))
     (apply_writes (slot+n2w (1+len*type_slot_size tv)) writes (get_storage cx mid tr)))` by
    simp[Abbr `ee`] >>
  `gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (staged,Gs,ts) [] (OK u,Gc,tf)` by simp[] >>
  qpat_assum `Abbrev (payload = _)` (fn ab =>
    qpat_assum `store_copy_normalize staged u = _`
      (assume_tac o PURE_REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] ab])) >>
  `!x. not_fresh_at sd x ==> lookup_var x u = lookup_var x staged /\
    FLOOKUP Gc x = FLOOKUP Gs x /\ op_taint tf (Var x) = op_taint ts (Var x)` by
    (qpat_assum `!x. not_fresh_at sd x ==> not_fresh_at sf x /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `(if tr then contract_storage u = contract_storage staged /\ tf.t_stor = ts.t_stor
    else contract_transient u = contract_transient staged /\ tf.t_trans = ts.t_trans)` by
    (qpat_assum `if tr then contract_storage u = _ else contract_transient u = _` mp_tac >>
     qpat_assum `if tr then tf.t_stor = _ else tf.t_trans = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `tr` >> simp[]) >>
  qpat_assum `gas_origin_ptr_path (DF H,lo,_,ctx,func,PG)
                      (staged,Gs,ts) [] (OK u,Gc,tf)`
    (mp_then (Pat `gas_origin_ptr_path _ _ _ _`) (fn path_th =>
      qpat_assum `stmt_state_rel H ctx func cenv cx mid staged`
        (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) (fn rel_th =>
          qpat_assum `return_buf_frame d cenv sd staged`
            (mp_then (Pat `return_buf_frame _ _ _ _`) (fn buf_th =>
              qpat_assum `!x. not_fresh_at sd x ==> not_fresh_at sf x`
                (mp_then (Pat `!x. not_fresh_at _ x ==> not_fresh_at _ x`) (fn fresh_th =>
                  qpat_assum `append_place cx _ v mid = (INL (),ee)`
                    (mp_then (Pat `append_place _ _ _ _ = _`) (fn eval_th =>
                      qpat_assum `encode_value tv v = SOME writes`
                        (mp_then (Pat `encode_value _ _ = _`) (fn enc_th =>
                          qpat_assum `!i. MEM i ks <=> MEM i (MAP FST writes)`
                            (mp_then (Pat `!i. MEM i _ <=> MEM i (MAP FST _)`)
                              (Q.ISPECL_THEN
                                [`len:num`, `(slot:bytes32)+n2w (1+len*type_slot_size tv)`,
                                 `n2w baseN : bytes32`] mp_tac) enc_th)) eval_th)) fresh_th))
                  buf_th)) rel_th)) path_th)) append_storage_aggregate_endpoint_post) >>
  (impl_tac >- (rewrite_tac[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >> suspend "outcome_post"
QED

Resume append_storage_aggregate_cont_full[outcome_post]:
  BETA_TAC >> qexists_tac `cenv` >>
  conj_tac >-
    (qpat_assum `emit_void _ [bop;nop] s8 = ((),sf)`
       (mp_tac o MATCH_MP emit_void_same_blocks) >>
     qpat_assum `counted.vs_current_bb = s8.cs_current_bb` mp_tac >>
     qpat_assum `Abbrev (u = _)` (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `tr` >> simp[loweringPostsTheory.stmt_lands_def,
       same_blocks_def,venomStateTheory.tstore_def,venomStateTheory.sstore_def]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qpat_assum `emit_void _ [bop;nop] s8 = ((),sf)`
       (mp_tac o MATCH_MP exprOpenPrimitivesTheory.emit_void_terminated) >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `tr` >> simp[venomInstTheory.is_terminator_def]) >>
  conj_tac >- simp[NoAsms,loweringPostsTheory.cenv_top_ext_def] >>
  conj_tac >- (rewrite_tac[stmt_state_rel_start_gas_obs] >> first_assum ACCEPT_TAC) >>
  conj_tac >-
    (`storage_well_formed_on cx (ee with gas_obs := []) (FST H) <=>
     storage_well_formed_on cx ee (FST H)` by
       (irule vyperStorageFootprintTheory.storage_well_formed_on_backends >> simp[NoAsms]) >>
     pop_assum (fn th => rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qpat_assum `u.vs_alloca_next = staged.vs_alloca_next` SUBST1_TAC >>
               first_assum ACCEPT_TAC) >>
  conj_tac >-
    (`ghost_inv_at (DF H) lo d cenv cx (ee with gas_obs := []) Gc tf u =
      ghost_inv_at (DF H) lo d cenv cx ee Gc tf u` by
       simp[NoAsms,bodyPtrDefsTheory.ghost_inv_at_def] >>
     pop_assum (fn th => rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
  conj_tac >-
    (gen_tac >> disch_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sd x /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at sd x ==> lookup_var x u = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  conj_tac >-
    (qpat_assum `u.vs_allocas = staged.vs_allocas` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  conj_tac >-
    (rewrite_tac[stmtSimDefsTheory.alloca_frame_gas_obs] >>
     irule stmtSimDefsTheory.alloca_frame_trans >>
     qexistsl_tac [`cenv`,`mid`,`staged`,`sd`] >>
     `sa.cs_next_id <= sd.cs_next_id` by
       (qpat_assum `ci_mono sa sd` mp_tac >> simp[NoAsms,ci_mono_def]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `tf.t_mem = ts.t_mem` SUBST1_TAC >> first_assum ACCEPT_TAC
QED

Finalise append_storage_aggregate_cont_full[local]

Theorem append_nested_storage_success_path:
  compile_dynarray_append cenv bop vop 1 1 elem src_ty cap T
    (if tr then LocTransient else LocStorage) sm = ((),sb) /\
  eval_operand bop t = SOME slot /\ eval_operand vop t = SOME w /\
  (!x. bop = Var x \/ vop = Var x ==> not_fresh_at sm x) /\
  cap < dimword (:256) /\ op_taint tn bop = {} /\ op_taint tn vop = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
  allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ ~t.vs_halted /\
  fn_has_code sm sb func /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  len = w2n (if tr then tload slot t else sload slot t) /\ len < cap /\
  ~t.vs_call_ctx.cc_static ==>
  ?u Gf tf.
    gas_path_ptr D lo ctx func PG G tn t 0 Gf tf
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    state_frame u = state_frame
      (if tr then tstore slot (n2w (len+1)) (tstore (slot+n2w (1+len)) w t)
       else sstore slot (n2w (len+1)) (sstore (slot+n2w (1+len)) w t)) /\
    tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
    (if tr then
       tf.t_trans = key_update (key_update tn.t_trans (slot+n2w (1+len)) {}) slot {} /\
       tf.t_stor = tn.t_stor
     else
       tf.t_stor = key_update (key_update tn.t_stor (slot+n2w (1+len)) {}) slot {} /\
       tf.t_trans = tn.t_trans) /\
    (!x. not_fresh_at sm x ==> FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tf (Var x) = op_taint tn (Var x)) /\
    (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x t) /\
    run_inst_seq (emitted_insts sm sb) t = OK u /\
    run_inst_seq_mem_ok (emitted_insts sm sb) t /\
    inst_seq_ptr D lo ctx func PG G tn (emitted_insts sm sb) t Gf tf /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
               i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS)
      (emitted_insts sm sb) /\
    inst_extends sm sb /\ sb.cs_current_bb = sm.cs_current_bb
Proof
  strip_tac >>
  drule_all stmtAppendStoragePathPtrTheory.append_storage_word_suffix_code >>
  strip_tac >>
  qpat_assum `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ = _`
    (mp_tac o REWRITE_RULE [stmtSimAppendStorageTheory.compile_dynarray_append_word_parts]) >>
  strip_tac >>
  `(!x. bop = Var x ==> not_fresh_at sm x) /\
   w2n (if tr then tload slot t else sload slot t) < cap` by metis_tac[] >>
  drule_all appendStorageStageTransportPtrTheory.append_storage_guard_actual >>
  disch_then (qspecl_then [`func`, `PG`, `G`, `D`] strip_assume_tac) >>
  suspend "suffix"
QED

Resume append_nested_storage_success_path[suffix]:
  `sm.cs_next_var <= s3.cs_next_var /\
   (!x. lop = Var x ==> not_fresh_at s3 x)` by
    (qpat_assum `emit_op (if tr then TLOAD else SLOAD) _ _ = _` mp_tac >>
     qpat_assum `emit_op LT _ _ = _` mp_tac >>
     qpat_assum `emit_void ASSERT _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     imp_res_tac emitHelperPropsTheory.emitted_insts_emit_op >>
     imp_res_tac emitHelperPropsTheory.emitted_insts_emit_void >>
     gvs[loweringStateRelDefsTheory.not_fresh_at_def] >> simp[]) >>
  `!x. bop = Var x \/ lop = Var x \/ vop = Var x ==> not_fresh_at s3 x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `eval_operand bop t' = SOME slot /\ eval_operand vop t' = SOME w /\
   op_taint tn' bop = {} /\ op_taint tn' vop = {}` by
    (Cases_on `bop` >> Cases_on `vop` >>
     gvs[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_taint_def]) >>
  `~t'.vs_call_ctx.cc_static` by
    (qpat_assum `state_frame t' = state_frame t` mp_tac >>
     qpat_assum `~t.vs_call_ctx.cc_static` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[stateFrameTheory.state_frame_def, venomStateTheory.venom_state_component_equality] >>
     metis_tac[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t'` by
    (`!u. allocas_below_fmp (state_frame u) <=> allocas_below_fmp u` by
       simp[stateFrameTheory.state_frame_def, ptrDisciplineTheory.allocas_below_fmp_def] >>
     metis_tac[]) >>
  drule_all appendStorageStageTransportPtrTheory.append_storage_suffix_actual >>
  disch_then (qspecl_then [`func`, `PG`, `G'`, `D`] strip_assume_tac) >>
  suspend "compose"
QED

Resume append_nested_storage_success_path[compose]:
  imp_res_tac emitHelperPropsTheory.inst_extends_emit_op >>
  imp_res_tac emitHelperPropsTheory.inst_extends_emit_void >>
  `inst_extends sm s3 /\ inst_extends s3 sb` by
    metis_tac[emitHelperPropsTheory.inst_extends_trans] >>
  `emitted_insts sm sb = emitted_insts sm s3 ++ emitted_insts s3 sb` by
    (irule exprLoweringPropsTheory.emitted_insts_append >>
     fs[emitHelperPropsTheory.inst_extends_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm s3)` by
    fs[EVERY_MEM] >>
  `run_inst_seq (emitted_insts sm sb) t = OK t''` by
    (irule emitHelperPropsTheory.run_inst_seq_compose_ok >>
     qexistsl_tac [`t'`, `s3`] >> simp[]) >>
  drule_all emittedSeqComposePtrTheory.emitted_inst_seq_ptr_uniform_compose >>
  strip_tac >>
  `inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sm sb) t G9 tn9` by
    (first_x_assum (qspec_then `t.vs_inst_idx` mp_tac) >> simp[]) >>
  suspend "lift"
QED

Resume append_nested_storage_success_path[lift]:
  `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> ALLOCA)
      (emitted_insts sm sb)` by
    (qpat_assum `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     drule bodyMemAppendFactsTheory.append_storage_word_suffix_footprint_mem >>
     simp[EVERY_MEM] >> strip_tac >> gen_tac >> disch_tac >>
     first_x_assum drule >> strip_tac >> gvs[]) >>
  `inst_seq_ptr D lo ctx func PG G tn (emitted_insts sm sb) t G9 tn9` by
    (irule fragGasCopySeqLiftPropsTheory.inst_seq_ptr_lower_bound_transport >>
     simp[] >> qexists_tac `0` >> simp[] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sm sb)` by
    (qpat_assum `EVERY (\i. _ /\ _ /\ _ /\ _) (emitted_insts sm sb)` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[EVERY_MEM] >> metis_tac[]) >>
  drule_all fragGasSeqPtrTheory.run_inst_seq_gas_path_ptr >> strip_tac >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm sb)) = 0` by
    (simp[LENGTH_NIL, FILTER_EQ_NIL] >> fs[EVERY_MEM]) >>
  qexistsl_tac [`t''`, `G9`, `tn9`] >>
  conj_tac
  >- (qpat_x_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      simp[arithmeticTheory.ADD_COMM]) >>
  suspend "post"
QED

Resume append_nested_storage_success_path[post]:
  conj_tac
  >- (qpat_assum `state_frame t'' = _` mp_tac >>
      qpat_assum `state_frame t' = state_frame t` mp_tac >>
      qpat_assum `len = _` mp_tac >>
      rpt (pop_assum kall_tac) >> Cases_on `tr` >>
      pure_rewrite_tac[boolTheory.COND_CLAUSES] >>
      disch_then SUBST1_TAC >>
      rewrite_tac[GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n] >>
      rpt strip_tac >>
      fs[stateFrameTheory.state_frame_def, venomStateTheory.tstore_def,
         venomStateTheory.sstore_def, wordsTheory.WORD_ADD_ASSOC]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (qpat_assum `if tr then _ else _` mp_tac >>
      qpat_assum `tn'.t_stor = tn.t_stor` mp_tac >>
      qpat_assum `tn'.t_trans = tn.t_trans` mp_tac >>
      qpat_assum `len = _` mp_tac >>
      rpt (pop_assum kall_tac) >> Cases_on `tr` >>
      pure_rewrite_tac[boolTheory.COND_CLAUSES] >>
      disch_then SUBST1_TAC >>
      rewrite_tac[GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n] >>
      simp[wordsTheory.WORD_ADD_ASSOC]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at s3 x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
      metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at s3 x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
      simp[venomStateTheory.lookup_var_def] >>
      metis_tac[venomStateTheory.lookup_var_def]) >>
  `run_inst_seq_mem_ok (emitted_insts sm sb) t` by
    (irule bodyMemAppendFactsTheory.append_storage_word_suffix_mem_ok >>
     goal_assum (drule_at Any)) >>
  `inst_extends sm sb` by metis_tac[emitHelperPropsTheory.inst_extends_trans] >>
  `sb.cs_current_bb = sm.cs_current_bb` by
    (qpat_assum `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     drule bodyMemAppendFactsTheory.append_storage_word_suffix_footprint_mem >>
     simp[exprLoweringPropsTheory.same_blocks_def]) >>
  simp[] >> fs[EVERY_MEM] >> metis_tac[]
QED

Finalise append_nested_storage_success_path

Theorem append_nested_storage_abort_path:
  compile_dynarray_append cenv bop vop 1 1 elem src_ty cap T
    (if tr then LocTransient else LocStorage) sm = ((),sb) /\
  eval_operand bop t = SOME slot /\ eval_operand vop t = SOME w /\
  (!x. bop = Var x \/ vop = Var x ==> not_fresh_at sm x) /\
  cap < dimword (:256) /\ op_taint tn bop = {} /\ op_taint tn vop = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
  allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ ~t.vs_halted /\
  fn_has_code sm sb func /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  len = w2n (if tr then tload slot t else sload slot t) /\ ~(len < cap) ==>
  ?u Gf tf.
    gas_path_ptr D lo ctx func PG G tn t 0 Gf tf (Abort Revert_abort u) /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sm x ==> FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tf (Var x) = op_taint tn (Var x)) /\
    ?r j. u = r with vs_inst_idx := j /\
      run_inst_seq (emitted_insts sm sb) t = Abort Revert_abort r /\
      run_inst_seq_mem_ok (emitted_insts sm sb) t /\
      (!D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sm sb) t Gf tf) /\
      EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
                 i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS)
        (emitted_insts sm sb) /\
      inst_extends sm sb /\ sb.cs_current_bb = sm.cs_current_bb
Proof
  strip_tac >>
  drule_all stmtAppendStoragePathPtrTheory.append_storage_word_suffix_code >> strip_tac >>
  qpat_assum `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ = _`
    (mp_tac o REWRITE_RULE [stmtSimAppendStorageTheory.compile_dynarray_append_word_parts]) >>
  strip_tac >>
  `(!x. bop = Var x ==> not_fresh_at sm x) /\
   ~(w2n (if tr then tload slot t else sload slot t) < cap)` by metis_tac[] >>
  drule_all appendStorageStageTransportPtrTheory.append_storage_guard_abort_actual >>
  disch_then (qspecl_then [`func`, `PG`, `G`,
    `<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`]
    strip_assume_tac) >>
  imp_res_tac emitHelperPropsTheory.inst_extends_emit_op >>
  imp_res_tac emitHelperPropsTheory.inst_extends_emit_void >>
  `inst_extends sm s3 /\ inst_extends s3 sb` by
    metis_tac[emitHelperPropsTheory.inst_extends_trans] >>
  `emitted_insts sm sb = emitted_insts sm s3 ++ emitted_insts s3 sb` by
    (irule exprLoweringPropsTheory.emitted_insts_append >>
     fs[emitHelperPropsTheory.inst_extends_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm s3)` by
    fs[EVERY_MEM] >>
  `run_inst_seq (emitted_insts sm sb) t = Abort Revert_abort t'` by
    simp[exprLoweringPropsTheory.run_inst_seq_append_err] >>
  drule_all emittedSeqComposePtrTheory.emitted_inst_seq_ptr_uniform_abort_extend >>
  strip_tac >>
  `inst_seq_ptr
      <|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>
      0 ctx func PG G tn (emitted_insts sm sb) t G' tn'` by
    (first_x_assum (qspec_then `t.vs_inst_idx` mp_tac) >> simp[]) >>
  suspend "lift"
QED

Resume append_nested_storage_abort_path[lift]:
  `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> ALLOCA)
      (emitted_insts sm sb)` by
    (qpat_assum `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     drule bodyMemAppendFactsTheory.append_storage_word_suffix_footprint_mem >>
     simp[EVERY_MEM] >> strip_tac >> gen_tac >> disch_tac >>
     first_x_assum drule >> strip_tac >> gvs[]) >>
  `!D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sm sb) t G' tn'` by
    (gen_tac >>
     irule fragGasCopySeqLiftPropsTheory.inst_seq_ptr_lower_bound_transport >>
     simp[] >> qexists_tac `0` >> simp[] >>
     irule instSeqPtrLoTheory.inst_seq_ptr_zero_to_lo >>
     simp[ptrDisciplineTheory.allocas_from_def] >> qexists_tac
       `<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>` >>
     simp[] >> metis_tac[]) >>
  `inst_seq_ptr D lo ctx func PG G tn (emitted_insts sm sb) t G' tn'` by simp[] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
      ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
    (qpat_assum `EVERY (\i. _ /\ _ /\ _ /\ _) (emitted_insts sm sb)` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[EVERY_MEM] >> metis_tac[]) >>
  drule_all stmtAppendStoragePathPtrTheory.run_inst_seq_abort_zero_path_ptr >> strip_tac >>
  qexistsl_tac [`t' with vs_inst_idx := j`, `G'`, `tn'`] >>
  simp[] >> qexists_tac `j` >> simp[] >>
  `run_inst_seq_mem_ok (emitted_insts sm sb) t` by
    (irule bodyMemAppendFactsTheory.append_storage_word_suffix_mem_ok >>
     goal_assum (drule_at Any)) >>
  `inst_extends sm sb` by metis_tac[emitHelperPropsTheory.inst_extends_trans] >>
  `sb.cs_current_bb = sm.cs_current_bb` by
    (qpat_assum `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     drule bodyMemAppendFactsTheory.append_storage_word_suffix_footprint_mem >>
     simp[exprLoweringPropsTheory.same_blocks_def]) >>
  simp[] >> fs[EVERY_MEM] >> metis_tac[]
QED

Finalise append_nested_storage_abort_path

Theorem append_nested_storage_endpoint_full:
  stmt_state_rel H ctx func cenv cx mid t /\
  storage_well_formed_on cx mid (FST H) /\
  ghost_inv_at D lo d cenv cx mid G tn t /\
  dead_lo_ok H D lo cenv cx /\
  return_buf_frame d cenv sm t /\
  regions_consistent (FST H) /\
  MEM (tr,rootk,root) (FST H) /\
  storage_subregion root path delta (ArrayTV tv (Dynamic cap)) /\
  w2n slot = w2n rootk + delta /\
  w2n rootk + type_slot_size root <= dimword (:256) /\
  type_slot_size tv = 1 /\ len < cap /\
  well_formed_type_value (ArrayTV tv (Dynamic cap)) /\
  value_has_type tv v /\
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v mid = (INL (),ee) /\
  ee = set_storage cx mid tr
    (update_storage slot (n2w (len+1))
      (update_storage (slot+n2w (1+len)) w (get_storage cx mid tr))) /\
  state_frame u = state_frame
    (if tr then tstore slot (n2w (len+1))
       (tstore (slot+n2w (1+len)) w t)
     else sstore slot (n2w (len+1))
       (sstore (slot+n2w (1+len)) w t)) /\
  tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
  (if tr then
     tf.t_trans = key_update (key_update tn.t_trans (slot+n2w (1+len)) {}) slot {} /\
     tf.t_stor = tn.t_stor
   else
     tf.t_stor = key_update (key_update tn.t_stor (slot+n2w (1+len)) {}) slot {} /\
     tf.t_trans = tn.t_trans) /\
  (!x. not_fresh_at sm x ==> FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tf (Var x) = op_taint tn (Var x)) /\
  (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x t) /\
  local_ptrs_reserved cenv sm /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x. lo <> 0 /\ cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sm x) /\
  (!x. not_fresh_at sm x ==> not_fresh_at sb x) /\
  z = (u with vs_inst_idx := LENGTH sb.cs_current_insts) ==>
  stmt_state_rel H ctx func cenv cx ee z /\
  storage_well_formed_on cx ee (FST H) /\
  ghost_inv_at D lo d cenv cx ee Gf tf z /\
  return_buf_frame d cenv sb z /\
  z.vs_alloca_next = t.vs_alloca_next /\
  z.vs_allocas = t.vs_allocas /\
  (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x t)
Proof
  strip_tac >>
  conj_tac >- suspend "state_rel" >>
  conj_tac >- (irule vyperFiniteStoragePreservationTheory.append_subregion_preserves_storage_well_formed_on >>
    goal_assum (drule_at Any) >> metis_tac[]) >>
  conj_tac >- suspend "ghost" >>
  suspend "frames"
QED

Resume append_nested_storage_endpoint_full[state_rel]:
  drule_all appendResolvedStorageRelTheory.stmt_state_rel_append_resolved_storage_updates >>
  disch_then (qspec_then `w` mp_tac) >>
  strip_tac >>
  irule assignTuplePtrLoadStepTheory.stmt_state_rel_old_vars_frame_ptr >>
  goal_assum (drule_at Any) >>
  qexists_tac `if tr then tstore slot (n2w (len+1))
       (tstore (slot+n2w (1+len)) w t)
     else sstore slot (n2w (len+1))
       (sstore (slot+n2w (1+len)) w t)` >>
  conj_tac >- (Cases_on `tr` >>
    simp[venomStateTheory.lookup_var_def, venomStateTheory.tstore_def,
         venomStateTheory.sstore_def] >>
    metis_tac[venomStateTheory.lookup_var_def]) >>
  reverse conj_tac >- asm_rewrite_tac[] >>
  suspend "state_frame"
QED

Resume append_nested_storage_endpoint_full[state_frame]:
  gvs[]
QED

Resume append_nested_storage_endpoint_full[ghost]:
  Cases_on `tr` >>
  (gvs[stateFrameTheory.state_frame_def, venomStateTheory.tstore_def,
       venomStateTheory.sstore_def] >>
   `!p sz. not_fresh_at sm p /\ ptr_covers G tn p t sz ==>
       ptr_covers Gf tf p (u with vs_inst_idx := LENGTH sb.cs_current_insts) sz` by
     (rw[bodyPtrDefsTheory.ptr_covers_def] >>
      gvs[venomStateTheory.lookup_var_def] >> metis_tac[]) >>
   gvs[bodyPtrDefsTheory.ghost_inv_at_def,
       vyperStorageBackendTheory.set_storage_def] >>
   conj_tac
   >- (rpt gen_tac >> strip_tac >>
       rename1 `lookup_scopes name mid.scopes = SOME entry` >>
       `not_fresh_at sm p` by
         metis_tac[loweringStateRelDefsTheory.local_ptrs_reserved_def] >>
       gvs[venomStateTheory.lookup_var_def] >> metis_tac[]) >>
   conj_tac
   >- (Cases_on `d` >> gvs[bodyPtrDefsTheory.return_buf_ptr_def] >>
       rename1 `return_buf_ptr (SOME rb)` >> PairCases_on `rb` >>
       gvs[bodyPtrDefsTheory.return_buf_ptr_def,
           venomStateTheory.lookup_var_def] >> metis_tac[])) >>
  rpt conj_tac >>
  gvs[ptrDisciplineTheory.allocas_from_def] >>
  suspend "storage_taint"
QED

Resume append_nested_storage_endpoint_full[storage_taint]:
  markerLib.RESUME_TAC >>
  gvs[bodyPtrDefsTheory.stor_taint_ok_at_def,
      bodyPtrDefsTheory.dead_lo_ok_def, sourceUnitExecutionTheory.cx_dead_def] >>
  Cases_on `t.vs_call_ctx.cc_address = cx.txn.target` >>
  gvs[vfmStateTheory.lookup_account_def, combinTheory.APPLY_UPDATE_THM,
      ptrDisciplineTheory.key_update_def, pred_setTheory.SUBSET_DEF,
      pred_setTheory.IN_DIFF] >>
  rpt strip_tac >> gvs[] >>
  irule (SRULE [arithmeticTheory.ADD_COMM]
    appendResolvedStorageRelTheory.append_resolved_storage_dead_mono) >>
  conj_tac >- metis_tac[] >>
  metis_tac[pairTheory.PAIR_EQ]
QED

Resume append_nested_storage_endpoint_full[frames]:
  Cases_on `tr` >>
  gvs[stateFrameTheory.state_frame_def, venomStateTheory.tstore_def,
      venomStateTheory.sstore_def] >>
  (simp[venomStateTheory.lookup_var_def] >>
   conj_tac
   >- (Cases_on `d` >> gvs[loweringPostsTheory.return_buf_frame_def] >>
       rename1 `return_buf_frame (SOME rb)` >> PairCases_on `rb` >>
       gvs[loweringPostsTheory.return_buf_frame_def] >>
       gvs[venomStateTheory.lookup_var_def]) >>
   gvs[venomStateTheory.lookup_var_def])
QED

Finalise append_nested_storage_endpoint_full

Theorem append_nested_storage_cont_framed[local]:
 !DF lo d ctx shadow_ctx PG func cx st0 lctx RetQ cenv env sa sm sb s0 G0 tn0
   mid t G tn tr slot tv v bop vop w elem src_ty cap.
  body_inv (cx_tops cx) ctx cenv cx /\
  gas_admissible (append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v)
    (stmt_res_ok lctx) mid /\
  expr_sim_inv cenv cx env mid /\ is_word_type elem /\
  evaluate_type (get_tenv cx) elem = SOME tv /\
  value_has_type tv v /\
  compile_dynarray_append cenv bop vop 1 1 elem src_ty cap T
    (if tr then LocTransient else LocStorage) sm = ((),sb) /\
  (!x. bop = Var x \/ vop = Var x ==> not_fresh_at sm x) /\
  eval_operand bop t = SOME slot /\ eval_operand vop t = SOME w /\
  w = typed_val_to_w256 tv v /\
  op_taint tn bop = {} /\ op_taint tn vop = {} /\ cap < dimword (:256) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid t /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx mid G tn t /\
    storage_place_observed H (StoragePlace tr slot (ArrayTV tv (Dynamic cap)))) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  fn_inst_ids_distinct func /\ fn_has_code sm sb func /\
  cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\
  local_ptrs_reserved cenv sa /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sm t /\ alloca_history func t /\
  s0.vs_alloca_next <= t.vs_alloca_next /\ ~t.vs_halted /\
  t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
  (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
    op_taint tn (Var x) = op_taint tn0 (Var x)) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0
    (append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v) (mid,t,G,tn)
    (\H res ee Gf tf u. ?cenv''.
      stmt_lands lctx sb res u /\ ~u.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv) /\
      cenv_top_ext cenv cenv'' ee.scopes /\
      stmt_state_rel H ctx func cenv'' cx ee u /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv'' sb u /\ alloca_history func u /\
      s0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv'' cx ee Gf tf u /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G0 x /\
         op_taint tf (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame cenv mid sm t cenv'' ee u /\ tf.t_mem SUBSET tn.t_mem)
    (\H res ee gt r. (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
      halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==>
        allocas_below_fmp s))
Proof
  rpt gen_tac >> strip_tac >>
  `!x. lo <> 0 /\ cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sm x` by
    (metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_imm_base,
               freshWritesTheory.not_fresh_at_mono]) >>
  suspend "classify"
QED

Resume append_nested_storage_cont_framed[classify]:
  `ptrDiscipline$ctx_has_dalloca ctx ==>
    !pre i post u. emitted_insts sm sb = pre ++ i::post /\
      run_inst_seq pre t = OK u ==> unitTransformDefs$dalloca_no_wrap i u` by
    (drule_then (mp_tac o CONJUNCT2 o CONJUNCT2)
       bodyMemAppendFactsTheory.append_storage_word_suffix_footprint_mem >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
     qpat_x_assum `EVERY _ _` mp_tac >>
     qpat_x_assum `emitted_insts sm sb = _` (fn th => pure_rewrite_tac[th]) >>
     simp[EVERY_APPEND] >> rpt strip_tac >> fs[]) >>
  `type_slot_size tv = 1` by metis_tac[exprSimUnwrapTheory.word_type_slot_size] >>
  `encode_value tv v = SOME [(0,typed_val_to_w256 tv v)]` by
    metis_tac[stmtSimAssignStorageFactsTheory.encode_value_word_typed] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- fs[vyperStorageFootprintTheory.storage_trace_domain_def]) >>
  strip_tac >>
  `t.vs_call_ctx.cc_static = cx.txn.is_static` by
    (drule stmt_state_rel_state_rel >>
     disch_then (mp_tac o MATCH_MP state_rel_call_ctx_rel) >>
     simp[loweringStateRelDefsTheory.call_ctx_rel_def]) >>
  `!raw. storage_read_live (storage_trace_horizon mid.storage_trace) tr raw slot
      (ArrayTV tv (Dynamic cap))` by
    (gen_tac >> irule accountsRelPropsTheory.storage_place_observed_read_live >>
     simp[vyperValueTheory.type_slot_size_def]) >>
  `w2n slot + type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword (:256)` by
    (fs[vyperStoragePlaceObservedTheory.storage_place_observed_def] >>
     `regions_consistent (FST (storage_trace_horizon mid.storage_trace))` by
       (fs[vyperStorageFootprintTheory.storage_trace_domain_def,
           vyperStorageFootprintTheory.valid_horizon_def]) >>
     drule_then assume_tac vyperStoragePlaceRegionTheory.storage_subregion_bounds >>
     `w2n root + type_slot_size tv' <= dimword (:256)` by
       metis_tac[vyperStorageFootprintTheory.regions_consistent_def] >>
     `w2n root + delta < dimword (:256)` by
       (fs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
     `delta < dimword (:256)` by decide_tac >>
     simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w] >> decide_tac) >>
  `(if tr then tload slot t else sload slot t) =
      lookup_storage slot (get_storage cx mid tr)` by
    (irule (INST_TYPE [alpha |-> ``:256``]
       (cj 2 targetSubscriptStorageTheory.target_storage_array_len_ok)) >>
     conj_tac >- (qexists_tac `bop` >> simp[]) >>
     qexistsl_tac [`storage_trace_horizon mid.storage_trace`, `cenv`, `ctx`, `func`,
                   `cap`, `tv`] >> simp[]) >>
  `key_taint (if tr then tn.t_trans else tn.t_stor) slot = {}` by
    (irule (INST_TYPE [alpha |-> ``:256``]
       appendStorageGhostPtrTheory.storage_dead_key_taint_empty) >>
     qexistsl_tac [`storage_trace_horizon mid.storage_trace`,
       `if tr then contract_transient t else contract_storage t`, `tr`,
       `ArrayTV tv (Dynamic cap)`] >>
     simp[vyperValueTheory.type_slot_size_def] >>
     qpat_assum `!H. dead_lo_ok H _ _ _ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` assume_tac) >>
     Cases_on `t.vs_call_ctx.cc_address = cx.txn.target` >>
     Cases_on `tr` >>
     fs[bodyPtrDefsTheory.ghost_inv_at_def, bodyPtrDefsTheory.stor_taint_ok_at_def,
        bodyPtrDefsTheory.dead_lo_ok_def,
        sourceUnitExecutionTheory.cx_dead_def, venomStateTheory.contract_storage_def,
        venomStateTheory.contract_transient_def, vfmStateTheory.lookup_account_def]) >>
  Cases_on `w2n (lookup_storage slot (get_storage cx mid tr)) < cap`
  >- suspend "success"
  >> suspend "capacity"
QED

Resume append_nested_storage_cont_framed[success]:
  Cases_on `cx.txn.is_static` >- suspend "static" >>
  `~t.vs_call_ctx.cc_static` by simp[] >>
  qabbrev_tac `len = w2n (lookup_storage slot (get_storage cx mid tr))` >>
  `append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v mid =
   (INL (), set_storage cx mid tr
      (update_storage slot (n2w (len+1))
        (update_storage (slot+n2w (1+len)) w (get_storage cx mid tr))))` by
    (mp_tac (Q.INST [`len` |-> `len`, `es` |-> `mid`, `w` |-> `w`]
       vyperStorageBackendTheory.append_storage_word_success) >>
     (impl_tac >- simp[Abbr `len`]) >>
     Cases_on `tr` >>
     simp[vyperStorageBackendTheory.set_storage_def]) >>
  suspend "source_success"
QED

Resume append_nested_storage_cont_framed[source_success]:
  `allocas_from lo t` by fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  `len = w2n (if tr then tload slot t else sload slot t)` by simp[Abbr `len`] >>
  drule_all append_nested_storage_success_path >>
  disch_then (qspecl_then [`PG`, `G`, `DF (storage_trace_horizon mid.storage_trace)`]
    strip_assume_tac) >>
  `!D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sm sb) t Gf tf` by
    (gen_tac >> drule_all append_nested_storage_success_path >>
     disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
     metis_tac[fragGasSeqPtrTheory.inst_seq_ptr_ghost_unique]) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) []
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tf)` by
    (rpt gen_tac >>
     qpat_assum `run_inst_seq (emitted_insts sm sb) t = OK u`
       (mp_then (Pat `run_inst_seq _ _ = _`) mp_tac
          fragGasOriginPtrLoopTheory.emitted_origin_ptr_path) >>
     simp[EVERY_MEM] >> disch_then irule >> simp[] >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all stmtAppendStoragePathPtrTheory.append_storage_word_suffix_code >> strip_tac >>
  `alloca_history func (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (`alloca_inv t` by fs[exprLoweringPropsTheory.stmt_state_rel_def] >>
     `?rest. DROP t.vs_inst_idx bb.bb_instructions = emitted_insts sm sb ++ rest` by
       metis_tac[rich_listTheory.IS_PREFIX_APPEND] >>
     `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
       (fs[EVERY_MEM] >> metis_tac[]) >>
     drule_all allocaHistoryFragmentTheory.alloca_history_run_inst_seq >> simp[]) >>
  qmatch_asmsub_abbrev_tac `append_place _ _ _ mid = (INL (),ee)` >>
  `!tail. append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v
      (mid with gas_obs := tail) = (INL (),ee with gas_obs := tail)` by
    (gen_tac >> mp_tac (Q.INST [`len` |-> `len`,
       `es` |-> `mid with gas_obs := tail`, `w` |-> `w`]
       vyperStorageBackendTheory.append_storage_word_success) >>
     (impl_tac >- (Cases_on `tr` >> simp[Abbr `len`, vyperStorageBackendTheory.get_storage_def])) >>
     Cases_on `tr` >> simp[Abbr `ee`, vyperStorageBackendTheory.set_storage_def,
       vyperStorageBackendTheory.get_storage_def]) >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_pure >>
  conj_tac >- (qexistsl_tac [`Gf`, `ee`, `INL ()`,
     `u with vs_inst_idx := LENGTH sb.cs_current_insts`, `tf`] >>
     simp[] >> gen_tac >> disch_tac >>
     `ee.storage_trace = mid.storage_trace /\ ee.scopes = mid.scopes` by
       (Cases_on `tr` >> simp[NoAsms, Abbr `ee`, vyperStorageBackendTheory.set_storage_def]) >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- fs[]) >> strip_tac >>
     `regions_consistent (FST H)` by
       fs[vyperStorageFootprintTheory.valid_horizon_def] >>
     qpat_assum `storage_place_observed H _`
       (strip_assume_tac o PURE_REWRITE_RULE
          [vyperStoragePlaceObservedTheory.storage_place_observed_def]) >>
     `w2n root + type_slot_size tv' <= dimword (:256)` by
       metis_tac[vyperStorageFootprintTheory.regions_consistent_def] >>
     `w2n slot = w2n root + delta` by
       (drule_then assume_tac vyperStoragePlaceRegionTheory.storage_subregion_bounds >>
        `w2n root + delta < dimword (:256)` by
          (fs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
        `delta < dimword (:256)` by decide_tac >>
        simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w]) >>
     `well_formed_type_value (ArrayTV tv (Dynamic cap))` by
       (`well_formed_type_value tv` by
          metis_tac[vyperTypingTheory.evaluate_type_well_formed] >>
        simp[vyperTypingTheory.well_formed_type_value_def,
          vyperValueTheory.type_slot_size_def]) >>
     `local_ptrs_reserved cenv sm /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
      (!x. not_fresh_at sm x ==> not_fresh_at sb x)` by
       (conj_tac >- (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
          qexists_tac `sa` >> simp[]) >>
        `sm.cs_next_var <= sb.cs_next_var` by
          metis_tac[bodyMemAppendFactsTheory.append_storage_word_suffix_grows_mem] >>
        metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
     `ee = set_storage cx mid tr (update_storage slot (n2w (len+1))
         (update_storage (slot+n2w (1+len)) w (get_storage cx mid tr)))` by
       simp[Abbr `ee`] >>
     `dead_lo_ok H (DF H) lo cenv cx` by simp[] >>
     rename1 `MEM (tr,rk,tv') (FST H)` >>
     mp_tac (Q.INST [`z` |-> `u with vs_inst_idx := LENGTH sb.cs_current_insts`,
        `D` |-> `DF H`, `rootk` |-> `rk`, `root` |-> `tv'`]
        append_nested_storage_endpoint_full) >>
     (impl_tac >- (rpt conj_tac >> rewrite_tac[] >> first_assum ACCEPT_TAC)) >>
     strip_tac >>
     `u.vs_current_bb = t.vs_current_bb /\ u.vs_halted = t.vs_halted` by
       (qpat_x_assum `state_frame u = _` mp_tac >> Cases_on `tr` >>
        simp[NoAsms, stateFrameTheory.state_frame_def,
          venomStateTheory.tstore_def, venomStateTheory.sstore_def,
          venomStateTheory.venom_state_component_equality]) >>
     conj_tac >- simp[loweringPostsTheory.stmt_lands_def] >>
     conj_tac >- simp[] >>
     conj_tac >- metis_tac[bodyMemAppendFactsTheory.append_storage_word_suffix_open_mem] >>
     conj_tac >- simp[loweringPostsTheory.cenv_top_ext_def] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (`storage_well_formed_on cx (ee with gas_obs := []) (FST H) <=>
                    storage_well_formed_on cx ee (FST H)` by
        (irule vyperStorageFootprintTheory.storage_well_formed_on_backends >>
         simp[NoAsms]) >> asm_rewrite_tac[]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qpat_x_assum `(_ with vs_inst_idx := _).vs_alloca_next = _` mp_tac >>
        simp_tac (srw_ss()) [] >> disch_then SUBST1_TAC >> first_assum ACCEPT_TAC) >>
     conj_tac >- (qpat_assum `ghost_inv_at (DF H) lo d cenv cx ee Gf tf _` mp_tac >>
        rpt (pop_assum kall_tac) >>
        simp_tac (srw_ss()) [bodyPtrDefsTheory.ghost_inv_at_def,
          bodyPtrDefsTheory.stor_taint_ok_at_def] >> metis_tac[]) >>
     `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
       metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     conj_tac >- metis_tac[] >>
     conj_tac >- (qpat_x_assum `(_ with vs_inst_idx := _).vs_allocas = _` mp_tac >>
        simp_tac (srw_ss()) [] >> disch_then SUBST1_TAC >> first_assum ACCEPT_TAC) >>
     conj_tac >- metis_tac[] >>
     `u.vs_memory = t.vs_memory` by
       (qpat_assum `state_frame u = _` mp_tac >> Cases_on `tr` >>
        simp[NoAsms, stateFrameTheory.state_frame_def,
          venomStateTheory.tstore_def, venomStateTheory.sstore_def,
          venomStateTheory.venom_state_component_equality]) >>
     irule (INST_TYPE [alpha |-> ``:256``] stmtSimDefsTheory.alloca_frame_of_mem_frame) >>
     simp[] >> qexistsl_tac [`H`, `ctx`, `cx`, `func`] >> simp[]) >> simp[]
QED

Resume append_nested_storage_cont_framed[capacity]:
  `append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v mid =
     (INR (Error (RuntimeError "append full storage array")),mid)` by
    (irule vyperStorageBackendTheory.append_storage_full >> decide_tac) >>
  `allocas_from lo t` by
    fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  mp_tac (Q.INST [`D` |->
    `<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`,
    `len` |-> `w2n (lookup_storage slot (get_storage cx mid tr))`]
    append_nested_storage_abort_path) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  strip_tac >>
  drule_all stmtAppendStoragePathPtrTheory.append_storage_word_suffix_code >>
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all bodyUnopFragMemoryTheory.run_inst_seq_abort_zero_path_mem >>
  strip_tac >>
  fs[fragGasModeTheory.gas_marked_path_def] >>
  suspend "capacity_joint"
QED

Resume append_nested_storage_cont_framed[capacity_joint]:
  rename1 `gas_path_mem ctx func t 0 (Abort Revert_abort (r with vs_inst_idx := jm))` >>
  `r with vs_inst_idx := jm = r with vs_inst_idx := j` by
    (qpat_assum `gas_path_mem _ _ _ _ _` mp_tac >>
     qpat_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     drule gasPathPtrExecTheory.gas_path_ptr_exec >>
     simp[fragExecTheory.exit_result_def] >> strip_tac >>
     drule fragGasPathMemTheory.gas_path_mem_exec >>
     simp[fragExecTheory.exit_result_def] >> strip_tac >>
     `run_from (fuel + fuel') ctx func t = Abort Revert_abort (r with vs_inst_idx := j)` by
       (irule fragGasPathTheory.gas_run_from_fuel_mono >>
        conj_tac >- simp[] >> qexists_tac `fuel` >> simp[]) >>
     `run_from (fuel + fuel') ctx func t = Abort Revert_abort (r with vs_inst_idx := jm)` by
       (irule fragGasPathTheory.gas_run_from_fuel_mono >>
        conj_tac >- simp[] >> qexists_tac `fuel'` >> simp[]) >> gvs[]) >>
  `!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,G,tn) [] (Abort Revert_abort (r with vs_inst_idx := j),Gf,tf)` by
    (gen_tac >> irule fragGasOriginPtrExecTheory.gas_zero_paths_joint >>
     simp[fragExecTheory.exit_result_def] >>
     conj_tac >- metis_tac[] >>
     irule ptrSafetyTransportTheory.gas_path_ptr_from_no_dead >> first_assum ACCEPT_TAC) >>
  suspend "capacity_exit"
QED

Resume append_nested_storage_cont_framed[capacity_exit]:
  `!tail. append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v
       (mid with gas_obs := tail) =
     (INR (Error (RuntimeError "append full storage array")),mid with gas_obs := tail)` by
    (gen_tac >> irule vyperStorageBackendTheory.append_storage_full >>
     Cases_on `tr` >>
     fs[vyperStorageBackendTheory.get_storage_def]) >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_exit >>
  conj_tac >- (qexistsl_tac [`Gf`, `mid`, `Abort Revert_abort (r with vs_inst_idx := j)`,
    `INR (Error (RuntimeError "append full storage array"))`, `tf`] >>
  simp[fragExecTheory.exit_result_def, bodyPtrDefsTheory.stmt_exit_ptr_def,
    exprSimDefsTheory.expr_exit_def, exprSimDefsTheory.halt_exit_def]) >> simp[]
QED

Resume append_nested_storage_cont_framed[static]:
  `allocas_from lo t` by fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  `w2n (if tr then tload slot t else sload slot t) < cap` by simp[] >>
  `t.vs_call_ctx.cc_static` by simp[] >>
  drule_all appendStorageStaticPtrTheory.append_storage_word_static_origin_path >>
  disch_then (qspecl_then [`PG`, `G`] strip_assume_tac) >>
  `!tail. append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v
      (mid with gas_obs := tail) =
      (INR (Error (RuntimeError "write in static context")),mid with gas_obs := tail)` by
    (gen_tac >> irule stmtSimAppendStorageTheory.append_storage_static >>
     Cases_on `tr` >> gvs[vyperStorageBackendTheory.get_storage_def]) >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_exit >>
  conj_tac >- (qexistsl_tac [`Gf`, `mid`,
    `Abort ExHalt_abort ((halt_state (set_returndata [] u)) with vs_inst_idx := j)`,
    `INR (Error (RuntimeError "write in static context"))`, `tf`] >>
    simp[fragExecTheory.exit_result_def, bodyPtrDefsTheory.stmt_exit_ptr_def,
      exprSimDefsTheory.expr_exit_def, exprSimDefsTheory.halt_exit_def]) >> simp[]
QED

Finalise append_nested_storage_cont_framed[local]

Theorem append_outcome_scopes[local]:
  eval_stmt cx (Append bt e) es = (res,ee) ==>
  MAP FDOM ee.scopes = MAP FDOM es.scopes /\
  res <> INR BreakException /\ res <> INR ContinueException
Proof
  pure_once_rewrite_tac[evaluate_def] >>
  simp[bind_def, AllCaseEqs()] >> strip_tac >>
  (conj_tac
  >- (imp_res_tac eval_target_place_preserves_scopes_dom >>
      imp_res_tac eval_expr_preserves_scopes_dom >>
      imp_res_tac read_result_state >> imp_res_tac append_place_scopes_dom >>
      gvs[] >> metis_tac[]) >>
  gvs[] >> rpt strip_tac >> gvs[] >>
  FIRST [
    qpat_assum `append_place _ _ _ _ = (INR _,_)`
      (mp_tac o MATCH_MP append_place_no_control),
    qpat_assum `read_result _ _ _ = (INR _,_)`
      (mp_tac o MATCH_MP read_result_no_control),
    qpat_assum `eval_expr _ _ _ = (INR _,_)`
      (mp_tac o MATCH_MP (cj 1 eval_expr_no_control)),
    qpat_assum `eval_target_place _ _ _ = (INR _,_)`
      (mp_tac o MATCH_MP eval_target_place_no_control)] >>
  simp[no_control_exc_def])
QED

Theorem append_return_buf_sep[local]:
  return_buf_frame d cenv sa s0 /\ return_buf_sep d cenv es s0 /\
  local_ptrs_reserved cenv sa /\ cenv' = cenv /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es s0) /\
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (eval_stmt cx (Append bt e)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?cenv''.
      stmt_lands lctx sb res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv') /\
      cenv_top_ext cenv cenv'' ee.scopes /\
      stmt_state_rel H ctx func cenv'' cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv'' sb t /\ alloca_history func t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv'' cx ee G tn t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
             lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
               FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==>
           FLOOKUP G x = FLOOKUP G0 x /\
           op_taint tn (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame cenv es sa s0 cenv'' ee t /\
      (!aid off sz i.
         FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
         (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                    off + sz <= b \/ b + sz' <= off) /\
         off <= i /\ i < off + sz /\ i IN tn.t_mem ==>
         i IN tn0.t_mem)) R ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (eval_stmt cx (Append bt e)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?cenv''.
      stmt_lands lctx sb res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv') /\
      cenv_top_ext cenv cenv'' ee.scopes /\
      stmt_state_rel H ctx func cenv'' cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv'' sb t /\ alloca_history func t /\
      return_buf_sep d cenv'' ee t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv'' cx ee G tn t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
             lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
               FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==>
           FLOOKUP G x = FLOOKUP G0 x /\
           op_taint tn (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame cenv es sa s0 cenv'' ee t /\
      (!aid off sz i.
         FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
         (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                    off + sz <= b \/ b + sz' <= off) /\
         off <= i /\ i < off + sz /\ i IN tn.t_mem ==>
         i IN tn0.t_mem)) R
Proof
  strip_tac >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (fn outcome =>
    qpat_assum `return_buf_frame d cenv sa s0` (fn frame =>
      qpat_assum `return_buf_sep d cenv es s0` (fn sep =>
        assume_tac (MATCH_MP gas_outcome_full_return_buf_allocas
          (LIST_CONJ [outcome,frame,sep]))))) >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ (\H res ee G tn t. _ /\
       (!bw cap. d = SOME (bw,cap) ==> allocas_from _ t)) R` (irule_at Any) >>
  simp[] >> rpt gen_tac >>
  disch_then (map_every strip_assume_tac o CONJUNCTS) >>
  `ee with gas_obs := [] = ee` by
    (qpat_x_assum `ee.gas_obs = []` (fn th => simp[GSYM th])) >>
  `eval_stmt cx (Append bt e) (es with gas_obs := xs) = (res,ee)` by
    (qpat_assum `ee with gas_obs := [] = ee` (fn eq =>
       qpat_assum `!tail. eval_stmt _ _ _ = _`
         (qspec_then `[]` (ACCEPT_TAC o PURE_REWRITE_RULE [listTheory.APPEND_NIL,eq])))) >>
  drule_then strip_assume_tac append_outcome_scopes >>
  `res = INL ()` by
    (qpat_assum `stmt_lands lctx sb res t`
       (strip_assume_tac o REWRITE_RULE [stmt_lands_def]) >> gvs[]) >>
  `cenv'' = cenv'` by fs[] >>
  `valid_horizon cx st0 H es.storage_trace` by
    (mp_tac (Q.INST [`st` |-> `es with gas_obs := xs`,
       `f` |-> `eval_stmt cx (Append bt e)`,
       `res` |-> `res`, `st'` |-> `ee`, `H` |-> `H`,
       `st0` |-> `st0`, `cx` |-> `cx`]
       (INST_TYPE [alpha |-> oneSyntax.one_ty] valid_horizon_frame)) >>
     simp[evaluate_storage_trace_frame]) >>
  `stmt_state_rel H ctx func cenv cx es s0` by metis_tac[] >>
  qexists_tac `cenv''` >> asm_rewrite_tac[] >>
  irule (INST_TYPE [alpha |-> ``:256``] return_buf_sep_locals_kept) >>
  conj_tac >- fs[arithmeticTheory.ADD_COMM] >>
  qexistsl_tac [`H`,`ctx`,`cx`,`es`,`func`,`s0`,`sa`] >> simp[]
QED

Theorem append_nested_suffix_frame_post[local]:
  alloca_frame cenv es sa s0 cenv mid t /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
  sa.cs_next_id <= sm.cs_next_id /\
  (!aid off sz i.
    FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
      off + sz <= b \/ b + sz' <= off) /\
    off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem) /\
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 f (mid,t,G,tn)
    (\H res ee Gf tf u. ?cenv''.
      stmt_lands lctx sb res u /\ ~u.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv) /\
      cenv_top_ext cenv cenv'' ee.scopes /\
      stmt_state_rel H ctx func cenv'' cx ee u /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv'' sb u /\ alloca_history func u /\
      s0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv'' cx ee Gf tf u /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G0 x /\
         op_taint tf (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame cenv mid sm t cenv'' ee u /\ tf.t_mem SUBSET tn.t_mem) R ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 f (mid,t,G,tn)
    (\H res ee Gf tf u. ?cenv''.
      stmt_lands lctx sb res u /\ ~u.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv) /\
      cenv_top_ext cenv cenv'' ee.scopes /\
      stmt_state_rel H ctx func cenv'' cx ee u /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv'' sb u /\ alloca_history func u /\
      s0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv'' cx ee Gf tf u /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G0 x /\
         op_taint tf (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame cenv es sa s0 cenv'' ee u /\
      (!aid off sz i.
        FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
        (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
          off + sz <= b \/ b + sz' <= off) /\
        off <= i /\ i < off + sz /\ i IN tf.t_mem ==> i IN tn0.t_mem)) R
Proof
  strip_tac >> irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
  goal_assum (drule_at (Pos last)) >> simp[] >>
  rpt gen_tac >> strip_tac >> qexists_tac `cenv''` >> simp[] >>
  conj_tac >- (irule stmtSimDefsTheory.alloca_frame_trans >>
    goal_assum (drule_at Any) >> simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `!aid off sz i. _` irule >>
  conj_tac >- (qexistsl_tac [`aid`, `off`, `sz`] >> simp[] >>
    first_assum ACCEPT_TAC) >>
  fs[pred_setTheory.SUBSET_DEF]
QED

Theorem append_resolved_copy_code_parts[local]:
  stmt_env cenv lctx ty (Append bt e) sa = (c,sf) /\
  compile_get_target_ptr compile_expr cenv bt sa =
    ((bop,SOME loc,SOME (ValPT (ArrayT elem (Dynamic cap)))),sp) /\
  ~is_word_type elem ==>
  c = cenv /\ ?sm raw tmp sc sd.
    lower_value compile_expr cenv elem e sp = (raw,sm) /\
    compile_alloc_buffer (type_memory_bytes cenv elem) sm = (tmp,sc) /\
    compile_store_memory cenv raw tmp.buf_operand elem
      (lowered_value_type cenv e) sc = ((),sd) /\
    compile_dynarray_append cenv bop tmp.buf_operand (word_scale loc)
      (elem_size_in_location cenv loc elem) elem elem cap F loc sd = ((),sf)
Proof
  strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, Once compile_stmt_def] >>
  Cases_on `lower_value compile_expr cenv elem e sp` >>
  rename1 `lower_value _ _ _ _ _ = (raw,sm)` >> simp[] >>
  Cases_on `compile_alloc_buffer (type_memory_bytes cenv elem) sm` >>
  rename1 `compile_alloc_buffer _ _ = (tmp,sc)` >> simp[] >>
  Cases_on `compile_store_memory cenv raw tmp.buf_operand elem (lowered_value_type cenv e) sc` >>
  rename1 `compile_store_memory _ _ _ _ _ _ = (u,sd)` >>
  Cases_on `u` >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[]
QED

Theorem append_memory_copy_suffix_parts[local]:
  compile_dynarray_append cenv bop src 32 stride elem elem cap F LocMemory a0 = ((),a9) <=>
  ?len valid data off dst next a1 a2 a3 a4 a5 a6 a7 a8.
    emit_op MLOAD [bop] a0 = (len,a1) /\
    emit_op LT [len; Lit (n2w cap)] a1 = (valid,a2) /\
    emit_void ASSERT [valid] a2 = ((),a3) /\
    emit_op ADD [bop; Lit 32w] a3 = (data,a4) /\
    emit_op MUL [len; Lit (n2w stride)] a4 = (off,a5) /\
    emit_op ADD [data; off] a5 = (dst,a6) /\
    compile_store_memory cenv src dst elem elem a6 = ((),a7) /\
    emit_op ADD [len; Lit 1w] a7 = (next,a8) /\
    emit_void MSTORE [bop; next] a8 = ((),a9)
Proof
  simp[compile_dynarray_append_def, contextTheory.compile_ptr_load_def,
       contextTheory.compile_ptr_store_def, comp_ignore_bind_def, comp_bind_def,
       comp_return_def, emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def, emitHelperTheory.emit_inst_def,
       fresh_var_def, fresh_id_def, emit_def] >>
  pairarg_tac >> simp[] >> eq_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `(\(_0,cs'). _) _ = _` mp_tac >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  goal_assum (drule_at Any) >> simp[]
QED


Theorem append_memory_robust_array[local]:
  (!mem. mem_agree_outside old_taint old_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) off mem) /\
  (!j. j < LENGTH vs ==> val_wf tv (EL j vs)) /\
  mem_word_at off new_memory = n2w (LENGTH vs + 1) /\
  DISJOINT {i | off <= i /\ i < off + 32} new_taint /\
  (!mem. mem_agree_outside new_taint new_memory mem ==>
    val_in_memory tv v (off + 32 + LENGTH vs * type_memory_size tv) mem) /\
  (!i. ~(off <= i /\ i < off + 32) /\
       ~(off + 32 + LENGTH vs * type_memory_size tv <= i /\
         i < off + 32 + (LENGTH vs + 1) * type_memory_size tv) ==>
    mem_bytes_at i 1 new_memory = mem_bytes_at i 1 old_memory /\
    (i IN new_taint <=> i IN old_taint)) ==>
  !mem. mem_agree_outside new_taint new_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap))
      (ArrayV (DynArrayV (vs ++ [v]))) off mem
Proof
  strip_tac >> match_mp_tac normalizationPrefixPtrTheory.robust_dynarray_clean_count_assemble >>
  simp[LENGTH_APPEND] >> qx_gen_tac `j` >> strip_tac >>
  Cases_on `j = LENGTH vs`
  >- (qpat_x_assum `j = LENGTH vs` SUBST_ALL_TAC >>
      simp_tac (srw_ss()) [EL_APPEND_EQN] >>
      qpat_assum `!mem. mem_agree_outside new_taint new_memory mem ==> _` mp_tac >>
      simp_tac (srw_ss()) [arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]) >>
  `j < LENGTH vs` by decide_tac >>
  `val_wf tv (EL j vs)` by metis_tac[] >>
  `val_footprint tv (EL j vs) <= type_memory_size tv` by
    metis_tac[exprSimPropsTheory.val_footprint_le] >>
  `(j+1) * type_memory_size tv <= LENGTH vs * type_memory_size tv` by simp[] >>
  `!mem. mem_agree_outside old_taint old_memory mem ==>
    val_in_memory tv (EL j vs) (off+32+j*type_memory_size tv) mem` by
    (rpt strip_tac >>
     `val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) off mem` by
       metis_tac[] >>
     `elems_in_memory vs (off+32) tv mem` by
       (qpat_assum `val_in_memory (ArrayTV _ _) _ _ _`
          (strip_assume_tac o PURE_ONCE_REWRITE_RULE [val_in_memory_def]) >>
        fs[]) >>
     drule_all exprSimAggregateEncodingTheory.elems_in_memory_EL >> simp[]) >>
  simp[EL_APPEND_EQN] >>
  match_mp_tac robust_val_in_memory_exterior_frame >>
  qexistsl_tac [`old_taint`, `old_memory`,
    `{i | off <= i /\ i < off+32} UNION
     {i | off+32+LENGTH vs*type_memory_size tv <= i /\
          i < off+32+(LENGTH vs+1)*type_memory_size tv}`] >>
  simp[]
  >- (qpat_assum `!mem. mem_agree_outside old_taint old_memory mem ==>
         val_in_memory tv (EL j vs) _ mem` mp_tac >>
      simp_tac (srw_ss()) [DECIDE ``off+32+n:num = off+(n+32)``]) >>
  rpt strip_tac >> first_assum irule >>
  qpat_assum `(j+1) * type_memory_size tv <= _` mp_tac >>
  simp[arithmeticTheory.RIGHT_ADD_DISTRIB] >> decide_tac
QED

Theorem append_memory_load_ready[local]:
  emit_op MLOAD [Var p] a = (lop,b) /\ fn_has_code a b func /\
  lookup_var p s = SOME bp /\ ptr_covers G tn p s 32 /\
  (!i. w2n bp <= i /\ i < w2n bp+32 ==> i NOTIN tn.t_mem) /\
  w2n bp+32 <= s.vs_alloca_next /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?x t Gf tf.
    lop = Var x /\ not_fresh_at b x /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    lookup_var x t = SOME (mload (w2n bp) s) /\
    op_taint tf lop = {} /\ op_prov Gf lop = NONE /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    typed_copy_state_frame a 0 0 s t /\ t.vs_memory = s.vs_memory /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\
    (!x. not_fresh_at a x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
  rename1 `lop = Var x` >>
  qabbrev_tac `u = update_var x (mload (w2n bp) s) s` >>
  `run_inst_seq (emitted_insts a b) s = OK u` by
    simp[Abbr `u`, run_inst_seq_def, venomStateTheory.eval_operand_def,
      venomExecSemanticsTheory.step_inst_base_opcode_eqs,
      venomExecSemanticsTheory.exec_read1_def, venomInstTheory.mk_inst_def] >>
  drule_all (Q.SPECL [`a`,`lop`,`b`,`p`,`s`,`u`,`bp`,`G`,`tn`,`ARB`,`ctx`,`PG`,`ARB`]
     decoderNavigationPtrTheory.emit_mload_clean_endpoint_ptr_origin_core_exact_frame) >>
  disch_then (qspecl_then [`ctx`,`PG`,`ARB`] (qx_choosel_then [`Gf`,`tf`] strip_assume_tac)) >>
  qexistsl_tac [`x`,`u with vs_inst_idx := LENGTH b.cs_current_insts`,`Gf`,`tf`] >>
  `a.cs_current_bb = b.cs_current_bb` by
    (drule exprLoweringPropsTheory.emit_op_same_blocks >> simp[exprLoweringPropsTheory.same_blocks_def]) >>
  `not_fresh_at b x` by metis_tac[typedMemoryCopyTheory.typed_copy_emit_op_fresh] >>
  `x = STRING #"%" (toString a.cs_next_var)` by
    (drule emitHelperPropsTheory.emitted_insts_emit_op >> simp[]) >>
  `!y. not_fresh_at a y ==> y <> x` by
    (simp[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  simp[typed_copy_state_frame_def, Abbr `u`, ptrDisciplineTheory.allocas_from_def,
    ptrDisciplineTheory.allocas_below_fmp_def, venomStateTheory.update_var_def,
    venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
    venomStateTheory.venom_state_component_equality] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem append_memory_test_ready[local]:
  emit_op LT [lop; Lit (n2w cap)] a = (valid,b) /\ fn_has_code a b func /\
  eval_operand lop s = SOME len /\ cap < dimword (:256) /\
  op_taint tn lop = {} /\ op_prov G lop = NONE /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?x t Gf tf.
    valid = Var x /\ not_fresh_at b x /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    eval_operand valid t = SOME (bool_to_word (w2n len < cap)) /\
    op_taint tf valid = {} /\ op_prov Gf valid = NONE /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    typed_copy_state_frame a 0 0 s t /\ t.vs_memory = s.vs_memory /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\
    (!x. not_fresh_at a x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  qabbrev_tac `w = bool_to_word (w2n len < cap)` >>
  `!out. step_inst_base (mk_inst a.cs_next_id LT [lop; Lit (n2w cap)] [out]) s =
    OK (update_var out w s)` by
    simp[Abbr `w`, venomExecSemanticsTheory.step_inst_base_opcode_eqs,
      venomInstTheory.mk_inst_def, venomExecSemanticsTheory.exec_pure2_def,
      venomStateTheory.eval_operand_def] >>
  `!D out. ptr_inst_ok D lo 0 ctx func G tn
    (mk_inst a.cs_next_id LT [lop; Lit (n2w cap)] [out]) s` by
    (rpt gen_tac >> irule ptrSafetyTransportTheory.ptr_inst_ok_lower_bound_transport >>
     conj_tac >- first_assum ACCEPT_TAC >> qexists_tac `0` >> simp[] >>
     irule bodyPtrBopScalarStepTheory.bop_scalar_ptr_inst_ok >>
     simp[ptrDisciplineTheory.op_prov_def, ptrDisciplineTheory.op_taint_def]) >>
  `!out. inst_mem_below_frontier (mk_inst a.cs_next_id LT [lop; Lit (n2w cap)] [out]) s /\
    inst_dload_in_section (mk_inst a.cs_next_id LT [lop; Lit (n2w cap)] [out]) s` by
    (simp[memSafeRunTheory.inst_dload_in_section_def, venomInstTheory.mk_inst_def] >>
     simp[GSYM venomInstTheory.mk_inst_def, instMemFrontierTheory.below_frontier_no_ranges,
       venomInstTheory.mk_inst_def]) >>
  `LT <> INVOKE /\ LT <> GAS /\ ~is_terminator LT` by
    simp[venomInstTheory.is_terminator_def] >>
  qabbrev_tac `x = STRING #"%" (toString a.cs_next_var)` >>
  `valid = Var x /\ not_fresh_at b x` by
    (drule emitHelperPropsTheory.emitted_insts_emit_op >>
     simp[Abbr `x`] >> metis_tac[typedMemoryCopyTheory.typed_copy_emit_op_fresh]) >>
  qabbrev_tac `u = update_var x w s` >>
  qabbrev_tac `ins = mk_inst a.cs_next_id LT [lop; Lit (n2w cap)] [x]` >>
  qabbrev_tac `t = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `Gf = step_prov PG G ins u` >>
  qabbrev_tac `tf = step_taint ins s u tn` >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf) /\
    eval_operand valid t = SOME w /\ typed_copy_state_frame a 0 0 s t /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts` by
    (gen_tac >> mp_tac (Q.INST [`a` |-> `a`, `b` |-> `b`, `opc` |-> `LT`,
      `args` |-> `[lop; Lit (n2w cap)]`, `op` |-> `valid`, `s` |-> `s`,
      `off` |-> `0`, `len` |-> `0`, `w` |-> `w`, `ctx` |-> `ctx`,
      `lo` |-> `lo`, `G` |-> `G`, `tn` |-> `tn`, `func` |-> `func`,
      `D` |-> `D`, `PG` |-> `PG`, `explicit` |-> `explicit`]
      typed_copy_origin_ptr_emit_op_path) >>
     simp[Abbr `t`, Abbr `Gf`, Abbr `tf`, Abbr `ins`, Abbr `u`] >> metis_tac[]) >>
  `!y. not_fresh_at a y ==> y <> x` by
    (simp[Abbr `x`, not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  qexistsl_tac [`x`,`t`,`Gf`,`tf`] >> simp[] >>
  mp_tac (Q.INST [`opc` |-> `LT`, `ops` |-> `[lop; Lit (n2w cap)]`,
      `tn` |-> `tn`, `G` |-> `G`, `PG` |-> `PG`, `u` |-> `u`, `s` |-> `s`,
      `tmp` |-> `x`, `id` |-> `a.cs_next_id`]
    bodyPtrBopScalarStepTheory.bop_scalar_ghost_frame) >>
  simp[Abbr `Gf`, Abbr `tf`, Abbr `ins`, Abbr `t`, Abbr `u`, ptrDisciplineTheory.op_prov_def, ptrDisciplineTheory.op_taint_def,
    ptrDisciplineTheory.allocas_from_def, ptrDisciplineTheory.allocas_below_fmp_def,
    venomStateTheory.update_var_def, venomStateTheory.lookup_var_def,
    finite_mapTheory.FLOOKUP_UPDATE, Abbr `w`] >> metis_tac[]
QED

Theorem append_memory_add_offset[local]:
  emit_op ADD [Var p;op] a = (dst,b) /\ fn_has_code a b func /\
  lookup_var p s = SOME bp /\ eval_operand op s = SOME (n2w delta) /\
  op_taint tn op = {} /\ ptr_covers G tn p s extent /\ delta + n <= extent /\
  w2n bp + delta < dimword (:256) /\ not_fresh_at a p /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?x t Gf tf.
    dst = Var x /\ not_fresh_at b x /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    lookup_var x t = SOME (n2w (w2n bp + delta)) /\ ptr_covers Gf tf x t n /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    typed_copy_state_frame a 0 0 s t /\ t.vs_memory = s.vs_memory /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\
    (!x. not_fresh_at a x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `eval_operand (Var p) s = SOME bp /\ op_taint tn (Var p) = {}` by
    (simp[venomStateTheory.eval_operand_def] >> fs[ptr_covers_def]) >>
  `!D. ?out t G' tn'.
    dst = Var out /\ not_fresh_at b out /\
    t = (update_var out (bp + n2w delta) s with vs_inst_idx := SUC s.vs_inst_idx) /\
    G' = step_prov PG G (mk_inst a.cs_next_id ADD [Var p;op] [out])
      (update_var out (bp + n2w delta) s) /\
    tn' = step_taint (mk_inst a.cs_next_id ADD [Var p;op] [out]) s
      (update_var out (bp + n2w delta) s) tn /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn') /\
    eval_operand dst t = SOME (bp + n2w delta) /\ t.vs_memory = s.vs_memory /\
    typed_copy_state_frame a 0 0 s t /\ ~t.vs_halted /\
    t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts` by
    (gen_tac >> mp_tac (Q.INST [`a` |-> `a`, `b` |-> `b`, `opc` |-> `ADD`,
      `left` |-> `Var p`, `right` |-> `op`, `op` |-> `dst`, `s` |-> `s`,
      `off` |-> `0`, `len` |-> `0`, `w` |-> `bp + n2w delta`, `ctx` |-> `ctx`,
      `x` |-> `bp`, `y` |-> `n2w delta`, `lo` |-> `lo`, `G` |-> `G`, `tn` |-> `tn`,
      `func` |-> `func`, `D` |-> `D`, `PG` |-> `PG`, `explicit` |-> `explicit`]
      typed_copy_origin_ptr_binop_path) >> simp[]) >>
  qpat_assum `!D. ?out t G' tn'. _` (qspec_then `ARB` strip_assume_tac) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')` by
    (gen_tac >> qpat_assum `!D. ?out t G' tn'. _` (qspec_then `D` strip_assume_tac) >> gvs[]) >>
  `out = STRING #"%" (toString a.cs_next_var)` by
    (drule emitHelperPropsTheory.emitted_insts_emit_op >> simp[]) >>
  `!y. not_fresh_at a y ==> y <> out` by
    (simp[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `ptr_covers G' tn' out t n` by
    (`p <> out` by metis_tac[] >>
     mp_tac (Q.SPECL [`PG`,`G`,`tn`,`s`,`p`,`op`,`out`,`a.cs_next_id`,`bp`,`delta`,`extent`,`n`]
       typed_copy_origin_ptr_offset_covers) >>
     simp[ptr_covers_def, venomStateTheory.lookup_var_def]) >>
  `bp + n2w delta = n2w (w2n bp + delta)` by
    simp[GSYM wordsTheory.word_add_n2w] >>
  qexistsl_tac [`out`,`t`,`G'`,`tn'`] >>
  gvs[venomStateTheory.eval_operand_def] >>
  simp[typed_copy_origin_ptr_binop_ghost_frame, ptrDisciplineTheory.allocas_from_def,
    ptrDisciplineTheory.allocas_below_fmp_def] >>
  rpt strip_tac >>
  `x <> STRING #"%" (toString a.cs_next_var)` by
    (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  simp[typed_copy_origin_ptr_binop_ghost_frame] >>
  gvs[venomStateTheory.update_var_def, venomStateTheory.lookup_var_def,
      finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem append_frame_inst_idx[local]:
  typed_copy_state_frame a off len s t ==>
  typed_copy_state_frame a off len s (t with vs_inst_idx := i)
Proof
  rw[typed_copy_state_frame_def, venomStateTheory.lookup_var_def] >>
  fs[venomStateTheory.venom_state_component_equality]
QED

Theorem append_memory_guard_path[local]:
  emit_op MLOAD [Var p] a = (lop,b) /\
  emit_op LT [lop; Lit (n2w cap)] b = (valid,c) /\
  emit_void ASSERT [valid] c = ((),d) /\ fn_has_code a d func /\
  lookup_var p s = SOME bp /\ ptr_covers G tn p s 32 /\
  (!i. w2n bp <= i /\ i < w2n bp+32 ==> i NOTIN tn.t_mem) /\
  w2n bp+32 <= s.vs_alloca_next /\ mload (w2n bp) s = n2w len /\
  len <= cap /\ cap < dimword (:256) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  if len < cap then
    ?x t Gf tf.
      lop = Var x /\ not_fresh_at d x /\ lookup_var x t = SOME (n2w len) /\
      op_taint tf lop = {} /\ op_prov Gf lop = NONE /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK t,Gf,tf)) /\
      allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      typed_copy_state_frame a 0 0 s t /\ t.vs_memory = s.vs_memory /\
      tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
      tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      ~t.vs_halted /\ t.vs_current_bb = d.cs_current_bb /\
      t.vs_inst_idx = LENGTH d.cs_current_insts /\
      (!x. not_fresh_at a x ==> not_fresh_at d x /\ lookup_var x t = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
  else
    ?r Gf tf. (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (Abort Revert_abort r,Gf,tf))
Proof
  strip_tac >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d` by
    metis_tac[typed_copy_emit_op_mono, exprLoweringPropsTheory.ci_mono_emit_void, pairTheory.SND] >>
  `cs_extends a b /\ cs_extends b c /\ cs_extends c d` by fs[ci_mono_def] >>
  `fn_has_code a b func /\ fn_has_code b c func /\ fn_has_code c d func` by
    metis_tac[fragExecTheory.fn_has_code_split, compileEnvTheory.cs_extends_trans] >>
  `!x. (not_fresh_at a x ==> not_fresh_at b x) /\
       (not_fresh_at b x ==> not_fresh_at c x) /\
       (not_fresh_at c x ==> not_fresh_at d x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono, ci_mono_def] >>
  drule_all append_memory_load_ready >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  rename1 `lop = Var x` >>
  rename1 `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t1,G1,tn1)` >>
  `eval_operand lop t1 = SOME (n2w len)` by simp[venomStateTheory.eval_operand_def] >>
  drule_all append_memory_test_ready >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  rename1 `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t1,G1,tn1) [] (OK t2,G2,tn2)` >>
  `eval_operand valid t2 = SOME (bool_to_word (len < cap))` by simp[] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t2,G2,tn2)` by
    metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans] >>
  Cases_on `len < cap` >> simp[]
  >- suspend "success" >> suspend "capacity"
QED

Resume append_memory_guard_path[success]:
  qpat_x_assum `lop = Var x` SUBST_ALL_TAC >>
  `run_inst_seq (emitted_insts c d) t2 = OK t2` by
    (irule appendStorageStageTransportPtrTheory.emit_append_assert_actual >> qexists_tac `valid` >> simp[]) >>
  qabbrev_tac `u = t2 with vs_inst_idx := LENGTH d.cs_current_insts` >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t2,G2,tn2) [] (OK u,G2,tn2)` by
    (gen_tac >>
     mp_tac (Q.INST [`sa` |-> `c`, `sb` |-> `d`, `op` |-> `valid`,
      `s` |-> `t2`, `t` |-> `t2`, `G` |-> `G2`, `tn` |-> `tn2`, `PG` |-> `PG`]
      decoderGuardClampCorePtrTheory.emit_assert_endpoint_ptr_origin_core) >>
     simp[] >> disch_then (mp_tac o Q.SPECL [`D`,`lo`,`explicit`,`ctx`,`func`] o CONJUNCT1) >>
     simp[Abbr `u`]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G2,tn2)` by
    metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans] >>
  `typed_copy_state_frame a 0 0 s t2` by
    metis_tac[typedMemoryCopyTheory.typed_copy_state_frame_mono, typed_copy_state_frame_trans] >>
  `typed_copy_state_frame a 0 0 s u` by
    (simp[Abbr `u`] >> irule append_frame_inst_idx >> simp[]) >>
  `d.cs_current_bb = c.cs_current_bb` by
    (drule exprLoweringPropsTheory.emit_void_same_blocks >> simp[exprLoweringPropsTheory.same_blocks_def]) >>
  qexistsl_tac [`u`, `G2`, `tn2`] >>
  simp[Abbr `u`, venomStateTheory.lookup_var_def, ptrDisciplineTheory.op_prov_def,
    ptrDisciplineTheory.allocas_from_def, ptrDisciplineTheory.allocas_below_fmp_def] >>
  fs[venomStateTheory.lookup_var_def, ptrDisciplineTheory.op_prov_def,
    ptrDisciplineTheory.allocas_from_def, ptrDisciplineTheory.allocas_below_fmp_def] >>
  metis_tac[]
QED

Resume append_memory_guard_path[capacity]:
  drule emitHelperPropsTheory.emitted_insts_emit_void >> strip_tac >>
  `d.cs_current_bb = c.cs_current_bb` by
    (drule exprLoweringPropsTheory.emit_void_same_blocks >> simp[exprLoweringPropsTheory.same_blocks_def]) >>
  mp_tac (Q.SPECL [`c`,`d`,`func`,`[mk_inst c.cs_next_id ASSERT [valid] []]`]
    fragExecTheory.fn_has_code_same_block) >> simp[] >> strip_tac >>
  `get_instruction bb t2.vs_inst_idx = SOME (mk_inst c.cs_next_id ASSERT [valid] [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `eval_operand valid t2 = SOME 0w` by fs[venomExecSemanticsTheory.bool_to_word_def] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t2,G2,tn2) []
    (Abort Revert_abort (revert_state (set_returndata [] t2)),G2,tn2)` by
    (gen_tac >>
     mp_tac (Q.INST [`s` |-> `t2`,`fn` |-> `func`,`bb` |-> `bb`,
       `id` |-> `c.cs_next_id`,`op` |-> `valid`,`tn` |-> `tn2`,
       `lo` |-> `lo`,`ctx` |-> `ctx`,`G` |-> `G2`,`PG` |-> `PG`]
        entryChecksRejectJointTheory.assert_revert_origin_ptr) >> simp[]) >>
  qexistsl_tac [`revert_state (set_returndata [] t2)`,`G2`,`tn2`] >>
  gen_tac >> metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans]
QED

Finalise append_memory_guard_path[local]

Theorem append_memory_address_ready[local]:
  emit_op ADD [Var p; Lit 32w] a = (dop,b) /\
  emit_op MUL [lop; Lit (n2w stride)] b = (off,c) /\
  emit_op ADD [dop;off] c = (dst,d) /\ fn_has_code a d func /\
  not_fresh_at a p /\ (!x. lop = Var x ==> not_fresh_at a x) /\
  lookup_var p s = SOME bp /\ eval_operand lop s = SOME (n2w len) /\
  ptr_covers G tn p s (32+cap*stride) /\ op_taint tn lop = {} /\
  0 < stride /\ len < cap /\ w2n bp + (32+cap*stride) < dimword (:256) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?x t Gf tf.
    dst = Var x /\ not_fresh_at d x /\
    lookup_var x t = SOME (n2w (w2n bp+32+len*stride)) /\
    ptr_covers Gf tf x t stride /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    typed_copy_state_frame a 0 0 s t /\ t.vs_memory = s.vs_memory /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    ~t.vs_halted /\ t.vs_current_bb = d.cs_current_bb /\
    t.vs_inst_idx = LENGTH d.cs_current_insts /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at a x ==> not_fresh_at d x /\
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d` by metis_tac[typed_copy_emit_op_mono] >>
  `cs_extends a b /\ cs_extends b c /\ cs_extends c d` by fs[ci_mono_def] >>
  `fn_has_code a b func /\ fn_has_code b c func /\ fn_has_code c d func` by
    metis_tac[fragExecTheory.fn_has_code_split, compileEnvTheory.cs_extends_trans] >>
  `!x. (not_fresh_at a x ==> not_fresh_at b x) /\
       (not_fresh_at b x ==> not_fresh_at c x) /\
       (not_fresh_at c x ==> not_fresh_at d x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono, ci_mono_def] >>
  `eval_operand (Lit 32w) s = SOME (n2w 32) /\ op_taint tn (Lit 32w) = {} /\
   32 + cap*stride <= 32+cap*stride /\ w2n bp + 32 < dimword (:256)` by
    (simp[venomStateTheory.eval_operand_def,ptrDisciplineTheory.op_taint_def] >> decide_tac) >>
  mp_tac (Q.INST [`delta` |-> `32`, `n` |-> `cap*stride`, `extent` |-> `32+cap*stride`,
    `op` |-> `Lit 32w`, `dst` |-> `dop`, `a` |-> `a`, `b` |-> `b`,
    `s` |-> `s`, `bp` |-> `bp`, `p` |-> `p`, `G` |-> `G`, `tn` |-> `tn`,
    `func` |-> `func`, `ctx` |-> `ctx`, `lo` |-> `lo`, `PG` |-> `PG`,
    `explicit` |-> `explicit`] append_memory_add_offset) >>
  simp[] >> strip_tac >>
  rename1 `dop = Var vdata` >>
  qpat_x_assum `dop = Var vdata` SUBST_ALL_TAC >>
  rename1 `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK q1,G1,tn1)` >>
  `q1.vs_labels = s.vs_labels` by
    fs[typed_copy_state_frame_def, venomStateTheory.venom_state_component_equality] >>
  `eval_operand lop q1 = SOME (n2w len) /\ op_taint tn1 lop = {}` by
    (Cases_on `lop` >> fs[venomStateTheory.eval_operand_def,ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
  `eval_operand (Lit (n2w stride)) q1 = SOME (n2w stride) /\
    op_taint tn1 (Lit (n2w stride)) = {}` by simp[venomStateTheory.eval_operand_def,ptrDisciplineTheory.op_taint_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `MUL`, `w` |-> `x*y`]
    append_storage_address_binop_uniform)) >>
  disch_then (qspecl_then [`explicit`,`PG`,`G1`] strip_assume_tac) >>
  rename1 `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (q1,G1,tn1) [] (OK q2,G2,tn2)` >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp q2` by
    metis_tac[typedCopyOriginPtrBaseTheory.typed_copy_state_frame_allocas_below_fmp] >>
  `lookup_var vdata q2 = SOME (n2w (w2n bp+32)) /\
   ptr_covers G2 tn2 vdata q2 (cap*stride)` by
    metis_tac[assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame] >>
  `eval_operand off q2 = SOME (n2w (len*stride))` by fs[wordsTheory.word_mul_n2w] >>
  `len*stride + stride <= cap*stride` by
    (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
  `w2n bp+32 < dimword (:256)` by decide_tac >>
  `w2n ((n2w (w2n bp+32)):bytes32) + len*stride < dimword (:256)` by
    (simp[] >> decide_tac) >>
  `not_fresh_at c vdata` by metis_tac[] >>
  mp_tac (Q.INST [`delta` |-> `len*stride`, `n` |-> `stride`, `extent` |-> `cap*stride`,
    `op` |-> `off`, `dst` |-> `dst`, `a` |-> `c`, `b` |-> `d`,
    `s` |-> `q2`, `bp` |-> `(n2w (w2n bp+32)):bytes32`, `p` |-> `vdata`,
    `G` |-> `G2`, `tn` |-> `tn2`, `func` |-> `func`, `ctx` |-> `ctx`, `lo` |-> `lo`,
    `PG` |-> `PG`, `explicit` |-> `explicit`] append_memory_add_offset) >>
  simp[] >> strip_tac >>
  rename1 `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (q2,G2,tn2) [] (OK t,Gf,tf)` >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf)` by
    metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans] >>
  `typed_copy_state_frame a 0 0 s t` by
    (`ci_mono a c` by metis_tac[exprLoweringPropsTheory.ci_mono_trans] >>
     `typed_copy_state_frame a 0 0 q1 q2 /\ typed_copy_state_frame a 0 0 q2 t` by
       metis_tac[typedMemoryCopyTheory.typed_copy_state_frame_mono] >>
     metis_tac[typed_copy_state_frame_trans]) >>
  qexistsl_tac [`x`,`t`,`Gf`,`tf`] >> simp[] >> metis_tac[]
QED

Theorem append_memory_set_length[local]:
  emit_void MSTORE [Var p;op] a = ((),b) /\ fn_has_code a b func /\
  lookup_var p s = SOME bp /\ eval_operand op s = SOME w /\
  op_taint tn op = {} /\ ptr_covers G tn p s 32 /\
  w2n bp+32 <= s.vs_alloca_next /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G,tf)) /\
    mem_word_at (w2n bp) t.vs_memory = w /\
    typed_copy_state_frame a (w2n bp) 32 s t /\
    tf.t_mem = tn.t_mem DIFF {i | w2n bp <= i /\ i < w2n bp+32} /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    tf.t_imm = tn.t_imm /\ tf.t_var = tn.t_var /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts
Proof
  strip_tac >> drule emitHelperPropsTheory.emitted_insts_emit_void >> strip_tac >>
  `b.cs_current_bb = a.cs_current_bb` by
    (drule exprLoweringPropsTheory.emit_void_same_blocks >> simp[exprLoweringPropsTheory.same_blocks_def]) >>
  mp_tac (Q.SPECL [`a`,`b`,`func`,`[mk_inst a.cs_next_id MSTORE [Var p;op] []]`]
    fragExecTheory.fn_has_code_same_block) >> simp[] >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME (mk_inst a.cs_next_id MSTORE [Var p;op] [])` by simp[] >>
  `inst_mem_below_frontier (mk_inst a.cs_next_id MSTORE [Var p;op] []) s /\
    inst_dload_in_section (mk_inst a.cs_next_id MSTORE [Var p;op] []) s` by
    simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
      memSafeRunTheory.inst_dload_in_section_def, venomInstTheory.mk_inst_def,
      codegenRelTheory.source_memory_write_ranges_def,
      contextCodegenRelTheory.source_memory_read_ranges_def,
      codegenRelTheory.fixed_source_write_range_def, venomStateTheory.eval_operand_def] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (mstore (w2n bp) w s with vs_inst_idx := SUC s.vs_inst_idx),G,
     step_taint (mk_inst a.cs_next_id MSTORE [Var p;op] []) s (mstore (w2n bp) w s) tn)` by
    (gen_tac >> irule bodyFullAbiEncodeStoreTheory.abi_encode_mstore_origin_path >>
     goal_assum (drule_at Any) >> simp[]) >>
  qexistsl_tac [`mstore (w2n bp) w s with vs_inst_idx := SUC s.vs_inst_idx`,
    `step_taint (mk_inst a.cs_next_id MSTORE [Var p;op] []) s
      (mstore (w2n bp) w s) tn`] >>
  simp[typedMemoryCopyTheory.typed_copy_mstore_state_frame,
    valueEncodingPropsTheory.mstore_mem_word_at_same,
    bodyPtrBytestringBuiltinsUintGhostTheory.clean_mstore_taint_state] >>
  simp[venomStateTheory.mstore_def, venomStateTheory.write_memory_with_expansion_def]
QED

Theorem append_frame_unchanged_memory[local]:
  typed_copy_state_frame a 0 0 s t /\ t.vs_memory = s.vs_memory ==>
  typed_copy_state_frame a off len s t
Proof
  simp[typed_copy_state_frame_def]
QED

Theorem append_copy_frame_byte[local]:
  typed_copy_state_frame a off len s t /\ ~(off <= i /\ i < off+len) ==>
  mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory
Proof
  rw[typed_copy_state_frame_def,typed_copy_frame_def] >>
  first_x_assum irule >> decide_tac
QED

(* The word and aggregate stores expose the same bounded destination frame. *)
Theorem append_memory_store_element[local]:
  compile_store_memory cenv src (Var xd) elem elem sa = ((),sb) /\
  evaluate_type tenv elem = SOME tv /\ type_memory_bytes cenv elem = type_memory_size tv /\
  0 < type_memory_size tv /\ type_memory_size tv + 64 < dimword (:256) /\
  value_has_type tv v /\ val_wf tv v /\
  not_fresh_at sa xd /\ (!x. src = Var x ==> not_fresh_at sa x) /\
  lookup_var xd s = SOME dw /\ ptr_covers G tn xd s (type_memory_size tv) /\
  w2n dw + type_memory_size tv <= s.vs_alloca_next /\ s.vs_alloca_next < dimword (:256) /\
  (if is_word_type elem then
     eval_operand src s = SOME (typed_val_to_w256 tv v) /\ op_taint tn src = {}
   else ?xs sw. src = Var xs /\ lookup_var xs s = SOME sw /\
     ptr_covers G tn xs s (type_memory_size tv) /\
     w2n sw + val_store_size tv v <= s.vs_alloca_next /\
     !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v (w2n sw) mem) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf)) /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==> val_in_memory tv v (w2n dw) mem) /\
    typed_copy_state_frame sa (w2n dw) (type_memory_size tv) s t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!i. ~(w2n dw <= i /\ i < w2n dw+type_memory_size tv) ==>
      (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `is_word_type elem` >> fs[]
  >- suspend "word" >>
  `w2n dw + type_memory_size tv < dimword (:256) /\
    w2n sw + val_store_size tv v < dimword (:256)` by decide_tac >>
  qpat_x_assum `src = Var xs` SUBST_ALL_TAC >>
  `not_fresh_at sa xs` by metis_tac[] >>
  `w2n dw + type_memory_size tv <= s.vs_alloca_next` by decide_tac >>
  drule_all bodyFullMemorySameTypeStoreTheory.body_full_memory_same_type_store_path >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`t`,`Gf`,`tf`] >> simp[]
QED

Resume append_memory_store_element[word]:
  `type_memory_size tv = 32` by metis_tac[entryDecodeStaticPropsTheory.word_type_memory_size] >>
  `emit_void MSTORE [Var xd;src] sa = ((),sb)` by fs[contextTheory.compile_store_memory_def] >>
  `ptr_covers G tn xd s 32` by fs[] >>
  `w2n (dw:bytes32) + 32 <= s.vs_alloca_next` by decide_tac >>
  drule_all append_memory_set_length >>
  disch_then (qspecl_then [`explicit`,`PG`] (qx_choosel_then [`t`,`tf`] strip_assume_tac)) >>
  qexistsl_tac [`t`,`G`,`tf`] >> simp[] >> conj_tac
  >- (gen_tac >> strip_tac >>
      `mem_word_at (w2n (dw:bytes32)) t.vs_memory = mem_word_at (w2n (dw:bytes32)) mem` by
        (irule bodyPtrPrecompileBuiltinsArithmeticValueTheory.clean_word_mem_agree >>
         goal_assum (drule_at Any) >> simp[]) >>
      mp_tac (Q.SPECL [`tenv`,`elem`,`tv`,`v`,`w2n (dw:bytes32)`,`mem`]
        exprSimPropsTheory.val_in_memory_word) >> simp[] >> metis_tac[]) >>
  fs[typed_copy_state_frame_def,ptrDisciplineTheory.op_taint_def]
QED

Finalise append_memory_store_element[local]

Theorem append_memory_input_frame[local]:
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  t.vs_alloca_next = s.vs_alloca_next /\ t.vs_allocas = s.vs_allocas /\
  t.vs_labels = s.vs_labels /\
  tf.t_mem = tn.t_mem /\ t.vs_memory = s.vs_memory /\
  (if is_word_type elem then
     eval_operand src s = SOME (typed_val_to_w256 tv v) /\ op_taint tn src = {}
   else ?xs sw. src = Var xs /\ lookup_var xs s = SOME sw /\
     ptr_covers G tn xs s (type_memory_size tv) /\
     w2n sw + val_store_size tv v <= s.vs_alloca_next /\
     !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v (w2n sw) mem) ==>
  (if is_word_type elem then
     eval_operand src t = SOME (typed_val_to_w256 tv v) /\ op_taint tf src = {}
   else ?xs sw. src = Var xs /\ lookup_var xs t = SOME sw /\
     ptr_covers Gf tf xs t (type_memory_size tv) /\
     w2n sw + val_store_size tv v <= t.vs_alloca_next /\
     !mem. mem_agree_outside tf.t_mem t.vs_memory mem ==> val_in_memory tv v (w2n sw) mem)
Proof
  strip_tac >> Cases_on `is_word_type elem` >> fs[]
  >- (Cases_on `src` >>
      gvs[venomStateTheory.eval_operand_def,ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
  metis_tac[assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame]
QED

Theorem append_memory_copy_payload_path[local]:
  emit_op ADD [Var p; Lit 32w] a = (dop,a1) /\
  emit_op MUL [Var lenvar; Lit (n2w (type_memory_size tv))] a1 = (off,a2) /\
  emit_op ADD [dop;off] a2 = (dst,a3) /\
  compile_store_memory cenv src dst elem elem a3 = ((),a4) /\
  emit_op ADD [Var lenvar; Lit 1w] a4 = (next,a5) /\
  emit_void MSTORE [Var p; next] a5 = ((),b) /\ fn_has_code a b func /\
  not_fresh_at a p /\ (!x. src = Var x ==> not_fresh_at a x) /\ not_fresh_at a lenvar /\
  lookup_var p s = SOME bp /\
  lookup_var lenvar s = SOME (n2w (LENGTH vs)) /\ op_taint tn (Var lenvar) = {} /\
  evaluate_type tenv elem = SOME tv /\
  type_memory_bytes cenv elem = type_memory_size tv /\
  0 < type_memory_size tv /\ type_memory_size tv + 64 < dimword (:256) /\
  value_has_type tv v /\ val_wf tv v /\ (!j. j < LENGTH vs ==> val_wf tv (EL j vs)) /\
  LENGTH vs < cap /\ cap < dimword (:256) /\
  ptr_covers G tn p s (32+cap*type_memory_size tv) /\
  w2n bp+32+cap*type_memory_size tv <= s.vs_alloca_next /\
  s.vs_alloca_next < dimword (:256) /\
  (if is_word_type elem then
     eval_operand src s = SOME (typed_val_to_w256 tv v) /\ op_taint tn src = {}
   else ?xs sw. src = Var xs /\ lookup_var xs s = SOME sw /\
     ptr_covers G tn xs s (type_memory_size tv) /\
     w2n sw + val_store_size tv v <= s.vs_alloca_next /\
     !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v (w2n sw) mem) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n bp) mem) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
      val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV (vs ++ [v]))) (w2n bp) mem) /\
    typed_copy_state_frame a (w2n bp) (32+cap*type_memory_size tv) s t /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!i. ~(w2n bp <= i /\ i < w2n bp+32+cap*type_memory_size tv) ==>
      (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    (!x. not_fresh_at a x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts
Proof
  strip_tac >>
  `ci_mono a a1 /\ ci_mono a1 a2 /\ ci_mono a2 a3 /\ ci_mono a3 a4 /\
   ci_mono a4 a5 /\ ci_mono a5 b` by
    metis_tac[typed_copy_emit_op_mono, exprLoweringPropsTheory.ci_mono_emit_void,
      exprLoweringPropsTheory.ci_mono_compile_store_memory, pairTheory.SND] >>
  `ci_mono a a3 /\ ci_mono a a4 /\ ci_mono a a5 /\ ci_mono a b` by
    metis_tac[exprLoweringPropsTheory.ci_mono_trans] >>
  `cs_extends a a3 /\ cs_extends a3 a4 /\ cs_extends a4 a5 /\ cs_extends a5 b` by fs[ci_mono_def] >>
  `fn_has_code a a3 func /\ fn_has_code a3 a4 func /\ fn_has_code a4 a5 func /\
   fn_has_code a5 b func` by
    metis_tac[fragExecTheory.fn_has_code_split, compileEnvTheory.cs_extends_trans] >>
  `!x. (not_fresh_at a3 x ==> not_fresh_at a4 x) /\
       (not_fresh_at a4 x ==> not_fresh_at a5 x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono, ci_mono_def] >>
  qabbrev_tac `arrsize = 32+cap*type_memory_size tv` >>
  qabbrev_tac `elemaddr = w2n bp+32+LENGTH vs*type_memory_size tv` >>
  `LENGTH vs * type_memory_size tv + type_memory_size tv <= cap * type_memory_size tv` by
    (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
  `w2n bp + arrsize < dimword (:256) /\
   elemaddr + type_memory_size tv <= s.vs_alloca_next /\ elemaddr < dimword (:256)` by
    (fs[Abbr `arrsize`, Abbr `elemaddr`] >> decide_tac) >>
  `eval_operand (Var lenvar) s = SOME (n2w (LENGTH vs))` by simp[venomStateTheory.eval_operand_def] >>
  mp_tac (Q.INST [`a` |-> `a`,`b` |-> `a1`,`c` |-> `a2`,`d` |-> `a3`,
    `lop` |-> `Var lenvar`,`stride` |-> `type_memory_size tv`,`len` |-> `LENGTH (vs : value list)`,
    `s` |-> `s`,`bp` |-> `bp`,`p` |-> `p`,`G` |-> `G`,`tn` |-> `tn`,
    `func` |-> `func`,`ctx` |-> `ctx`,`PG` |-> `PG`,`lo` |-> `lo`,
    `explicit` |-> `explicit`] append_memory_address_ready) >>
  (impl_tac >- simp[Abbr `arrsize`]) >>
  disch_then (qx_choosel_then [`xd`,`q1`,`G1`,`tn1`] strip_assume_tac) >>
  suspend "copy"
QED

Resume append_memory_copy_payload_path[copy]:
  qpat_x_assum `dst = Var xd` SUBST_ALL_TAC >>
  `q1.vs_allocas = s.vs_allocas /\ q1.vs_alloca_next = s.vs_alloca_next /\
    q1.vs_labels = s.vs_labels` by
    fs[typed_copy_state_frame_def, venomStateTheory.venom_state_component_equality] >>
  `(if is_word_type elem then
     eval_operand src q1 = SOME (typed_val_to_w256 tv v) /\ op_taint tn1 src = {}
   else ?xs sw. src = Var xs /\ lookup_var xs q1 = SOME sw /\
     ptr_covers G1 tn1 xs q1 (type_memory_size tv) /\
     w2n sw + val_store_size tv v <= q1.vs_alloca_next /\
     !mem. mem_agree_outside tn1.t_mem q1.vs_memory mem ==> val_in_memory tv v (w2n sw) mem)` by
    (mp_tac (Q.INST [`sa` |-> `a`, `s` |-> `s`, `t` |-> `q1`,
       `G` |-> `G`, `Gf` |-> `G1`, `tn` |-> `tn`, `tf` |-> `tn1`,
       `src` |-> `src`, `elem` |-> `elem`, `tv` |-> `tv`, `v` |-> `v`]
       append_memory_input_frame) >> simp[]) >>
  mp_tac (Q.INST [`s` |-> `q1`, `sa` |-> `a3`, `sb` |-> `a4`, `G` |-> `G1`,
    `tn` |-> `tn1`, `dw` |-> `(n2w elemaddr):bytes32`, `elem` |-> `elem`,
    `src` |-> `src`, `tv` |-> `tv`, `tenv` |-> `tenv`, `xd` |-> `xd`,
    `ctx` |-> `ctx`, `func` |-> `func`, `lo` |-> `lo`, `explicit` |-> `explicit`,
    `PG` |-> `PG`, `cenv` |-> `cenv`, `v` |-> `v`]
    append_memory_store_element) >>
  (impl_tac >- (simp[Abbr `elemaddr`] >> rpt strip_tac >> res_tac >> decide_tac)) >>
  disch_then (qx_choosel_then [`q2`,`G2`,`tn2`] strip_assume_tac) >>
  `q2.vs_alloca_next = s.vs_alloca_next /\ allocas_from lo q2 /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp q2)` by
    (fs[typed_copy_state_frame_def, venomStateTheory.venom_state_component_equality,
        ptrDisciplineTheory.allocas_from_def, ptrDisciplineTheory.allocas_below_fmp_def] >>
     metis_tac[]) >>
  `eval_operand (Var lenvar) q2 = SOME (n2w (LENGTH vs)) /\ op_taint tn2 (Var lenvar) = {}` by
    (simp[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  `eval_operand (Lit 1w) q2 = SOME 1w /\ op_taint tn2 (Lit 1w) = {}` by
    simp[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_taint_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`, `w` |-> `x+y`]
    append_storage_address_binop_uniform)) >>
  disch_then (qspecl_then [`explicit`,`PG`,`G2`] strip_assume_tac) >>
  rename1 `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (q2,G2,tn2) [] (OK q3,G3,tn3)` >>
  suspend "store"
QED

Resume append_memory_copy_payload_path[store]:
  `ctx_has_dalloca ctx ==> allocas_below_fmp q3` by
    metis_tac[typedCopyOriginPtrBaseTheory.typed_copy_state_frame_allocas_below_fmp] >>
  `lookup_var p q3 = SOME bp /\ ptr_covers G3 tn3 p q3 arrsize` by
    metis_tac[assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame] >>
  `ptr_covers G3 tn3 p q3 32` by
    (fs[ptr_covers_def, Abbr `arrsize`] >> rpt strip_tac >> res_tac >> decide_tac) >>
  `q3.vs_alloca_next = s.vs_alloca_next` by
    fs[typed_copy_state_frame_def, venomStateTheory.venom_state_component_equality] >>
  `w2n bp+32 <= q3.vs_alloca_next` by decide_tac >>
  `eval_operand next q3 = SOME (n2w (LENGTH vs+1))` by
    fs[GSYM wordsTheory.word_add_n2w] >>
  drule_all append_memory_set_length >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  rename1 `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (q3,G3,tn3) [] (OK t,G3,tf)` >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G3,tf)` by
    metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans] >>
  `typed_copy_state_frame a (w2n bp) arrsize s t` by suspend "memory_frame" >>
  `!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV (vs ++ [v]))) (w2n bp) mem`
    by suspend "robust_array" >>
  qexistsl_tac [`t`,`G3`,`tf`] >> simp[GSYM markerTheory.Abbrev_def] >>
  conj_tac >- suspend "exterior_taint" >>
  rpt strip_tac >> fs[typed_copy_state_frame_def, ptrDisciplineTheory.op_taint_def] >> metis_tac[]
QED

Resume append_memory_copy_payload_path[memory_frame]:
  `w2n ((n2w elemaddr):bytes32) = elemaddr` by simp[] >>
  `w2n bp <= elemaddr /\ elemaddr + type_memory_size tv <= w2n bp + arrsize /\
    w2n bp + 32 <= w2n bp + arrsize` by
    (fs[Abbr `elemaddr`, Abbr `arrsize`] >> decide_tac) >>
  `typed_copy_state_frame a (w2n bp) arrsize s q1` by
    metis_tac[append_frame_unchanged_memory] >>
  `typed_copy_state_frame a (w2n bp) arrsize q1 q2` by
    metis_tac[typed_copy_state_frame_subinterval, typed_copy_state_frame_mono] >>
  `typed_copy_state_frame a (w2n bp) arrsize q2 q3` by
    metis_tac[append_frame_unchanged_memory, typed_copy_state_frame_mono] >>
  `typed_copy_state_frame a (w2n bp) 32 q3 t` by
    (match_mp_tac (Q.INST [`sb` |-> `a5`] typed_copy_state_frame_mono) >>
     simp[]) >>
  `typed_copy_state_frame a (w2n bp) arrsize q3 t` by
    (match_mp_tac (Q.INST [`child` |-> `w2n (bp:bytes32)`, `clen` |-> `32`]
       typed_copy_state_frame_subinterval) >> simp[Abbr `arrsize`] >> decide_tac) >>
  metis_tac[typed_copy_state_frame_trans]
QED

Resume append_memory_copy_payload_path[robust_array]:
  `w2n ((n2w elemaddr):bytes32) = elemaddr` by simp[] >>
  `!i. ~(w2n bp <= i /\ i < w2n bp+32) ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 q3.vs_memory` by
    metis_tac[append_copy_frame_byte] >>
  `!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==> val_in_memory tv v elemaddr mem` by
    (match_mp_tac robust_val_in_memory_exterior_frame >>
     qexistsl_tac [`tn3.t_mem`,`q3.vs_memory`,`{i | w2n bp <= i /\ i < w2n bp+32}`] >>
     simp[] >> rpt strip_tac >> fs[Abbr `elemaddr`] >> decide_tac) >>
  `!i. ~(elemaddr <= i /\ i < elemaddr+type_memory_size tv) ==>
    mem_bytes_at i 1 q2.vs_memory = mem_bytes_at i 1 q1.vs_memory` by
    metis_tac[append_copy_frame_byte] >>
  `DISJOINT {i | w2n bp <= i /\ i < w2n bp+32} tf.t_mem` by
    (simp[pred_setTheory.DISJOINT_DEF,pred_setTheory.EXTENSION] >> metis_tac[]) >>
  mp_tac (Q.INST [`off` |-> `w2n (bp:bytes32)`, `old_taint` |-> `tn.t_mem`,
    `old_memory` |-> `s.vs_memory`, `new_taint` |-> `tf.t_mem`,
    `new_memory` |-> `t.vs_memory`] append_memory_robust_array) >>
  impl_tac >-
   (simp[Abbr `elemaddr`] >> qx_gen_tac `i` >> strip_tac >>
    `~(w2n bp+32+LENGTH vs*type_memory_size tv <= i /\
       i < w2n bp+32+LENGTH vs*type_memory_size tv+type_memory_size tv)` by
      (fs[arithmeticTheory.LEFT_ADD_DISTRIB] >> decide_tac) >>
    metis_tac[pred_setTheory.IN_DIFF, pred_setTheory.GSPECIFICATION]) >>
  simp[]
QED

Resume append_memory_copy_payload_path[exterior_taint]:
  rpt strip_tac >> fs[Abbr `arrsize`, Abbr `elemaddr`] >> res_tac >> decide_tac
QED

Finalise append_memory_copy_payload_path[local]

Theorem append_nested_memory_cont_full[local]:
  compile_dynarray_append cenv (Var p) src 32 (type_memory_size tv)
    elem elem cap F LocMemory sa = ((),sb) /\
  body_inv (cx_tops cx) ctx cenv cx /\ expr_sim_inv cenv cx env mid /\
  gas_admissible (append_place cx (MemoryPlace id path) v) (stmt_res_ok lctx) mid /\
  lookup_scopes id mid.scopes = SOME entry /\
  subscripts_type entry.type path = SOME (ArrayTV tv (Dynamic cap)) /\
  read_memory_path entry path = INL (ArrayV (DynArrayV vs)) /\
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) bp (SOME LocMemory)
    (Type (ArrayT elem (Dynamic cap))) /\
  (!t0. cenv.ce_var_type id = SOME t0 ==> evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  evaluate_type (get_tenv cx) elem = SOME tv /\
  type_memory_bytes cenv elem = type_memory_size tv /\
  type_memory_size tv + 64 < dimword (:256) /\ 0 < type_memory_size tv /\
  cap < dimword (:256) /\ value_has_type tv v /\ val_wf tv v /\
  lookup_var p s = SOME bp /\
  not_fresh_at sa p /\ (!x. src = Var x ==> not_fresh_at sa x) /\
  ptr_covers G tn p s (32+cap*type_memory_size tv) /\
  w2n bp+32+cap*type_memory_size tv <= s.vs_alloca_next /\ lo <= w2n bp /\
  (if is_word_type elem then
     eval_operand src s = SOME (typed_val_to_w256 tv v) /\ op_taint tn src = {}
   else ?xs sw. src = Var xs /\ lookup_var xs s = SOME sw /\
     ptr_covers G tn xs s (type_memory_size tv) /\
     w2n sw + val_store_size tv v <= s.vs_alloca_next /\
     !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v (w2n sw) mem) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n bp) mem) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid s /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx mid G tn s) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (append_place cx (MemoryPlace id path) v) (mid,s,G,tn)
    (\H res ee Gf tf u. ?cenv''.
      stmt_lands lctx sb res u /\ ~u.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv) /\
      cenv_top_ext cenv cenv'' ee.scopes /\ stmt_state_rel H ctx func cenv'' cx ee u /\
      storage_well_formed_on cx ee (FST H) /\ return_buf_frame d cenv'' sb u /\
      alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
      s.vs_alloca_next <= u.vs_alloca_next /\ ghost_inv_at (DF H) lo d cenv'' cx ee Gf tf u /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
      alloca_frame cenv mid sa s cenv'' ee u /\
      (!aid off sz i. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
        aid < sa.cs_next_id /\ off <= i /\ i < off+sz /\
        (!name a len. local_region cenv mid.scopes s name a len ==>
          off+sz <= a \/ a+len <= off) /\ i IN tf.t_mem ==> i IN tn.t_mem))
    (\H res ee gt r. (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
      halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==>
        allocas_below_fmp s))
Proof
  strip_tac >>
  qabbrev_tac `H0 = storage_trace_horizon mid.storage_trace` >>
  `valid_horizon cx st0 H0 mid.storage_trace` by
    fs[Abbr `H0`, vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `H0` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    metis_tac[bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp] >>
  `s.vs_alloca_next < dimword (:256)` by
    metis_tac[stateRelProjTheory.stmt_state_rel_alloca_room,
      exprLoweringPropsTheory.alloca_room_next_lt] >>
  `LENGTH vs <= cap /\ (!j. j < LENGTH vs ==> val_wf tv (EL j vs))` by
    (fs[vyperTypingTheory.value_has_type_def, vyperTypingTheory.all_have_type_EVERY,
        listTheory.EVERY_EL] >> metis_tac[valueEncodingTypingTheory.value_has_type_val_wf]) >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==> mem_word_at (w2n bp) m = n2w (LENGTH vs)` by
    (rpt strip_tac >>
     `val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n bp) m` by
       metis_tac[] >>
     qpat_x_assum `val_in_memory _ _ _ m`
       (mp_tac o PURE_ONCE_REWRITE_RULE [val_in_memory_def]) >> simp[]) >>
  `(!i. w2n bp <= i /\ i < w2n bp+32 ==> i NOTIN tn.t_mem) /\
    mem_word_at (w2n bp) s.vs_memory = n2w (LENGTH vs)` by
    metis_tac[representationCleanPtrTheory.robust_mem_word_at_clean,
      mem_agree_outside_def] >>
  `mload (w2n bp) s = n2w (LENGTH vs)` by
    fs[valueEncodingPropsTheory.mem_word_at_eq_mload] >>
  `ptr_covers G tn p s 32 /\ w2n bp+32 <= s.vs_alloca_next` by
    (fs[ptr_covers_def] >> rpt strip_tac >> res_tac >> decide_tac) >>
  qpat_assum `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ = _`
    (strip_assume_tac o REWRITE_RULE [append_memory_copy_suffix_parts]) >>
  rename1 `emit_op MLOAD [Var p] sa = (lop,a1)` >>
  rename1 `emit_op LT [lop; Lit (n2w cap)] a1 = (valid,a2)` >>
  rename1 `emit_void ASSERT [valid] a2 = ((),a3)` >>
  `ci_mono sa a3 /\ ci_mono a3 sb` by suspend "code" >>
  `fn_has_code sa a3 func /\ fn_has_code a3 sb func` by
    metis_tac[fragExecTheory.fn_has_code_split, ci_mono_def] >>
  drule_all append_memory_guard_path >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`] mp_tac) >>
  Cases_on `LENGTH vs < cap` >> simp[] >> strip_tac
  >- suspend "success" >> suspend "capacity"
QED

Resume append_nested_memory_cont_full[code]:
  drule_then assume_tac typed_copy_emit_op_mono >>
  `ci_mono sa a1 /\ ci_mono a1 a2 /\ ci_mono a3 a4 /\ ci_mono a4 a5 /\
   ci_mono a5 a6 /\ ci_mono a7 a8` by metis_tac[typed_copy_emit_op_mono] >>
  `ci_mono a2 a3 /\ ci_mono a8 sb` by
    metis_tac[exprLoweringPropsTheory.ci_mono_emit_void, pairTheory.SND] >>
  `ci_mono a6 a7` by
    metis_tac[exprLoweringPropsTheory.ci_mono_compile_store_memory, pairTheory.SND] >>
  conj_tac
  >- (irule exprLoweringPropsTheory.ci_mono_trans >> qexists_tac `a2` >>
      simp[] >> metis_tac[exprLoweringPropsTheory.ci_mono_trans]) >>
  `ci_mono a3 a6 /\ ci_mono a6 sb` by metis_tac[exprLoweringPropsTheory.ci_mono_trans] >>
  metis_tac[exprLoweringPropsTheory.ci_mono_trans]
QED

Resume append_nested_memory_cont_full[capacity]:
  `!tail. append_place cx (MemoryPlace id path) v (mid with gas_obs := tail) =
    (INR (Error (RuntimeError "append overflow")),mid with gas_obs := tail)` by
    (simp[append_place_def, place_type_value_def, read_place_def,
       vyperValueOperationTheory.append_element_def, vyperValueTheory.compatible_bound_def,
       get_scopes_def, lift_option_type_def, lift_option_def, bind_def, return_def,
       raise_def, lift_sum_def] >> decide_tac) >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_exit >>
  conj_tac
  >- (qexistsl_tac [`Gf`,`mid`,`Abort Revert_abort r`,
      `INR (Error (RuntimeError "append overflow"))`,`tf`] >>
      simp[fragExecTheory.exit_result_def, bodyPtrDefsTheory.stmt_exit_ptr_def,
           exprSimDefsTheory.expr_exit_def, exprSimDefsTheory.halt_exit_def]) >>
  simp[]
QED

Resume append_nested_memory_cont_full[success]:
  rename1 `!D. gas_origin_ptr_path
    (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (s,G,tn) [] (OK guarded,Gg,tg)` >>
  qpat_x_assum `lop = Var x` SUBST_ALL_TAC >>
  `guarded.vs_alloca_next = s.vs_alloca_next /\ guarded.vs_allocas = s.vs_allocas /\
    guarded.vs_labels = s.vs_labels` by
    fs[typed_copy_state_frame_def, venomStateTheory.venom_state_component_equality] >>
  `lo <= guarded.vs_alloca_next /\ guarded.vs_alloca_next < dimword (:256) /\
   w2n bp+32+cap*type_memory_size tv <= guarded.vs_alloca_next` by simp[] >>
  `not_fresh_at a3 p /\ (!x. src = Var x ==> not_fresh_at a3 x)` by metis_tac[] >>
  `lookup_var p guarded = SOME bp /\ ptr_covers Gg tg p guarded (32+cap*type_memory_size tv)` by
    metis_tac[assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame] >>
  `!mem. mem_agree_outside tg.t_mem guarded.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n bp) mem` by metis_tac[] >>
  `(if is_word_type elem then
     eval_operand src guarded = SOME (typed_val_to_w256 tv v) /\ op_taint tg src = {}
   else ?xs sw. src = Var xs /\ lookup_var xs guarded = SOME sw /\
     ptr_covers Gg tg xs guarded (type_memory_size tv) /\
     w2n sw + val_store_size tv v <= guarded.vs_alloca_next /\
     !mem. mem_agree_outside tg.t_mem guarded.vs_memory mem ==> val_in_memory tv v (w2n sw) mem)` by
    (mp_tac (Q.INST [`sa` |-> `sa`, `s` |-> `s`, `t` |-> `guarded`,
       `G` |-> `G`, `Gf` |-> `Gg`, `tn` |-> `tn`, `tf` |-> `tg`,
       `src` |-> `src`, `elem` |-> `elem`, `tv` |-> `tv`, `v` |-> `v`]
       append_memory_input_frame) >> simp[]) >>
  drule_all append_memory_copy_payload_path >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`] strip_assume_tac) >>
  rename1 `!D. gas_origin_ptr_path
    (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (guarded,Gg,tg) [] (OK t,Gf,tf)` >>
  `!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (s,G,tn) [] (OK t,Gf,tf)` by
    metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans] >>
  `typed_copy_state_frame sa (w2n bp) (32+cap*type_memory_size tv) s t` by
    (`typed_copy_state_frame sa (w2n bp) (32+cap*type_memory_size tv) s guarded /\
      typed_copy_state_frame sa (w2n bp) (32+cap*type_memory_size tv) guarded t` by
       metis_tac[append_frame_unchanged_memory, typedMemoryCopyTheory.typed_copy_state_frame_mono] >> metis_tac[typedMemoryCopyTheory.typed_copy_state_frame_trans]) >>
  suspend "source_and_post"
QED

Resume append_nested_memory_cont_full[source_and_post]:
  `?pre sc rest. find_containing_scope id mid.scopes = SOME (pre,sc,entry,rest)` by
    metis_tac[vyperLookupTheory.lookup_scopes_find_containing_scope] >>
  `entry.assignable` by
    (CCONTR_TAC >>
     `append_place cx (MemoryPlace id path) v (mid with gas_obs := []) =
       (INR (Error (TypeError "write_place not assignable")),mid with gas_obs := [])` by
       simp[append_place_def, read_place_def, place_type_value_def,
         vyperValueOperationTheory.append_element_def, vyperValueTheory.compatible_bound_def,
         vyperTypingTheory.safe_cast_well_typed, write_place_def, bind_def, ignore_bind_def, get_scopes_def,
         lift_option_type_def, lift_option_def, type_check_def, assert_def, lift_sum_def,
         return_def, raise_def] >>
     drule_all gasContextTheory.gas_admissible_result >> simp[stmtSimDefsTheory.stmt_res_ok_def]) >>
  qabbrev_tac `arr = ArrayV (DynArrayV (vs ++ [v]))` >>
  `?entry'. replace_memory_entry entry path arr = INL entry'` by suspend "replace" >>
  qabbrev_tac `ff = mid with scopes := pre ++ (sc |+ (id,entry'))::rest` >>
  `write_place cx (MemoryPlace id path) arr mid = (INL (),ff)` by
    simp[write_place_def, bind_def, ignore_bind_def, get_scopes_def, lift_option_type_def, lift_option_def,
         type_check_def, assert_def, lift_sum_def, return_def, set_scopes_def, Abbr `ff`] >>
  `!tail. append_place cx (MemoryPlace id path) v (mid with gas_obs := tail) =
    (INL (),ff with gas_obs := tail)` by
    simp[append_place_def, read_place_def, place_type_value_def,
      vyperValueOperationTheory.append_element_def, vyperValueTheory.compatible_bound_def,
      vyperTypingTheory.safe_cast_well_typed, SNOC_APPEND, write_place_def, bind_def, ignore_bind_def,
      get_scopes_def, lift_option_type_def, lift_option_def, type_check_def, assert_def,
      lift_sum_def, return_def, set_scopes_def, Abbr `ff`, GSYM markerTheory.Abbrev_def] >>
  `typed_copy_effect ctx func sa sb s t (w2n bp) (type_memory_size (ArrayTV tv (Dynamic cap)))`
    by suspend "effect" >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`Gf`,`ff`,`INL ()`,`t`,`tf`] >> simp[] >> suspend "post"
QED

Resume append_nested_memory_cont_full[replace]:
  Cases_on `evaluate_subscripts entry.type entry.value path` >> simp[replace_memory_entry_def] >>
  rename1 `evaluate_subscripts _ _ _ = INL old` >>
  `value_has_type entry.type entry.value` by
    (irule vyperTypeStatePreservationTheory.lookup_scopes_state_well_typed_value_has_type >>
     qexistsl_tac [`id`,`mid`] >> fs[expr_sim_inv_def]) >>
  `value_has_type (ArrayTV tv (Dynamic cap)) arr` by
    fs[Abbr `arr`, vyperTypingTheory.value_has_type_def,
      vyperTypingTheory.all_have_type_EVERY, EVERY_APPEND] >>
  Cases_on `assign_subscripts entry.type entry.value path (Replace arr)` >> simp[] >>
  drule_all stmtSimAugAssignPlaceMemoryTheory.aug_place_replace_read_error >> strip_tac >> gvs[] >>
  `?pre sc rest. find_containing_scope id mid.scopes = SOME (pre,sc,entry,rest)` by
    metis_tac[vyperLookupTheory.lookup_scopes_find_containing_scope] >>
  `append_place cx (MemoryPlace id path) v (mid with gas_obs := []) =
     (INR (Error (TypeError msg)),mid with gas_obs := [])` by
    simp[append_place_def, read_place_def, place_type_value_def,
      vyperValueOperationTheory.append_element_def, vyperValueTheory.compatible_bound_def,
      vyperTypingTheory.safe_cast_well_typed, SNOC_APPEND, write_place_def, bind_def, ignore_bind_def,
      get_scopes_def, lift_option_type_def, lift_option_def, type_check_def, assert_def,
      lift_sum_def, return_def, raise_def, replace_memory_entry_def, GSYM markerTheory.Abbrev_def] >>
  drule_all gasContextTheory.gas_admissible_result >> simp[stmtSimDefsTheory.stmt_res_ok_def]
QED

Resume append_nested_memory_cont_full[effect]:
  `gas_marked_path F ctx func s 0 (OK t)` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK t,Gf,tf)`
        (qspec_then `DF H0` mp_tac) >>
     disch_then (mp_tac o MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_projections) >>
     strip_tac >> drule fragGasOriginTheory.gas_origin_path_erase >>
     simp[fragGasModeTheory.gas_marked_path_def] >>
     metis_tac[fragGasPathMemTheory.gas_path_mem_exec]) >>
  fs[placeMemoryCopyEffectTheory.typed_copy_effect_def, typed_copy_state_frame_def,
    typedMemoryCopyTheory.typed_copy_frame_def, valueEncodingTheory.type_memory_size_def,
    venomStateTheory.venom_state_component_equality] >> metis_tac[]
QED

Resume append_nested_memory_cont_full[post]:
  gen_tac >> strip_tac >>
  `evaluate_type (get_tenv cx) (ArrayT elem (Dynamic cap)) = SOME (ArrayTV tv (Dynamic cap))` by
    (qpat_assum `place_ptr_rel _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.place_ptr_rel_def]) >>
     drule_then strip_assume_tac exprSimPropsTheory.mem_path_offset_sound >>
     qpat_assum `!t0. cenv.ce_var_type id = SOME t0 ==> _`
       (qspec_then `t0` mp_tac) >> simp[] >> strip_tac >> gvs[]) >>
  `value_has_type (ArrayTV tv (Dynamic cap)) arr` by
    fs[Abbr `arr`, vyperTypingTheory.value_has_type_def,
      vyperTypingTheory.all_have_type_EVERY, EVERY_APPEND] >>
  `valid_horizon cx st0 H mid.storage_trace` by fs[Abbr `ff`] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by
    metis_tac[] >>
  mp_tac (Q.INST [`p` |-> `MemoryPlace id path`, `dw` |-> `bp`,
    `ee` |-> `mid`, `v` |-> `arr`, `D` |-> `DF H`,
    `dty` |-> `ArrayT elem (Dynamic cap)`, `dtv` |-> `ArrayTV tv (Dynamic cap)`]
    (INST_TYPE [alpha |-> ``:256``]
      memoryPlaceStorePostTheory.body_assign_memory_place_store_post)) >>
  (impl_tac >- (simp[valueEncodingTheory.type_memory_size_def,
     GSYM markerTheory.Abbrev_def] >> metis_tac[])) >>
  strip_tac >> suspend "finish"
QED

Resume append_nested_memory_cont_full[finish]:
  simp[loweringPostsTheory.stmt_lands_def, loweringPostsTheory.cenv_top_ext_def] >>
  rpt conj_tac
  >- (drule emitHelperPropsTheory.emitted_insts_emit_void >> strip_tac >>
      Cases_on `a8.cs_current_insts` >>
      simp[compileEnvTheory.block_is_terminated_def, listTheory.LAST_APPEND_CONS,
        listTheory.LAST_CONS_cond, venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def])
  >- (`!b. get_storage cx (ff with gas_obs := []) b = get_storage cx mid b` by
        (Cases >> simp[Abbr `ff`,vyperStorageBackendTheory.get_storage_def]) >>
      fs[vyperStorageFootprintTheory.storage_well_formed_on_def])
  >- (irule bodyMemoryDefsTheory.return_buf_frame_frame >> qexistsl_tac [`cenv`,`s`,`sa`] >>
      `ci_mono sa sb` by metis_tac[exprLoweringPropsTheory.ci_mono_trans] >>
      fs[ci_mono_def,typed_copy_state_frame_def,venomStateTheory.venom_state_component_equality])
  >- (irule bodyFullPathHistoryTheory.body_full_path_alloca_history >>
       fs[exprLoweringPropsTheory.stmt_state_rel_def] >> metis_tac[]) >>
  all_tac >~ [`ctx_has_dalloca ctx ==> allocas_below_fmp t`]
  >- (qpat_assum `stmt_state_rel H ctx func cenv cx ff t`
        (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  all_tac >~ [`ghost_inv_at _ _ _ _ _ (ff with gas_obs := []) _ _ _`]
  >- (qpat_assum `ghost_inv_at (DF H) lo d cenv cx ff Gf tf t`
        (mp_tac o REWRITE_RULE [ghost_inv_at_def]) >>
      simp_tac (srw_ss()) [ghost_inv_at_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `typed_copy_state_frame sa _ _ s t`
    (strip_assume_tac o SIMP_RULE (srw_ss())
      [typed_copy_state_frame_def, venomStateTheory.venom_state_component_equality]) >>
  simp[] >> qx_genl_tac [`aid`, `base_loc`, `alloc_len`, `i`] >> strip_tac >>
  qpat_assum `!aid off sz j. _ ==> j IN tn.t_mem`
    (qspecl_then [`aid`, `base_loc`, `alloc_len`, `i`] mp_tac) >>
  simp[] >>
  qpat_assum `!name a len. local_region cenv mid.scopes s name a len ==> _`
    (fn th => POP_ASSUM_LIST (K ALL_TAC) >> mp_tac th) >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Finalise append_nested_memory_cont_full[local]

Theorem append_memory_copy_cont_full[local]:
  compile_dynarray_append cenv (Var p) (Var xs) 32 (type_memory_size tv)
    elem elem cap F LocMemory sa = ((),sb) /\
  body_inv (cx_tops cx) ctx cenv cx /\ expr_sim_inv cenv cx env mid /\
  gas_admissible (append_place cx (MemoryPlace id path) v) (stmt_res_ok lctx) mid /\
  lookup_scopes id mid.scopes = SOME entry /\
  subscripts_type entry.type path = SOME (ArrayTV tv (Dynamic cap)) /\
  read_memory_path entry path = INL (ArrayV (DynArrayV vs)) /\
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) bp (SOME LocMemory)
    (Type (ArrayT elem (Dynamic cap))) /\
  (!t0. cenv.ce_var_type id = SOME t0 ==> evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  ~is_word_type elem /\ evaluate_type (get_tenv cx) elem = SOME tv /\
  type_memory_bytes cenv elem = type_memory_size tv /\
  type_memory_size tv + 64 < dimword (:256) /\ 0 < type_memory_size tv /\
  cap < dimword (:256) /\ value_has_type tv v /\ val_wf tv v /\
  lookup_var p s = SOME bp /\ lookup_var xs s = SOME sw /\
  not_fresh_at sa p /\ not_fresh_at sa xs /\
  ptr_covers G tn p s (32+cap*type_memory_size tv) /\
  ptr_covers G tn xs s (type_memory_size tv) /\
  w2n bp+32+cap*type_memory_size tv <= s.vs_alloca_next /\ lo <= w2n bp /\
  w2n sw+val_store_size tv v <= s.vs_alloca_next /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv v (w2n sw) mem /\
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n bp) mem) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid s /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx mid G tn s) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (append_place cx (MemoryPlace id path) v) (mid,s,G,tn)
    (\H res ee Gf tf u. ?cenv''.
      stmt_lands lctx sb res u /\ ~u.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv) /\
      cenv_top_ext cenv cenv'' ee.scopes /\ stmt_state_rel H ctx func cenv'' cx ee u /\
      storage_well_formed_on cx ee (FST H) /\ return_buf_frame d cenv'' sb u /\
      alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
      s.vs_alloca_next <= u.vs_alloca_next /\ ghost_inv_at (DF H) lo d cenv'' cx ee Gf tf u /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
      alloca_frame cenv mid sa s cenv'' ee u /\
      (!aid off sz i. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
        aid < sa.cs_next_id /\ off <= i /\ i < off+sz /\
        (!name a len. local_region cenv mid.scopes s name a len ==>
          off+sz <= a \/ a+len <= off) /\ i IN tf.t_mem ==> i IN tn.t_mem))
    (\H res ee gt r. (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
      halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==>
        allocas_below_fmp s))
Proof
  strip_tac >>
  mp_tac (Q.INST [`bp` |-> `(bp:bytes32)`, `cap` |-> `cap`, `elem` |-> `elem`,
    `entry` |-> `entry`, `p` |-> `p`, `src` |-> `Var xs`, `tv` |-> `tv`,
    `vs` |-> `vs`, `env` |-> `env`] append_nested_memory_cont_full) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  simp[]
QED

Theorem append_aggregate_input[local]:
  expr_body_pre cenv cx env e es /\
  bind (eval_expr cx e) (read_result cx) es = (INL v,ee) /\
  expr_post H ctx func cenv cx e es sa sb s0 ee v op s /\
  lower_value compile_expr cenv dty e sa = (op,sb) /\
  local_ptrs_reserved cenv sa /\
  ptr_val_ok cx (post_value_type cenv e) v op G tn s /\
  (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G s) /\
  expr_store_bound cx (post_value_type cenv e) v op s /\
  ~is_word_type dty /\ type_widens_to env.type_defs (expr_type e) dty /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\ 0 < type_memory_size dtv ==>
  ?stv src w.
    type_widens_to (get_tenv cx) (lowered_value_type cenv e) dty /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
    ~is_word_type (lowered_value_type cenv e) /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size stv /\
    0 < type_memory_size stv /\ value_has_type stv v /\ val_wf stv v /\
    value_has_type dtv v /\ val_wf dtv v /\
    expr_val_at cenv cx (lowered_value_type cenv e) sa sb ee v op s /\
    op = Var src /\ not_fresh_at sb src /\ lookup_var src s = SOME w /\
    ptr_covers G tn src s (type_memory_size stv) /\
    w2n w + val_store_size stv v <= s.vs_alloca_next /\
    w2n w + val_store_size stv v < dimword (:256) /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory stv v (w2n w) mem)
Proof
  strip_tac >>
  drule_all_then assume_tac immutableDeployPhysicalSourceTheory.immutable_rhs_physical_widens >>
  `~is_word_type (lowered_value_type cenv e)` by
    metis_tac[typedMemoryCopyTheory.return_source_word_widens_eq] >>
  drule immutableDeployPhysicalSourceTheory.immutable_rhs_post_physical_classify >>
  disch_then assume_tac >>
  `~is_word_type (post_value_type cenv e)` by metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
  drule_all_then (qx_choose_then `stv` strip_assume_tac)
    (SRULE [SF ETA_ss] immutableDeployPhysicalSourceTheory.immutable_rhs_physical_typed) >>
  `0 < type_memory_size stv` by
    (drule_all placeMemoryTypeInterfacesTheory.type_widens_to_zero_memory_size >>
     fs[valueEncodingPropsTheory.type_memory_size_slots] >> decide_tac) >>
  `value_has_type dtv v` by
    metis_tac[vyperTypeArgFitsTheory.type_widens_to_value_has_type, optionTheory.SOME_11] >>
  `val_wf dtv v` by (irule (cj 1 valueEncodingTypingTheory.value_has_type_val_wf) >> simp[]) >>
  drule_all_then (qx_choose_then `ptv` (qx_choose_then `sw` strip_assume_tac))
    (SRULE [SF ETA_ss] immutableDeployPhysicalSourceTheory.immutable_rhs_physical_memory) >>
  `val_store_size stv v = val_store_size ptv v` by suspend "source_store_size" >>
  `0 < val_store_size stv v` by simp[bodyDeclCopyMemoryTheory.val_store_size_pos] >>
  `w2n sw + val_store_size stv v <= s.vs_alloca_next` by
    (qpat_assum `expr_store_bound cx (post_value_type cenv e) v op s`
       (mp_tac o REWRITE_RULE [exprSimMemDefsTheory.expr_store_bound_def]) >>
     disch_then (qspecl_then [`ptv`,`sw`] mp_tac) >> simp[] >> decide_tac) >>
  `s.vs_alloca_next < dimword (:256)` by
    (qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
     qpat_assum `stmt_state_rel H ctx func cenv cx ee s`
       (mp_then (Pos hd) assume_tac stateRelProjTheory.stmt_state_rel_alloca_room) >>
     drule exprLoweringPropsTheory.alloca_room_next_lt >> simp[]) >>
  `w2n sw + val_store_size stv v < dimword (:256)` by decide_tac >>
  `ptr_buf_ok cenv e op G s /\ op_taint tn op = {}` by
    (qpat_assum `ptr_val_ok cx (post_value_type cenv e) _ _ _ _ _`
       (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.ptr_val_ok_def]) >> simp[]) >>
  `?src. op = Var src /\ ptr_covers G tn src s (type_memory_size stv)` by
    (irule assignBasePtrBoundaryTheory.ptr_buf_ok_read_covers >> simp[] >>
     qexistsl_tac [`cenv`,`e`] >> simp[]) >>
  `not_fresh_at sb src` by (drule_all exprOperandVarTheory.compile_lower_value_var >> simp[]) >>
  `lookup_var src s = SOME sw` by fs[venomStateTheory.eval_operand_def] >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory stv v (w2n sw) mem` by
    (drule_all (SRULE [SF ETA_ss] bodyFullStructLitPhysicalTheory.structlit_child_physical_robust) >>
     strip_tac >> gvs[]) >>
  qexistsl_tac [`stv`,`src`,`sw`] >> simp[] >>
  irule abiEncodeArgsSimTheory.abi_args_at_lowered_transport >>
  conj_tac
  >- metis_tac[] >>
  conj_tac
  >- (qexistsl_tac [`env`,`es`] >> simp[]) >>
  fs[expr_post_def]
QED

Resume append_aggregate_input[source_store_size]:
  Cases_on `post_value_type cenv e = lowered_value_type cenv e`
  >- (gvs[] >> simp[]) >>
  irule valueCopyBytesTheory.bytestring_val_store_size_eq >> simp[] >>
  qexistsl_tac [`lowered_value_type cenv e`,`post_value_type cenv e`,`get_tenv cx`] >>
  qpat_x_assum `post_value_type cenv e = lowered_value_type cenv e \/ _` mp_tac >> simp[]
QED

Finalise append_aggregate_input[local]

Theorem append_memory_local_inputs[local]:
  expr_sim_inv cenv cx env es /\ body_inv (cx_tops cx) ctx cenv cx /\
  target_mutable env (NameTarget id) /\
  FLOOKUP env.var_types id = SOME (ArrayT elem (Dynamic cap)) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  stmt_state_rel H ctx func cenv cx es s /\ ghost_inv_at D lo d cenv cx es G tn s /\
  dead_lo_ok H D lo cenv cx ==>
  ?entry bp tv vs.
    lookup_scopes id es.scopes = SOME entry /\ entry.assignable /\
    entry.type = ArrayTV tv (Dynamic cap) /\
    read_memory_path entry [] = INL (ArrayV (DynArrayV vs)) /\
    subscripts_type entry.type [] = SOME (ArrayTV tv (Dynamic cap)) /\
    value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
    lookup_var p s = SOME bp /\
    evaluate_type (get_tenv cx) elem = SOME tv /\ 0 < type_memory_size tv /\
    cenv.ce_var_type id = SOME (ArrayT elem (Dynamic cap)) /\
    place_ptr_rel cenv cx s (PlaceR (MemoryPlace id [])) bp (SOME LocMemory)
      (Type (ArrayT elem (Dynamic cap))) /\
    ptr_covers G tn p s (32+cap*type_memory_size tv) /\
    w2n bp+32+cap*type_memory_size tv <= s.vs_alloca_next /\ lo <= w2n bp /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n bp) mem)
Proof
  strip_tac >>
  drule_all_then (strip_assume_tac o CONJUNCT2) targetPlaceSimTheory.expr_sim_inv_local >>
  `cenv.ce_var_type id = SOME (ArrayT elem (Dynamic cap))` by fs[expr_sim_inv_def] >>
  `entry.assignable` by
    (fs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
      vyperTypeInvariantsTheory.env_scopes_consistent_def, vyperTypeSystemTheory.target_mutable_def] >>
     qpat_assum `!id. FLOOKUP env.var_assignable id = SOME T ==>
        ?en. lookup_scopes id es.scopes = SOME en /\ en.assignable`
       (qspec_then `id` (drule_then (qx_choose_then `en` strip_assume_tac))) >> gvs[]) >>
  `value_has_type entry.type entry.value` by
    (irule vyperTypeStatePreservationTheory.lookup_scopes_state_well_typed_value_has_type >>
     qexistsl_tac [`id`,`es`] >> fs[expr_sim_inv_def]) >>
  `evaluate_type (get_tenv cx) (ArrayT elem (Dynamic cap)) = SOME entry.type` by
    (qpat_assum `!en. lookup_scopes id es.scopes = SOME en ==>
       evaluate_type (get_tenv cx) (ArrayT elem (Dynamic cap)) = SOME en.type`
       (qspec_then `entry` (drule_then ACCEPT_TAC))) >>
  drule_then (qx_choose_then `tv` strip_assume_tac)
    vyperTypeValuesTheory.evaluate_type_ArrayT_cases >>
  `0 < type_slot_size tv` by
    (Cases_on `0 < type_slot_size tv` >> simp[] >>
     qpat_assum `evaluate_type _ (ArrayT elem _) = SOME entry.type`
       (mp_tac o PURE_ONCE_REWRITE_RULE [evaluate_type_def]) >>
     simp[LET_THM]) >>
  `0 < type_memory_size tv` by metis_tac[cj 1 valueEncodingPropsTheory.type_memory_size_pos] >>
  `?vs. entry.value = ArrayV (DynArrayV vs)` by
    (qpat_x_assum `value_has_type entry.type entry.value` mp_tac >> simp[] >>
     Cases_on `entry.value` >> simp[vyperTypingTheory.value_has_type_def] >>
     rename1 `ArrayV av` >> Cases_on `av` >> simp[vyperTypingTheory.value_has_type_def]) >>
  drule stateRelProjTheory.stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  `?bp. lookup_var p s = SOME bp /\ w2n bp+sz <= s.vs_alloca_next /\
        32+cap*type_memory_size tv <= sz` by
    (qpat_assum `local_ptrs_rel _ _ _ _`
       (qspecl_then [`id`,`entry`,`p`,`sz`] mp_tac o CONJUNCT1 o
        REWRITE_RULE [local_ptrs_rel_def]) >>
     simp[valueEncodingTheory.type_memory_size_def] >> strip_tac >>
     qexists_tac `w` >> simp[]) >>
  `local_region cenv es.scopes s id (w2n bp) sz` by simp[local_region_def] >>
  `0 < sz` by decide_tac >>
  `lo <= w2n bp` by
    (irule bodyFullMemoryFramesTheory.body_full_local_region_lower_bound >>
     goal_assum (drule_at Any) >>
     qexistsl_tac [`D`,`H`,`cenv`,`ctx`,`cx`,`env`,`es`,`es`,`func`,`id`,`s`,`cx_tops cx`] >> simp[]) >>
  `ptr_covers G tn p s sz /\
   !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory entry.type entry.value (w2n bp) mem` by
    (qpat_assum `ghost_inv_at D lo d cenv cx es G tn s`
       (mp_tac o REWRITE_RULE [ghost_inv_at_def]) >>
     disch_then (mp_tac o CONJUNCT1) >>
     disch_then (qspecl_then [`id`,`entry`,`p`,`sz`] mp_tac) >> simp[]) >>
  qexistsl_tac [`entry`,`bp`,`tv`,`vs`] >>
  fs[read_memory_path_def, evaluate_subscripts_def, subscripts_type_def] >>
  conj_tac >- (pure_rewrite_tac[loweringPostsTheory.place_ptr_rel_def] >>
    qexistsl_tac [`p`,`sz`,`bp`,`ArrayT elem (Dynamic cap)`,
      `ArrayTV tv (Dynamic cap)`,`0`,`ArrayTV tv (Dynamic cap)`,`ArrayT elem (Dynamic cap)`] >>
    simp[mem_path_offset_def, wordsTheory.WORD_ADD_0]) >>
  conj_tac >- (irule reasonCopySourcePtrTheory.ptr_covers_mono >>
    qexists_tac `sz` >> simp[arithmeticTheory.ADD_COMM]) >>
  qpat_assum `entry.type = ArrayTV tv (Dynamic cap)` (fn ty =>
    qpat_assum `entry.value = ArrayV (DynArrayV vs)` (fn value =>
      qpat_assum `!mem. mem_agree_outside _ _ mem ==> val_in_memory entry.type entry.value _ mem`
        (ACCEPT_TAC o PURE_REWRITE_RULE [ty,value])))
QED

Theorem body_append_local_nonword_frag_full:
  !cx id e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv
    env env' ret_ty lctx RetQ es elem cap.
  (!s p t. eval_target_place cx (NameTarget id) s = (INL p,t) ==>
     body_expr_full_ok cx e) /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (Append (NameTarget id) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Append (NameTarget id) e) ==> occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
  locals_alloc_ok cenv env /\
  type_stmt env ret_ty (Append (NameTarget id) e) = SOME env' /\
  type_place_target env (NameTarget id) = SOME (Type (ArrayT elem (Dynamic cap))) /\
  ~is_word_type elem /\ stmt_exprs_ok cenv (Append (NameTarget id) e) /\
  call_evaluation_safe cx (int_calls_stmt (Append (NameTarget id) e)) /\
  frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ cenv ret_ty ==>
  stmt_frag_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (Append (NameTarget id) e))
    (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Append (NameTarget id) e)))
    (eval_stmt cx (Append (NameTarget id) e)) es
Proof
  rpt gen_tac >> strip_tac >>
  `~(?nid. NameTarget id = TopLevelNameTarget nid)` by simp[] >>
  drule_all bodyAppendResolvedPreTheory.body_append_typed_pre >> strip_tac >> gvs[] >>
  `FLOOKUP env.var_types id = SOME (ArrayT elem (Dynamic cap))` by
    gvs[Once vyperTypeSystemTheory.well_typed_expr_def, AllCaseEqs()] >>
  drule_all targetPlaceSimTheory.expr_sim_inv_local >> strip_tac >>
  `eval_target_place cx (NameTarget id) es = (INL (MemoryPlace id []),es)` by
    (irule exprSimPopTheory.eval_target_place_name >> simp[]) >>
  `body_expr_full_ok cx e` by metis_tac[] >>
  `cenv.ce_var_type id = SOME (ArrayT elem (Dynamic cap))` by fs[expr_sim_inv_def] >>
  rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `compile_get_target_ptr compile_expr cenv (NameTarget id) sa =
    ((Var p,SOME LocMemory,SOME (ValPT (ArrayT elem (Dynamic cap)))),sa) /\
   compile_get_target_ptr compile_expr (gas_shadow_env T cenv) (NameTarget id) shadow_sa =
    ((Var p,SOME LocMemory,SOME (ValPT (ArrayT elem (Dynamic cap)))),shadow_sa)` by
    simp[compile_get_target_ptr_def, comp_return_def] >>
  qpat_assum `stmt_env _ _ _ (Append _ e) sa = _`
    (mp_then (Pos hd) mp_tac append_resolved_copy_code_parts) >>
  simp[] >> strip_tac >> gvs[] >>
  irule append_return_buf_sep >> asm_simp_tac bool_ss [] >>
  irule gas_outcome_full_initial_domain >>
  conj_tac >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  simp[] >> strip_tac >>
  `!tail. eval_target_place cx (NameTarget id) (es with gas_obs := tail) =
    (INL (MemoryPlace id []),es with gas_obs := tail)` by
    (gen_tac >> irule exprSimPopTheory.eval_target_place_name >> simp[]) >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (eval_target_place cx (NameTarget id))
      (es,s0,G0,tn0)
      (\H res ee G tn u. res = INL (MemoryPlace id []) /\ ee = es with gas_obs := [] /\
        G = G0 /\ tn = tn0 /\ u = s0) (\H res ee gt r. F)` by
    (irule gas_outcome_full_pure >> simp[] >>
     qexistsl_tac [`G0`,`es`,`INL (MemoryPlace id [])`,`s0`,`tn0`] >>
     simp[fragGasOriginPtrTheory.gas_origin_ptr_path_rules]) >>
  pure_once_rewrite_tac[vyperInterpreterTheory.evaluate_def] >>
  pure_rewrite_tac[GSYM bind_assoc] >>
  irule gas_outcome_full_bind_all >>
  conj_tac >- simp[vyperStorageTraceTheory.storage_trace_frame_bind,
    vyperStorageTraceTheory.evaluate_storage_trace_frame,
    vyperStorageTraceTheory.storage_trace_frame_read_result,
    vyperStorageTraceTheory.storage_trace_frame_append_place] >>
  conj_tac >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_place >>
    goal_assum (drule_at Any) >> fs[]) >>
  conj_tac >- metis_tac[gasExemptCertTheory.gas_exempt_cert_error_place] >>
  conj_tac >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` mp_tac >>
  disch_then (fn th =>
    irule_at (Pos last) gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
    irule_at (Pos hd) th) >>
  qexists_tac `\H res ee G tn u. res = INL (MemoryPlace id []) /\ ee = es with gas_obs := [] /\
        G = G0 /\ tn = tn0 /\ u = s0` >> simp[] >>
  suspend "rhs_setup"
QED

Resume body_append_local_nonword_frag_full[rhs_setup]:
  rpt strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  disj1_tac >> qexists_tac `MemoryPlace id []` >> conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `!tail. INL (MemoryPlace id []) = res /\ _` kall_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
     res = INL (MemoryPlace id []) /\ _` kall_tac >>
  qpat_x_assum `res = INL (MemoryPlace id [])` kall_tac >>
  qpat_x_assum `t = s0` SUBST_ALL_TAC >>
  qpat_x_assum `G1 = G0` SUBST_ALL_TAC >>
  qpat_x_assum `tn1 = tn0` SUBST_ALL_TAC >>
  qpat_assum `stmt_env _ _ _ (gas_shadow_stmt _) shadow_sa = _`
    (mp_tac o SRULE [gasShadowTheory.gas_shadow_stmt_def, gasShadowTheory.gas_shadow_expr_def]) >>
  strip_tac >>
  qpat_assum `stmt_env _ _ _ (Append (NameTarget _) (gas_shadow_expr _)) shadow_sa = _`
    (mp_then (Pos hd) mp_tac append_resolved_copy_code_parts) >>
  simp[IgnAsm `mid = es with gas_obs := []`] >> strip_tac >>
  rename1 `lower_value compile_expr cenv elem e sa = (vop,sm)` >>
  rename1 `lower_value compile_expr _ elem (gas_shadow_expr e) shadow_sa = (vop',shadow_sm)` >>
  `vop' = vop /\ gas_shadow_state sm shadow_sm` by
    (irule bodyFullSharedTheory.gas_shadow_step >>
     qpat_assum `lower_value _ _ _ e sa = _` (irule_at Any) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr e) shadow_sa = _` (irule_at Any) >>
     simp[] >> irule gas_shadow_stmt_lower_value_env) >>
  qpat_x_assum `vop' = vop` SUBST_ALL_TAC >>
  `ci_mono sm sb /\ ci_mono shadow_sm shadow_sb` by
    metis_tac[ci_mono_compile_dynarray_append,ci_mono_compile_alloc_buffer,
      ci_mono_compile_store_memory,exprLoweringPropsTheory.ci_mono_trans,pairTheory.SND] >>
  `ci_mono sa sm /\ ci_mono shadow_sa shadow_sm` by
    metis_tac[ci_mono_lower_value_compile_expr,pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func /\
   fn_has_code shadow_sa shadow_sm shadow_func` by
    (fs[ci_mono_def] >> metis_tac[fragExecTheory.fn_has_code_split]) >>
  `(!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x)` by
    fs[loweringPostsTheory.ret_pc_ok_def] >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by simp[] >>
  `expr_body_pre cenv cx env e mid` by
    fs[exprSimSourceTheory.expr_body_pre_gas_obs] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok mid` by
    (irule expr_body_pre_gas_admissible >> goal_assum (drule_at Any)) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx elem e mid` by
    (qpat_assum `body_expr_full_ok cx e`
       (mp_tac o ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
     qpat_assum `body_inv tops ctx cenv cx` mp_tac >>
     qpat_assum `shadow_body_inv tops ctx shadow_ctx` mp_tac >>
     qpat_assum `body_const_cells_agree [(NONE,tops)] cx env mid` mp_tac >>
     qpat_assum `expr_body_pre cenv cx env e mid` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`vop`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (
    `!H. valid_horizon cx st0 H mid.storage_trace ==>
      stmt_state_rel H ctx func cenv cx mid s0 /\ storage_well_formed_on cx mid (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx mid G0 tn0 s0` by
      (gen_tac >> strip_tac >>
       `valid_horizon cx st0 H es.storage_trace` by
         (qpat_assum `mid = es with gas_obs := []` (fn mid_eq =>
           qpat_assum `valid_horizon cx st0 H mid.storage_trace`
             (ACCEPT_TAC o SRULE [mid_eq]))) >>
       qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==>
          stmt_state_rel H ctx func cenv cx es s0 /\ _`
         (qspec_then `H` (drule_then strip_assume_tac)) >>
       `!b. get_storage cx (es with gas_obs := []) b = get_storage cx es b` by
         (Cases >> simp[vyperStorageBackendTheory.get_storage_def]) >>
       qpat_assum `mid = es with gas_obs := []` SUBST1_TAC >>
       conj_tac >- simp[stmt_state_rel_start_gas_obs] >>
       conj_tac >- fs[vyperStorageFootprintTheory.storage_well_formed_on_def] >>
       qpat_assum `ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0` mp_tac >>
       simp_tac (srw_ss()) [ghost_inv_at_def] >>
       strip_tac >> first_assum ACCEPT_TAC) >>
    simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ Q1 R1` >>
  irule gas_outcome_full_bind_all >>
  conj_tac >- simp[vyperStorageTraceTheory.storage_trace_frame_append_place] >>
  conj_tac >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
    goal_assum (drule_at Any) >> gvs[]) >>
  conj_tac >- metis_tac[gasExemptCertTheory.gas_exempt_cert_error_value] >>
  conj_tac >- simp[vyperStorageTraceTheory.storage_trace_frame_bind,
    vyperStorageTraceTheory.evaluate_storage_trace_frame,
    vyperStorageTraceTheory.storage_trace_frame_read_result] >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` mp_tac >>
  disch_then (fn th =>
    irule_at (Pos last) gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
    irule_at (Pos hd) th) >>
  qexists_tac `\H res ee G tn t. Q1 H res ee G tn t /\ ~t.vs_halted` >>
  conj_tac >- simp[] >>
  conj_tac >- suspend "rhs_exit" >>
  simp_tac (srw_ss()) [Abbr `Q1`] >> suspend "rhs_success"
QED

Resume body_append_local_nonword_frag_full[rhs_exit]:
  simp[Abbr `R1`] >> rpt gen_tac >> strip_tac >>
  Cases_on `res` >> Cases_on `r` >> gvs[exprSimDefsTheory.expr_exit_def] >>
  rename1 `INR exc` >> Cases_on `exc` >>
  qpat_x_assum `expr_exit _ _` mp_tac >>
  qpat_x_assum `halt_exit _ _ _ _ _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  gvs[exprSimDefsTheory.expr_exit_def, stmt_exit_ptr_def,
      exprSimDefsTheory.halt_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >>
  gvs[exprSimDefsTheory.expr_exit_def, stmt_exit_ptr_def]
QED

Resume body_append_local_nonword_frag_full[rhs_success]:
  rpt strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid'.storage_trace) mid'.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid'.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid'.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  disj1_tac >> qexists_tac `v` >> simp[] >>
  qabbrev_tac `gas_in = mid with gas_obs :=
     gas_explicit marks s0.vs_gas_readings ++ mid'.gas_obs` >>
  `bind (eval_expr cx e) (read_result cx) gas_in = (INL v,mid')` by
    (qpat_assum `!tail. bind (eval_expr cx e) (read_result cx) _ = _`
       (qspec_then `mid'.gas_obs` mp_tac) >> simp[Abbr `gas_in`]) >>
  `expr_body_pre cenv cx env e gas_in` by
    fs[Abbr `gas_in`,exprSimSourceTheory.expr_body_pre_gas_obs] >>
  `expr_sim_inv cenv cx env mid'` by
    (drule_all (SRULE [SF ETA_ss] exprSimSourceTheory.expr_body_pre_eval) >> simp[]) >>
  `expr_post (storage_trace_horizon mid'.storage_trace) ctx func cenv cx e
    gas_in sa sm s0 mid' v vop t` by
    (qpat_assum `expr_post _ _ _ _ _ _ mid _ _ _ mid' _ _ _` mp_tac >>
     simp[Abbr `gas_in`,exprSimExtract32PostTheory.extract32_expr_post_start_gas_obs]) >>
  `gas_admissible (append_place cx (MemoryPlace id []) v) (stmt_res_ok lctx) mid'` by
    suspend "admissible" >>
  `!H. valid_horizon cx st0 H mid'.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid' t /\ storage_well_formed_on cx mid' (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx mid' G1 tn1 t` by
    (qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid'.storage_trace ==> (?v. _) /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     qpat_assum `expr_post H _ _ _ _ _ mid _ _ _ mid' _ _ _`
       (map_every assume_tac o CONJUNCTS o REWRITE_RULE [expr_post_def]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `target_mutable env (NameTarget id)` by
    (qpat_x_assum `type_stmt _ _ (Append _ _) = _` mp_tac >>
     simp[Once vyperTypeSystemTheory.type_stmt_def, AllCaseEqs()]) >>
  `cx_tops cx = tops` by metis_tac[bodyInvCodePropsTheory.body_inv_main_code] >>
  `body_inv (cx_tops cx) ctx cenv cx` by asm_rewrite_tac[] >>
  qpat_assum `!H. dead_lo_ok H (DF H) lo cenv cx`
    (qspec_then `storage_trace_horizon mid'.storage_trace` assume_tac) >>
  qpat_assum `!H. valid_horizon cx st0 H mid'.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid' t /\ _`
    (qspec_then `storage_trace_horizon mid'.storage_trace` (drule_then strip_assume_tac)) >>
  drule_all_then strip_assume_tac append_memory_local_inputs >>
  drule_all_then (qx_choosel_then [`stv`,`src`,`sw`] strip_assume_tac) append_aggregate_input >>
  qpat_x_assum `vop = Var src` SUBST_ALL_TAC >>
  suspend "stage_setup"
QED

Resume body_append_local_nonword_frag_full[admissible]:
  qpat_assum `gas_admissible (eval_stmt _ _) _ es`
    (mp_tac o ONCE_REWRITE_RULE [vyperInterpreterTheory.evaluate_def]) >>
  qpat_assum `!tail. eval_target_place _ _ (es with gas_obs := tail) = _` mp_tac >>
  qpat_assum `!tail. bind (eval_expr cx e) (read_result cx) _ = _` mp_tac >>
  qpat_assum `res = INL v` mp_tac >>
  qpat_assum `mid = es with gas_obs := []` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >>
  simp[gasContextTheory.gas_admissible_def] >> strip_tac >>
  qx_gen_tac `gs` >> rpt gen_tac >> disch_tac >>
  qpat_assum `mid = es with gas_obs := []` (fn mid_eq =>
    qpat_assum `res = INL v` (fn res_eq =>
      qpat_assum `!tail. bind (eval_expr cx e) (read_result cx) _ = _`
        (qspec_then `gs` (assume_tac o SRULE [mid_eq,res_eq])))) >>
  qpat_assum `!gs res ee. _ ==> stmt_res_ok lctx res`
    (qspec_then `gas_explicit marks s0.vs_gas_readings ++ gs` mp_tac) >>
  simp[GSYM bind_assoc, Once bind_def] >> simp[Once bind_def, SF ETA_ss] >>
  disch_then (qspecl_then [`res'`,`ee`] mp_tac) >> simp[]
QED

Resume body_append_local_nonword_frag_full[stage_setup]:
  `type_memory_bytes cenv elem = type_memory_size tv /\ type_memory_bytes cenv elem < 2**64` by
    metis_tac[appendMemoryRelTheory.append_memory_element_size_bound] >>
  `type_memory_size tv + 64 < dimword (:256)` by
    (qpat_assum `type_memory_bytes cenv elem = type_memory_size tv` (fn size =>
       qpat_assum `type_memory_bytes cenv elem < 2**64`
         (mp_tac o PURE_REWRITE_RULE [size])) >>
     simp_tac (srw_ss()) [wordsTheory.dimword_def] >> decide_tac) >>
  `t.vs_alloca_next < dimword (:256)` by
    (qpat_assum `stmt_state_rel (storage_trace_horizon _) ctx func cenv cx mid' t`
       (ACCEPT_TAC o MATCH_MP exprLoweringPropsTheory.alloca_room_next_lt o
        MATCH_MP stateRelProjTheory.stmt_state_rel_alloca_room)) >>
  `cap < dimword (:256)` by
    (`cap <= cap*type_memory_size tv` by
       (Cases_on `type_memory_size tv` >> fs[] >> simp[arithmeticTheory.MULT_CLAUSES]) >>
     decide_tac) >>
  `ci_mono sm sc /\ ci_mono sc sd /\ ci_mono sd sb` by
    metis_tac[ci_mono_compile_alloc_buffer,ci_mono_compile_store_memory,
      ci_mono_compile_dynarray_append,pairTheory.SND] >>
  `cs_extends sm sc /\ cs_extends sc sd /\ cs_extends sd sb` by fs[ci_mono_def] >>
  `fn_has_code sm sc func /\ fn_has_code sc sd func /\ fn_has_code sd sb func` by
    metis_tac[fragExecTheory.fn_has_code_split,compileEnvTheory.cs_extends_trans] >>
  `local_ptrs_reserved cenv sm` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `sa` >> fs[ci_mono_def]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> fs[ci_mono_def] >> goal_assum (drule_at Any)) >>
  `return_buf_frame d cenv sm t` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`,`s0`,`sa`] >> fs[expr_post_def,ci_mono_def]) >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by fs[ghost_inv_at_def] >>
  drule_all_then strip_assume_tac
    immutableDeployAssignRangesTheory.immutable_assign_copy_metadata >>
  qpat_assum `type_memory_bytes cenv elem = type_memory_size tv` (fn th =>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> assume_tac th) >>
  `word_scale LocMemory = 32 /\ elem_size_in_location cenv LocMemory elem = type_memory_size tv` by
    simp[word_scale_def,elem_size_in_location_def,is_slot_addressed_def] >>
  `compile_dynarray_append cenv (Var p) tmp.buf_operand 32 (type_memory_size tv)
    elem elem cap F LocMemory sd = ((),sb)` by
    (qpat_assum `word_scale LocMemory = 32` (fn scale =>
      qpat_assum `elem_size_in_location cenv LocMemory elem = type_memory_size tv` (fn size =>
        qpat_assum `compile_dynarray_append cenv (Var p) _ (word_scale LocMemory) _ _ _ _ F LocMemory sd = _`
          (ACCEPT_TAC o PURE_REWRITE_RULE [scale,size])))) >>
  drule_all (SRULE [] (Q.INST [`n` |-> `type_memory_size dtv`]
    (INST_TYPE [beta |-> ``:256``] append_storage_aggregate_stage_ready))) >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (qx_choosel_then [`staged`,`root`,`b`,`Gs`,`ts`] strip_assume_tac)) >>
  qpat_x_assum `tmp.buf_operand = Var root` SUBST_ALL_TAC >>
  suspend "staged_suffix"
QED

Resume body_append_local_nonword_frag_full[staged_suffix]:
  `!H. valid_horizon cx st0 H mid'.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid' staged /\ storage_well_formed_on cx mid' (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx mid' Gs ts staged` by metis_tac[] >>
  `local_ptrs_reserved cenv sd` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `sm` >> fs[ci_mono_def]) >>
  `not_fresh_at sd p` by
    (qpat_assum `local_ptrs_reserved cenv sd` (mp_tac o REWRITE_RULE [local_ptrs_reserved_def]) >>
     qpat_assum `FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sd x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sd x)` by metis_tac[] >>
  `return_buf_frame d cenv sd staged` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`,`t`,`sm`] >> fs[ci_mono_def] >> decide_tac) >>
  `!H. gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (t,G1,tn1) [] (OK staged,Gs,ts)` by simp[] >>
  irule gasOutcomeFullStmtsTheory.gas_outcome_full_zero_prefix >>
  goal_assum (drule_at Any) >>
  `stmt_state_rel (storage_trace_horizon mid'.storage_trace) ctx func cenv cx mid' staged` by
    metis_tac[] >>
  `ghost_inv_at (DF (storage_trace_horizon mid'.storage_trace)) lo d cenv cx mid' Gs ts staged` by
    metis_tac[] >>
  drule_all_then (qx_choosel_then [`staged_entry`,`staged_bp`,`staged_tv`,`staged_vs`] strip_assume_tac)
    (Q.INST [`s` |-> `staged`] append_memory_local_inputs) >>
  `staged_tv = tv` by fs[] >>
  qpat_x_assum `staged_tv = tv` SUBST_ALL_TAC >>
  `w2n ((n2w b):bytes32) = b` by simp[] >>
  `w2n ((n2w b):bytes32) + val_store_size tv v <= staged.vs_alloca_next` by
    (qpat_assum `val_wf tv v` (mp_tac o MATCH_MP exprSimPropsTheory.val_store_size_le) >>
     qpat_assum `b + type_memory_size tv <= staged.vs_alloca_next` mp_tac >>
     qpat_assum `w2n ((n2w b):bytes32) = b` SUBST1_TAC >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  `!t0. cenv.ce_var_type id = SOME t0 ==> evaluate_type (get_tenv cx) t0 = SOME staged_entry.type` by
    (rpt strip_tac >> irule bodySimAugPlaceLoadTheory.aug_place_entry_type_agrees >>
     qpat_assum `lookup_scopes id mid'.scopes = SOME staged_entry` (irule_at Any) >>
     qpat_assum `expr_sim_inv cenv cx env mid'` (irule_at Any) >> simp[]) >>
  `!mem. mem_agree_outside ts.t_mem staged.vs_memory mem ==>
    val_in_memory tv v (w2n ((n2w b):bytes32)) mem /\
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV staged_vs)) (w2n staged_bp) mem` by
    (qx_gen_tac `mem` >> strip_tac >>
     qpat_assum `w2n ((n2w b):bytes32) = b` SUBST1_TAC >>
     conj_tac
     >- (qpat_assum `!mem. mem_agree_outside ts.t_mem staged.vs_memory mem ==>
            val_in_memory tv v b mem` (qspec_then `mem` (drule_then ACCEPT_TAC))) >>
     qpat_assum `!mem. mem_agree_outside ts.t_mem staged.vs_memory mem ==>
       val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV staged_vs)) _ mem`
       (qspec_then `mem` (drule_then ACCEPT_TAC))) >>
  irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
  irule_at (Pat `gas_outcome_full _ _ _ _ _ _ _ _`) append_memory_copy_cont_full >>
  qpat_assum `compile_dynarray_append cenv (Var p) (Var root) _ _ _ _ _ F LocMemory sd = _`
    (irule_at Any) >>
  simp[] >> suspend "staged_post"
QED

Resume body_append_local_nonword_frag_full[staged_post]:
  `gas_in.storage_trace = es.storage_trace /\ gas_in.scopes = es.scopes` by
    (qpat_assum `mid = es with gas_obs := []` (fn mid_eq =>
      simp_tac (srw_ss()) [Abbr `gas_in`,mid_eq])) >>
  `?obs. mid'.storage_trace = es.storage_trace ++ obs` by
    (`storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
       simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
         vyperStorageTraceTheory.evaluate_storage_trace_frame,
         vyperStorageTraceTheory.storage_trace_frame_read_result] >>
     qpat_assum `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` (fn frame =>
       qpat_assum `bind (eval_expr cx e) (read_result cx) gas_in = (INL v,mid')`
         (strip_assume_tac o MATCH_MP vyperStorageTraceTheory.storage_trace_frame_prefix o CONJ frame)) >>
     qexists_tac `observations` >> fs[]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid'.storage_trace) es.storage_trace` by
    (irule gasOutcomeFullTheory.valid_horizon_append >>
     qexists_tac `obs` >>
     qpat_assum `mid'.storage_trace = es.storage_trace ++ obs` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  `stmt_state_rel (storage_trace_horizon mid'.storage_trace) ctx func cenv cx gas_in s0` by
    (qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es s0 /\ _`
       (qspec_then `storage_trace_horizon mid'.storage_trace` (drule_then strip_assume_tac)) >>
     qpat_assum `stmt_state_rel (storage_trace_horizon _) ctx func cenv cx es s0` mp_tac >>
     qpat_assum `mid = es with gas_obs := []` (fn mid_eq =>
       simp_tac (srw_ss()) [Abbr `gas_in`,mid_eq,stmt_state_rel_start_gas_obs])) >>
  `MAP FDOM mid'.scopes = MAP FDOM gas_in.scopes` by
    (qpat_assum `bind (eval_expr cx e) (read_result cx) gas_in = (INL v,mid')`
      (ACCEPT_TAC o MATCH_MP stmtSimDefsTheory.eval_read_preserves_scopes_dom)) >>
  `alloca_frame cenv es sa s0 cenv mid' t` by
    (`alloca_frame cenv gas_in sa s0 cenv mid' t` by
       (irule (INST_TYPE [alpha |-> ``:256``] stmtSimDefsTheory.expr_post_alloca_frame) >>
        qpat_assum `expr_post (storage_trace_horizon _) ctx func cenv cx e gas_in sa sm s0 mid' _ _ t`
          (irule_at Any) >> simp[]) >>
     qpat_assum `gas_in.scopes = es.scopes` (fn scope_eq =>
       qpat_assum `alloca_frame cenv gas_in sa s0 cenv mid' t`
         (mp_tac o PURE_REWRITE_RULE [stmtSimDefsTheory.alloca_frame_def,scope_eq])) >>
     REWRITE_TAC [stmtSimDefsTheory.alloca_frame_def]) >>
  qpat_assum `expr_post (storage_trace_horizon _) _ _ _ _ _ gas_in sa sm s0 mid' _ _ t`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [expr_post_def]) >>
  qpat_assum `mid = es with gas_obs := []` (fn mid_eq =>
    qpat_assum `ghost_kept_at lo cenv mid sa G0 tn0 s0 G1 tn1`
      (map_every assume_tac o CONJUNCTS o SRULE [ghost_kept_at_def,mid_eq])) >>
  qexistsl_tac [`lctx`,`env`,`d`,`RetQ`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid'.storage_trace ==> stmt_state_rel _ _ _ _ _ _ staged /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac >- (rpt gen_tac >> strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qx_genl_tac [`H`,`ans`,`ee`,`Gf`,`tf`,`fin_state`] >>
  disch_then (qx_choose_then `cenvf` strip_assume_tac) >>
  qexists_tac `cenvf` >> simp[] >> suspend "staged_frame"
QED

Resume body_append_local_nonword_frag_full[staged_frame]:
  `sa.cs_next_id <= sm.cs_next_id /\ sa.cs_next_id <= sd.cs_next_id` by
    (fs[ci_mono_def] >> decide_tac) >>
  `alloca_frame cenv es sa s0 cenv mid' staged` by
    (irule stmtSimDefsTheory.alloca_frame_trans >>
     qpat_assum `alloca_frame cenv mid' sm t cenv mid' staged` (irule_at Any) >>
     simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==> FLOOKUP staged.vs_allocas aid = SOME a` by
    (rpt strip_tac >>
     qpat_assum `!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==> FLOOKUP t.vs_allocas aid = SOME a`
       (qspecl_then [`aid`,`a`] (drule_then assume_tac)) >>
     qpat_assum `!aid a. FLOOKUP t.vs_allocas aid = SOME a ==> FLOOKUP staged.vs_allocas aid = SOME a`
       (qspecl_then [`aid`,`a`] (drule_then ACCEPT_TAC))) >>
  `!x. not_fresh_at sa x ==> lookup_var x fin_state = lookup_var x t /\
    FLOOKUP Gf x = FLOOKUP G1 x /\ op_taint tf (Var x) = op_taint tn1 (Var x)` by
    (qx_gen_tac `x` >> strip_tac >>
     `not_fresh_at sm x` by
       (irule exprOperandVarTheory.compiler_ci_mono_not_fresh >> qexists_tac `sa` >> simp[]) >>
     qpat_assum `!x. not_fresh_at sm x ==> not_fresh_at sd x /\ _`
       (qspec_then `x` (drule_then strip_assume_tac)) >>
     qpat_assum `!x. not_fresh_at sd x ==> lookup_var x fin_state = _ /\ _`
       (qspec_then `x` (drule_then strip_assume_tac)) >> simp[]) >>
  conj_tac >-
    (qx_genl_tac [`x`,`w`] >> strip_tac >>
     qpat_assum `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w`
       (qspecl_then [`x`,`w`] mp_tac) >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x fin_state = _ /\ _`
       (qspec_then `x` (drule_then strip_assume_tac)) >> simp[]) >>
  conj_tac >-
    (qx_gen_tac `x` >> strip_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> FLOOKUP G1 x = _ /\ _`
       (qspec_then `x` (drule_then strip_assume_tac)) >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x fin_state = _ /\ _`
       (qspec_then `x` (drule_then strip_assume_tac)) >> simp[]) >>
  conj_tac >-
    (irule stmtSimDefsTheory.alloca_frame_trans >>
     qpat_assum `alloca_frame cenv mid' sd staged cenvf ee fin_state` (irule_at Any) >>
     simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qx_genl_tac [`aid`,`off`,`sz0`,`i`] >> strip_tac >>
  `aid < sm.cs_next_id /\ aid < sd.cs_next_id` by
    (conj_tac >> irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
     qexists_tac `sa.cs_next_id` >> simp[]) >>
  `FLOOKUP t.vs_allocas aid = SOME (off,sz0)` by
    (qpat_assum `!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==> FLOOKUP t.vs_allocas aid = SOME a`
       (qspecl_then [`aid`,`(off,sz0)`] (drule_then ACCEPT_TAC))) >>
  `FLOOKUP staged.vs_allocas aid = SOME (off,sz0)` by
    (qpat_assum `!aid a. FLOOKUP t.vs_allocas aid = SOME a ==> FLOOKUP staged.vs_allocas aid = SOME a`
       (qspecl_then [`aid`,`(off,sz0)`] (drule_then ACCEPT_TAC))) >>
  `!n b sz'. local_region cenv mid'.scopes staged n b sz' ==> off + sz0 <= b \/ b + sz' <= off` by
    (qpat_assum `alloca_frame cenv es sa s0 cenv mid' staged`
       (qspecl_then [`aid`,`off`,`sz0`] mp_tac o REWRITE_RULE [stmtSimDefsTheory.alloca_frame_def]) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `i IN ts.t_mem` by
    (qpat_assum `!aid off sz i. FLOOKUP staged.vs_allocas aid = SOME (off,sz) /\ _ ==> i IN ts.t_mem`
       (qspecl_then [`aid`,`off`,`sz0`,`i`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
  `i IN tn1.t_mem` by
    (qpat_assum `!aid off sz. aid < sm.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (off,sz) ==> _`
       (qspecl_then [`aid`,`off`,`sz0`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (qspec_then `i` mp_tac) >> simp[]) >>
  qpat_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ _ ==> i IN tn0.t_mem`
    (qspecl_then [`aid`,`off`,`sz0`,`i`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]
QED

Finalise body_append_local_nonword_frag_full

Theorem append_subscript_operand_var[local]:
  (compile_mapping_subscript bop kop sa = (op,sb) \/
   compile_array_subscript bop kop is_dyn arr_count ws elem_sz is_signed loader sa = (op,sb)) ==>
  ?x. op = Var x
Proof
  simp[compile_mapping_subscript_def,compile_array_subscript_def,LET_THM,
       comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  drule emitHelperPropsTheory.emitted_insts_emit_op >> metis_tac[]
QED

Theorem append_nested_target_operand_var[local]:
  ((?bt idx. t = SubscriptTarget bt idx) \/
   (?bt fld. t = AttributeTarget bt fld)) /\
  compile_get_target_ptr compile_expr cenv t sa = (r,sb) ==>
  ?x. FST r = Var x
Proof
  strip_tac >> gvs[]
  >- (qpat_x_assum `compile_get_target_ptr _ _ (SubscriptTarget _ _) _ = _` mp_tac >>
      simp[Once compile_get_target_ptr_def,comp_bind_def,comp_return_def] >>
      pairarg_tac >> simp[] >>
      Cases_on `SND (SND result)` >> simp[]
      >- (simp[comp_bind_def,comp_return_def] >>
          rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
          irule append_subscript_operand_var >> metis_tac[])
      >> rename1 `SND (SND result) = SOME pty` >> Cases_on `pty` >>
      simp[comp_bind_def,comp_return_def] >>
      rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
      irule append_subscript_operand_var >> metis_tac[]) >>
  drule targetPlaceSimCasesBaseTheory.compile_get_target_ptr_attr >>
  strip_tac >> gvs[] >> drule emitHelperPropsTheory.emitted_insts_emit_op >> metis_tac[]
QED

Theorem append_resolved_rhs_code_full[local]:
  stmt_env cenv lctx ty (Append bt e) sa = (cenv,sf) /\
  compile_get_target_ptr compile_expr cenv bt sa =
    ((bop,SOME loc,SOME (ValPT (ArrayT elem (Dynamic cap)))),sp) /\
  fn_has_code sp sf func ==>
  ?vop sm. lower_value compile_expr cenv elem e sp = (vop,sm) /\
    ci_mono sp sm /\ ci_mono sm sf /\
    fn_has_code sp sm func /\ fn_has_code sm sf func /\
    (if is_word_type elem then
      compile_dynarray_append cenv bop vop (word_scale loc)
        (elem_size_in_location cenv loc elem) elem (lowered_value_type cenv e)
        cap T loc sm = ((),sf)
    else ?tmp sc sd. compile_alloc_buffer (type_memory_bytes cenv elem) sm = (tmp,sc) /\
      compile_store_memory cenv vop tmp.buf_operand elem
        (lowered_value_type cenv e) sc = ((),sd) /\
      compile_dynarray_append cenv bop tmp.buf_operand (word_scale loc)
        (elem_size_in_location cenv loc elem) elem elem cap F loc sd = ((),sf))
Proof
  strip_tac >> Cases_on `is_word_type elem`
  >- (drule_all_then strip_assume_tac stmtSimAppendResolvedTheory.append_resolved_word_code_parts >>
      `ci_mono sp sm /\ ci_mono sm sf` by
        metis_tac[ci_mono_lower_value_compile_expr,ci_mono_compile_dynarray_append,pairTheory.SND] >>
      qexistsl_tac [`vop`,`sm`] >> simp[] >>
      irule fragExecTheory.fn_has_code_split >> fs[ci_mono_def]) >>
  drule_all_then strip_assume_tac append_resolved_copy_code_parts >>
  `ci_mono sp sm /\ ci_mono sm sf` by
    metis_tac[ci_mono_lower_value_compile_expr,ci_mono_compile_dynarray_append,
      ci_mono_compile_alloc_buffer,ci_mono_compile_store_memory,
      exprLoweringPropsTheory.ci_mono_trans,pairTheory.SND] >>
  qexistsl_tac [`raw`,`sm`] >> simp[] >>
  `fn_has_code sp sm func /\ fn_has_code sm sf func` by
    (irule fragExecTheory.fn_has_code_split >> fs[ci_mono_def]) >>
  simp[] >> qexistsl_tac [`tmp`,`sc`,`sd`] >> simp[]
QED

Theorem append_memory_word_uses_store[local]:
  is_word_type elem ==>
  compile_dynarray_append cenv bop vop 32 stride elem sty cap T LocMemory =
  compile_dynarray_append cenv bop vop 32 stride elem elem cap F LocMemory
Proof
  strip_tac >> rw[FUN_EQ_THM,compile_dynarray_append_def,LET_THM,
    contextTheory.compile_ptr_store_def,contextTheory.compile_store_memory_def,
    comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
  rpt (pairarg_tac >> simp[])
QED

Theorem append_nested_word_input[local]:
  expr_body_pre cenv cx env e es /\
  bind (eval_expr cx e) (read_result cx) es = (INL v,ee) /\
  expr_post H ctx func cenv cx e es sa sb s0 ee v vop s /\
  lower_value compile_expr cenv elem e sa = (vop,sb) /\
  ptr_val_ok cx (post_value_type cenv e) v vop G tn s /\
  is_word_type elem /\ type_widens_to env.type_defs (expr_type e) elem /\
  evaluate_type (get_tenv cx) elem = SOME tv ==>
  value_has_type tv v /\ val_wf tv v /\ type_memory_size tv = 32 /\
  type_slot_size tv = 1 /\ eval_operand vop s = SOME (typed_val_to_w256 tv v) /\
  op_taint tn vop = {} /\ (!x. vop = Var x ==> not_fresh_at sb x)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_type e = elem` by metis_tac[compileEnvTheory.type_widens_to_word] >>
  `is_word_type (expr_type e)` by simp[] >>
  `post_value_type cenv e = expr_type e` by metis_tac[loweringPostsTheory.post_value_type_word] >>
  `value_has_type tv v` by
    (drule_all (SRULE [SF ETA_ss] exprSimSourceTheory.expr_body_pre_word_type_result) >>
     simp[] >> metis_tac[]) >>
  `eval_operand vop s = SOME (typed_val_to_w256 tv v)` by
    metis_tac[exprSimPrecompilesTheory.expr_post_typed_stack_operand] >>
  `(!x. vop = Var x ==> not_fresh_at sb x)` by
    drule_all_then strip_assume_tac exprSimSourceTheory.expr_body_pre_lower_value_word_shape >>
  simp[] >> metis_tac[cj 1 valueEncodingTypingTheory.value_has_type_val_wf,
    entryDecodeStaticPropsTheory.word_type_memory_size,exprSimUnwrapTheory.word_type_slot_size,
    bodyPtrDefsTheory.ptr_val_ok_def]
QED

Theorem append_rhs_scope_facts_mods[local]:
  expr_body_pre_mods mods cenv cx env e (mid with gas_obs := gs) ==>
  state_well_typed mid /\ state_well_typed (mid with gas_obs := gs) /\
  popped_keys_indexed mid.scopes /\ functions_well_typed cx /\
  context_well_typed cx /\ accounts_well_typed mid.accounts /\
  env_consistent env cx (mid with gas_obs := gs) /\ well_typed_expr env e
Proof
  simp[expr_body_pre_mods_def, expr_sim_inv_mods_def]
QED

Theorem append_nested_memory_rhs_view_mods[local]:
  expr_body_pre_mods mods cenv cx env e (mid with gas_obs := gs) /\
  (0 < sz ==> lo <= w2n basew) /\
  bind (eval_expr cx e) (read_result cx) (mid with gas_obs := gs) =
    (INL v,fin) /\
  expr_post H ctx func cenv cx e mid sp sm s fin v vop u /\
  stmt_state_rel H ctx func cenv cx mid s /\
  ghost_inv_at D lo d cenv cx mid G tn s /\
  ghost_inv_at D lo d cenv cx fin Gf tf u /\
  ghost_kept_at lo cenv mid sp G tn s Gf tf /\
  local_ptrs_reserved cenv sp /\
  lookup_scopes id mid.scopes = SOME initial /\
  evaluate_subscripts initial.type initial.value path = INL v0 /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var root) sz) /\
  lookup_var root s = SOME basew /\
  mem_path_offset initial.type path = SOME (k,ArrayTV tv (Dynamic cap)) /\
  bp = basew + n2w k ==>
  ?entry vs.
    lookup_scopes id fin.scopes = SOME entry /\ entry.type = initial.type /\
    subscripts_type entry.type path = SOME (ArrayTV tv (Dynamic cap)) /\
    read_memory_path entry path = INL (ArrayV (DynArrayV vs)) /\
    value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
    lo <= w2n bp /\ w2n bp + 32+cap*type_memory_size tv <= u.vs_alloca_next /\
    !mem. mem_agree_outside tf.t_mem u.vs_memory mem ==>
      val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n bp) mem
Proof
  strip_tac >>
  drule_then strip_assume_tac append_rhs_scope_facts_mods >>
  drule_then assume_tac exprBodyPreCallSafetyPropsTheory.expr_body_pre_mods_call_evaluation_safe >>
  qpat_assum `bind _ _ _ = (INL v,fin)`
    (mp_then Any mp_tac vyperStatePreservationTheory.bind_split) >>
  simp[sumTheory.sum_distinct] >> strip_tac >>
  drule vyperStateTheory.read_result_state >>
  disch_then (SUBST_ALL_TAC o SYM) >>
  `typed_scope_transition (mid with gas_obs := gs) fin` by
    (irule (cj 2 (cj 5 vyperTypeEvalSoundnessTheory.eval_scc_type_sound_mutual)) >>
     qpat_assum `eval_expr cx e _ = _` (irule_at Any) >> qexists_tac `env` >> simp[]) >>
  `typed_scope_transition mid fin` by
    (irule vyperTypeEvalProofsTheory.typed_scope_transition_trans >>
     qexists_tac `mid with gas_obs := gs` >>
     simp[vyperTypeEvalProofsTheory.typed_scope_transition_scopes]) >>
  drule exprSimPropsTheory.mem_path_offset_sound >> strip_tac >>
  `live_memory_result mid (PlaceR (MemoryPlace id path))` by
    (irule vyperTypeEvalProofsTheory.live_memory_result_fresh >>
     goal_assum (drule_at Any) >>
     simp[vyperPlaceResultTypingTheory.memory_eval_path_def] >> metis_tac[]) >>
  drule_all_then assume_tac vyperTypeEvalProofsTheory.live_memory_result_transport >>
  qpat_assum `typed_scope_transition mid fin`
    (strip_assume_tac o REWRITE_RULE [vyperTypeEvalProofsTheory.typed_scope_transition_def]) >>
  drule_all_then strip_assume_tac vyperPlaceResultTypingTheory.scope_pop_trace_lookup >>
  drule_then strip_assume_tac vyperPlaceResultTypingTheory.entry_pop_trace_metadata >>
  drule_all_then assume_tac vyperPlaceResultTypingTheory.entry_events_valid >>
  `state_well_typed fin` by
    (drule_all (SRULE [SF ETA_ss] bodySimStmtFactsTheory.expr_body_pre_eval_mods) >>
     simp[expr_sim_inv_mods_def]) >>
  `value_has_type initial.type initial.value /\ well_formed_type_value initial.type /\
   value_has_type entry'.type entry'.value` by
    metis_tac[vyperTypeStatePreservationTheory.lookup_scopes_state_well_typed_value_has_type,
      vyperTypeEnvTheory.scope_well_typed_lookup_scopes,
      vyperTypeInvariantsTheory.state_well_typed_def] >>
  `local_ptrs_rel func cenv mid.scopes s` by
    metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca] >>
  drule_all nameLoweringPropsTheory.local_ptrs_rel_value >>
  simp[venomStateTheory.eval_operand_def] >> strip_tac >>
  qpat_assum `expr_post H ctx func cenv cx e mid sp sm s fin v vop u`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [expr_post_def]) >>
  `not_fresh_at sp root` by metis_tac[local_ptrs_reserved_def] >>
  `lookup_var root u = SOME basew` by
    (qpat_assum `!x w. not_fresh_at sp x /\ lookup_var x s = SOME w ==> _`
      (qspecl_then [`root`,`basew`] mp_tac) >> simp[]) >>
  `w2n basew + sz <= u.vs_alloca_next` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx fin u`
       (assume_tac o CONJUNCT1 o MATCH_MP stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >>
     qpat_assum `local_ptrs_rel func cenv fin.scopes u` (fn ptrs =>
       qpat_assum `lookup_scopes id fin.scopes = SOME entry'` (fn entry =>
         qpat_assum `FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var root) sz)` (fn loc =>
           mp_tac (MATCH_MP nameLoweringPropsTheory.local_ptrs_rel_value (LIST_CONJ [ptrs,entry,loc]))))) >>
     simp[venomStateTheory.eval_operand_def]) >>
  `w2n bp = w2n basew + k` by
    (`s.vs_alloca_next < dimword (:256)` by
       metis_tac[stateRelProjTheory.stmt_state_rel_alloca_room,exprLoweringPropsTheory.alloca_room_next_lt] >>
     `k < dimword (:256) /\ w2n basew+k < dimword (:256)` by decide_tac >>
     `basew + n2w k = (n2w (w2n basew + k):bytes32)` by
       simp[GSYM wordsTheory.word_add_n2w] >>
     pure_asm_rewrite_tac [wordsTheory.w2n_n2w] >>
     irule arithmeticTheory.LESS_MOD >> first_assum ACCEPT_TAC) >>
  `local_region cenv mid.scopes s id (w2n basew) sz` by
    simp[local_region_def] >>
  `popped_kept cenv mid fin s u` by fs[expr_post_def,locals_kept_def] >>
  `?v1. read_result cx (PlaceR (MemoryPlace id path)) fin = (INL v1,fin) /\
    value_has_type (ArrayTV tv (Dynamic cap)) v1 /\
    well_formed_type_value (ArrayTV tv (Dynamic cap)) /\
    k + type_memory_size (ArrayTV tv (Dynamic cap)) <= sz /\
    !mem. mem_agree_outside tf.t_mem u.vs_memory mem ==>
      val_in_memory (ArrayTV tv (Dynamic cap)) v1 (w2n bp) mem` by
    (irule bodyFullSubscriptCoveredRowTheory.subscript_covered_row_read_robust >>
     qpat_assum `entry_pop_trace initial _ entry'` (irule_at Any) >>
     qpat_assum `local_region cenv mid.scopes s id _ sz` (irule_at Any) >>
     qpat_assum `ghost_inv_at D lo d cenv cx mid G tn s` (irule_at Any) >>
     qpat_assum `ghost_inv_at D lo d cenv cx fin Gf tf u` (irule_at Any) >>
     qpat_assum `evaluate_subscripts initial.type initial.value path = INL v0` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo cenv mid sp G tn s Gf tf` (irule_at Any) >>
     simp[wordArgsPtrTheory.ghost_kept_at_refl] >> fs[]) >>
  `0 < sz` by (fs[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
  `lo <= w2n basew` by metis_tac[] >>
  `?values. v1 = ArrayV (DynArrayV values)` by
    (qpat_assum `value_has_type (ArrayTV tv (Dynamic cap)) v1` mp_tac >>
     Cases_on `v1` >> simp[NoAsms,vyperTypingTheory.value_has_type_def] >>
     rename1 `ArrayV arr` >> Cases_on `arr` >>
     simp[NoAsms,vyperTypingTheory.value_has_type_def]) >>
  qpat_x_assum `v1 = ArrayV (DynArrayV values)` SUBST_ALL_TAC >>
  qexists_tac `values` >> simp[] >>
  conj_tac >-
    (Cases_on `read_memory_path entry' path` >>
     qpat_x_assum `read_result cx (PlaceR (MemoryPlace id path)) fin = _` mp_tac >>
     simp[read_result_def,read_place_def,get_scopes_def,bind_def,
       lift_option_type_def,lift_sum_def,return_def,raise_def]) >>
  qpat_assum `bp = basew + n2w k` (SUBST1_TAC o SYM) >>
  simp[] >>
  qpat_assum `k + type_memory_size (ArrayTV tv (Dynamic cap)) <= sz`
    (assume_tac o REWRITE_RULE [valueEncodingTheory.type_memory_size_def]) >>
  decide_tac
QED

Theorem append_typed_target_place[local]:
  !t cenv cx env es vt.
    expr_sim_inv cenv cx env es /\ ~immutable_root cx t /\
    type_place_target env t = SOME vt ==>
    target_place_type cenv t = SOME (value_type_place vt)
Proof
  recInduct targetPlaceSimCasesBaseTheory.base_assignment_target_induct >> rpt conj_tac
  >- suspend "name"
  >- suspend "top"
  >- suspend "subscript" >>
  suspend "attribute"
QED

Resume append_typed_target_place[name]:
  rpt gen_tac >>
  simp[vyperTypeEnvTheory.type_place_target_NameTarget,
       allocLimitsTheory.target_place_type_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  gvs[exprLoweringTheory.value_type_place_def] >>
  qpat_assum `expr_sim_inv cenv cx env es`
    (mp_tac o REWRITE_RULE [expr_sim_inv_def]) >>
  simp[] >> metis_tac[]
QED

Resume append_typed_target_place[top]:
  gen_tac >> PairCases_on `nsid` >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  rename1 `type_place_target env (TopLevelNameTarget (src,id)) = SOME vt` >>
  `!ts. get_module_code cx src = SOME ts ==> find_var_decl_by_name id ts <> NONE` by
    fs[targetPlaceSimTheory.immutable_root_def,targetPlaceSimTheory.target_root_def] >>
  drule_all_then strip_assume_tac targetPlaceSimTheory.toplevel_target_decl >>
  drule_all_then strip_assume_tac targetPlaceSimTheory.toplevel_target_env >>
  gvs[allocLimitsTheory.target_place_type_def,exprLoweringTheory.value_type_place_def]
QED

Resume append_typed_target_place[subscript]:
  simp[vyperTypeEnvTheory.type_place_target_SubscriptTarget,
       targetPlaceSimTheory.immutable_root_def,targetPlaceSimTheory.target_root_def] >>
  rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  rename1 `subscript_vtype base_vt (expr_type key) = SOME vt` >>
  Cases_on `base_vt` >> gvs[exprLoweringTheory.value_type_place_def,
      allocLimitsTheory.target_place_type_def,vyperTypeSystemTheory.subscript_vtype_def,AllCaseEqs()] >>
  rename1 `subscript_vtype (Type ty) _ = _` >> Cases_on `ty` >>
  gvs[vyperTypeSystemTheory.subscript_vtype_def,AllCaseEqs(),
     exprLoweringTheory.value_type_place_def]
QED

Resume append_typed_target_place[attribute]:
  simp[vyperTypeEnvTheory.type_place_target_AttributeTarget,
       targetPlaceSimTheory.immutable_root_def,targetPlaceSimTheory.target_root_def] >>
  rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def,vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
  Cases_on `tgt_ty` >> gvs[vyperTypeSystemTheory.attribute_type_def] >>
  `attribute_type (get_tenv cx) (StructT p) s = SOME ty` by
    simp[vyperTypeSystemTheory.attribute_type_def] >>
  drule_all_then strip_assume_tac stmtSimAssignAttrTheory.attribute_type_struct_field >>
  gvs[allocLimitsTheory.target_place_type_def,exprLoweringTheory.value_type_place_def]
QED

Finalise append_typed_target_place[local]

Theorem body_append_nested_frag_full[local]:
  !cx t e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv
    env env' ret_ty lctx RetQ es elem cap.
  (!s p mid. eval_target_place cx t s = (INL p,mid) ==>
     body_expr_full_ok cx e) /\
  body_base_target_full_ok cx t /\
  ((?base key. t = SubscriptTarget base key) \/
   (?base fld. t = AttributeTarget base fld)) /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (Append t e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Append t e) ==> occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
  locals_alloc_ok cenv env /\
  type_stmt env ret_ty (Append t e) = SOME env' /\
  type_place_target env t = SOME (Type (ArrayT elem (Dynamic cap))) /\
  stmt_exprs_ok cenv (Append t e) /\
  call_evaluation_safe cx (int_calls_stmt (Append t e)) /\
  frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ cenv ret_ty ==>
  stmt_frag_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (Append t e))
    (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Append t e)))
    (eval_stmt cx (Append t e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `!raw cs ce. compile_get_target_ptr compile_expr cenv t cs = (raw,ce) ==>
      ?x. FST raw = Var x` by
    (rpt strip_tac >> irule append_nested_target_operand_var >>
     goal_assum (drule_at (Pat `compile_get_target_ptr _ _ _ _ = _`)) >>
     first_assum ACCEPT_TAC) >>
  `~(?nid. t = TopLevelNameTarget nid)` by fs[] >>
  qpat_x_assum `(?bt idx. t = SubscriptTarget bt idx) \/
    (?bt fld. t = AttributeTarget bt fld)` kall_tac >>
  drule_all body_append_typed_pre >> strip_tac >> gvs[] >>
  rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all stmtSimAppendResolvedTheory.append_resolved_target_prefix >>
  strip_tac >> gvs[] >>
  rename1 `compile_get_target_ptr compile_expr cenv t sa = (r,sp)` >>
  qpat_assum `!r a b. compile_get_target_ptr _ _ _ a = (r,b) ==> _`
    (qspecl_then [`r`,`sa`,`sp`] mp_tac) >> simp[] >> strip_tac >>
  irule append_return_buf_sep >>
  asm_simp_tac bool_ss [] >>
  irule gas_outcome_full_initial_domain >>
  simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >> disch_tac >>
  drule_all body_target_place_sim_full >>
  disch_then (qspecl_then [`DF`, `lo`, `d`, `PG`, `func`, `shadow_func`]
    assume_tac) >>
  `compile_get_target_ptr compile_expr (gas_shadow_env T cenv) (gas_shadow_target t) shadow_sa =
      (r,SND (compile_get_target_ptr compile_expr (gas_shadow_env T cenv) (gas_shadow_target t) shadow_sa)) /\
   gas_shadow_state sp
     (SND (compile_get_target_ptr compile_expr (gas_shadow_env T cenv) (gas_shadow_target t) shadow_sa))` by
    (Cases_on `compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
                (gas_shadow_target t) shadow_sa` >> simp[] >>
     irule bodyFullSharedTheory.gas_shadow_step >>
     qpat_assum `compile_get_target_ptr _ _ t sa = _` (irule_at Any) >>
     qpat_assum `compile_get_target_ptr _ _ (gas_shadow_target t) shadow_sa = _`
       (irule_at Any) >>
     simp[] >> irule gas_shadow_stmt_get_target_ptr_env) >>
  qmatch_asmsub_abbrev_tac `gas_shadow_state sp shadow_sp` >>
  `ci_mono shadow_sa shadow_sp /\ ci_mono shadow_sp shadow_sb /\
   fn_has_code shadow_sa shadow_sp shadow_func /\
   fn_has_code shadow_sp shadow_sb shadow_func` by
    (qpat_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _` mp_tac >>
     rewrite_tac[gasShadowTheory.gas_shadow_stmt_def] >> strip_tac >>
     drule_all stmtSimAppendResolvedTheory.append_resolved_target_prefix >>
     simp[] >> metis_tac[]) >>
  `gas_admissible (eval_target_place cx t) target_place_res_ok es` by
    (rw[gasContextTheory.gas_admissible_def] >> Cases_on `res`
     >- simp[targetPlaceSimCasesTheory.target_place_res_ok_def] >>
     rename1 `eval_target_place cx t _ = (INR ex,ee)` >>
     `no_control_exc ex` by metis_tac[vyperExprNoControlTheory.eval_target_place_no_control] >>
     `eval_stmt cx (Append t e) (es with gas_obs := gs) = (INR ex,ee)` by
       simp[Once vyperInterpreterTheory.evaluate_def, bind_def] >>
     `stmt_res_ok lctx (INR ex)` by
       metis_tac[gasContextTheory.gas_admissible_def] >>
     gvs[stmtSimDefsTheory.stmt_res_ok_def, targetPlaceSimCasesTheory.target_place_res_ok_def,
         vyperExprNoControlTheory.no_control_exc_def]) >>
  qpat_x_assum `target_place_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[bodyFullTargetDefsTheory.target_place_sim_full_def] >>
  disch_then (qspecl_then [`st0`, `ArrayT elem (Dynamic cap)`,
    `sa`, `sp`, `shadow_sa`, `shadow_sp`, `r`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> fs[loweringPostsTheory.ret_pc_ok_def] >>
    first_assum ACCEPT_TAC)) >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ Q1 R1` >>
  pure_once_rewrite_tac[vyperInterpreterTheory.evaluate_def] >>
  pure_rewrite_tac[GSYM bind_assoc] >>
  irule gas_outcome_full_bind_all_path >> BETA_TAC >> rpt conj_tac
  >~ [`storage_trace_frame (eval_target_place _ _)`]
  >- simp[cj 8 vyperStorageTraceTheory.evaluate_storage_trace_frame]
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      simp[cj 5 vyperStorageTraceTheory.evaluate_storage_trace_frame,
           vyperStorageTraceTheory.storage_trace_frame_read_result,
           vyperStorageTraceTheory.storage_trace_frame_append_place,
           vyperStorageTraceTheory.storage_trace_frame_bind])
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_place >>
      goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_place >> simp[]) >>
  qexists_tac `\H res ee G tn u. Q1 H res ee G tn u /\ ~u.vs_halted /\ ee.gas_obs = []` >>
  reverse conj_tac
  >- (irule gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ Q1 R1` (irule_at Any) >>
      BETA_TAC >> conj_tac >- simp[] >> suspend "target_exit") >>
  suspend "target_success"
QED

Resume body_append_nested_frag_full[target_exit]:
  simp[Abbr `R1`] >> rpt gen_tac >> strip_tac >>
  Cases_on `res` >> Cases_on `r'` >> gvs[exprSimDefsTheory.expr_exit_def] >>
  rename1 `INR exc` >> Cases_on `exc` >>
  gvs[exprSimDefsTheory.expr_exit_def, stmt_exit_ptr_def,
      exprSimDefsTheory.halt_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >>
  gvs[exprSimDefsTheory.expr_exit_def, stmt_exit_ptr_def]
QED

Resume body_append_nested_frag_full[target_success]:
  qx_genl_tac [`target_marks`,`place_res`,`mid`,`Gm`,`tm`,`target_state`] >>
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
    gas_origin_ptr_path _ (s0,G0,tn0) target_marks (OK target_state,Gm,tm)`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `!fn inst state. frag_reachable ctx func target_state fn inst state ==>
    dalloca_fmp_headroom inst state` by
    (`!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
       metis_tac[bodyFullIfExpReachTheory.body_inv_no_phi] >>
     qpat_assum `gas_origin_ptr_path _ _ _ (OK target_state,Gm,tm)` (fn path =>
       qpat_assum `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` (fn no_phi =>
         qpat_assum `!fn inst st. frag_reachable ctx func s0 fn inst st ==> dalloca_fmp_headroom inst st`
           (ACCEPT_TAC o MATCH_MP bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom
             o CONJ path o CONJ no_phi)))) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> Q1 H place_res mid Gm tm target_state /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> simp[Abbr `Q1`,NoAsms] >>
  disch_then (CONJUNCTS_THEN2
    (qx_choose_then `p` (CONJUNCTS_THEN2 SUBST_ALL_TAC
       (map_every assume_tac o CONJUNCTS))) (map_every assume_tac o CONJUNCTS)) >>
  disj1_tac >> qexists_tac `p` >> simp[] >>
  `eval_target_place cx t
      (es with gas_obs := gas_explicit target_marks s0.vs_gas_readings) = (INL p,mid)` by
    (`mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
     qpat_assum `!tail. eval_target_place cx t _ = (INL p,_)`
       (qspec_then `[]` mp_tac) >>
     qpat_assum `mid with gas_obs := [] = mid`
       (fn th => rewrite_tac[APPEND_NIL,th])) >>
  `target_pre cenv cx env t
      (es with gas_obs := gas_explicit target_marks s0.vs_gas_readings)` by
    simp[targetPlaceSimTheory.target_pre_def,exprSimHypsDefsTheory.expr_sim_inv_gas_obs] >>
  `expr_body_pre cenv cx env e
      (es with gas_obs := gas_explicit target_marks s0.vs_gas_readings)` by
    fs[exprSimSourceTheory.expr_body_pre_gas_obs] >>
  `expr_body_pre cenv cx env e mid` by
    metis_tac[bodyAppendResolvedPreTheory.append_resolved_rhs_body_pre] >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (irule body_const_cells_agree_target >>
     qpat_assum `eval_target_place cx t (_ with gas_obs := _) = (INL p,mid)`
       (irule_at (Pat `eval_target_place _ _ _ = _`)) >>
     simp[]) >>
  `?trace. mid.storage_trace = es.storage_trace ++ trace` by
    (`storage_trace_frame (eval_target_place cx t)` by
       simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
     qpat_assum `storage_trace_frame (eval_target_place cx t)` (fn fr =>
       qpat_assum `eval_target_place cx t (_ with gas_obs := _) = (INL p,mid)`
         (strip_assume_tac o MATCH_MP vyperStorageTraceTheory.storage_trace_frame_prefix o CONJ fr)) >>
     qexists_tac `observations` >> fs[]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) es.storage_trace` by
    metis_tac[gasOutcomeFullTheory.valid_horizon_append] >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx es s0` by
    metis_tac[] >>
  `MAP FDOM mid.scopes = MAP FDOM es.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_target_place_preserves_scopes_dom >> simp[]) >>
  `alloca_frame cenv es sa s0 cenv mid target_state` by
    (irule (INST_TYPE [alpha |-> ``:256``] stmtSimDefsTheory.target_post_alloca_frame) >>
     qpat_assum `target_post (storage_trace_horizon _) ctx func cenv cx es sa sp s0 mid _ _ r target_state`
       (irule_at Any) >> simp[]) >>
  qpat_assum `target_post _ _ _ _ _ _ _ _ _ mid (PlaceR p) _ r target_state`
    (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.target_post_def]) >>
  PairCases_on `r` >> fs[exprLoweringTheory.value_type_place_def] >>
  `?loc. r1 = SOME loc` by (Cases_on `p` >> fs[place_ptr_rel_def]) >>
  gvs[] >>
  `body_expr_full_ok cx e` by metis_tac[] >>
  `gas_admissible (bind (bind (eval_expr cx e) (read_result cx)) (append_place cx p))
     (stmt_res_ok lctx) mid` by suspend "rhs_admissible" >>
  suspend "rhs"
QED

Resume body_append_nested_frag_full[rhs_admissible]:
  `gas_admissible (bind (eval_target_place cx t)
       (\p. bind (bind (eval_expr cx e) (read_result cx)) (append_place cx p)))
       (stmt_res_ok lctx) es` by
    (qpat_assum `gas_admissible (eval_stmt _ _) _ _`
       (mp_tac o ONCE_REWRITE_RULE [vyperInterpreterTheory.evaluate_def]) >>
     pure_rewrite_tac[GSYM bind_assoc] >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >> REWRITE_TAC []) >>
  drule_all (SRULE [SF ETA_ss] stmtSimForRoundsTheory.gas_admissible_bind_tail) >>
  simp[evaluation_state_component_equality]
QED

Resume body_append_nested_frag_full[rhs]:
  drule_all_then strip_assume_tac append_resolved_rhs_code_full >>
  qpat_assum `stmt_env _ _ _ (gas_shadow_stmt _) shadow_sa = _`
    (mp_then (Pos hd) mp_tac (SRULE [GSYM gasShadowTheory.gas_shadow_stmt_def]
       (Q.INST [`bt` |-> `gas_shadow_target t`, `e` |-> `gas_shadow_expr e`,
         `func` |-> `shadow_func`] append_resolved_rhs_code_full))) >>
  simp[] >>
  disch_then (qspec_then `shadow_func` (drule_then strip_assume_tac)) >>
  rename1 `lower_value _ _ _ (gas_shadow_expr e) shadow_sp = (shadow_op,shadow_sm)` >>
  `shadow_op = vop /\ gas_shadow_state sm shadow_sm` by
    (irule bodyFullSharedTheory.gas_shadow_step >>
     qpat_assum `lower_value _ _ _ e sp = _` (irule_at Any) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr e) shadow_sp = _` (irule_at Any) >>
     simp[] >> irule gas_shadow_stmt_lower_value_env) >>
  qpat_x_assum `shadow_op = vop` SUBST_ALL_TAC >>
  `local_ptrs_reserved cenv sp` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> fs[ci_mono_def]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sp x` by
    metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh] >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sp x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sp x)` by
    metis_tac[loweringPostsTheory.ret_pc_ok_def] >>
  `return_buf_frame d cenv sp target_state` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`,`s0`,`sa`] >> fs[ci_mono_def,loweringPostsTheory.target_post_def]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok mid` by
    (irule expr_body_pre_gas_admissible >> goal_assum (drule_at Any)) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx elem e mid` by
    (qpat_assum `body_expr_full_ok cx e` (mp_tac o ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
     qpat_assum `body_inv tops ctx cenv cx` mp_tac >>
     qpat_assum `shadow_body_inv tops ctx shadow_ctx` mp_tac >>
     qpat_assum `body_const_cells_agree [(NONE,tops)] cx env mid` mp_tac >>
     qpat_assum `expr_body_pre cenv cx env e mid` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid target_state /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx mid Gm tm target_state` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> target_post H _ _ _ _ _ _ _ _ mid _ _ _ target_state /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >-
       (qpat_assum `mid.storage_trace = _` (fn eq => pure_rewrite_tac [GSYM eq]) >>
        first_assum ACCEPT_TAC)) >>
     disch_then (CONJUNCTS_THEN2
       (map_every assume_tac o CONJUNCTS o REWRITE_RULE [loweringPostsTheory.target_post_def])
       assume_tac) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`,`sp`,`sm`,`shadow_sp`,`shadow_sm`,`vop`,
    `target_state`,`Gm`,`tm`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac
    `gas_outcome_full _ _ _ _ (bind (eval_expr cx e) (read_result cx)) _ rhsQ rhsR` >>
  irule gas_outcome_full_bind_all >>
  conj_tac >- simp[vyperStorageTraceTheory.storage_trace_frame_append_place] >>
  conj_tac >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
    goal_assum (drule_at Any) >> gvs[]) >>
  conj_tac >- metis_tac[gasExemptCertTheory.gas_exempt_cert_error_value] >>
  conj_tac >- simp[vyperStorageTraceTheory.storage_trace_frame_bind,
    vyperStorageTraceTheory.evaluate_storage_trace_frame,
    vyperStorageTraceTheory.storage_trace_frame_read_result] >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ rhsQ rhsR` mp_tac >>
  disch_then (fn th =>
    irule_at (Pos last) gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
    irule_at (Pos hd) th) >>
  qexists_tac `\H res ee G tn t. rhsQ H res ee G tn t /\ ~t.vs_halted` >>
  conj_tac >- simp[] >>
  conj_tac >- suspend "rhs_exit" >>
  simp_tac (srw_ss()) [Abbr `rhsQ`] >> suspend "rhs_success"
QED

Resume body_append_nested_frag_full[rhs_exit]:
  simp[Abbr `rhsR`] >> rpt gen_tac >> strip_tac >>
  Cases_on `res` >> Cases_on `r` >> gvs[exprSimDefsTheory.expr_exit_def] >>
  rename1 `INR exc` >> Cases_on `exc` >>
  qpat_x_assum `expr_exit _ _` mp_tac >>
  qpat_x_assum `halt_exit _ _ _ _ _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  gvs[exprSimDefsTheory.expr_exit_def, stmt_exit_ptr_def,
      exprSimDefsTheory.halt_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >>
  gvs[exprSimDefsTheory.expr_exit_def, stmt_exit_ptr_def]
QED

Resume body_append_nested_frag_full[rhs_success]:
  qx_genl_tac [`marks`,`res`,`rhs_state`,`Gr`,`trhs`,`u`] >>
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon rhs_state.storage_trace)
     rhs_state.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H rhs_state.storage_trace ==> _`
    (qspec_then `storage_trace_horizon rhs_state.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (CONJUNCTS_THEN2
    (qx_choose_then `v` (CONJUNCTS_THEN2 SUBST_ALL_TAC
       (map_every assume_tac o CONJUNCTS))) (map_every assume_tac o CONJUNCTS)) >>
  disj1_tac >> qexists_tac `v` >> simp[] >>
  qabbrev_tac `gas_in = mid with gas_obs :=
    gas_explicit marks target_state.vs_gas_readings ++ rhs_state.gas_obs` >>
  `bind (eval_expr cx e) (read_result cx) gas_in = (INL v,rhs_state)` by
    (qpat_assum `!tail. bind (eval_expr cx e) (read_result cx) _ = _`
       (qspec_then `rhs_state.gas_obs` mp_tac) >> simp[Abbr `gas_in`]) >>
  `expr_body_pre cenv cx env e gas_in` by
    fs[Abbr `gas_in`,exprSimSourceTheory.expr_body_pre_gas_obs] >>
  `expr_sim_inv cenv cx env rhs_state /\
   value_runtime_typed env (expr_type e) v` by
    (drule_at (Pat `bind _ _ _ = _`)
        (SRULE [SF ETA_ss] exprSimSourceTheory.expr_body_pre_eval) >>
     disch_then (qspecl_then [`cenv`,`env`] mp_tac) >>
     simp[vyperTypeExprResultTheory.expr_result_typed_def,
          vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
          vyperTypeInvariantsTheory.value_result_typed_def,
          vyperTypeExprSoundnessTheory.value_runtime_typed_def]) >>
  `!H. valid_horizon cx st0 H rhs_state.storage_trace ==>
     expr_post H ctx func cenv cx e mid sp sm target_state rhs_state v vop u /\
     ghost_inv_at (DF H) lo d cenv cx rhs_state Gr trhs u` by
    (qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H rhs_state.storage_trace ==> (?v. _) /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >> fs[]) >>
  `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
    (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
     simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
          vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
  `?trace. rhs_state.storage_trace = mid.storage_trace ++ trace` by
    (qpat_assum `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` (fn frame =>
      qpat_assum `bind (eval_expr cx e) (read_result cx) gas_in = (INL v,rhs_state)` (fn eval =>
        mp_tac (MATCH_MP vyperStorageTraceTheory.storage_trace_frame_prefix (CONJ frame eval)))) >>
     simp[Abbr `gas_in`]) >>
  `!H. valid_horizon cx st0 H rhs_state.storage_trace ==>
       valid_horizon cx st0 H mid.storage_trace` by
    metis_tac[gasOutcomeFullTheory.valid_horizon_append] >>
  `gas_admissible (append_place cx p v) (stmt_res_ok lctx) rhs_state` by
    (drule_all (SRULE [SF ETA_ss] stmtSimForRoundsTheory.gas_admissible_bind_tail) >>
     simp[evaluation_state_component_equality]) >>
  `expr_post (storage_trace_horizon rhs_state.storage_trace) ctx func cenv cx e
    gas_in sp sm target_state rhs_state v vop u` by
    (qpat_assum `!H. valid_horizon cx st0 H rhs_state.storage_trace ==>
       expr_post H _ _ _ _ _ mid _ _ _ rhs_state _ _ _ /\ _`
       (qspec_then `storage_trace_horizon rhs_state.storage_trace`
         (drule_then strip_assume_tac)) >>
     simp[Abbr `gas_in`,exprSimExtract32PostTheory.extract32_expr_post_start_gas_obs]) >>
  suspend "rhs_frame"
QED

Resume body_append_nested_frag_full[rhs_frame]:
  `valid_horizon cx st0 (storage_trace_horizon rhs_state.storage_trace)
     mid.storage_trace` by metis_tac[] >>
  `stmt_state_rel (storage_trace_horizon rhs_state.storage_trace)
     ctx func cenv cx mid target_state` by metis_tac[] >>
  `expr_post (storage_trace_horizon rhs_state.storage_trace)
    ctx func cenv cx e mid sp sm target_state rhs_state v vop u` by
    metis_tac[] >>
  `(!x y. not_fresh_at sp x /\ lookup_var x target_state = SOME y ==>
       lookup_var x u = SOME y) /\
   (!aid b. FLOOKUP target_state.vs_allocas aid = SOME b ==>
       FLOOKUP u.vs_allocas aid = SOME b)` by fs[expr_post_def] >>
  `sa.cs_next_var <= sm.cs_next_var /\ sp.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sp.cs_next_id /\ sp.cs_next_id <= sm.cs_next_id` by
    (fs[ci_mono_def,compileEnvTheory.cs_extends_def] >> decide_tac) >>
  `return_buf_frame d cenv sm u` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`,`target_state`,`sp`] >> simp[]) >>
  `(!x y. not_fresh_at sa x /\ lookup_var x s0 = SOME y ==> lookup_var x u = SOME y) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sa x ==> FLOOKUP Gr x = FLOOKUP G0 x /\
      op_taint trhs (Var x) = op_taint tn0 (Var x))` by
    (fs[ghost_kept_at_def] >> rpt strip_tac >>
     metis_tac[loweringShapeDefsTheory.not_fresh_at_mono,ci_mono_def]) >>
  `MAP FDOM rhs_state.scopes = MAP FDOM mid.scopes` by
    (qpat_assum `bind (eval_expr cx e) (read_result cx) gas_in = (INL v,rhs_state)`
       (mp_tac o MATCH_MP stmtSimDefsTheory.eval_read_preserves_scopes_dom) >>
     simp[Abbr `gas_in`]) >>
  `alloca_frame cenv mid sp target_state cenv rhs_state u` by
    (irule (INST_TYPE [alpha |-> ``:256``] stmtSimDefsTheory.expr_post_alloca_frame) >>
     qpat_assum `expr_post (storage_trace_horizon _) ctx func cenv cx e mid sp sm target_state rhs_state v vop u`
       (irule_at Any) >> simp[]) >>
  `alloca_frame cenv es sa s0 cenv rhs_state u` by
    (irule stmtSimDefsTheory.alloca_frame_trans >>
     qexistsl_tac [`cenv`,`mid`,`target_state`,`sp`] >> simp[]) >>
  `!aid off sz i.
    FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
      off + sz <= b \/ b + sz' <= off) /\
    off <= i /\ i < off + sz /\ i IN trhs.t_mem ==> i IN tn0.t_mem` by
    (match_mp_tac (Q.INST [`c1` |-> `cenv`, `e1` |-> `mid`,
       `s1` |-> `target_state`, `sa1` |-> `sp`, `tn1` |-> `tm`, `tn2` |-> `trhs`]
       alloca_taint_kept_trans) >>
     fs[ghost_kept_at_def] >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `cs_extends sa sm` by
    metis_tac[exprLoweringPropsTheory.ci_mono_def,compileEnvTheory.cs_extends_trans] >>
  `!H. valid_horizon cx st0 H rhs_state.storage_trace ==>
    stmt_state_rel H ctx func cenv cx rhs_state u /\
    storage_well_formed_on cx rhs_state (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx rhs_state Gr trhs u` by
    (qpat_assum `!H. valid_horizon cx st0 H rhs_state.storage_trace ==>
       expr_post H ctx func cenv cx e mid sp sm target_state rhs_state v vop u /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[loweringPostsTheory.expr_post_def]) >>
  suspend "resolve_pointer"
QED

Resume body_append_nested_frag_full[resolve_pointer]:
  rename1 `eval_operand (Var x) target_state = SOME addr` >>
  `lookup_var x target_state = SOME addr` by
    fs[venomStateTheory.eval_operand_def] >>
  `lookup_var x u = SOME addr /\ not_fresh_at sm x` by
    metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh] >>
  `eval_operand (Var x) u = SOME addr` by
    simp[venomStateTheory.eval_operand_def] >>
  `place_ptr_rel cenv cx u (PlaceR p) addr (SOME loc)
        (Type (ArrayT elem (Dynamic cap)))` by
    (Cases_on `p` >> fs[place_ptr_rel_def] >>
     rename1 `FLOOKUP cenv.ce_vars nm = SOME (PtrVar (Var pv) psz)` >>
     `not_fresh_at sp pv` by
       (qpat_x_assum `local_ptrs_reserved cenv sp` mp_tac >>
        rewrite_tac[loweringStateRelDefsTheory.local_ptrs_reserved_def] >>
        strip_tac >> qpat_x_assum `!n1 n2 p sz1 sz2. _` drule >>
        disch_then (qspecl_then [`nm`,`psz`] strip_assume_tac)) >>
     qpat_x_assum `!x y. not_fresh_at sp x /\ _ ==> lookup_var x u = SOME y`
       irule >> simp[]) >>
  `op_taint trhs (Var x) = {}` by
    fs[bodyFullTargetDefsTheory.target_ptr_ok_def,ghost_kept_at_def] >>
  `target_ptr_ok cenv (PlaceR p)
      (Var x,SOME loc,SOME (ValPT (ArrayT elem (Dynamic cap)))) Gr trhs u` by
    (irule targetPtrFactsTheory.target_ptr_ok_operand_transport >>
     qpat_assum `target_ptr_ok _ (PlaceR p) _ _ _ target_state` (irule_at Any) >>
     fs[ghost_kept_at_def,ptrDisciplineTheory.op_prov_def] >>
     metis_tac[loweringStateRelDefsTheory.local_ptrs_reserved_def]) >>
  `cx_tops cx = tops` by metis_tac[bodyInvCodePropsTheory.body_inv_main_code] >>
  `body_inv (cx_tops cx) ctx cenv cx` by asm_rewrite_tac[] >>
  `?tv. evaluate_type (get_tenv cx) elem = SOME tv` by
    (qpat_assum `place_ptr_rel _ _ u (PlaceR p) _ _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `p` >> simp[loweringPostsTheory.place_ptr_rel_def] >>
     metis_tac[vyperTypeValuesTheory.evaluate_type_ArrayT_cases]) >>
  `well_formed_type_value tv` by
    metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value] >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def,vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
  `value_has_type tv v` by
    (qpat_assum `type_widens_to env.type_defs (expr_type e) elem` mp_tac >>
     qpat_assum `evaluate_type (get_tenv cx) elem = SOME tv` mp_tac >>
     qpat_assum `value_runtime_typed env (expr_type e) v` mp_tac >>
     qpat_assum `env.type_defs = get_tenv cx` (fn tenv =>
       POP_ASSUM_LIST (K all_tac) >>
       rewrite_tac[vyperTypeExprSoundnessTheory.value_runtime_typed_def,tenv]) >>
     metis_tac[vyperTypeArgFitsTheory.type_widens_to_value_has_type,optionTheory.SOME_11]) >>
  `assignable_type (get_tenv cx) elem` by
    (qpat_assum `type_stmt env ret_ty (Append t e) = SOME env'`
       (mp_tac o ONCE_REWRITE_RULE [vyperTypeSystemTheory.type_stmt_def]) >> simp[]) >>
  `val_wf tv v` by metis_tac[cj 1 valueEncodingTypingTheory.value_has_type_val_wf] >>
  `?writes. encode_value tv v = SOME writes` by
    (rewrite_tac[GSYM optionTheory.IS_SOME_EXISTS] >>
     irule (cj 1 vyperTypingTheory.value_has_type_equiv) >> simp[]) >>
  Cases_on `p`
  >- suspend "storage"
  >- suspend "memory" >>
  fs[loweringPostsTheory.place_ptr_rel_def]
QED

Resume body_append_nested_frag_full[memory]:
  rename1 `place_ptr_rel _ _ u (PlaceR (MemoryPlace id path)) _ _ _` >>
  qpat_assum `place_ptr_rel _ _ u (PlaceR (MemoryPlace id path)) _ _ _`
    (mp_tac o REWRITE_RULE [place_ptr_rel_def]) >>
  disch_then (qx_choosel_then [`root_var`,`root_size`,`root_word`,`root_ty`,`root_tv`,
    `delta`,`leaf`,`arr_ty`] strip_assume_tac) >>
  fs[] >>
  `leaf = ArrayTV tv (Dynamic cap)` by
    (qpat_assum `ArrayT elem (Dynamic cap) = arr_ty` (fn ty =>
       qpat_assum `evaluate_type (get_tenv cx) arr_ty = SOME leaf`
         (mp_tac o PURE_REWRITE_RULE [GSYM ty])) >>
     simp[vyperValueTheory.evaluate_type_def]) >>
  qpat_x_assum `ArrayT elem (Dynamic cap) = arr_ty` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `leaf = ArrayTV tv (Dynamic cap)` SUBST_ALL_TAC >>
  qpat_assum `addr = root_word + n2w delta` (fn eq =>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM eq]) >> assume_tac eq) >>
  rename1 `lookup_scopes id mid.scopes = SOME initial` >>
  rename1 `evaluate_subscripts initial.type initial.value path = INL old` >>
  `expr_sim_inv cenv cx env mid` by
    metis_tac[exprBodyPrePropsTheory.expr_body_pre_static_facts,
              exprSimHypsDefsTheory.expr_sim_inv_gas_obs] >>
  `initial.type = root_tv` by
    (qpat_assum `lookup_scopes id mid.scopes = SOME initial` (fn entry =>
       qpat_assum `cenv.ce_var_type id = SOME root_ty` (fn ty =>
         mp_tac (CONJ entry ty))) >>
     qpat_assum `expr_sim_inv cenv cx env mid` mp_tac >>
     qpat_assum `evaluate_type (get_tenv cx) root_ty = SOME root_tv` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[bodySimAugPlaceLoadTheory.aug_place_entry_type_agrees,optionTheory.SOME_11]) >>
  `lookup_var root_var target_state = SOME root_word` by
    (qpat_assum `place_ptr_rel _ _ target_state (PlaceR (MemoryPlace id path)) _ _ _`
       (mp_tac o REWRITE_RULE [place_ptr_rel_def]) >>
     simp[] >> metis_tac[]) >>
  suspend "memory_view"
QED

Resume body_append_nested_frag_full[memory_view]:
  qabbrev_tac `H = storage_trace_horizon rhs_state.storage_trace` >>
  `valid_horizon cx st0 H rhs_state.storage_trace` by
    (qpat_assum `rhs_state.storage_trace = _` (fn eq =>
       simp_tac bool_ss [Abbr `H`,eq]) >> first_assum ACCEPT_TAC) >>
  `storage_trace_domain cx st0 rhs_state.storage_trace` by
    (qpat_assum `valid_horizon cx st0 H rhs_state.storage_trace` mp_tac >>
     simp_tac bool_ss [Abbr `H`,vyperStorageFootprintTheory.storage_trace_domain_def]) >>
  `valid_horizon cx st0 H mid.storage_trace` by metis_tac[] >>
  `dead_lo_ok H (DF H) lo cenv cx` by
    (qpat_assum `!H. dead_lo_ok H (DF H) lo cenv cx` (qspec_then `H` ACCEPT_TAC)) >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_assum `rhs_state.storage_trace = _` (fn eq =>
    qpat_assum `valid_horizon cx st0 H rhs_state.storage_trace`
      (assume_tac o PURE_REWRITE_RULE [eq])) >>
  qpat_assum `!H. valid_horizon cx st0 H _ ==>
    expr_post H ctx func cenv cx e mid sp sm target_state rhs_state v vop u`
    (qspec_then `H` (drule_then assume_tac)) >>
  `bind (eval_expr cx e) (read_result cx) (mid with gas_obs := gas_in.gas_obs) =
     (INL v,rhs_state)` by simp[Abbr `gas_in`] >>
  `?entry vs.
      lookup_scopes id rhs_state.scopes = SOME entry /\
      entry.type = initial.type /\
      subscripts_type entry.type path = SOME (ArrayTV tv (Dynamic cap)) /\
      read_memory_path entry path = INL (ArrayV (DynArrayV vs)) /\
      value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
      lo <= w2n addr /\ w2n addr + 32 + cap * type_memory_size tv <= u.vs_alloca_next /\
      (!mem. mem_agree_outside trhs.t_mem u.vs_memory mem ==>
        val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n addr) mem)` by
    (`expr_body_pre_mods [(NONE,tops)] cenv cx env e
        (mid with gas_obs := gas_in.gas_obs)` by
       metis_tac[exprBodyPrePropsTheory.body_inv_expr_body_pre_mods,
                 exprSimSourceTheory.expr_body_pre_gas_obs] >>
     `0 < root_size ==> lo <= w2n root_word` by
       (`local_region cenv mid.scopes target_state id (w2n root_word) root_size` by
          simp[local_region_def] >>
        strip_tac >>
        mp_tac (Q.INST [`D` |-> `DF H`, `H` |-> `H`,
          `b` |-> `w2n (root_word:256 word)`,
          `cenv` |-> `cenv`,
          `ctx` |-> `ctx`, `cx` |-> `cx`, `env` |-> `env`, `es0` |-> `mid`,
          `es` |-> `mid`, `func` |-> `func`, `id` |-> `id`, `n` |-> `root_size`,
          `s` |-> `target_state`, `tops` |-> `tops`]
          (INST_TYPE [alpha |-> ``:256``]
            (SPEC_ALL bodyFullMemoryFramesTheory.body_full_local_region_lower_bound))) >>
        impl_tac >- simp[] >> disch_then ACCEPT_TAC) >>
     irule (INST_TYPE [alpha |-> ``:256``] append_nested_memory_rhs_view_mods) >>
     conj_tac >- (qexists_tac `old` >> first_assum ACCEPT_TAC) >>
     qexistsl_tac [`DF H`,`Gm`,`Gr`,`H`,`root_word`,`cenv`,`ctx`,`cx`,`d`,`e`,
       `env`,`func`,`gas_in.gas_obs`,`delta`,`mid`,`[(NONE,tops)]`,`root_var`,`target_state`,
       `sm`,`sp`,`root_size`,`tm`,`v`,`vop`] >>
     simp[exprSimSourceTheory.expr_body_pre_gas_obs] >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC) >>
  suspend "memory_bounds"
QED

Resume body_append_nested_frag_full[memory_bounds]:
  `!t0. cenv.ce_var_type id = SOME t0 ==>
     evaluate_type (get_tenv cx) t0 = SOME entry.type` by
    (rpt strip_tac >> irule bodySimAugPlaceLoadTheory.aug_place_entry_type_agrees >>
     qpat_assum `lookup_scopes id rhs_state.scopes = SOME entry` (irule_at Any) >>
     qpat_assum `expr_sim_inv cenv cx env rhs_state` (irule_at Any) >> simp[]) >>
  `local_region cenv rhs_state.scopes u id (w2n root_word) root_size` by
    simp[local_region_def] >>
  qpat_assum `!H. valid_horizon cx st0 H rhs_state.storage_trace ==>
    stmt_state_rel H ctx func cenv cx rhs_state u /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  `w2n root_word + root_size <= u.vs_alloca_next /\ type_memory_size entry.type <= root_size` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx rhs_state u`
       (assume_tac o CONJUNCT1 o MATCH_MP stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >>
     drule_all_then strip_assume_tac nameLoweringPropsTheory.local_ptrs_rel_value >>
     fs[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  `ptr_covers Gr trhs root_var u root_size` by
    (qpat_assum `ghost_inv_at (DF H) lo d cenv cx rhs_state Gr trhs u`
      (mp_tac o CONJUNCT1 o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def]) >>
     disch_then (qspecl_then [`id`,`entry`,`root_var`,`root_size`] mp_tac) >> simp[]) >>
  `u.vs_alloca_next < dimword (:256)` by
    metis_tac[stateRelProjTheory.stmt_state_rel_alloca_room,exprLoweringPropsTheory.alloca_room_next_lt] >>
  `delta + (32 + cap * type_memory_size tv) <= root_size` by
    (drule exprSimPropsTheory.mem_path_offset_sound >> simp[valueEncodingTheory.type_memory_size_def] >>
     strip_tac >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `w2n addr = w2n root_word + delta` by
    (`w2n root_word + delta < dimword (:256)` by
       (qpat_assum `delta + (32 + cap * type_memory_size tv) <= root_size` mp_tac >>
        qpat_assum `w2n root_word + root_size <= u.vs_alloca_next` mp_tac >>
        qpat_assum `u.vs_alloca_next < dimword (:256)` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
     `root_word + n2w delta = (n2w (w2n root_word + delta):bytes32)` by
       simp[GSYM wordsTheory.word_add_n2w] >>
     pure_asm_rewrite_tac [wordsTheory.w2n_n2w] >>
     irule arithmeticTheory.LESS_MOD >> first_assum ACCEPT_TAC) >>
  `FLOOKUP Gr x = FLOOKUP Gr root_var` by
    fs[bodyFullTargetDefsTheory.target_ptr_ok_def,ptrDisciplineTheory.op_prov_def] >>
  `ptr_covers Gr trhs x u (32 + cap*type_memory_size tv)` by
    (qpat_assum `ptr_covers Gr trhs root_var u root_size`
       (mp_tac o PURE_REWRITE_RULE [bodyPtrDefsTheory.ptr_covers_def]) >>
     disch_then (CONJUNCTS_THEN2 assume_tac
       (qx_choosel_then [`root_address`,`region_base`,`region_size`] strip_assume_tac)) >>
     `root_address = root_word` by fs[] >>
     simp[bodyPtrDefsTheory.ptr_covers_def] >>
     qpat_assum `addr = root_word + n2w delta` (SUBST1_TAC o SYM) >>
     qpat_assum `w2n addr = w2n root_word + delta` SUBST1_TAC >>
     qpat_assum `delta + (32 + cap * type_memory_size tv) <= root_size` mp_tac >>
     qpat_assum `root_address = root_word` (fn eq =>
       qpat_assum `region_base <= w2n root_address` (mp_tac o PURE_REWRITE_RULE [eq]) >>
       qpat_assum `w2n root_address + root_size <= region_base + region_size`
         (mp_tac o PURE_REWRITE_RULE [eq])) >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  `~immutable_root cx t` by fs[targetPlaceSimTheory.target_pre_def] >>
  `target_place_type cenv t = SOME (ValPT (ArrayT elem (Dynamic cap)))` by
    (drule_all append_typed_target_place >> simp[exprLoweringTheory.value_type_place_def]) >>
  `type_memory_bytes cenv elem = type_memory_size tv` by
    (irule exprSimHypsTheory.expr_sim_inv_memory_size >>
     qpat_assum `expr_sim_inv cenv cx env rhs_state` (irule_at Any) >> simp[]) >>
  `type_memory_bytes cenv elem < 2**64` by
    (qpat_assum `target_place_type cenv t = _` (fn ty =>
       qpat_assum `stmt_exprs_ok cenv (Append t e)`
         (mp_tac o SRULE [stmt_exprs_ok_def,allocLimitsTheory.alloc_limits_stmt_def,ty])) >>
     Cases_on `is_word_type elem` >> simp[] >>
     drule_all_then (fn size => simp[size]) entryDecodeStaticPropsTheory.word_type_memory_size) >>
  `type_memory_size tv + 64 < dimword (:256)` by
    (qpat_assum `type_memory_bytes cenv elem = type_memory_size tv` (fn size =>
       qpat_assum `type_memory_bytes cenv elem < 2**64`
         (mp_tac o PURE_REWRITE_RULE [size])) >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  `0 < type_slot_size tv` by
    drule_all_then ACCEPT_TAC vyperTypeSystemTheory.assignable_type_slot_size_pos >>
  `0 < type_memory_size tv` by simp[valueEncodingPropsTheory.type_memory_size_slots] >>
  `cap < dimword (:256)` by
    (`cap <= cap*type_memory_size tv` by
       (qpat_assum `0 < type_memory_size tv` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        Cases_on `type_memory_size tv` >> simp[arithmeticTheory.MULT_CLAUSES]) >>
     qpat_assum `w2n addr + 32 + cap * type_memory_size tv <= u.vs_alloca_next` mp_tac >>
     qpat_assum `u.vs_alloca_next < dimword (:256)` mp_tac >>
     qpat_assum `cap <= cap*type_memory_size tv` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  `elem_size_in_location cenv LocMemory elem = type_memory_size tv /\ word_scale LocMemory = 32` by
    simp[word_scale_def,elem_size_in_location_def,is_slot_addressed_def] >>
  `local_ptrs_reserved cenv sm` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `sa` >> simp[]) >>
  `!q sz. cenv.ce_return_pc = SOME (PtrVar (Var q) sz) ==> not_fresh_at sa q` by
    fs[loweringPostsTheory.ret_pc_ok_def] >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by
    (qpat_assum `s0.vs_alloca_next <= target_state.vs_alloca_next` mp_tac >>
     qpat_assum `target_state.vs_alloca_next <= u.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  qpat_assum `cx_tops cx = tops` (SUBST1_TAC o SYM) >>
  Cases_on `is_word_type elem`
  >- suspend "memory_word" >> suspend "memory_aggregate"
QED

Resume body_append_nested_frag_full[memory_aggregate]:
  qpat_assum `~is_word_type elem` (fn nonword =>
    qpat_assum `if is_word_type elem then
       compile_dynarray_append cenv (Var x) vop _ _ _ _ _ T _ sm = _ else _`
      (qx_choosel_then [`tmp`,`sc`,`sd`] strip_assume_tac o SRULE [nonword])) >>
  `type_widens_to env.type_defs (expr_type e) elem` by simp[] >>
  drule_all_then (qx_choosel_then [`stv`,`src`,`sw`] strip_assume_tac) append_aggregate_input >>
  qpat_x_assum `vop = Var src` SUBST_ALL_TAC >>
  `ci_mono sm sc /\ ci_mono sc sd /\ ci_mono sd sb` by
    metis_tac[ci_mono_compile_alloc_buffer,ci_mono_compile_store_memory,
      ci_mono_compile_dynarray_append,pairTheory.SND] >>
  `cs_extends sm sc /\ cs_extends sc sd /\ cs_extends sd sb` by fs[ci_mono_def] >>
  `fn_has_code sm sc func /\ fn_has_code sc sd func /\ fn_has_code sd sb func` by
    metis_tac[fragExecTheory.fn_has_code_split,compileEnvTheory.cs_extends_trans] >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by fs[ghost_inv_at_def] >>
  drule_all_then strip_assume_tac
    immutableDeployAssignRangesTheory.immutable_assign_copy_metadata >>
  qpat_assum `type_memory_bytes cenv elem = type_memory_size tv` (fn th =>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> assume_tac th) >>
  `compile_dynarray_append cenv (Var x) tmp.buf_operand 32 (type_memory_size tv)
    elem elem cap F LocMemory sd = ((),sb)` by
    (qpat_assum `word_scale LocMemory = 32` (fn scale =>
      qpat_assum `elem_size_in_location cenv LocMemory elem = type_memory_size tv` (fn size =>
        qpat_assum `compile_dynarray_append cenv (Var x) _ (word_scale LocMemory) _ _ _ _ F LocMemory sd = _`
          (ACCEPT_TAC o PURE_REWRITE_RULE [scale,size])))) >>
  drule_all (SRULE [] (Q.INST [`n` |-> `type_memory_size dtv`]
    (INST_TYPE [beta |-> ``:256``] append_storage_aggregate_stage_ready))) >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (qx_choosel_then [`staged`,`root`,`b`,`Gs`,`ts`] strip_assume_tac)) >>
  qpat_x_assum `tmp.buf_operand = Var root` SUBST_ALL_TAC >>
  suspend "staged_view"
QED

Resume body_append_nested_frag_full[staged_view]:
  `!H. valid_horizon cx st0 H rhs_state.storage_trace ==>
    stmt_state_rel H ctx func cenv cx rhs_state staged /\
    storage_well_formed_on cx rhs_state (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx rhs_state Gs ts staged` by metis_tac[] >>
  `!x. not_fresh_at sm x ==> not_fresh_at sd x` by
    metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh,
      exprLoweringPropsTheory.ci_mono_trans] >>
  `local_ptrs_reserved cenv sd` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `sm` >> fs[ci_mono_def] >> decide_tac) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sd x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sd x)` by metis_tac[] >>
  `return_buf_frame d cenv sd staged` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`,`u`,`sm`] >> fs[ci_mono_def] >> rpt conj_tac >>
     TRY decide_tac >> metis_tac[]) >>
  `lookup_var x staged = SOME addr /\
    lookup_var root_var staged = SOME root_word /\ not_fresh_at sd x` by
    metis_tac[local_ptrs_reserved_def] >>
  `place_ptr_rel cenv cx staged (PlaceR (MemoryPlace id path)) addr (SOME LocMemory)
    (Type (ArrayT elem (Dynamic cap)))` by
    (simp[loweringPostsTheory.place_ptr_rel_def] >>
     qexistsl_tac [`root_var`,`root_size`,`root_word`,`root_ty`,`root_tv`,
       `delta`,`ArrayTV tv (Dynamic cap)`] >> simp[]) >>
  `local_region cenv rhs_state.scopes staged id (w2n root_word) root_size` by
    simp[local_region_def] >>
  `regions_disjoint b (type_memory_size tv) (w2n root_word) root_size` by
    (qpat_assum `!name a len. local_region cenv rhs_state.scopes staged name a len ==> _`
       (qspecl_then [`id`,`w2n root_word`,`root_size`] (drule_then ACCEPT_TAC))) >>
  `ptr_covers Gs ts x staged (32 + cap * type_memory_size tv)` by
    (irule assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame >>
     qpat_assum `ptr_covers Gr trhs x u _` (irule_at Any) >> simp[] >>
     qpat_assum `!x. not_fresh_at sm x ==> _` (qspec_then `x` mp_tac) >> simp[]) >>
  `w2n addr + 32 + cap * type_memory_size tv <= staged.vs_alloca_next` by decide_tac >>
  `w2n ((n2w b):bytes32) = b` by simp[] >>
  `w2n ((n2w b):bytes32) + val_store_size tv v <= staged.vs_alloca_next` by
    (qpat_assum `val_wf tv v` (mp_tac o MATCH_MP exprSimPropsTheory.val_store_size_le) >>
     qpat_assum `b + type_memory_size tv <= staged.vs_alloca_next` mp_tac >>
     qpat_assum `w2n ((n2w b):bytes32) = b` SUBST1_TAC >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  `!m. mem_agree_outside ts.t_mem staged.vs_memory m ==>
      val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n addr) m` by
    suspend "staged_read" >>
  `!H. gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (u,Gr,trhs) [] (OK staged,Gs,ts)` by simp[] >>
  irule gasOutcomeFullStmtsTheory.gas_outcome_full_zero_prefix >>
  goal_assum (drule_at Any) >>
  suspend "staged_cont"
QED

Resume body_append_nested_frag_full[staged_read]:
  match_mp_tac robustCopyTransportPtrTheory.robust_val_in_memory_exterior_frame >>
  qexistsl_tac [`trhs.t_mem`,`u.vs_memory`,`{i | b <= i /\ i < b+type_memory_size tv}`] >>
  simp[] >>
  `val_wf (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs))` by
    metis_tac[cj 1 valueEncodingTypingTheory.value_has_type_val_wf] >>
  simp[] >> rpt strip_tac >>
  drule exprSimPropsTheory.val_footprint_le >> simp[] >>
  fs[regions_disjoint_def,valueEncodingTheory.type_memory_size_def] >> decide_tac
QED

Resume body_append_nested_frag_full[staged_cont]:
  irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
  irule_at (Pat `gas_outcome_full _ _ _ _ _ _ _ _`) append_nested_memory_cont_full >>
  qpat_assum `compile_dynarray_append cenv (Var x) (Var root) _ _ _ _ _ F LocMemory sd = _`
    (irule_at Any) >>
  qpat_assum `lookup_scopes id rhs_state.scopes = SOME entry` (irule_at Any) >>
  qpat_assum `read_memory_path entry path = INL (ArrayV (DynArrayV vs))` (irule_at Any) >>
  qpat_assum `lookup_var x staged = SOME addr` (irule_at Any) >>
  simp[] >>
  qexistsl_tac [`lctx`,`env`,`d`,`RetQ`] >>
  suspend "staged_conditions"
QED

Resume body_append_nested_frag_full[staged_conditions]:
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qx_gen_tac `final_horizon` >> strip_tac >>
     qpat_assum `rhs_state.storage_trace = _` (fn eq =>
       qpat_assum `!H. valid_horizon _ _ H rhs_state.storage_trace ==>
         stmt_state_rel H ctx func cenv cx rhs_state staged /\ _`
         (qspec_then `final_horizon` (mp_tac o PURE_REWRITE_RULE [eq]))) >>
     (impl_tac >- simp[]) >> strip_tac >> first_assum ACCEPT_TAC) >>
  simp[] >>
  reverse conj_tac >- (rpt gen_tac >> strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qx_genl_tac [`final_horizon`,`ans`,`ee`,`Gf`,`tf`,`fin_state`] >>
  disch_then (qx_choose_then `cenvf` strip_assume_tac) >>
  qexists_tac `cenvf` >> simp[] >>
  suspend "nested_staged_frame"
QED

Resume body_append_nested_frag_full[nested_staged_frame]:
  `s0.vs_alloca_next <= fin_state.vs_alloca_next` by
    (qpat_assum `s0.vs_alloca_next <= u.vs_alloca_next` mp_tac >>
     qpat_assum `u.vs_alloca_next <= staged.vs_alloca_next` mp_tac >>
     qpat_assum `staged.vs_alloca_next <= fin_state.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  `sm.cs_next_id <= sd.cs_next_id` by
    (qpat_assum `ci_mono sm sc`
       (mp_tac o CONJUNCT2 o CONJUNCT2 o REWRITE_RULE [ci_mono_def]) >>
     qpat_assum `ci_mono sc sd`
       (mp_tac o CONJUNCT2 o CONJUNCT2 o REWRITE_RULE [ci_mono_def]) >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  `sa.cs_next_id <= sm.cs_next_id` by
    (qpat_assum `sa.cs_next_id <= sp.cs_next_id` mp_tac >>
     qpat_assum `sp.cs_next_id <= sm.cs_next_id` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  `sa.cs_next_id <= sd.cs_next_id` by
    (qpat_assum `sa.cs_next_id <= sm.cs_next_id` mp_tac >>
     qpat_assum `sm.cs_next_id <= sd.cs_next_id` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  `alloca_frame cenv es sa s0 cenv rhs_state staged` by
    (irule stmtSimDefsTheory.alloca_frame_trans >>
     qpat_assum `alloca_frame cenv rhs_state sm u cenv rhs_state staged` (irule_at Any) >>
     simp[]) >>
  `!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==> FLOOKUP u.vs_allocas aid = SOME a` by
    (qpat_assum `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> _` mp_tac >>
     qpat_assum `!aid b. FLOOKUP target_state.vs_allocas aid = SOME b ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==> FLOOKUP staged.vs_allocas aid = SOME a` by
    (rpt strip_tac >>
     qpat_assum `!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==> FLOOKUP u.vs_allocas aid = SOME a`
       (qspecl_then [`aid`,`a`] (drule_then assume_tac)) >>
     qpat_assum `!aid a. FLOOKUP u.vs_allocas aid = SOME a ==> FLOOKUP staged.vs_allocas aid = SOME a`
       (qspecl_then [`aid`,`a`] (drule_then ACCEPT_TAC))) >>
  `!x. not_fresh_at sa x ==> lookup_var x fin_state = lookup_var x u /\
    FLOOKUP Gf x = FLOOKUP Gr x /\ op_taint tf (Var x) = op_taint trhs (Var x)` by
    (qx_gen_tac `saved_reg` >> strip_tac >>
     `not_fresh_at sm saved_reg` by
       (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
     qpat_assum `!x. not_fresh_at sm x ==> not_fresh_at sd x /\ _`
       (qspec_then `saved_reg` (drule_then strip_assume_tac)) >>
     qpat_assum `!x. not_fresh_at sd x ==> lookup_var x fin_state = _ /\ _`
       (qspec_then `saved_reg` (drule_then strip_assume_tac)) >> simp[]) >>
  simp[] >>
  conj_tac >-
    (irule stmtSimDefsTheory.alloca_frame_trans >>
     qpat_assum `alloca_frame cenv rhs_state sd staged cenvf ee fin_state` (irule_at Any) >>
     simp[]) >>
  `!aid off sz i. FLOOKUP u.vs_allocas aid = SOME (off,sz) /\ aid < sm.cs_next_id /\
     (!n b sz'. local_region cenv rhs_state.scopes u n b sz' ==> off+sz <= b \/ b+sz' <= off) /\
     off <= i /\ i < off+sz /\ i IN ts.t_mem ==> i IN trhs.t_mem` by
    (qx_genl_tac [`aid`,`off`,`sz`,`i`] >> strip_tac >>
     qpat_assum `!aid off sz. aid < sm.cs_next_id /\ FLOOKUP u.vs_allocas aid = SOME (off,sz) ==> _`
       (qspecl_then [`aid`,`off`,`sz`] mp_tac) >> simp[] >>
     disch_then (qspec_then `i` mp_tac) >> simp[]) >>
  `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!n b sz'. local_region cenv es.scopes s0 n b sz' ==> off+sz <= b \/ b+sz' <= off) /\
    off <= i /\ i < off+sz /\ i IN ts.t_mem ==> i IN tn0.t_mem` by
    (match_mp_tac (Q.INST [`c1` |-> `cenv`,`e1` |-> `rhs_state`,
       `s1` |-> `u`,`sa1` |-> `sm`,`tn1` |-> `trhs`]
       (INST_TYPE [alpha |-> ``:256``,beta |-> ``:256``] alloca_taint_kept_trans)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  match_mp_tac (Q.INST [`c1` |-> `cenv`,`e1` |-> `rhs_state`,
    `s1` |-> `staged`,`sa1` |-> `sd`,`tn1` |-> `ts`]
       (INST_TYPE [alpha |-> ``:256``,beta |-> ``:256``] alloca_taint_kept_trans)) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `!aid off sz i. FLOOKUP staged.vs_allocas aid = SOME (off,sz) /\ _ ==> i IN ts.t_mem` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[]
QED

Resume body_append_nested_frag_full[memory_word]:
  `type_widens_to env.type_defs (expr_type e) elem` by simp[] >>
  drule_all_then strip_assume_tac append_nested_word_input >>
  `compile_dynarray_append cenv (Var x) vop 32 (type_memory_size tv)
    elem elem cap F LocMemory sm = ((),sb)` by
    (qpat_assum `is_word_type elem` (fn word =>
       qpat_assum `word_scale LocMemory = 32` (fn scale =>
         qpat_assum `elem_size_in_location cenv LocMemory elem = type_memory_size tv` (fn stride =>
           qpat_assum `if is_word_type elem then
             compile_dynarray_append cenv (Var x) vop _ _ _ _ _ T _ sm = _ else _`
             (mp_tac o SRULE [word,scale,stride])))) >>
     simp[append_memory_word_uses_store]) >>
  `w2n addr + 32 + cap * type_memory_size tv <= u.vs_alloca_next` by simp[] >>
  irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
  irule_at (Pat `gas_outcome_full _ _ _ _ _ _ _ _`) append_nested_memory_cont_full >>
  qpat_assum `compile_dynarray_append cenv (Var x) vop 32 _ _ _ _ F LocMemory sm = _`
    (irule_at Any) >>
  qpat_assum `lookup_scopes id rhs_state.scopes = SOME entry` (irule_at Any) >>
  qpat_assum `read_memory_path entry path = INL (ArrayV (DynArrayV vs))` (irule_at Any) >>
  qpat_assum `lookup_var x u = SOME addr` (irule_at Any) >>
  simp[] >>
  qexistsl_tac [`lctx`,`env`,`d`,`RetQ`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- (simp[vyperStorageFootprintTheory.storage_trace_domain_def] >>
    first_assum ACCEPT_TAC)) >>
  reverse conj_tac >- (POP_ASSUM_LIST (K all_tac) >> metisTools.METIS_TAC []) >>
  suspend "memory_word_post"
QED

Resume body_append_nested_frag_full[memory_word_post]:
  rpt gen_tac >> disch_then (qx_choose_then `cenvf` strip_assume_tac) >>
  qexists_tac `cenvf` >> simp[] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  conj_tac >-
    (qx_genl_tac [`saved_reg`,`saved_word`] >> strip_tac >>
     `not_fresh_at sm saved_reg` by simp[] >>
     qpat_assum `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w`
       (qspecl_then [`saved_reg`,`saved_word`] mp_tac) >>
     qpat_assum `!x. not_fresh_at sm x ==> _` (qspec_then `saved_reg` mp_tac) >>
     simp[]) >>
  conj_tac >-
    (qx_gen_tac `saved_reg` >> strip_tac >>
     `not_fresh_at sm saved_reg` by simp[] >>
     qpat_assum `not_fresh_at sa saved_reg` (fn fresh =>
       qpat_assum `!x. not_fresh_at sa x ==> FLOOKUP Gr x = _ /\ _`
         (qspec_then `saved_reg` (strip_assume_tac o C MP fresh))) >>
     qpat_assum `not_fresh_at sm saved_reg` (fn fresh =>
       qpat_assum `!x. not_fresh_at sm x ==> lookup_var x t' = _ /\ _`
         (qspec_then `saved_reg` (strip_assume_tac o C MP fresh))) >>
     fs[ptrDisciplineTheory.op_taint_def]) >>
  conj_tac >-
    (irule stmtSimDefsTheory.alloca_frame_trans >>
     qpat_assum `alloca_frame cenv rhs_state sm u cenvf _ t'` (irule_at Any) >>
     simp[]) >>
  `sa.cs_next_id <= sm.cs_next_id` by fs[compileEnvTheory.cs_extends_def] >>
  `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b` by
    (qpat_assum `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> _` mp_tac >>
     qpat_assum `!aid b. FLOOKUP target_state.vs_allocas aid = SOME b ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  match_mp_tac (Q.INST [`c1` |-> `cenv`, `e1` |-> `rhs_state`,
    `s1` |-> `u`, `sa1` |-> `sm`, `tn1` |-> `trhs`]
    (INST_TYPE [alpha |-> ``:256``,beta |-> ``:256``] alloca_taint_kept_trans)) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `!aid off sz i. FLOOKUP u.vs_allocas aid = SOME (off,sz) /\ _ ==> i IN trhs.t_mem` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[]
QED

Resume body_append_nested_frag_full[storage]:
  rename1 `place_ptr_rel _ _ _ (PlaceR (StoragePlace tr slot leaf)) _ _ _` >>
  qpat_assum `place_ptr_rel _ _ u (PlaceR (StoragePlace tr slot leaf)) _ _ _`
    (strip_assume_tac o REWRITE_RULE [place_ptr_rel_def]) >>
  gvs[] >>
  qpat_assum `evaluate_type (get_tenv cx) (ArrayT elem (Dynamic cap)) = SOME leaf`
    (strip_assume_tac o MATCH_MP vyperTypeValuesTheory.evaluate_type_ArrayT_cases) >>
  gvs[] >>
  rename1 `eval_operand (Var x) u = SOME addr` >>
  rename1 `evaluate_type (get_tenv cx) elem = SOME tv` >>
  `!H. valid_horizon cx st0 H rhs_state.storage_trace ==>
    storage_place_observed H (StoragePlace tr addr (ArrayTV tv (Dynamic cap)))` by
    (qx_gen_tac `H` >> strip_tac >>
     irule stmtSimAugAssignPlaceStorageTheory.aug_place_target_observed >>
     qexistsl_tac [`cx`,`es with gas_obs := gas_explicit target_marks s0.vs_gas_readings`,
       `mid`,`st0`,`t`] >> simp[] >>
     qpat_assum `rhs_state.storage_trace = _` (fn eq =>
       qpat_assum `valid_horizon cx st0 H rhs_state.storage_trace`
         (assume_tac o PURE_REWRITE_RULE [eq])) >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> valid_horizon _ _ H _`
       (qspec_then `H` (drule_then ACCEPT_TAC))) >>
  `0 < type_slot_size tv` by
    drule_all_then ACCEPT_TAC vyperTypeSystemTheory.assignable_type_slot_size_pos >>
  `cap < dimword (:256)` by suspend "storage_cap" >>
  Cases_on `is_word_type elem`
  >- suspend "storage_word" >> suspend "storage_aggregate"
QED

Resume body_append_nested_frag_full[storage_cap]:
  qabbrev_tac `H = storage_trace_horizon rhs_state.storage_trace` >>
  `valid_horizon cx st0 H rhs_state.storage_trace` by simp[Abbr `H`] >>
  `regions_consistent (FST H)` by fs[vyperStorageFootprintTheory.valid_horizon_def] >>
  qpat_assum `!H. valid_horizon _ _ H rhs_state.storage_trace ==> storage_place_observed H _`
    (qspec_then `H` (drule_then assume_tac)) >>
  drule_all_then strip_assume_tac append_observed_array_bounds >>
  `cap <= cap * type_slot_size tv` by
    (qpat_assum `0 < type_slot_size tv` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `type_slot_size tv` >>
     simp[arithmeticTheory.MULT_CLAUSES]) >>
  qpat_assum `w2n addr + (1+cap*type_slot_size tv) <= dimword (:256)` mp_tac >>
  qpat_assum `cap <= cap * type_slot_size tv` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> decide_tac
QED

Resume body_append_nested_frag_full[storage_aggregate]:
  qpat_assum `~is_word_type elem` (fn nonword =>
    qpat_assum `if is_word_type elem then
       compile_dynarray_append cenv (Var x) vop _ _ _ _ _ T _ sm = _ else _`
      (qx_choosel_then [`tmp`,`sc`,`sd`] strip_assume_tac o
       SRULE [nonword])) >>
  `type_widens_to env.type_defs (expr_type e) elem` by simp[] >>
  `~immutable_root cx t` by fs[targetPlaceSimTheory.target_pre_def] >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by
    (qpat_assum `s0.vs_alloca_next <= target_state.vs_alloca_next` mp_tac >>
     qpat_assum `target_state.vs_alloca_next <= u.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  `0 < type_memory_size tv /\ type_memory_bytes cenv elem = type_memory_size tv` by
    (conj_tac >- simp[valueEncodingPropsTheory.type_memory_size_slots] >>
     irule exprSimHypsTheory.expr_sim_inv_memory_size >>
     qpat_assum `expr_sim_inv cenv cx env rhs_state` (irule_at Any) >> simp[]) >>
  drule_all_then (qx_choosel_then [`stv`,`src`,`sw`] strip_assume_tac) append_aggregate_input >>
  qpat_x_assum `vop = Var src` SUBST_ALL_TAC >>
  `local_ptrs_reserved cenv sm` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `sa` >> simp[]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  drule_all_then strip_assume_tac
    immutableDeployAssignRangesTheory.immutable_assign_copy_metadata >>
  `target_place_type cenv t = SOME (ValPT (ArrayT elem (Dynamic cap)))` by
    (drule_all append_typed_target_place >> simp[exprLoweringTheory.value_type_place_def]) >>
  `type_memory_bytes cenv elem < 2**64` by
    (qpat_assum `target_place_type cenv t = _` (fn ty =>
       qpat_assum `~is_word_type elem` (fn nonword =>
         qpat_assum `stmt_exprs_ok cenv (Append t e)`
           (mp_tac o SRULE [stmt_exprs_ok_def,
             allocLimitsTheory.alloc_limits_stmt_def,ty,nonword]))) >>
     simp[]) >>
  `type_memory_size tv+64 < dimword (:256)` by
    (qpat_assum `type_memory_bytes cenv elem = type_memory_size tv` (fn size =>
       qpat_assum `type_memory_bytes cenv elem < 2**64`
         (mp_tac o PURE_REWRITE_RULE [size])) >>
     simp_tac (srw_ss()) [wordsTheory.dimword_def] >> decide_tac) >>
  `word_scale (slot_loc tr) = 1 /\ elem_size_in_location cenv (slot_loc tr) elem = type_slot_size tv` by
    (Cases_on `tr` >> simp[loweringPostsTheory.slot_loc_def,elem_size_in_location_def,
       word_scale_def,is_slot_addressed_def,valueEncodingPropsTheory.type_memory_size_slots,
       arithmeticTheory.ADD_DIV_RWT]) >>
  qpat_assum `type_memory_bytes cenv elem = type_memory_size tv` (fn bytes =>
    qpat_assum `word_scale (slot_loc tr) = 1` (fn scale =>
      qpat_assum `elem_size_in_location cenv (slot_loc tr) elem = type_slot_size tv`
        (fn stride =>
          RULE_ASSUM_TAC (PURE_REWRITE_RULE [bytes,scale,stride]) >> assume_tac bytes))) >>
  `compile_dynarray_append cenv (Var x) tmp.buf_operand 1 (type_slot_size tv)
    elem elem cap F (if tr then LocTransient else LocStorage) sd = ((),sb)` by
    (qpat_assum `compile_dynarray_append cenv (Var x) _ 1 _ elem elem _ F (slot_loc tr) sd = ((),sb)`
       (ACCEPT_TAC o PURE_REWRITE_RULE [loweringPostsTheory.slot_loc_def])) >>
  irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
  irule_at (Pat `gas_outcome_full _ _ _ _ _ _ _ _`) append_storage_aggregate_cont_full >>
  qpat_assum `compile_dynarray_append cenv (Var x) _ 1 _ elem elem _ F (if tr then _ else _) sd = ((),sb)` (irule_at Any) >>
  qpat_assum `compile_alloc_buffer (type_memory_size tv) sm = (tmp,sc)` (irule_at Any) >>
  qpat_assum `compile_store_memory cenv (Var src) tmp.buf_operand elem _ sc = ((),sd)` (irule_at Any) >>
  qpat_assum `lookup_var src u = SOME sw` (irule_at Any) >>
  qpat_assum `encode_value tv v = SOME writes` (irule_at Any) >>
  simp[venomStateTheory.eval_operand_def,ptrDisciplineTheory.op_taint_def,
       loweringPostsTheory.slot_loc_def] >>
  qexistsl_tac [`sp`,`lctx`,`d`,`RetQ`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!H. valid_horizon cx st0 H _ ==>
       stmt_state_rel H ctx func cenv cx rhs_state u /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     first_assum ACCEPT_TAC) >>
  simp[] >>
  reverse conj_tac >- (POP_ASSUM_LIST (K all_tac) >> metisTools.METIS_TAC []) >>
  suspend "aggregate_post"
QED

Resume body_append_nested_frag_full[aggregate_post]:
  rpt gen_tac >> disch_then (qx_choose_then `cenvf` strip_assume_tac) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t'` by
    (qpat_assum `stmt_state_rel H ctx func cenvf cx ee t'`
      (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  `s0.vs_alloca_next <= t'.vs_alloca_next` by
    (`s0.vs_alloca_next <= u.vs_alloca_next` by decide_tac >>
     qpat_assum `s0.vs_alloca_next <= u.vs_alloca_next` mp_tac >>
     qpat_assum `u.vs_alloca_next <= t'.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  qexists_tac `cenvf` >> simp[] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  conj_tac >-
    (qx_genl_tac [`saved_reg`,`saved_word`] >> strip_tac >>
     qpat_assum `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> _`
       (qspecl_then [`saved_reg`,`saved_word`] mp_tac) >>
     qpat_assum `!x. not_fresh_at sm x ==> _` (qspec_then `saved_reg` mp_tac) >> simp[]) >>
  conj_tac >-
    (qx_gen_tac `saved_reg` >> strip_tac >>
     `not_fresh_at sm saved_reg` by simp[] >>
     qpat_assum `not_fresh_at sa saved_reg` (fn fresh =>
       qpat_assum `!x. not_fresh_at sa x ==> FLOOKUP Gr x = _ /\ _`
         (qspec_then `saved_reg` (strip_assume_tac o C MP fresh))) >>
     qpat_assum `not_fresh_at sm saved_reg` (fn fresh =>
       qpat_assum `!x. not_fresh_at sm x ==> lookup_var x t' = _ /\ _`
         (qspec_then `saved_reg` (strip_assume_tac o C MP fresh))) >>
     fs[ptrDisciplineTheory.op_taint_def]) >>
  conj_tac >-
    (irule stmtSimDefsTheory.alloca_frame_trans >>
     goal_assum (drule_at Any) >> simp[]) >>
  `sa.cs_next_id <= sm.cs_next_id` by
    fs[compileEnvTheory.cs_extends_def] >>
  `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b` by
    (qpat_assum `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> _` mp_tac >>
     qpat_assum `!aid b. FLOOKUP target_state.vs_allocas aid = SOME b ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  match_mp_tac (Q.INST [`c1` |-> `cenv`,`e1` |-> `rhs_state`,
     `s1` |-> `u`,`sa1` |-> `sm`,`tn1` |-> `trhs`] alloca_taint_kept_trans) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qx_genl_tac [`aid0`,`start0`,`extent0`,`mem_i`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!aid off sz. aid < sm.cs_next_id /\ _ ==> !i. _`
    (qspecl_then [`aid0`,`start0`,`extent0`] mp_tac) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qspec_then `mem_i` mp_tac) >> simp[]
QED

Resume body_append_nested_frag_full[storage_word]:
  `type_widens_to env.type_defs (expr_type e) elem` by simp[] >>
  drule_all_then strip_assume_tac append_nested_word_input >>
  `type_memory_bytes cenv elem = 32` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size,
      entryDecodeStaticPropsTheory.word_type_memory_size] >>
  `elem_size_in_location cenv (slot_loc tr) elem = 1 /\ word_scale (slot_loc tr) = 1` by
    (Cases_on `tr` >> simp[loweringPostsTheory.slot_loc_def,elem_size_in_location_def,
       word_scale_def,is_slot_addressed_def]) >>
  `compile_dynarray_append cenv (Var x) vop 1 1 elem
    (lowered_value_type cenv e) cap T (slot_loc tr) sm = ((),sb)` by
    (qpat_assum `is_word_type elem` (fn word =>
       qpat_assum `elem_size_in_location cenv (slot_loc tr) elem = 1` (fn stride =>
         qpat_assum `word_scale (slot_loc tr) = 1` (fn scale =>
           qpat_assum `if is_word_type elem then
             compile_dynarray_append cenv (Var x) vop _ _ _ _ _ T _ sm = _ else _`
             (ACCEPT_TAC o PURE_REWRITE_RULE [word,boolTheory.COND_CLAUSES,scale,stride]))))) >>
  `compile_dynarray_append cenv (Var x) vop 1 1 elem
    (lowered_value_type cenv e) cap T
    (if tr then LocTransient else LocStorage) sm = ((),sb)` by
    (qpat_assum `compile_dynarray_append cenv (Var x) vop 1 1 elem _ _ T (slot_loc tr) sm = _`
       (ACCEPT_TAC o PURE_REWRITE_RULE [loweringPostsTheory.slot_loc_def])) >>
  `!q. Var x = Var q \/ vop = Var q ==> not_fresh_at sm q` by
    metis_tac[venomStateTheory.operand_11] >>
  qpat_assum `!q. Var x = Var q \/ vop = Var q ==> not_fresh_at sm q`
    (assume_tac o PURE_REWRITE_RULE [venomStateTheory.operand_11]) >>
  `!q sz. cenv.ce_return_pc = SOME (PtrVar (Var q) sz) ==> not_fresh_at sa q` by
    fs[loweringPostsTheory.ret_pc_ok_def] >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by
    (qpat_assum `s0.vs_alloca_next <= target_state.vs_alloca_next` mp_tac >>
     qpat_assum `target_state.vs_alloca_next <= u.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  `!H. valid_horizon cx st0 H rhs_state.storage_trace ==>
    stmt_state_rel H ctx func cenv cx rhs_state u /\
    storage_well_formed_on cx rhs_state (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx rhs_state Gr trhs u /\
    storage_place_observed H (StoragePlace tr addr (ArrayTV tv (Dynamic cap)))` by
    (qx_gen_tac `H` >> strip_tac >>
     qpat_assum `rhs_state.storage_trace = _` (fn eq =>
       qpat_assum `valid_horizon cx st0 H rhs_state.storage_trace`
         (assume_tac o PURE_REWRITE_RULE [eq])) >>
     qpat_assum `!H. valid_horizon _ _ H _ ==>
       stmt_state_rel H ctx func cenv cx rhs_state u /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     qpat_assum `!H. valid_horizon _ _ H rhs_state.storage_trace ==>
       storage_place_observed H _` (qspec_then `H` (drule_then assume_tac)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
  irule_at (Pat `gas_outcome_full _ _ _ _ _ _ _ _`)
    (Q.INST [`R` |-> `\H res ee gt r.
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
      halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==>
        allocas_below_fmp s)`] append_nested_suffix_frame_post) >>
  qexistsl_tac [`tn0`,`sm`,`sb`,`sa`,`s0`,`lctx`,`es`,`d`,`cenv`,`RetQ`,`G0`] >>
  simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (irule append_nested_storage_cont_framed >>
     qpat_assum `compile_dynarray_append cenv (Var x) vop 1 1 elem _ _ T (if tr then _ else _) sm = _`
       (irule_at Any) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     simp[loweringPostsTheory.slot_loc_def] >> qexists_tac `env` >> simp[] >>
     first_assum ACCEPT_TAC) >>
  rpt gen_tac >> disch_then (qx_choose_then `cenvf` strip_assume_tac) >>
  qexists_tac `cenvf` >> simp[] >>
  conj_tac >-
    (qpat_assum `stmt_state_rel _ ctx func cenvf cx _ _`
      (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  first_assum ACCEPT_TAC
QED

Finalise body_append_nested_frag_full[local]

Theorem body_append_nested_subscript_frag_full:
  !cx base key e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv
    env env' ret_ty lctx RetQ es elem cap.
  (!s p t. eval_target_place cx (SubscriptTarget base key) s = (INL p,t) ==>
     body_expr_full_ok cx e) /\
  body_base_target_full_ok cx (SubscriptTarget base key) /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (Append (SubscriptTarget base key) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Append (SubscriptTarget base key) e) ==> occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
  locals_alloc_ok cenv env /\
  type_stmt env ret_ty (Append (SubscriptTarget base key) e) = SOME env' /\
  type_place_target env (SubscriptTarget base key) = SOME (Type (ArrayT elem (Dynamic cap))) /\
  stmt_exprs_ok cenv (Append (SubscriptTarget base key) e) /\
  call_evaluation_safe cx (int_calls_stmt (Append (SubscriptTarget base key) e)) /\
  frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ cenv ret_ty ==>
  stmt_frag_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (Append (SubscriptTarget base key) e))
    (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Append (SubscriptTarget base key) e)))
    (eval_stmt cx (Append (SubscriptTarget base key) e)) es
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `type_place_target env (SubscriptTarget root_bt key) = SOME _` >>
  qspecl_then [`cx`,`SubscriptTarget root_bt key`,`e`,`DF`,`lo`,`d`,`PG`,`tops`,`bindings`,`ctx`,
    `shadow_ctx`,`func`,`shadow_func`,`cenv`,`env`,`env'`,`ret_ty`,`lctx`,`RetQ`,
    `es`,`elem`,`cap`] mp_tac body_append_nested_frag_full >>
  simp[] >> disch_then irule >> first_assum ACCEPT_TAC
QED

Theorem body_append_nested_attribute_frag_full:
  !cx base field e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv
    env env' ret_ty lctx RetQ es elem cap.
  (!s p t. eval_target_place cx (AttributeTarget base field) s = (INL p,t) ==>
     body_expr_full_ok cx e) /\
  body_base_target_full_ok cx (AttributeTarget base field) /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (Append (AttributeTarget base field) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Append (AttributeTarget base field) e) ==> occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
  locals_alloc_ok cenv env /\
  type_stmt env ret_ty (Append (AttributeTarget base field) e) = SOME env' /\
  type_place_target env (AttributeTarget base field) = SOME (Type (ArrayT elem (Dynamic cap))) /\
  stmt_exprs_ok cenv (Append (AttributeTarget base field) e) /\
  call_evaluation_safe cx (int_calls_stmt (Append (AttributeTarget base field) e)) /\
  frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ cenv ret_ty ==>
  stmt_frag_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (Append (AttributeTarget base field) e))
    (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Append (AttributeTarget base field) e)))
    (eval_stmt cx (Append (AttributeTarget base field) e)) es
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `type_place_target env (AttributeTarget root_bt field_name) = SOME _` >>
  qspecl_then [`cx`,`AttributeTarget root_bt field_name`,`e`,`DF`,`lo`,`d`,`PG`,`tops`,`bindings`,`ctx`,
    `shadow_ctx`,`func`,`shadow_func`,`cenv`,`env`,`env'`,`ret_ty`,`lctx`,`RetQ`,
    `es`,`elem`,`cap`] mp_tac body_append_nested_frag_full >>
  simp[] >> disch_then irule >> first_assum ACCEPT_TAC
QED

Theorem body_append_storage_word_frag_full:
  !cx nid e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv
    env env' ret_ty lctx RetQ es elem cap.
  (!s p t. eval_target_place cx (TopLevelNameTarget nid) s = (INL p,t) ==>
     body_expr_full_ok cx e) /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (Append (TopLevelNameTarget nid) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Append (TopLevelNameTarget nid) e) ==> occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
  locals_alloc_ok cenv env /\
  type_stmt env ret_ty (Append (TopLevelNameTarget nid) e) = SOME env' /\
  type_place_target env (TopLevelNameTarget nid) = SOME (Type (ArrayT elem (Dynamic cap))) /\
  is_word_type elem /\
  stmt_exprs_ok cenv (Append (TopLevelNameTarget nid) e) /\
  call_evaluation_safe cx (int_calls_stmt (Append (TopLevelNameTarget nid) e)) /\
  frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ cenv ret_ty ==>
  stmt_frag_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (Append (TopLevelNameTarget nid) e))
    (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Append (TopLevelNameTarget nid) e)))
    (eval_stmt cx (Append (TopLevelNameTarget nid) e)) es
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `type_place_target env (TopLevelNameTarget nid) =
    SOME (Type (ArrayT checked_elem (Dynamic checked_cap)))` >>
  PairCases_on `nid` >>
  `nid0 = NONE` by metis_tac[bodyTypedTargetScopeTheory.body_inv_toplevel_target_main,
                              optionTheory.IS_SOME_EXISTS] >>
  `?vis mut elem cap ast_slot.
     supported_variable_decl tops (nid0,nid1) =
       SOME (vis,mut,ArrayT elem (Dynamic cap),SOME ast_slot) /\
     (mut = Storage \/ mut = Transient)` suffices_by
    (disch_then (qx_choose_then `vis` (qx_choose_then `mut`
      (qx_choose_then `elem` (qx_choose_then `cap` (qx_choose_then `ast_slot`
        (map_every assume_tac o CONJUNCTS)))))) >>
     drule_all bodyAppendStorageLayoutFactsTheory.append_aggregate_target_layout >>
     strip_tac >>
     drule_all bodyAppendStorageFactsTheory.body_append_root_metadata >> strip_tac >>
     `body_expr_full_ok cx e` by metis_tac[] >>
     rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >>
     disch_then (map_every assume_tac o CONJUNCTS) >> suspend "compose") >>
  qpat_x_assum `supported_stmt _ _ _` mp_tac >>
  simp[Once supported_stmt_def, supportedStmtsTheory.supported_append_target_def] >>
  mp_tac (Q.INST [`nid` |-> `(NONE,nid1)`, `tops` |-> `tops`]
    bodyAppendStorageFactsTheory.supported_append_storage_decl) >>
  simp[] >> metis_tac[]
QED

Resume body_append_storage_word_frag_full[compose]:
  `cenv' = cenv` by
    (qpat_assum `stmt_env _ _ _ (Append _ e) sa = (cenv',sb)` (fn code =>
       qpat_assum `fn_has_code sa sb func` (fn has_code =>
         ACCEPT_TAC (CONJUNCT1 (MATCH_MP stmtSimAppendResolvedTheory.append_resolved_target_prefix
           (CONJ code has_code)))))) >>
  irule append_return_buf_sep >>
  asm_simp_tac bool_ss [] >>
  irule gas_outcome_full_initial_domain >>
  conj_tac >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  simp[] >> strip_tac >>
  drule stmtSimAppendStorageComposeTheory.append_toplevel_place_any >> strip_tac >>
  qmatch_asmsub_abbrev_tac `eval_target_place cx _ es = (INL place, observed)` >>
  `!tail. eval_target_place cx (TopLevelNameTarget (nid0,nid1))
      (es with gas_obs := tail) = (INL place, observed with gas_obs := tail)` by
    simp[Abbr `observed`, Abbr `place`, vyperStateTheory.evaluation_state_fupdfupds_comp] >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (eval_target_place cx (TopLevelNameTarget (nid0,nid1)))
      (es,s0,G0,tn0)
      (\H res ee G tn u. res = INL place /\ ee = observed with gas_obs := [] /\
        G = G0 /\ tn = tn0 /\ u = s0) (\H res ee gt r. F)` by
    (irule gas_outcome_full_pure >> simp[] >>
     qexistsl_tac [`G0`, `observed`, `INL place`, `s0`, `tn0`] >>
     simp[fragGasOriginPtrTheory.gas_origin_ptr_path_rules]) >>
  pure_once_rewrite_tac[vyperInterpreterTheory.evaluate_def] >>
  pure_rewrite_tac[GSYM bind_assoc] >>
  irule gas_outcome_full_bind_all >>
  conj_tac >- simp[vyperStorageTraceTheory.storage_trace_frame_bind,
    vyperStorageTraceTheory.evaluate_storage_trace_frame,
    vyperStorageTraceTheory.storage_trace_frame_read_result,
    vyperStorageTraceTheory.storage_trace_frame_append_place] >>
  conj_tac >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_place >>
    goal_assum (drule_at Any) >> fs[]) >>
  conj_tac >- metis_tac[gasExemptCertTheory.gas_exempt_cert_error_place] >>
  conj_tac >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _`
    (fn th => qpat_assum `nid0 = NONE`
      (fn src => mp_tac (PURE_REWRITE_RULE [src] th))) >>
  disch_then (fn th =>
    irule_at (Pos last) gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
    irule_at (Pos hd) th) >>
  qexists_tac `\H res ee G tn u. res = INL place /\ ee = observed with gas_obs := [] /\
        G = G0 /\ tn = tn0 /\ u = s0` >> simp[] >>
  suspend "after_root"
QED

Resume body_append_storage_word_frag_full[after_root]:
  rpt strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  disj1_tac >> qexists_tac `place` >> conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `!tail. eval_target_place cx (TopLevelNameTarget (NONE,nid1)) _ =
    (res,mid with gas_obs := tail)` kall_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> res = INL place /\ _` kall_tac >>
  qpat_x_assum `res = INL place` kall_tac >>
  qpat_x_assum `t = s0` SUBST_ALL_TAC >>
  qpat_x_assum `G1 = G0` SUBST_ALL_TAC >>
  qpat_x_assum `tn1 = tn0` SUBST_ALL_TAC >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx mid s0 /\
     storage_well_formed_on cx mid (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx mid G0 tn0 s0` by
    (gen_tac >> disch_tac >>
     `valid_horizon cx st0 H es.storage_trace` by
       ((irule gasOutcomeFullTheory.valid_horizon_append >>
        qexists_tac `[StorageRoot (mut = Transient) rslot (ArrayTV tv (Dynamic cap))]` >>
        fs[Abbr `observed`] >> (gvs[]))) >>
     qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     `mid.accounts = es.accounts /\ mid.tStorage = es.tStorage` by
       simp[Abbr `observed`] >>
     `storage_well_formed_on cx mid (FST H)` by
       metis_tac[vyperStorageFootprintTheory.storage_well_formed_on_backends] >>
     conj_tac >- simp[stmt_state_rel_start_gas_obs, Abbr `observed`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     `mid.scopes = es.scopes` by simp[Abbr `observed`] >>
     pure_rewrite_tac[bodyPtrDefsTheory.ghost_inv_at_def] >>
     qpat_assum `mid.scopes = es.scopes` SUBST1_TAC >>
     qpat_assum `ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0`
       (ACCEPT_TAC o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def])) >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    metis_tac[stateRelProjTheory.stmt_state_rel_vars_rels] >>
  `get_module_code cx nid0 = SOME tops` by
    (drule bodyStorageMetadataTheory.supported_variable_decl_mem >>
     strip_tac >> metis_tac[bodyInvCodePropsTheory.body_inv_main_code]) >>
  drule_all bodyAppendStorageFactsTheory.append_storage_compiler_location >> strip_tac >>
  `supported_pure_expr tops e` by
    (qpat_assum `supported_stmt _ _ _`
       (mp_tac o ONCE_REWRITE_RULE [supported_stmt_def]) >> simp[]) >>
  drule bodyAppendStorageFactsTheory.append_typing_target >> strip_tac >>
  `body_stmt_safe tops (Append (TopLevelNameTarget (nid0,nid1)) e)` by
    (drule bodyExprPreFactsTheory.supported_stmt_body_safe >> simp[]) >>
  `supported_expr tops e` by simp[supportedExprsTheory.supported_expr_def] >>
  drule_all bodyAppendStorageAdapterTheory.body_append_expr_pre >> strip_tac >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (`mid.immutables = es.immutables` by simp[Abbr `observed`] >>
     metis_tac[body_const_cells_agree_immutables]) >>
  `expr_body_pre cenv cx env e mid` by simp[Abbr `observed`] >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  `find_var_decl_by_name nid1 tops <> NONE` by simp[] >>
  `is_word_type elem` by
    (drule_all bodyAppendStorageFactsTheory.append_typed_storage_target >>
     strip_tac >> fs[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s0` by
    metis_tac[bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp] >>
  suspend "rhs_code"
QED

Resume body_append_storage_word_frag_full[rhs_code]:
  qpat_x_assum `nid0 = NONE` SUBST_ALL_TAC >>
  qpat_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _`
    (assume_tac o SRULE [gasShadowTheory.gas_shadow_stmt_def,
       gasShadowTheory.gas_shadow_expr_def]) >>
  `?vop raw_shadow sm shadow_sm. cenv' = cenv /\
     lower_value compile_expr cenv elem e sa = (vop,sm) /\
     lower_value compile_expr (gas_shadow_env T cenv) elem (gas_shadow_expr e) shadow_sa = (raw_shadow,shadow_sm) /\
     ci_mono sm sb /\ ci_mono shadow_sm shadow_sb` by
    (`type_slot_size tv = 1` by metis_tac[exprSimUnwrapTheory.word_type_slot_size] >>
       `type_memory_bytes cenv elem = 32` by simp[] >>
       every_drule stmtSimAppendStorageComposeTheory.append_storage_word_code_parts >>
       simp[] >>
       ntac 2 (disch_then (qspecl_then [`mut = Transient`,`n2w rslot`] mp_tac) >>
         (impl_tac >- simp[]) >> strip_tac) >>
       rename [`lower_value _ _ _ e sa = (vop,sm)`,
               `lower_value _ _ _ (gas_shadow_expr e) shadow_sa = (raw_shadow,shadow_sm)`] >>
       qexistsl_tac [`vop`,`raw_shadow`,`sm`,`shadow_sm`] >> simp[] >>
       rpt (goal_assum (drule_at Any)) >>
       simp[] >> metis_tac[ci_mono_compile_dynarray_append,pairTheory.SND]) >>
  `raw_shadow = vop /\ gas_shadow_state sm shadow_sm` by
    (irule bodyFullSharedTheory.gas_shadow_step >>
     qpat_assum `lower_value _ _ _ e sa = _` (irule_at Any) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr e) shadow_sa = _` (irule_at Any) >>
     simp[] >> irule gas_shadow_stmt_lower_value_env) >>
  qpat_x_assum `raw_shadow = vop` SUBST_ALL_TAC >>
  `ci_mono sa sm /\ ci_mono shadow_sa shadow_sm` by
    metis_tac[ci_mono_lower_value_compile_expr,pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func /\
   fn_has_code shadow_sa shadow_sm shadow_func` by
    (fs[ci_mono_def] >> metis_tac[fragExecTheory.fn_has_code_split]) >>
  `(!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
      not_fresh_at sa x)` by fs[loweringPostsTheory.ret_pc_ok_def] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok mid` by
    (irule expr_body_pre_gas_admissible >> goal_assum (drule_at Any)) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx elem e mid` by
    (fs[body_expr_full_ok_def] >> first_x_assum (irule o cj 1) >> metis_tac[]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`vop`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ Q1 R1` >>
  irule gas_outcome_full_bind_all >>
  conj_tac >- simp[vyperStorageTraceTheory.storage_trace_frame_append_place] >>
  conj_tac >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
    goal_assum (drule_at Any) >> gvs[]) >>
  conj_tac >- metis_tac[gasExemptCertTheory.gas_exempt_cert_error_value] >>
  conj_tac >- simp[vyperStorageTraceTheory.storage_trace_frame_bind,
    vyperStorageTraceTheory.evaluate_storage_trace_frame,
    vyperStorageTraceTheory.storage_trace_frame_read_result] >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` mp_tac >>
  disch_then (fn th =>
    irule_at (Pos last) gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
    irule_at (Pos hd) th) >>
  qexists_tac `\H res ee G tn t. Q1 H res ee G tn t /\ ~t.vs_halted` >>
  conj_tac >- simp[] >>
  conj_tac >- suspend "rhs_exit" >>
  simp[Abbr `Q1`] >> suspend "suffix"
QED

Resume body_append_storage_word_frag_full[rhs_exit]:
  simp[Abbr `R1`] >>
  qx_genl_tac [`H`, `result`, `ee`, `gt`, `r`] >>
  Cases_on `result` >> simp[exprSimDefsTheory.expr_exit_INL] >>
  strip_tac >> simp[stmt_exit_ptr_def] >>
  conj_tac >- metis_tac[stmtSimPropsTheory.expr_exit_INR_type] >>
  fs[exprSimDefsTheory.halt_exit_def] >>
  rpt strip_tac >> gvs[] >>
  rename1 `expr_exit (INR exc) (IntRet _ _)` >>
  qpat_assum `expr_exit (INR exc) (IntRet _ _)` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  Cases_on `exc` >> simp[exprSimDefsTheory.expr_exit_def] >>
  rename1 `expr_exit (INR (Error err)) (IntRet _ _)` >>
  Cases_on `err` >> simp[exprSimDefsTheory.expr_exit_def]
QED

Resume body_append_storage_word_frag_full[suffix]:
  rpt strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid'.storage_trace) mid'.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid'.storage_trace ==> (?v. _) /\ _`
    (qspec_then `storage_trace_horizon mid'.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (CONJUNCTS_THEN2 (qx_choose_then `v` STRIP_ASSUME_TAC) assume_tac) >>
  disj1_tac >> qexists_tac `v` >> conj_tac >- first_assum ACCEPT_TAC >>
  `!H. valid_horizon cx st0 H mid'.storage_trace ==>
       expr_post H ctx func cenv cx e (observed with gas_obs := []) sa sm s0 mid' v vop t /\
       ghost_inv_at (DF H) lo d cenv cx mid' G1 tn1 t` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid'.storage_trace ==> (?v. _) /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> gvs[]) >>
  qpat_assum `!tail. bind (eval_expr cx e) (read_result cx) _ = _`
    (qspec_then `[]` (assume_tac o SRULE [])) >>
  `?xs. mid'.storage_trace = mid.storage_trace ++ xs` by
    (qpat_assum `bind (eval_expr cx e) (read_result cx) _ = (res,_)` mp_tac >>
     qpat_assum `mid = observed with gas_obs := []` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     drule_at Any vyperStorageTraceTheory.storage_trace_frame_prefix >>
     simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
          vyperStorageTraceTheory.evaluate_storage_trace_frame,
          vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
  `!H. valid_horizon cx st0 H mid'.storage_trace ==>
       MEM (mut = Transient,n2w rslot,ArrayTV tv (Dynamic cap)) (FST H)` by
    (rpt gen_tac >> disch_tac >>
     irule vyperFiniteStoragePreservationTheory.storage_observations_ok_root >>
     qexistsl_tac [`cx`,`mid'.storage_trace`] >>
     simp[Abbr `observed`,listTheory.MEM_APPEND] >>
     gvs[vyperStorageFootprintTheory.valid_horizon_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid'.storage_trace) mid.storage_trace` by
    (irule gasOutcomeFullTheory.valid_horizon_append >>
     qexists_tac `xs` >> metis_tac[]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid'.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `mid.scopes = es.scopes` by simp[Abbr `observed`] >>
  `MAP FDOM mid'.scopes = MAP FDOM mid.scopes` by
    (qpat_assum `bind (eval_expr cx e) (read_result cx) _ = (res,_)`
       (mp_tac o MATCH_MP (REWRITE_RULE [ETA_AX]
         exprSimWordArgsTheory.forced_eval_expr_preserves_scopes_dom)) >>
     simp[Abbr `observed`]) >>
  `alloca_frame cenv es sa s0 cenv mid' t` by
    (`alloca_frame cenv mid sa s0 cenv mid' t` by
       (irule (INST_TYPE [alpha |-> ``:256``] stmtSimDefsTheory.expr_post_alloca_frame) >>
        metisTools.METIS_TAC []) >>
     qpat_assum `alloca_frame cenv mid sa s0 cenv mid' t` mp_tac >>
     qpat_assum `mid.scopes = es.scopes` (fn th =>
       rewrite_tac[stmtSimDefsTheory.alloca_frame_def,th])) >>
  qpat_assum `expr_post (storage_trace_horizon _) _ _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [expr_post_def]) >>
  qpat_assum `ci_mono sa sm`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [ci_mono_def]) >>
  `return_buf_frame d cenv sm t` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[]) >>
  qpat_assum `ghost_kept_at lo cenv _ sa G0 tn0 s0 G1 tn1`
    (fn th => qpat_assum `mid.scopes = es.scopes` (fn s_eq =>
       qpat_assum `mid = observed with gas_obs := []` (fn m_eq =>
         map_every assume_tac (CONJUNCTS
           (REWRITE_RULE [ghost_kept_at_def,GSYM m_eq,s_eq] th))))) >>
  `!H. valid_horizon cx st0 H mid'.storage_trace ==>
       stmt_state_rel H ctx func cenv cx mid' t /\
       storage_well_formed_on cx mid' (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx mid' G1 tn1 t /\
       MEM (mut = Transient,n2w rslot,ArrayTV tv (Dynamic cap)) (FST H)` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid'.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
       (map_every assume_tac o CONJUNCTS o REWRITE_RULE [expr_post_def]) >>
     qpat_assum `!H. valid_horizon _ _ H mid'.storage_trace ==> MEM _ (FST H)`
       (qspec_then `H` (drule_then assume_tac)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `gas_admissible (append_place cx place v) (stmt_res_ok lctx) mid'` by
    (qpat_assum `gas_admissible (eval_stmt _ _) _ es`
       (mp_tac o ONCE_REWRITE_RULE [vyperInterpreterTheory.evaluate_def]) >>
     qpat_assum `!tail. eval_target_place _ _ (es with gas_obs := tail) = _` mp_tac >>
     qpat_assum `!tail. bind (eval_expr cx e) (read_result cx) _ = _` mp_tac >>
     qpat_assum `res = INL v` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     strip_tac >> strip_tac >> strip_tac >>
     rewrite_tac[GSYM bind_assoc, gasContextTheory.gas_admissible_def] >> strip_tac >>
     qx_gen_tac `gs` >> rpt gen_tac >> disch_tac >>
     qpat_assum `!gs res ee. _ ==> stmt_res_ok lctx res`
       (qspec_then `gas_explicit marks s0.vs_gas_readings ++ gs` mp_tac) >>
     simp[Once bind_def] >> simp[Once bind_def]) >>
  `expr_sim_inv cenv cx env mid' /\ value_runtime_typed env (expr_type e) v` by
    (`expr_body_pre cenv cx env e
        (observed with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
       (qpat_assum `expr_body_pre cenv cx env e mid` mp_tac >>
        qpat_assum `mid = observed with gas_obs := []` SUBST1_TAC >>
        simp[exprSimSourceTheory.expr_body_pre_gas_obs]) >>
     qpat_assum `expr_body_pre _ _ _ _ (observed with gas_obs := _)` mp_tac >>
     qpat_assum `bind (eval_expr cx e) (read_result cx)
       (observed with gas_obs := _) = _` mp_tac >>
     qpat_assum `res = INL v` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[] >>
     drule_at (Pat `bind _ _ _ = _`)
       (SRULE [SF ETA_ss] bodySimStmtFactsTheory.expr_body_pre_eval) >>
     disch_then (qspecl_then [`cenv`,`env`] mp_tac) >> simp[]) >>
  simp[Abbr `place`] >>
  suspend "word"
QED

Resume body_append_storage_word_frag_full[word]:
  `env_consistent env cx es /\ env.type_defs = get_tenv cx` by
    (qpat_assum `expr_sim_inv cenv cx env es` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     rewrite_tac[expr_sim_inv_def] >> strip_tac >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_x_assum `env_consistent env cx es` mp_tac >>
     rewrite_tac[vyperTypeInvariantsTheory.env_consistent_def,
                 vyperTypeInvariantsTheory.env_context_consistent_def] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `elem' = elem` by
    (`find_var_decl_by_name nid1 tops <> NONE` by simp[] >>
     drule_all bodyAppendStorageFactsTheory.append_typed_storage_target >>
     simp[] >> strip_tac >> gvs[]) >>
  `expr_type e = elem` by
    metis_tac[compileEnvTheory.type_widens_to_word] >>
  `type_slot_size tv = 1` by metis_tac[exprSimUnwrapTheory.word_type_slot_size] >>
  `cap < dimword (:256)` by
    (qpat_assum `type_slot_size (ArrayTV tv (Dynamic cap)) < _` mp_tac >>
     qpat_assum `type_slot_size tv = 1` (fn th =>
       rewrite_tac[vyperValueTheory.type_slot_size_def,th,arithmeticTheory.MULT_RIGHT_1]) >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  `value_has_type tv v` by
    (qpat_assum `value_runtime_typed env (expr_type e) v` (fn typed =>
       qpat_assum `expr_type e = elem` (fn ty =>
         qpat_assum `env.type_defs = get_tenv cx` (fn tenv =>
           qpat_assum `evaluate_type (get_tenv cx) elem = SOME tv` (fn tv =>
             mp_tac (REWRITE_RULE
               [vyperTypeExprSoundnessTheory.value_runtime_typed_def,ty,tenv,tv] typed))))) >>
     simp[]) >>
  suspend "word_operand"
QED

Resume body_append_storage_word_frag_full[word_operand]:
  `eval_operand vop t = SOME (typed_val_to_w256 tv v)` by
    (drule exprSimPrecompilesTheory.expr_post_typed_stack_operand >> simp[]) >>
  `op_taint tn1 vop = {}` by
    (qpat_assum `ptr_val_ok cx _ v vop G1 tn1 t`
       (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [bodyPtrDefsTheory.ptr_val_ok_def])) >>
  `!x. vop = Var x ==> not_fresh_at sm x` by
    ((metisTools.METIS_TAC [exprSimSourceTheory.expr_body_pre_lower_value_word_shape])) >>
  `type_memory_bytes cenv elem = 32` by simp[] >>
  `compile_dynarray_append cenv (Lit (n2w rslot)) vop 1 1 elem
     (lowered_value_type cenv e) cap T (if mut = Transient then LocTransient else LocStorage)
     sm = ((),sb)` by
    (qpat_assum `stmt_env _ _ _ (Append _ e) sa = _`
       (mp_then (Pos hd) mp_tac stmtSimAppendStorageComposeTheory.append_storage_word_code_parts) >>
     disch_then (qspecl_then [`mut = Transient`,`n2w rslot`] mp_tac) >> simp[]) >>
  `!H. valid_horizon cx st0 H mid'.storage_trace ==>
       stmt_state_rel H ctx func cenv cx mid' t /\
       storage_well_formed_on cx mid' (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx mid' G1 tn1 t /\
       storage_place_observed H (StoragePlace (mut = Transient) (n2w rslot)
         (ArrayTV tv (Dynamic cap)))` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid'.storage_trace ==> _ /\ _ /\ _ /\ MEM _ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     simp[vyperStoragePlaceObservedTheory.storage_place_observed_def] >>
     qexistsl_tac [`n2w rslot`,`ArrayTV tv (Dynamic cap)`,`[]`,`0`] >>
     simp[vyperStoragePlaceRegionTheory.storage_subregion_def,wordsTheory.WORD_ADD_0]) >>
  irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
  irule_at (Pat `gas_outcome_full _ _ _ _ _ _ _ _`)
    (Q.INST [`R` |-> `\H res ee gt r.
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
      halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==>
        allocas_below_fmp s)`] append_nested_suffix_frame_post) >>
  qexistsl_tac [`tn0`,`sm`,`sb`,`sa`,`s0`,`lctx`,`es`,`d`,`cenv`,`RetQ`,`G0`] >>
  simp[] >> conj_tac >- first_assum ACCEPT_TAC >> conj_tac >-
    (`ctx_has_dalloca ctx ==> allocas_below_fmp t` by
       metis_tac[bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp] >>
     irule append_nested_storage_cont_framed >>
     qpat_assum `compile_dynarray_append cenv (Lit _) vop 1 1 _ _ _ _ _ sm = _`
       (irule_at Any) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     simp[venomStateTheory.eval_operand_def,ptrDisciplineTheory.op_taint_def] >>
     qexists_tac `env` >>
     `cx_tops cx = tops` by metis_tac[bodyInvCodePropsTheory.body_inv_main_code] >> simp[]) >>
  rpt gen_tac >> disch_then (qx_choose_then `cenvf` strip_assume_tac) >>
  qexists_tac `cenvf` >> simp[] >>
  conj_tac >-
    (qpat_assum `stmt_state_rel H ctx func cenvf cx ee t'`
      (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  first_assum ACCEPT_TAC
QED

Finalise body_append_storage_word_frag_full

Theorem body_append_storage_aggregate_frag_full[local]:
  !cx nid e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv
    env env' ret_ty lctx RetQ es elem cap.
  (!s p t. eval_target_place cx (TopLevelNameTarget nid) s = (INL p,t) ==>
     body_expr_full_ok cx e) /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (Append (TopLevelNameTarget nid) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Append (TopLevelNameTarget nid) e) ==> occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
  locals_alloc_ok cenv env /\
  type_stmt env ret_ty (Append (TopLevelNameTarget nid) e) = SOME env' /\
  type_place_target env (TopLevelNameTarget nid) = SOME (Type (ArrayT elem (Dynamic cap))) /\
  ~is_word_type elem /\
  stmt_exprs_ok cenv (Append (TopLevelNameTarget nid) e) /\
  call_evaluation_safe cx (int_calls_stmt (Append (TopLevelNameTarget nid) e)) /\
  frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ cenv ret_ty ==>
  stmt_frag_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (Append (TopLevelNameTarget nid) e))
    (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Append (TopLevelNameTarget nid) e)))
    (eval_stmt cx (Append (TopLevelNameTarget nid) e)) es
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `type_place_target env (TopLevelNameTarget nid) =
    SOME (Type (ArrayT checked_elem (Dynamic checked_cap)))` >>
  PairCases_on `nid` >>
  `nid0 = NONE` by metis_tac[bodyTypedTargetScopeTheory.body_inv_toplevel_target_main,
                              optionTheory.IS_SOME_EXISTS] >>
  `?vis mut elem cap ast_slot.
     supported_variable_decl tops (nid0,nid1) =
       SOME (vis,mut,ArrayT elem (Dynamic cap),SOME ast_slot) /\
     (mut = Storage \/ mut = Transient)` suffices_by
    (disch_then (qx_choose_then `vis` (qx_choose_then `mut`
      (qx_choose_then `elem` (qx_choose_then `cap` (qx_choose_then `ast_slot`
        (map_every assume_tac o CONJUNCTS)))))) >>
     drule_all bodyAppendStorageLayoutFactsTheory.append_aggregate_target_layout >>
     strip_tac >>
     drule_all bodyAppendStorageFactsTheory.body_append_root_metadata >> strip_tac >>
     `body_expr_full_ok cx e` by metis_tac[] >>
     rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >>
     disch_then (map_every assume_tac o CONJUNCTS) >> suspend "compose") >>
  qpat_x_assum `supported_stmt _ _ _` mp_tac >>
  simp[Once supported_stmt_def, supportedStmtsTheory.supported_append_target_def] >>
  mp_tac (Q.INST [`nid` |-> `(NONE,nid1)`, `tops` |-> `tops`]
    bodyAppendStorageFactsTheory.supported_append_storage_decl) >>
  simp[] >> metis_tac[]
QED

Resume body_append_storage_aggregate_frag_full[compose]:
  `cenv' = cenv` by
    (qpat_assum `stmt_env _ _ _ (Append _ e) sa = (cenv',sb)` (fn code =>
       qpat_assum `fn_has_code sa sb func` (fn has_code =>
         ACCEPT_TAC (CONJUNCT1 (MATCH_MP stmtSimAppendResolvedTheory.append_resolved_target_prefix
           (CONJ code has_code)))))) >>
  irule append_return_buf_sep >>
  asm_simp_tac bool_ss [] >>
  irule gas_outcome_full_initial_domain >>
  conj_tac >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  simp[] >> strip_tac >>
  drule stmtSimAppendStorageComposeTheory.append_toplevel_place_any >> strip_tac >>
  qmatch_asmsub_abbrev_tac `eval_target_place cx _ es = (INL place, observed)` >>
  `!tail. eval_target_place cx (TopLevelNameTarget (nid0,nid1))
      (es with gas_obs := tail) = (INL place, observed with gas_obs := tail)` by
    simp[Abbr `observed`, Abbr `place`, vyperStateTheory.evaluation_state_fupdfupds_comp] >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (eval_target_place cx (TopLevelNameTarget (nid0,nid1)))
      (es,s0,G0,tn0)
      (\H res ee G tn u. res = INL place /\ ee = observed with gas_obs := [] /\
        G = G0 /\ tn = tn0 /\ u = s0) (\H res ee gt r. F)` by
    (irule gas_outcome_full_pure >> simp[] >>
     qexistsl_tac [`G0`, `observed`, `INL place`, `s0`, `tn0`] >>
     simp[fragGasOriginPtrTheory.gas_origin_ptr_path_rules]) >>
  pure_once_rewrite_tac[vyperInterpreterTheory.evaluate_def] >>
  pure_rewrite_tac[GSYM bind_assoc] >>
  irule gas_outcome_full_bind_all >>
  conj_tac >- simp[vyperStorageTraceTheory.storage_trace_frame_bind,
    vyperStorageTraceTheory.evaluate_storage_trace_frame,
    vyperStorageTraceTheory.storage_trace_frame_read_result,
    vyperStorageTraceTheory.storage_trace_frame_append_place] >>
  conj_tac >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_place >>
    goal_assum (drule_at Any) >> fs[]) >>
  conj_tac >- metis_tac[gasExemptCertTheory.gas_exempt_cert_error_place] >>
  conj_tac >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _`
    (fn th => qpat_assum `nid0 = NONE`
      (fn src => mp_tac (PURE_REWRITE_RULE [src] th))) >>
  disch_then (fn th =>
    irule_at (Pos last) gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
    irule_at (Pos hd) th) >>
  qexists_tac `\H res ee G tn u. res = INL place /\ ee = observed with gas_obs := [] /\
        G = G0 /\ tn = tn0 /\ u = s0` >> simp[] >>
  suspend "after_root"
QED

Resume body_append_storage_aggregate_frag_full[after_root]:
  rpt strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  disj1_tac >> qexists_tac `place` >> conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `!tail. eval_target_place cx (TopLevelNameTarget (NONE,nid1)) _ =
    (res,mid with gas_obs := tail)` kall_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> res = INL place /\ _` kall_tac >>
  qpat_x_assum `res = INL place` kall_tac >>
  qpat_x_assum `t = s0` SUBST_ALL_TAC >>
  qpat_x_assum `G1 = G0` SUBST_ALL_TAC >>
  qpat_x_assum `tn1 = tn0` SUBST_ALL_TAC >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx mid s0 /\
     storage_well_formed_on cx mid (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx mid G0 tn0 s0` by
    (gen_tac >> disch_tac >>
     `valid_horizon cx st0 H es.storage_trace` by
       ((irule gasOutcomeFullTheory.valid_horizon_append >>
        qexists_tac `[StorageRoot (mut = Transient) rslot (ArrayTV tv (Dynamic cap))]` >>
        fs[Abbr `observed`] >> (gvs[]))) >>
     qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     `mid.accounts = es.accounts /\ mid.tStorage = es.tStorage` by
       simp[Abbr `observed`] >>
     `storage_well_formed_on cx mid (FST H)` by
       metis_tac[vyperStorageFootprintTheory.storage_well_formed_on_backends] >>
     conj_tac >- simp[stmt_state_rel_start_gas_obs, Abbr `observed`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     `mid.scopes = es.scopes` by simp[Abbr `observed`] >>
     pure_rewrite_tac[bodyPtrDefsTheory.ghost_inv_at_def] >>
     qpat_assum `mid.scopes = es.scopes` SUBST1_TAC >>
     qpat_assum `ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0`
       (ACCEPT_TAC o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def])) >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    metis_tac[stateRelProjTheory.stmt_state_rel_vars_rels] >>
  `get_module_code cx nid0 = SOME tops` by
    (drule bodyStorageMetadataTheory.supported_variable_decl_mem >>
     strip_tac >> metis_tac[bodyInvCodePropsTheory.body_inv_main_code]) >>
  drule_all bodyAppendStorageFactsTheory.append_storage_compiler_location >> strip_tac >>
  `supported_pure_expr tops e` by
    (qpat_assum `supported_stmt _ _ _`
       (mp_tac o ONCE_REWRITE_RULE [supported_stmt_def]) >> simp[]) >>
  drule bodyAppendStorageFactsTheory.append_typing_target >> strip_tac >>
  `body_stmt_safe tops (Append (TopLevelNameTarget (nid0,nid1)) e)` by
    (drule bodyExprPreFactsTheory.supported_stmt_body_safe >> simp[]) >>
  `supported_expr tops e` by simp[supportedExprsTheory.supported_expr_def] >>
  drule_all bodyAppendStorageAdapterTheory.body_append_expr_pre >> strip_tac >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (`mid.immutables = es.immutables` by simp[Abbr `observed`] >>
     metis_tac[body_const_cells_agree_immutables]) >>
  `expr_body_pre cenv cx env e mid` by simp[Abbr `observed`] >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  `find_var_decl_by_name nid1 tops <> NONE` by simp[] >>
  `~is_word_type elem` by
    (drule_all bodyAppendStorageFactsTheory.append_typed_storage_target >>
     strip_tac >> fs[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s0` by
    metis_tac[bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp] >>
  suspend "rhs_code"
QED

Resume body_append_storage_aggregate_frag_full[rhs_code]:
  qpat_x_assum `nid0 = NONE` SUBST_ALL_TAC >>
  qpat_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _`
    (assume_tac o SRULE [gasShadowTheory.gas_shadow_stmt_def,
       gasShadowTheory.gas_shadow_expr_def]) >>
  `?vop raw_shadow sm shadow_sm. cenv' = cenv /\
     lower_value compile_expr cenv elem e sa = (vop,sm) /\
     lower_value compile_expr (gas_shadow_env T cenv) elem (gas_shadow_expr e) shadow_sa = (raw_shadow,shadow_sm) /\
     ci_mono sm sb /\ ci_mono shadow_sm shadow_sb` by
    (every_drule stmtSimAppendStorageComposeTheory.append_storage_copy_code_parts >>
     simp[] >>
     ntac 2 (disch_then (qspecl_then [`mut = Transient`,`n2w rslot`] mp_tac) >>
       (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac) >>
     rename [`lower_value _ _ _ e sa = (vop,sm)`,
             `lower_value _ _ _ (gas_shadow_expr e) shadow_sa = (raw_shadow,shadow_sm)`] >>
     qexistsl_tac [`vop`,`raw_shadow`,`sm`,`shadow_sm`] >> simp[] >>
     metis_tac[ci_mono_compile_dynarray_append,ci_mono_compile_alloc_buffer,
       ci_mono_compile_store_memory,exprLoweringPropsTheory.ci_mono_trans,pairTheory.SND]) >>
  `raw_shadow = vop /\ gas_shadow_state sm shadow_sm` by
    (irule bodyFullSharedTheory.gas_shadow_step >>
     qpat_assum `lower_value _ _ _ e sa = _` (irule_at Any) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr e) shadow_sa = _` (irule_at Any) >>
     simp[] >> irule gas_shadow_stmt_lower_value_env) >>
  qpat_x_assum `raw_shadow = vop` SUBST_ALL_TAC >>
  `ci_mono sa sm /\ ci_mono shadow_sa shadow_sm` by
    metis_tac[ci_mono_lower_value_compile_expr,pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func /\
   fn_has_code shadow_sa shadow_sm shadow_func` by
    (fs[ci_mono_def] >> metis_tac[fragExecTheory.fn_has_code_split]) >>
  `(!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
      not_fresh_at sa x)` by fs[loweringPostsTheory.ret_pc_ok_def] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok mid` by
    (irule expr_body_pre_gas_admissible >> goal_assum (drule_at Any)) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx elem e mid` by
    (qpat_assum `body_expr_full_ok cx e`
       (mp_tac o ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
     qpat_assum `body_inv tops ctx cenv cx` mp_tac >>
     qpat_assum `shadow_body_inv tops ctx shadow_ctx` mp_tac >>
     qpat_assum `body_const_cells_agree [(NONE,tops)] cx env mid` mp_tac >>
     qpat_assum `expr_body_pre cenv cx env e mid` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`vop`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ Q1 R1` >>
  irule gas_outcome_full_bind_all >>
  conj_tac >- simp[vyperStorageTraceTheory.storage_trace_frame_append_place] >>
  conj_tac >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
    goal_assum (drule_at Any) >> gvs[]) >>
  conj_tac >- metis_tac[gasExemptCertTheory.gas_exempt_cert_error_value] >>
  conj_tac >- simp[vyperStorageTraceTheory.storage_trace_frame_bind,
    vyperStorageTraceTheory.evaluate_storage_trace_frame,
    vyperStorageTraceTheory.storage_trace_frame_read_result] >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` mp_tac >>
  disch_then (fn th =>
    irule_at (Pos last) gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
    irule_at (Pos hd) th) >>
  qexists_tac `\H res ee G tn t. Q1 H res ee G tn t /\ ~t.vs_halted` >>
  conj_tac >- simp[] >>
  conj_tac >- suspend "rhs_exit" >>
  simp[Abbr `Q1`] >> suspend "suffix"
QED

Resume body_append_storage_aggregate_frag_full[rhs_exit]:
  simp[Abbr `R1`] >>
  qx_genl_tac [`H`, `result`, `ee`, `gt`, `r`] >>
  Cases_on `result` >> simp[exprSimDefsTheory.expr_exit_INL] >>
  strip_tac >> simp[stmt_exit_ptr_def] >>
  conj_tac >- metis_tac[stmtSimPropsTheory.expr_exit_INR_type] >>
  fs[exprSimDefsTheory.halt_exit_def] >>
  rpt strip_tac >> gvs[] >>
  rename1 `expr_exit (INR exc) (IntRet _ _)` >>
  qpat_assum `expr_exit (INR exc) (IntRet _ _)` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  Cases_on `exc` >> simp[exprSimDefsTheory.expr_exit_def] >>
  rename1 `expr_exit (INR (Error err)) (IntRet _ _)` >>
  Cases_on `err` >> simp[exprSimDefsTheory.expr_exit_def]
QED

Resume body_append_storage_aggregate_frag_full[suffix]:
  rpt strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid'.storage_trace) mid'.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid'.storage_trace ==> (?v. _) /\ _`
    (qspec_then `storage_trace_horizon mid'.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (CONJUNCTS_THEN2 (qx_choose_then `v` STRIP_ASSUME_TAC) assume_tac) >>
  disj1_tac >> qexists_tac `v` >> conj_tac >- first_assum ACCEPT_TAC >>
  `!H. valid_horizon cx st0 H mid'.storage_trace ==>
       expr_post H ctx func cenv cx e (observed with gas_obs := []) sa sm s0 mid' v vop t /\
       ghost_inv_at (DF H) lo d cenv cx mid' G1 tn1 t` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid'.storage_trace ==> (?v. _) /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> gvs[]) >>
  qpat_assum `!tail. bind (eval_expr cx e) (read_result cx) _ = _`
    (qspec_then `[]` (assume_tac o SRULE [])) >>
  `?xs. mid'.storage_trace = mid.storage_trace ++ xs` by
    (qpat_assum `bind (eval_expr cx e) (read_result cx) _ = (res,_)` mp_tac >>
     qpat_assum `mid = observed with gas_obs := []` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     drule_at Any vyperStorageTraceTheory.storage_trace_frame_prefix >>
     simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
          vyperStorageTraceTheory.evaluate_storage_trace_frame,
          vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
  `!H. valid_horizon cx st0 H mid'.storage_trace ==>
       MEM (mut = Transient,n2w rslot,ArrayTV tv (Dynamic cap)) (FST H)` by
    (rpt gen_tac >> disch_tac >>
     irule vyperFiniteStoragePreservationTheory.storage_observations_ok_root >>
     qexistsl_tac [`cx`,`mid'.storage_trace`] >>
     simp[Abbr `observed`,listTheory.MEM_APPEND] >>
     gvs[vyperStorageFootprintTheory.valid_horizon_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid'.storage_trace) mid.storage_trace` by
    (irule gasOutcomeFullTheory.valid_horizon_append >>
     qexists_tac `xs` >> metis_tac[]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid'.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `mid.scopes = es.scopes` by simp[Abbr `observed`] >>
  `MAP FDOM mid'.scopes = MAP FDOM mid.scopes` by
    (qpat_assum `bind (eval_expr cx e) (read_result cx) _ = (res,_)`
       (mp_tac o MATCH_MP (REWRITE_RULE [ETA_AX]
         exprSimWordArgsTheory.forced_eval_expr_preserves_scopes_dom)) >>
     simp[Abbr `observed`]) >>
  `alloca_frame cenv es sa s0 cenv mid' t` by
    (`alloca_frame cenv mid sa s0 cenv mid' t` by
       (irule (INST_TYPE [alpha |-> ``:256``] stmtSimDefsTheory.expr_post_alloca_frame) >>
        metisTools.METIS_TAC []) >>
     qpat_assum `alloca_frame cenv mid sa s0 cenv mid' t` mp_tac >>
     qpat_assum `mid.scopes = es.scopes` (fn th =>
       rewrite_tac[stmtSimDefsTheory.alloca_frame_def,th])) >>
  qpat_assum `expr_post (storage_trace_horizon _) _ _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [expr_post_def]) >>
  qpat_assum `ci_mono sa sm`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [ci_mono_def]) >>
  `return_buf_frame d cenv sm t` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[]) >>
  qpat_assum `ghost_kept_at lo cenv _ sa G0 tn0 s0 G1 tn1`
    (fn th => qpat_assum `mid.scopes = es.scopes` (fn s_eq =>
       qpat_assum `mid = observed with gas_obs := []` (fn m_eq =>
         map_every assume_tac (CONJUNCTS
           (REWRITE_RULE [ghost_kept_at_def,GSYM m_eq,s_eq] th))))) >>
  `!H. valid_horizon cx st0 H mid'.storage_trace ==>
       stmt_state_rel H ctx func cenv cx mid' t /\
       storage_well_formed_on cx mid' (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx mid' G1 tn1 t /\
       MEM (mut = Transient,n2w rslot,ArrayTV tv (Dynamic cap)) (FST H)` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid'.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
       (map_every assume_tac o CONJUNCTS o REWRITE_RULE [expr_post_def]) >>
     qpat_assum `!H. valid_horizon _ _ H mid'.storage_trace ==> MEM _ (FST H)`
       (qspec_then `H` (drule_then assume_tac)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `gas_admissible (append_place cx place v) (stmt_res_ok lctx) mid'` by
    (qpat_assum `gas_admissible (eval_stmt _ _) _ es`
       (mp_tac o ONCE_REWRITE_RULE [vyperInterpreterTheory.evaluate_def]) >>
     qpat_assum `!tail. eval_target_place _ _ (es with gas_obs := tail) = _` mp_tac >>
     qpat_assum `!tail. bind (eval_expr cx e) (read_result cx) _ = _` mp_tac >>
     qpat_assum `res = INL v` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     strip_tac >> strip_tac >> strip_tac >>
     rewrite_tac[GSYM bind_assoc, gasContextTheory.gas_admissible_def] >> strip_tac >>
     qx_gen_tac `gs` >> rpt gen_tac >> disch_tac >>
     qpat_assum `!gs res ee. _ ==> stmt_res_ok lctx res`
       (qspec_then `gas_explicit marks s0.vs_gas_readings ++ gs` mp_tac) >>
     simp[Once bind_def] >> simp[Once bind_def]) >>
  `expr_sim_inv cenv cx env mid' /\ value_runtime_typed env (expr_type e) v` by
    (`expr_body_pre cenv cx env e
        (observed with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
       (qpat_assum `expr_body_pre cenv cx env e mid` mp_tac >>
        qpat_assum `mid = observed with gas_obs := []` SUBST1_TAC >>
        simp[exprSimSourceTheory.expr_body_pre_gas_obs]) >>
     qpat_assum `expr_body_pre _ _ _ _ (observed with gas_obs := _)` mp_tac >>
     qpat_assum `bind (eval_expr cx e) (read_result cx)
       (observed with gas_obs := _) = _` mp_tac >>
     qpat_assum `res = INL v` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[] >>
     drule_at (Pat `bind _ _ _ = _`)
       (SRULE [SF ETA_ss] bodySimStmtFactsTheory.expr_body_pre_eval) >>
     disch_then (qspecl_then [`cenv`,`env`] mp_tac) >> simp[]) >>
  simp[Abbr `place`] >>
  suspend "aggregate"
QED

Resume body_append_storage_aggregate_frag_full[aggregate]:
  `type_memory_bytes cenv elem = type_memory_size tv` by
    simp[valueEncodingPropsTheory.type_memory_size_slots] >>
  `(type_memory_bytes cenv elem + 31) DIV 32 = type_slot_size tv` by
    (simp[IgnAsm `type_memory_bytes cenv elem = type_memory_size tv`,
          arithmeticTheory.ADD_DIV_RWT]) >>
  qpat_assum `stmt_env _ _ _ (Append _ e) sa = _`
    (mp_then (Pos hd) mp_tac stmtSimAppendStorageComposeTheory.append_storage_copy_code_parts) >>
  disch_then (qspecl_then [`mut = Transient`,`n2w rslot`] mp_tac) >>
  simp[] >> strip_tac >> suspend "aggregate_typed"
QED

Resume body_append_storage_aggregate_frag_full[aggregate_typed]:
  `env.type_defs = get_tenv cx` by
    (qpat_assum `env_consistent env cx es` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     rewrite_tac[vyperTypeInvariantsTheory.env_consistent_def,
                 vyperTypeInvariantsTheory.env_context_consistent_def] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `elem' = elem` by
    (drule_all bodyAppendStorageFactsTheory.append_typed_storage_target >>
     simp[] >> strip_tac >> gvs[]) >>
  `type_widens_to (get_tenv cx) (expr_type e) elem` by
    (qpat_assum `env.type_defs = get_tenv cx` (fn tenv =>
       qpat_assum `elem' = elem` (fn equality =>
         qpat_assum `type_widens_to env.type_defs (expr_type e) elem'`
           (ACCEPT_TAC o REWRITE_RULE [tenv,equality])))) >>
  `value_has_type tv v` by
    (qpat_assum `type_widens_to (get_tenv cx) (expr_type e) elem` mp_tac >>
     qpat_assum `evaluate_type (get_tenv cx) elem = SOME tv` mp_tac >>
     qpat_assum `value_runtime_typed env (expr_type e) v` mp_tac >>
     qpat_assum `env.type_defs = get_tenv cx` (fn tenv =>
       POP_ASSUM_LIST (K all_tac) >>
       rewrite_tac[vyperTypeExprSoundnessTheory.value_runtime_typed_def,tenv]) >>
     metis_tac[vyperTypeArgFitsTheory.type_widens_to_value_has_type,
               optionTheory.SOME_11]) >>
  `val_wf tv v` by
    (irule (cj 1 valueEncodingTypingTheory.value_has_type_val_wf) >> simp[]) >>
  `?writes. encode_value tv v = SOME writes` by
    (rewrite_tac[GSYM optionTheory.IS_SOME_EXISTS] >>
     irule (cj 1 vyperTypingTheory.value_has_type_equiv) >> simp[]) >>
  `well_formed_type_value tv` by
    (drule vyperTypeValuesTheory.evaluate_type_well_formed_type_value >> simp[]) >>
  `cap < dimword (:256)` by
    (`cap <= cap * type_slot_size tv` by
       (Cases_on `type_slot_size tv` >> fs[] >> simp[arithmeticTheory.MULT_CLAUSES]) >>
     qpat_assum `type_slot_size (ArrayTV tv (Dynamic cap)) < _` mp_tac >>
     qpat_assum `cap <= cap * type_slot_size tv` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     pure_rewrite_tac[type_slot_size_def, bound_length_def] >> decide_tac) >>
  drule_all_then strip_assume_tac
    immutableDeployAssignRangesTheory.immutable_assign_copy_metadata >>
  `local_ptrs_reserved cenv sm` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `sa` >> simp[]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[] >> goal_assum (drule_at Any)) >>
  suspend "aggregate_rhs"
QED

Resume body_append_storage_aggregate_frag_full[aggregate_rhs]:
  `type_widens_to env.type_defs (expr_type e) elem` by simp[] >>
  drule_all_then assume_tac immutableDeployPhysicalSourceTheory.immutable_rhs_physical_widens >>
  `~is_word_type (lowered_value_type cenv e)` by
    metis_tac[typedMemoryCopyTheory.return_source_word_widens_eq] >>
  drule immutableDeployPhysicalSourceTheory.immutable_rhs_post_physical_classify >>
  disch_then assume_tac >>
  `~is_word_type (post_value_type cenv e)` by
    metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
  `expr_body_pre cenv cx env e
      (observed with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    (qpat_assum `expr_body_pre cenv cx env e mid` mp_tac >>
     qpat_assum `mid = observed with gas_obs := []` SUBST1_TAC >>
     simp[exprSimSourceTheory.expr_body_pre_gas_obs]) >>
  `bind (eval_expr cx e) (read_result cx)
      (observed with gas_obs := gas_explicit marks s0.vs_gas_readings) =
      (INL v,mid' with gas_obs := [])` by simp[] >>
  drule_all_then (qx_choose_then `stv` strip_assume_tac)
    (SRULE [SF ETA_ss] immutableDeployPhysicalSourceTheory.immutable_rhs_physical_typed) >>
  `0 < type_memory_size stv` by
    (drule_all placeMemoryTypeInterfacesTheory.type_widens_to_zero_memory_size >>
     simp[valueEncodingPropsTheory.type_memory_size_slots]) >>
  `expr_val_at cenv cx (lowered_value_type cenv e) sa sm mid' v vop t` by
    suspend "physical_at" >>
  `expr_post (storage_trace_horizon mid'.storage_trace) ctx func cenv cx e
      (observed with gas_obs := gas_explicit marks s0.vs_gas_readings)
      sa sm s0 (mid' with gas_obs := []) v vop t` by
    (qpat_assum `expr_post (storage_trace_horizon mid'.storage_trace) _ _ _ _ _ _ _ _ _ mid' _ _ _`
       mp_tac >>
     pure_rewrite_tac[exprSimExtract32PostTheory.extract32_expr_post_start_gas_obs,
                      exprSimExtract32PostTheory.extract32_expr_post_end_gas_obs] >>
     simp_tac bool_ss []) >>
  drule_all_then (qx_choose_then `ptv` (qx_choose_then `sw` strip_assume_tac))
    (SRULE [SF ETA_ss] immutableDeployPhysicalSourceTheory.immutable_rhs_physical_memory) >>
  `val_store_size stv v = val_store_size ptv v` by
    suspend "source_store_size" >>
  `0 < val_store_size stv v` by simp[bodyDeclCopyMemoryTheory.val_store_size_pos] >>
  `w2n sw + val_store_size stv v <= t.vs_alloca_next` by
    (qpat_assum `expr_store_bound cx (post_value_type cenv e) v vop t`
       (mp_tac o REWRITE_RULE [exprSimMemDefsTheory.expr_store_bound_def]) >>
     disch_then (qspecl_then [`ptv`,`sw`] mp_tac) >> simp[] >> decide_tac) >>
  `t.vs_alloca_next < dimword (:256)` by
    (qpat_assum `stmt_state_rel (storage_trace_horizon mid'.storage_trace) ctx func cenv cx mid' t`
       (mp_then (Pos hd) assume_tac stateRelProjTheory.stmt_state_rel_alloca_room) >>
     drule exprLoweringPropsTheory.alloca_room_next_lt >> simp[]) >>
  `w2n sw + val_store_size stv v < dimword (:256)` by decide_tac >>
  `ptr_buf_ok cenv e vop G1 t /\ op_taint tn1 vop = {}` by
    (qpat_assum `ptr_val_ok cx (post_value_type cenv e) _ _ _ _ _`
       (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.ptr_val_ok_def]) >>
     simp[]) >>
  `?src. vop = Var src /\ ptr_covers G1 tn1 src t (type_memory_size stv)` by
    (irule assignBasePtrBoundaryTheory.ptr_buf_ok_read_covers >>
     simp[] >> qexistsl_tac [`cenv`,`e`] >> simp[]) >>
  `not_fresh_at sm src` by
    (drule_all exprOperandVarTheory.compile_lower_value_var >> simp[]) >>
  `lookup_var src t = SOME sw` by
    fs[venomStateTheory.eval_operand_def] >>
  `!mem. mem_agree_outside tn1.t_mem t.vs_memory mem ==>
     val_in_memory stv v (w2n sw) mem` by
    (drule_all
      (SRULE [SF ETA_ss] bodyFullStructLitPhysicalTheory.structlit_child_physical_robust) >>
     strip_tac >> gvs[]) >>
  qpat_x_assum `vop = Var src` SUBST_ALL_TAC >>
  suspend "aggregate_cont"
QED

Resume body_append_storage_aggregate_frag_full[physical_at]:
  qpat_assum `expr_post (storage_trace_horizon mid'.storage_trace) _ _ _ _ _ _ _ _ _ mid' _ _ _`
    (mp_then (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
      mp_tac abiEncodeArgsSimTheory.abi_args_expr_post_lowered_at) >>
  simp[] >> metis_tac[]
QED

Resume body_append_storage_aggregate_frag_full[source_store_size]:
  Cases_on `post_value_type cenv e = lowered_value_type cenv e`
  >- (gvs[] >> simp[]) >>
  irule valueCopyBytesTheory.bytestring_val_store_size_eq >> simp[] >>
  qexistsl_tac [`lowered_value_type cenv e`,`post_value_type cenv e`,`get_tenv cx`] >>
  qpat_x_assum `post_value_type cenv e = lowered_value_type cenv e \/ _` mp_tac >> simp[]
QED

Resume body_append_storage_aggregate_frag_full[aggregate_cont]:
  `type_memory_bytes cenv elem < 2 ** 64` by
    (qpat_assum `cenv.ce_hashmap_info _ = NONE` (fn no_map =>
       qpat_assum `cenv.ce_module_var_type _ = SOME (ArrayT elem _)` (fn ty =>
         qpat_assum `~is_word_type elem` (fn nonword =>
           qpat_assum `stmt_exprs_ok cenv (Append (TopLevelNameTarget _) e)`
             (strip_assume_tac o SRULE [stmt_exprs_ok_def,
               allocLimitsTheory.alloc_limits_stmt_def,
               allocLimitsTheory.target_place_type_def,no_map,ty,nonword])))) >>
     simp[]) >>
  `32 * type_slot_size tv + 64 < dimword (:256)` by
    (qpat_assum `type_memory_bytes cenv elem = 32 * type_slot_size tv` (fn size =>
       qpat_assum `type_memory_bytes cenv elem < 2 ** 64`
         (mp_tac o PURE_REWRITE_RULE [size])) >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  qpat_x_assum `(type_memory_bytes cenv elem + 31) DIV 32 = type_slot_size tv`
    (fn slots => qpat_assum `type_memory_bytes cenv elem = type_memory_size tv`
      (fn bytes => RULE_ASSUM_TAC (PURE_REWRITE_RULE [slots,bytes]) >> assume_tac bytes)) >>
  `!H. valid_horizon cx st0 H mid'.storage_trace ==>
    storage_place_observed H
      (StoragePlace (mut = Transient) (n2w rslot) (ArrayTV tv (Dynamic cap)))` by
    (qx_gen_tac `H` >> strip_tac >>
     simp[vyperStoragePlaceObservedTheory.storage_place_observed_def] >>
     qexistsl_tac [`n2w rslot`,`ArrayTV tv (Dynamic cap)`,`[]`,`0`] >>
     simp[vyperStoragePlaceRegionTheory.storage_subregion_def,wordsTheory.WORD_ADD_0]) >>
  irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
  irule_at (Pat `gas_outcome_full _ _ _ _ _ _ _ _`) append_storage_aggregate_cont_full >>
  qpat_assum `compile_dynarray_append cenv (Lit _) _ 1 _ elem elem _ F _ sd = ((),sb)`
    (irule_at Any) >>
  qpat_assum `compile_alloc_buffer (type_memory_size tv) sm = (tmp,sc)` (irule_at Any) >>
  qpat_assum `compile_store_memory cenv (Var src) tmp.buf_operand elem _ sc = ((),sd)` (irule_at Any) >>
  qpat_assum `lookup_var src t = SOME sw` (irule_at Any) >>
  qpat_assum `encode_value tv v = SOME writes` (irule_at Any) >>
  simp[venomStateTheory.eval_operand_def,ptrDisciplineTheory.op_taint_def] >>
  qexistsl_tac [`sa`,`lctx`,`d`,`RetQ`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!H. valid_horizon cx st0 H mid'.storage_trace ==> _ /\ _ /\ _ /\ _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  simp[] >>
  reverse conj_tac >- (POP_ASSUM_LIST (K all_tac) >> metisTools.METIS_TAC []) >>
  rpt gen_tac >> disch_then (qx_choose_then `cenvf` strip_assume_tac) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t'` by
    (qpat_assum `stmt_state_rel H ctx func cenvf cx ee t'`
      (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  `s0.vs_alloca_next <= t'.vs_alloca_next` by
    (qpat_assum `s0.vs_alloca_next <= t.vs_alloca_next` mp_tac >>
     qpat_assum `t.vs_alloca_next <= t'.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  qexists_tac `cenvf` >> simp[] >>
  suspend "aggregate_post"
QED

Resume body_append_storage_aggregate_frag_full[aggregate_post]:
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  conj_tac >-
    (map_every qx_gen_tac [`x`,`w`] >> strip_tac >>
     qpat_assum `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> _`
       (qspecl_then [`x`,`w`] mp_tac) >>
     qpat_assum `!x. not_fresh_at sm x ==> _` (qspec_then `x` mp_tac) >> simp[]) >>
  conj_tac >-
    (qx_gen_tac `x` >> strip_tac >>
     `not_fresh_at sm x` by simp[] >>
     qpat_assum `not_fresh_at sa x` (fn fresh =>
       qpat_assum `!x. not_fresh_at sa x ==> FLOOKUP G1 x = _ /\ _`
         (qspec_then `x` (strip_assume_tac o C MP fresh))) >>
     qpat_assum `not_fresh_at sm x` (fn fresh =>
       qpat_assum `!x. not_fresh_at sm x ==> lookup_var x t' = _ /\ _`
         (qspec_then `x` (strip_assume_tac o C MP fresh))) >>
     fs[ptrDisciplineTheory.op_taint_def]) >>
  conj_tac >-
    (irule stmtSimDefsTheory.alloca_frame_trans >>
     goal_assum (drule_at Any) >> simp[]) >>
  map_every qx_gen_tac [`aid`,`off`,`sz`,`i`] >> strip_tac >>
  `aid < sm.cs_next_id` by
    (irule arithmeticTheory.LESS_LESS_EQ_TRANS >> qexists_tac `sa.cs_next_id` >> simp[]) >>
  `FLOOKUP t.vs_allocas aid = SOME (off,sz)` by
    (qpat_assum `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> _`
       (qspecl_then [`aid`,`(off,sz)`] mp_tac) >> simp[]) >>
  qpat_assum `!aid off sz. aid < sm.cs_next_id /\ _ ==> !i. _`
    (qspecl_then [`aid`,`off`,`sz`] (drule_then (qspec_then `i` mp_tac))) >>
  simp[] >> strip_tac >>
  qpat_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ _ ==> _`
    (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >> simp[]
  >> (metisTools.METIS_TAC [])
QED

Finalise body_append_storage_aggregate_frag_full[local]

Theorem body_append_storage_bytestring_frag_full:
  !cx nid e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv
    env env' ret_ty lctx RetQ es elem cap.
  (!s p t. eval_target_place cx (TopLevelNameTarget nid) s = (INL p,t) ==>
     body_expr_full_ok cx e) /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (Append (TopLevelNameTarget nid) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Append (TopLevelNameTarget nid) e) ==> occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
  locals_alloc_ok cenv env /\
  type_stmt env ret_ty (Append (TopLevelNameTarget nid) e) = SOME env' /\
  type_place_target env (TopLevelNameTarget nid) = SOME (Type (ArrayT elem (Dynamic cap))) /\
  is_bytestring_type elem /\
  stmt_exprs_ok cenv (Append (TopLevelNameTarget nid) e) /\
  call_evaluation_safe cx (int_calls_stmt (Append (TopLevelNameTarget nid) e)) /\
  frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ cenv ret_ty ==>
  stmt_frag_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (Append (TopLevelNameTarget nid) e))
    (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Append (TopLevelNameTarget nid) e)))
    (eval_stmt cx (Append (TopLevelNameTarget nid) e)) es
Proof
  rpt strip_tac >>
  drule_then assume_tac valueCopyBytesTheory.is_bytestring_word_type >>
  irule body_append_storage_aggregate_frag_full >> simp[] >> metis_tac[]
QED

Theorem body_append_storage_flat_copy_frag_full:
  !cx nid e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv
    env env' ret_ty lctx RetQ es elem cap.
  (!s p t. eval_target_place cx (TopLevelNameTarget nid) s = (INL p,t) ==>
     body_expr_full_ok cx e) /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (Append (TopLevelNameTarget nid) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Append (TopLevelNameTarget nid) e) ==> occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
  locals_alloc_ok cenv env /\
  type_stmt env ret_ty (Append (TopLevelNameTarget nid) e) = SOME env' /\
  type_place_target env (TopLevelNameTarget nid) = SOME (Type (ArrayT elem (Dynamic cap))) /\
  ~is_word_type elem /\ ~is_bytestring_type elem /\
  elem = lowered_value_type cenv e /\
  stmt_exprs_ok cenv (Append (TopLevelNameTarget nid) e) /\
  call_evaluation_safe cx (int_calls_stmt (Append (TopLevelNameTarget nid) e)) /\
  frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ cenv ret_ty ==>
  stmt_frag_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (Append (TopLevelNameTarget nid) e))
    (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Append (TopLevelNameTarget nid) e)))
    (eval_stmt cx (Append (TopLevelNameTarget nid) e)) es
Proof
  rpt strip_tac >> irule body_append_storage_aggregate_frag_full >> simp[] >>
  metis_tac[]
QED

Theorem body_append_storage_typed_copy_frag_full:
  !cx nid e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv
    env env' ret_ty lctx RetQ es elem cap.
  (!s p t. eval_target_place cx (TopLevelNameTarget nid) s = (INL p,t) ==>
     body_expr_full_ok cx e) /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (Append (TopLevelNameTarget nid) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Append (TopLevelNameTarget nid) e) ==> occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
  locals_alloc_ok cenv env /\
  type_stmt env ret_ty (Append (TopLevelNameTarget nid) e) = SOME env' /\
  type_place_target env (TopLevelNameTarget nid) = SOME (Type (ArrayT elem (Dynamic cap))) /\
  ~is_word_type elem /\ ~is_bytestring_type elem /\
  elem <> lowered_value_type cenv e /\
  ~tuple_memory_layout_eq elem (lowered_value_type cenv e) /\
  stmt_exprs_ok cenv (Append (TopLevelNameTarget nid) e) /\
  call_evaluation_safe cx (int_calls_stmt (Append (TopLevelNameTarget nid) e)) /\
  frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ cenv ret_ty ==>
  stmt_frag_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (Append (TopLevelNameTarget nid) e))
    (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Append (TopLevelNameTarget nid) e)))
    (eval_stmt cx (Append (TopLevelNameTarget nid) e)) es
Proof
  rpt strip_tac >> irule body_append_storage_aggregate_frag_full >> simp[] >>
  metis_tac[]
QED

Theorem body_append_storage_tuple_layout_frag_full:
  !cx nid e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv
    env env' ret_ty lctx RetQ es elem cap.
  (!s p t. eval_target_place cx (TopLevelNameTarget nid) s = (INL p,t) ==>
     body_expr_full_ok cx e) /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (Append (TopLevelNameTarget nid) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Append (TopLevelNameTarget nid) e) ==> occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
  locals_alloc_ok cenv env /\
  type_stmt env ret_ty (Append (TopLevelNameTarget nid) e) = SOME env' /\
  type_place_target env (TopLevelNameTarget nid) = SOME (Type (ArrayT elem (Dynamic cap))) /\
  ~is_word_type elem /\ ~is_bytestring_type elem /\
  elem <> lowered_value_type cenv e /\
  tuple_memory_layout_eq elem (lowered_value_type cenv e) /\
  stmt_exprs_ok cenv (Append (TopLevelNameTarget nid) e) /\
  call_evaluation_safe cx (int_calls_stmt (Append (TopLevelNameTarget nid) e)) /\
  frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ cenv ret_ty ==>
  stmt_frag_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (Append (TopLevelNameTarget nid) e))
    (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Append (TopLevelNameTarget nid) e)))
    (eval_stmt cx (Append (TopLevelNameTarget nid) e)) es
Proof
  rpt strip_tac >> irule body_append_storage_aggregate_frag_full >> simp[] >>
  metis_tac[]
QED

Theorem body_append_local_full:
  !cx id e.
    (!s'' p t'.
       eval_target_place cx (NameTarget id) s'' = (INL p,t') ==>
       body_expr_full_ok cx e) ==>
    body_stmt_full_ok cx (Append (NameTarget id) e)
Proof
  rpt gen_tac >> strip_tac >> rw[body_stmt_full_ok_def] >>
  drule_then strip_assume_tac bodyAppendStorageFactsTheory.append_typing_target >>
  rename1 `type_place_target env (NameTarget id) = SOME (Type (ArrayT elem (Dynamic lim)))` >>
  Cases_on `is_word_type elem`
  >- (`elem = expr_type e` by metis_tac[bodyAppendStorageFactsTheory.type_widens_to_word] >>
      qspecl_then [`cx`,`id`,`e`] mp_tac body_append_local_primitive_full >>
      (impl_tac >- ((conj_tac >- metis_tac[]) >> first_assum ACCEPT_TAC)) >>
      disch_then (mp_tac o REWRITE_RULE [body_stmt_full_ok_def]) >>
      disch_then (qspecl_then [`DF`,`lo`,`d`,`PG`,`tops`,`bindings`,`ctx`,
        `shadow_ctx`,`func`,`shadow_func`,`cenv`,`env`,`env'`,`ret_ty`,
        `lctx`,`RetQ`,`es`] mp_tac) >> simp[]) >>
  qspecl_then [`cx`,`id`,`e`,`DF`,`lo`,`d`,`PG`,`tops`,`bindings`,`ctx`,
      `shadow_ctx`,`func`,`shadow_func`,`cenv`,`env`,`env'`,`ret_ty`,
      `lctx`,`RetQ`,`es`,`elem`,`lim`] mp_tac
    body_append_local_nonword_frag_full >>
  simp[] >> disch_then irule >> first_assum ACCEPT_TAC
QED

Theorem body_append_nested_full:
  !cx t e.
    (!id. t <> NameTarget id) /\ (!nid. t <> TopLevelNameTarget nid) /\
    (!s'' p t'.
       eval_target_place cx t s'' = (INL p,t') ==> body_expr_full_ok cx e) /\
    body_base_target_full_ok cx t ==>
    body_stmt_full_ok cx (Append t e)
Proof
  rpt gen_tac >> strip_tac >> rw[body_stmt_full_ok_def] >>
  drule_then strip_assume_tac bodyAppendStorageFactsTheory.append_typing_target >>
  rename1 `type_place_target env t = SOME (Type (ArrayT elem (Dynamic lim)))` >>
  Cases_on `t` >> gvs[]
  >- (
    rename1 `supported_stmt _ _ (Append (SubscriptTarget b e2) e)` >>
    qspecl_then [`cx`,`b`,`e2`,`e`,`DF`,`lo`,`d`,`PG`,`tops`,`bindings`,`ctx`,
        `shadow_ctx`,`func`,`shadow_func`,`cenv`,`env`,`env'`,`ret_ty`,
        `lctx`,`RetQ`,`es`,`elem`,`lim`] mp_tac
      body_append_nested_subscript_frag_full >>
    simp[] >> disch_then irule >> first_assum ACCEPT_TAC) >>
  rename1 `supported_stmt _ _ (Append (AttributeTarget b fld) e)` >>
  qspecl_then [`cx`,`b`,`fld`,`e`,`DF`,`lo`,`d`,`PG`,`tops`,`bindings`,`ctx`,
      `shadow_ctx`,`func`,`shadow_func`,`cenv`,`env`,`env'`,`ret_ty`,
      `lctx`,`RetQ`,`es`,`elem`,`lim`] mp_tac
    body_append_nested_attribute_frag_full >>
  simp[] >> disch_then irule >> first_assum ACCEPT_TAC
QED

Theorem body_append_storage_full:
  !cx nid e.
    (!s'' p t'.
       eval_target_place cx (TopLevelNameTarget nid) s'' = (INL p,t') ==>
       body_expr_full_ok cx e) ==>
    body_stmt_full_ok cx (Append (TopLevelNameTarget nid) e)
Proof
  rpt gen_tac >> strip_tac >> rw[body_stmt_full_ok_def] >>
  drule_then strip_assume_tac bodyAppendStorageFactsTheory.append_typing_target >>
  rename1 `type_place_target env (TopLevelNameTarget nid) = SOME (Type (ArrayT elem (Dynamic lim)))` >>
  Cases_on `is_word_type elem`
  >- (
    qspecl_then [`cx`,`nid`,`e`,`DF`,`lo`,`d`,`PG`,`tops`,`bindings`,`ctx`,
        `shadow_ctx`,`func`,`shadow_func`,`cenv`,`env`,`env'`,`ret_ty`,
        `lctx`,`RetQ`,`es`,`elem`,`lim`] mp_tac
      body_append_storage_word_frag_full >>
    simp[] >> disch_then irule >> first_assum ACCEPT_TAC) >>
  Cases_on `is_bytestring_type elem`
  >- (
    qspecl_then [`cx`,`nid`,`e`,`DF`,`lo`,`d`,`PG`,`tops`,`bindings`,`ctx`,
        `shadow_ctx`,`func`,`shadow_func`,`cenv`,`env`,`env'`,`ret_ty`,
        `lctx`,`RetQ`,`es`,`elem`,`lim`] mp_tac
      body_append_storage_bytestring_frag_full >>
    simp[] >> disch_then irule >> first_assum ACCEPT_TAC) >>
  Cases_on `elem = lowered_value_type cenv e`
  >- (
    qspecl_then [`cx`,`nid`,`e`,`DF`,`lo`,`d`,`PG`,`tops`,`bindings`,`ctx`,
        `shadow_ctx`,`func`,`shadow_func`,`cenv`,`env`,`env'`,`ret_ty`,
        `lctx`,`RetQ`,`es`,`elem`,`lim`] mp_tac
      body_append_storage_flat_copy_frag_full >>
    simp[] >> disch_then irule >> first_assum ACCEPT_TAC) >>
  Cases_on `tuple_memory_layout_eq elem (lowered_value_type cenv e)`
  >- (
    qspecl_then [`cx`,`nid`,`e`,`DF`,`lo`,`d`,`PG`,`tops`,`bindings`,`ctx`,
        `shadow_ctx`,`func`,`shadow_func`,`cenv`,`env`,`env'`,`ret_ty`,
        `lctx`,`RetQ`,`es`,`elem`,`lim`] mp_tac
      body_append_storage_tuple_layout_frag_full >>
    simp[] >> disch_then irule >> first_assum ACCEPT_TAC) >>
  qspecl_then [`cx`,`nid`,`e`,`DF`,`lo`,`d`,`PG`,`tops`,`bindings`,`ctx`,
      `shadow_ctx`,`func`,`shadow_func`,`cenv`,`env`,`env'`,`ret_ty`,
      `lctx`,`RetQ`,`es`,`elem`,`lim`] mp_tac
    body_append_storage_typed_copy_frag_full >>
  simp[] >> disch_then irule >> first_assum ACCEPT_TAC
QED
