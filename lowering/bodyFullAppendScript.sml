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
  bodyFullShadowBodyInv bodyFullMemoryStore immutableDeployAssignRanges
  placeMemoryTypeInterfaces
  bodyFullStoreSlotsPath bodyFullStoreSlotsStatic
  memoryPlaceStorePost
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
  vyperFiniteStoragePreservation assignTuplePtrLoadStep targetSubscriptStorage appendStorageGhostPtr
  bodyFullPreds bodySimFull gasShadow bodySim exprSimHypsDefs supportedStmts
  compileEnv exprLowering stmtLowering vyperTypeSystem vyperContext
  vyperInterpreter vyperState vyperValue vyperAST list finite_map
  targetPlaceSimCases vyperExprNoControl vyperTypeCallGraph
  vyperTypeCallStackSoundness bodyFullShared vyperStorageTrace vyperStorageFootprint
  vyperEvalExprPreservesScopesDom immutableDeployPhysicalSource

val _ = Parse.hide "body";

Theorem array_set_index_indexed_error[local]:
  !tv av i x vj err.
    array_index tv av i = SOME x /\ array_set_index tv av i vj = INR err ==>
    ?msg. err = TypeError msg
Proof
  rpt gen_tac >>
  simp[vyperValueOperationTheory.array_index_def,
       vyperValueOperationTheory.array_set_index_def, LET_THM] >>
  Cases_on `0 <= i` >> simp[] >>
  Cases_on `av`
  >~ [`DynArrayV l`]
  >- (simp[listTheory.oEL_THM] >> Cases_on `Num i < LENGTH l` >> simp[])
  >~ [`TupleV l`] >- simp[] >>
  Cases_on `tv` >> simp[] >>
  Cases_on `b` >> simp[] >>
  rename1 `Num i < n` >> Cases_on `Num i < n` >> simp[]
QED

Theorem aug_place_replace_read_error[local]:
  !path tv a old v err.
    evaluate_subscripts tv a path = INL old /\
    assign_subscripts tv a path (Replace v) = INR err ==>
    ?msg. err = TypeError msg
Proof
  Induct_on `path` >- simp[assign_subscripts_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `h`
  >~ [`ValueSubscript key`]
  >- (`?i av. key = IntV i /\ a = ArrayV av` by
        (Cases_on `key` >> fs[evaluate_subscripts_def] >>
         Cases_on `a` >> fs[]) >>
      gvs[] >>
      qpat_x_assum `evaluate_subscripts _ _ _ = _` mp_tac >>
      qpat_x_assum `assign_subscripts _ _ _ _ = _` mp_tac >>
      simp[Once evaluate_subscripts_def, Once assign_subscripts_def, LET_THM] >>
      Cases_on `array_index tv av i` >> simp[] >>
      rename1 `array_index tv av i = SOME elt` >>
      qmatch_goalsub_abbrev_tac `assign_subscripts etv elt path` >>
      Cases_on `assign_subscripts etv elt path (Replace v)` >> simp[]
      >- metis_tac[array_set_index_indexed_error] >>
      Cases_on `evaluate_subscripts etv elt path` >> simp[] >>
      first_x_assum drule_all >> rpt strip_tac >> gvs[])
  >~ [`AttrSubscript id`]
  >- (`?al. a = StructV al` by (Cases_on `a` >> fs[evaluate_subscripts_def]) >>
      gvs[] >>
      qpat_x_assum `evaluate_subscripts _ _ _ = _` mp_tac >>
      qpat_x_assum `assign_subscripts _ _ _ _ = _` mp_tac >>
      simp[Once evaluate_subscripts_def, Once assign_subscripts_def, LET_THM] >>
      Cases_on `ALOOKUP al id` >> simp[] >>
      rename1 `ALOOKUP al id = SOME fld` >>
      qmatch_goalsub_abbrev_tac `assign_subscripts ftv fld path` >>
      Cases_on `assign_subscripts ftv fld path (Replace v)` >> simp[] >>
      Cases_on `evaluate_subscripts ftv fld path` >> simp[] >>
      first_x_assum drule_all >> rpt strip_tac >> gvs[]) >>
  fs[evaluate_subscripts_def]
QED

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
  n < dimword (:256) /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  alloca_history func s /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  not_fresh_at sa xs /\ lookup_var xs s = SOME sw /\
  evaluate_type (get_tenv cx) sty = SOME tv /\ ~is_word_type sty /\
  ~is_bytestring_type sty /\ ~is_word_type dty /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\ type_memory_size dtv = n /\
  type_memory_bytes cenv dty = n /\ 0 < type_memory_size tv /\
  value_has_type tv v /\ value_has_type dtv v /\ val_wf tv v /\ val_wf dtv v /\
  expr_val_at cenv cx sty start sa es v (Var xs) s /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv v (w2n sw) mem) /\
  ptr_covers G tn xs s (type_memory_size tv) /\
  w2n sw + type_memory_size tv < dimword (:256) /\
  w2n sw + type_memory_size tv <= s.vs_alloca_next /\
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
      !i. off <= i /\ i < off+sz ==> (i IN tf.t_mem <=> i IN tn.t_mem))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
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
  `b+n <= u.vs_alloca_next` by suspend "end_bound" >>
  `compile_store_memory cenv (Var xs) (Var root) dty sty sm = ((),sb)` by metis_tac[] >>
  `ptr_covers G1 tn1 xs u (type_memory_size tv)` by metis_tac[] >>
  `w2n ((n2w b):bytes32) = b` by simp[] >>
  SUBGOAL_THEN
    ``w2n (sw:bytes32) + type_memory_size tv <= b \/ b+n <= w2n sw``
    ASSUME_TAC >- suspend "separation" >>
  mp_tac (Q.INST [`sa` |-> `sm`, `s` |-> `u`, `tn` |-> `tn1`,
    `G` |-> `G1`, `xd` |-> `root`, `dw` |-> `(n2w b):bytes32`,
    `tenv` |-> `get_tenv cx`, `stv` |-> `tv`]
    (SPEC_ALL bodyFullMemoryStoreTheory.body_full_memory_store_path)) >>
  (impl_tac >- (simp[] >> rpt gen_tac >> strip_tac >> res_tac >> simp[])) >>
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
  conj_tac >- suspend "frame" >> suspend "older_taint"
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

(* The top-level storage/transient dynamic array. *)
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
  MEM (tr,slot,ArrayTV tv (Dynamic cap)) (FST H) /\
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
  `val_in_memory tv v (w2n b) s.vs_memory` by
    metis_tac[bodyPtrDefsTheory.mem_agree_outside_def] >>
  `(!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s)` by metis_tac[] >>
  `res = INL () /\ stmt_state_rel H ctx func cenv cx ee u /\
    storage_well_formed_on cx ee (FST H)` by
    (qpat_assum `k = _` (fn th =>
       RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
     drule_all stmtSimAppendStorageComposeTheory.append_storage_copy_success_post >>
     simp[]) >>
  simp[] >>
  conj_tac >- suspend "ghost" >>
  conj_tac >- suspend "return" >>
  conj_tac >- (irule bodyFullPathHistoryTheory.body_full_path_alloca_history >>
    goal_assum (drule_at Any) >>
    metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca]) >>
  suspend "frame"
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
  `w2n k + type_slot_size tv <= dimword (:256)` by
    metis_tac[vyperStorageWritePreservationTheory.dynamic_array_child_region_bounds,
      vyperStorageFootprintTheory.regions_consistent_def] >>
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
    (irule bodyFullAppendNestedFramesTheory.append_sparse_keys_dead_subset >>
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
   mid s G tn tr slot tv stv v xs sw elem sty cap buf writes.
  evaluate_type (get_tenv cx) elem = SOME tv /\ ~is_word_type elem /\
  ~is_word_type sty /\ ~is_bytestring_type sty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  type_widens_to (get_tenv cx) sty elem /\
  type_memory_bytes cenv elem = type_memory_size tv /\
  value_has_type stv v /\ val_wf stv v /\ 0 < type_memory_size stv /\
  0 < type_slot_size tv /\ well_formed_type_value tv /\
  type_memory_size tv < dimword (:256) /\ cap < dimword (:256) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !rt. evaluate_type (get_tenv cx) fty = SOME rt ==>
      sz = type_memory_size rt) fields) /\
  value_has_type tv v /\ val_wf tv v /\ encode_value tv v = SOME writes /\
  compile_alloc_buffer (type_memory_size tv) sa = (buf,sc) /\
  compile_store_memory cenv (Var xs) buf.buf_operand elem sty sc = ((),sd) /\
  compile_dynarray_append cenv (Lit slot) buf.buf_operand 1 (type_slot_size tv)
    elem elem cap F (if tr then LocTransient else LocStorage) sd = ((),sf) /\
  fn_has_code sa sf func /\ fn_inst_ids_distinct func /\
  not_fresh_at sa xs /\ lookup_var xs s = SOME sw /\
  (?start. expr_val_at cenv cx sty start sa mid v (Var xs) s) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory stv v (w2n sw) mem) /\
  ptr_covers G tn xs s (type_memory_size stv) /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid s /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx mid G tn s /\
    MEM (tr,slot,ArrayTV tv (Dynamic cap)) (FST H)) /\
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
    (qpat_x_assum `regions_consistent (FST H0)` mp_tac >>
     simp[vyperStorageFootprintTheory.regions_consistent_def] >>
     disch_then (mp_tac o cj 1) >>
     disch_then (qspecl_then [`tr`,`slot`,`ArrayTV tv (Dynamic cap)`] mp_tac) >>
     simp[type_slot_size_def]) >>
  `storage_place_observed H0 (StoragePlace tr slot (ArrayTV tv (Dynamic cap)))` by
    (simp[vyperStoragePlaceObservedTheory.storage_place_observed_def] >>
     qexistsl_tac [`slot`,`ArrayTV tv (Dynamic cap)`,`[]`,`0`] >>
     simp[vyperStoragePlaceRegionTheory.storage_subregion_def,wordsTheory.WORD_ADD_0]) >>
  `storage_read_live H0 tr (get_storage cx mid tr) slot (ArrayTV tv (Dynamic cap))` by
    (irule accountsRelPropsTheory.storage_place_observed_read_live >>
     simp[type_slot_size_def]) >>
  `eval_operand (Lit slot) staged = SOME slot /\ op_taint ts (Lit slot) = {} /\
   (!x. Lit slot = Var x ==> not_fresh_at sd x)` by
    simp[venomStateTheory.eval_operand_def,ptrDisciplineTheory.op_taint_def] >>
  `(if tr then tload slot staged else sload slot staged) =
   lookup_storage slot (get_storage cx mid tr)` by
    (irule (INST_TYPE [alpha |-> ``:256``]
       (cj 2 targetSubscriptStorageTheory.target_storage_array_len_ok)) >>
     conj_tac >- (qexists_tac `Lit slot` >> simp[]) >>
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
  `eval_operand (Lit slot) guarded = SOME slot /\ op_taint tg (Lit slot) = {} /\
   eval_operand lop guarded = SOME (n2w len)` by
    simp[Abbr `guarded`,Abbr `len`,venomStateTheory.eval_operand_def,
      ptrDisciplineTheory.op_taint_def,venomStateTheory.lookup_var_def,
      CaseEq "operand"] >>
  `!x. Lit slot = Var x \/ lop = Var x ==> not_fresh_at s3 x` by
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
    (qpat_assum `emit_op _ [Lit slot] sd = (lop,s1)`
       (mp_tac o cj 2 o MATCH_MP emitHelperPropsTheory.emitted_insts_emit_op) >>
     disch_then SUBST_ALL_TAC >>
     qpat_assum `!x. Lit slot = Var x \/ _ ==> _`
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
  `eval_operand (Lit slot) counted = SOME slot /\ op_taint tc (Lit slot) = {}` by
    simp[venomStateTheory.eval_operand_def,ptrDisciplineTheory.op_taint_def] >>
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
    (qpat_assum `emit_void _ [Lit slot;nop] s8 = ((),sf)`
       (mp_tac o MATCH_MP emit_void_same_blocks) >>
     qpat_assum `counted.vs_current_bb = s8.cs_current_bb` mp_tac >>
     qpat_assum `Abbrev (u = _)` (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `tr` >> simp[loweringPostsTheory.stmt_lands_def,
       same_blocks_def,venomStateTheory.tstore_def,venomStateTheory.sstore_def]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qpat_assum `emit_void _ [Lit slot;nop] s8 = ((),sf)`
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

Theorem append_nested_robust_array_project:
  mem_path_offset rt path = SOME (k,ArrayTV tv (Dynamic cap)) /\
  value_has_type rt a /\ well_formed_type_value rt /\
  evaluate_subscripts rt a path = INL (ArrayV (DynArrayV vs)) /\
  (!m. mem_agree_outside tm mem m ==> val_in_memory rt a b m) ==>
  (!m. mem_agree_outside tm mem m ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (b+k) m) /\
  (!i. b+k <= i /\ i < b+k+32 ==> i NOTIN tm)
Proof
  strip_tac >>
  `!m. mem_agree_outside tm mem m ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (b+k) m` by
    (rpt strip_tac >> irule bodySimAugPlaceLoadTheory.aug_place_path_project >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  `!m. mem_agree_outside tm mem m ==>
    mem_word_at (b+k) m = n2w (LENGTH vs)` by
    (rpt strip_tac >>
     qpat_x_assum `!m. _ ==> val_in_memory (ArrayTV _ _) _ _ _` drule >>
     simp[val_in_memory_def]) >>
  drule representationCleanPtrTheory.robust_mem_word_at_clean >> simp[]
QED

Theorem append_nested_memory_reserved_lookup:
  compile_dynarray_append cenv bop vop 32 32 elem src_ty cap T LocMemory sm = ((),sb) /\
  run_inst_seq (emitted_insts sm sb) t = OK u ==>
  !x. not_fresh_at sm x ==> lookup_var x u = lookup_var x t
Proof
  rpt strip_tac >>
  irule appendStorageStageTransportPtrTheory.run_inst_seq_non_output_vars >>
  qexists_tac `emitted_insts sm sb` >> simp[] >>
  qpat_x_assum `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_dynarray_append_def, contextTheory.compile_ptr_load_def,
       contextTheory.compile_ptr_store_def,
       compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.comp_return_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       compileEnvTheory.fresh_id_def, compileEnvTheory.fresh_var_def,
       compileEnvTheory.emit_def] >> strip_tac >> gvs[] >>
  simp[exprLoweringPropsTheory.emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def] >>
  fs[loweringStateRelDefsTheory.not_fresh_at_def]
QED

Theorem append_nested_memory_cont_full[local]:
 !DF lo d ctx shadow_ctx PG func cx st0 lctx RetQ cenv env sa sm sb s0 G0 tn0
   mid t G tn id path entry rp sz rootw k tv vs v p bp vop w elem src_ty cap.
  body_inv (cx_tops cx) ctx cenv cx /\
  gas_admissible (append_place cx (MemoryPlace id path) v) (stmt_res_ok lctx) mid /\
  expr_sim_inv cenv cx env mid /\ supported_full_word_type elem /\ 
  evaluate_type (get_tenv cx) elem = SOME tv /\
  type_memory_size tv = 32 /\ value_has_type tv v /\ abi_tuple_word tv v /\
  lookup_scopes id mid.scopes = SOME entry /\ entry.assignable /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var rp) sz) /\
  lookup_var rp t = SOME rootw /\
  mem_path_offset entry.type path = SOME (k,ArrayTV tv (Dynamic cap)) /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV (DynArrayV vs)) /\
  place_ptr_rel cenv cx t (PlaceR (MemoryPlace id path)) bp (SOME LocMemory)
    (Type (ArrayT elem (Dynamic cap))) /\
  compile_dynarray_append cenv (Var p) vop 32 32 elem src_ty cap T LocMemory sm = ((),sb) /\
  not_fresh_at sm p /\ (!x. vop = Var x ==> not_fresh_at sm x) /\
  lookup_var p t = SOME bp /\ eval_operand vop t = SOME w /\
  w = typed_val_to_w256 tv v /\ op_taint tn vop = {} /\
  ptr_covers G tn p t (32*(1+cap)) /\
  (!i. w2n bp <= i /\ i < w2n bp+32 ==> i NOTIN tn.t_mem) /\
  cap < dimword (:256) /\ w2n bp+32*(1+cap) <= t.vs_alloca_next /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid t /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx mid G tn t) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\ ~ctx_has_dalloca ctx /\
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
    (cx_tops cx) cx st0 (append_place cx (MemoryPlace id path) v) (mid,t,G,tn)
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
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- fs[vyperStorageFootprintTheory.storage_trace_domain_def]) >>
  strip_tac >>
  `t.vs_alloca_next < dimword (:256)` by
    (fs[exprLoweringPropsTheory.stmt_state_rel_def, exprLoweringPropsTheory.alloca_room_def] >> decide_tac) >>
  `w2n bp + 32*(1+cap) <= dimword (:256)` by decide_tac >>
  drule_all appendMemoryRelTheory.append_memory_array_layout_general >>
  strip_tac >> gvs[] >>
  `mload (w2n bp) t = n2w (LENGTH vs)` by
    (qpat_assum `val_in_memory (ArrayTV _ _) _ _ _` mp_tac >>
     pure_rewrite_tac[valueEncodingDefsTheory.val_in_memory_def] >> strip_tac >>
     fs[venomStateTheory.mload_def, valueEncodingDefsTheory.mem_word_at_def]) >>
  `LENGTH vs <= cap /\ LENGTH vs < dimword (:256)` by
    (fs[vyperTypingTheory.value_has_type_def] >> decide_tac) >>
  `w2n (mload (w2n bp) t) = LENGTH vs` by simp[] >>
  drule exprSimPropsTheory.mem_path_offset_sound >> strip_tac >>
  `!st. st.scopes = mid.scopes ==>
    place_type_value cx (MemoryPlace id path) st = (INL (ArrayTV tv (Dynamic cap)),st) /\
    read_place cx (MemoryPlace id path) st = (INL (ArrayV (DynArrayV vs)),st)` by
    (rpt strip_tac >>
     simp[place_type_value_def, read_place_def, get_scopes_def,
          lift_option_type_def, lift_option_def, bind_def, return_def,
          read_memory_path_def, lift_sum_def]) >>
  `!st. st.scopes = mid.scopes ==>
    append_place cx (MemoryPlace id path) v st =
    bind (lift_sum (append_element (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) v))
         (write_place cx (MemoryPlace id path)) st` by
    (rpt strip_tac >> simp[append_place_def, bind_def]) >>
  Cases_on `LENGTH vs < cap`
  >- suspend "success"
  >> suspend "capacity"
QED

Resume append_nested_memory_cont_full[capacity]:
  `!st. st.scopes = mid.scopes ==>
    append_place cx (MemoryPlace id path) v st =
      (INR (Error (RuntimeError "append overflow")),st)` by
    (rpt strip_tac >>
     simp[vyperValueOperationTheory.append_element_def,
          vyperValueTheory.compatible_bound_def, bind_def, lift_sum_def, raise_def] >>
     decide_tac) >>
  `run_inst_seq_mem_ok (emitted_insts sm sb) t` by
    (irule appendMemoryPathTheory.append_memory_word_mem_ok >>
     qpat_assum `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
     simp[venomStateTheory.eval_operand_def, arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
  qabbrev_tac `lv = STRING #"%" (toString sm.cs_next_var)` >>
  qabbrev_tac `ov = STRING #"%" (toString (sm.cs_next_var+1))` >>
  qabbrev_tac `load = mk_inst sm.cs_next_id MLOAD [Var p] [lv]` >>
  qabbrev_tac `test = mk_inst (sm.cs_next_id+1) LT [Var lv; Lit (n2w cap)] [ov]` >>
  qabbrev_tac `assertinst = mk_inst (sm.cs_next_id+2) ASSERT [Var ov] []` >>
  `?rest. emitted_insts sm sb = load::test::assertinst::rest` by
    (qpat_assum `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[NoAsms, compile_dynarray_append_def, contextTheory.compile_ptr_load_def,
          contextTheory.compile_ptr_store_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
          fresh_id_def, fresh_var_def, emit_def] >>
     disch_then (SUBST1_TAC o SYM) >>
     simp_tac (srw_ss()) [exprLoweringPropsTheory.emitted_insts_def] >>
     pure_rewrite_tac [GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
     simp[Abbr `load`, Abbr `test`, Abbr `assertinst`, Abbr `lv`, Abbr `ov`]) >>
  `p <> lv /\ p <> ov /\ lv <> ov` by
    (gvs[Abbr `lv`, Abbr `ov`, loweringStateRelDefsTheory.not_fresh_at_def] >>
     metis_tac[emitHelperPropsTheory.fresh_var_neq, DECIDE ``n <= n+1``]) >>
  qabbrev_tac `s1 = update_var lv (mload (w2n bp) t) t` >>
  qabbrev_tac `s2 = update_var ov 0w s1` >>
  `step_inst_base load t = OK s1 /\
   step_inst_base test s1 = OK s2 /\
   step_inst_base assertinst s2 = Abort Revert_abort (revert_state (set_returndata [] s2))` by
    simp[Abbr `load`, Abbr `test`, Abbr `assertinst`, Abbr `s1`, Abbr `s2`,
         venomExecSemanticsTheory.step_inst_base_opcode_eqs, venomInstTheory.mk_inst_def,
         venomExecSemanticsTheory.exec_read1_def, venomExecSemanticsTheory.exec_pure2_def,
         venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
         venomStateTheory.update_var_def, FLOOKUP_UPDATE,
         venomExecSemanticsTheory.bool_to_word_def] >>
  `allocas_from lo t` by fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  `ptr_covers G tn p t (32*(1+cap))` by simp[arithmeticTheory.ADD_COMM] >>
  `cap < dimword (:256) /\ w2n bp+32*(1+cap) <= dimword (:256)` by decide_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by simp[] >>
  drule_all appendMemoryPtrTheory.append_memory_word_ptr >>
  disch_then (qspecl_then [`func`, `PG`, `DF (storage_trace_horizon mid.storage_trace)`]
    strip_assume_tac) >>
  `!D k. inst_seq_ptr D lo ctx func PG G tn
    (emitted_insts sm sb) (t with vs_inst_idx := k) Gf tnf` by
    (rpt gen_tac >>
     drule_all appendMemoryPtrTheory.append_memory_word_ptr >>
     disch_then (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
     qpat_x_assum `!k. inst_seq_ptr (DF _) _ _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_x_assum `!k. inst_seq_ptr D _ _ _ _ _ _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     metis_tac[fragGasSeqPtrTheory.inst_seq_ptr_ghost_unique]) >>
  `inst_mem_below_frontier load t /\ inst_dload_in_section load t /\
   inst_mem_below_frontier test s1 /\ inst_dload_in_section test s1 /\
   inst_mem_below_frontier assertinst s2 /\ inst_dload_in_section assertinst s2` by
    (qpat_assum `run_inst_seq_mem_ok _ t` mp_tac >>
     qpat_assum `emitted_insts sm sb = _` (fn th => pure_rewrite_tac[th]) >>
     pure_rewrite_tac[fragExecMemTheory.run_inst_seq_mem_ok_def] >> simp[]) >>
  qabbrev_tac `G1 = step_prov PG G load s1` >>
  qabbrev_tac `tn1 = step_taint load t s1 tn` >>
  qabbrev_tac `G2 = step_prov PG G1 test (s2 with vs_inst_idx := SUC t.vs_inst_idx)` >>
  qabbrev_tac `tn2 = step_taint test (s1 with vs_inst_idx := SUC t.vs_inst_idx)
                                (s2 with vs_inst_idx := SUC t.vs_inst_idx) tn1` >>
  `~is_terminator load.inst_opcode /\ ~is_terminator test.inst_opcode /\
   ~is_terminator assertinst.inst_opcode` by
    simp[Abbr `load`, Abbr `test`, Abbr `assertinst`,
         venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def] >>
  `!D. ptr_inst_ok D lo 0 ctx func G tn load t /\
    ptr_inst_ok D lo 0 ctx func G1 tn1 test (s1 with vs_inst_idx := SUC t.vs_inst_idx) /\
    ptr_inst_ok D lo 0 ctx func G2 tn2 assertinst (s2 with vs_inst_idx := t.vs_inst_idx+2) /\
    Gf = G2 /\ tnf = tn2` by
    (gen_tac >>
     qpat_assum `!D k. inst_seq_ptr D _ _ _ _ _ _ _ _ _ _`
       (qspecl_then [`D`, `t.vs_inst_idx`] mp_tac) >>
     qpat_assum `emitted_insts sm sb = _` (fn th => pure_rewrite_tac[th]) >>
     pure_rewrite_tac[fragGasSeqPtrTheory.inst_seq_ptr_def] >>
     simp[instIdxIndepTheory.step_inst_inst_idx_indep,
          instIdxIndepTheory.exec_result_map_def,
          Abbr `G1`, Abbr `tn1`, Abbr `G2`, Abbr `tn2`, arithmeticTheory.ADD1]) >>
  drule appendMemoryPathTheory.append_memory_word_footprint >> strip_tac >>
  `sb.cs_current_bb = sm.cs_current_bb /\
   sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb` by
    (fs[exprLoweringPropsTheory.same_blocks_def,
        emitHelperPropsTheory.inst_extends_def,
        exprLoweringPropsTheory.emitted_insts_def] >>
     gvs[rich_listTheory.IS_PREFIX_APPEND]) >>
  drule_all fragExecTheory.fn_has_code_same_block >> strip_tac >>
  `get_instruction bb t.vs_inst_idx = SOME load /\
   get_instruction bb (SUC t.vs_inst_idx) = SOME test /\
   get_instruction bb (t.vs_inst_idx+2) = SOME assertinst` by
    (qpat_x_assum `!i. i < LENGTH _ ==> _` mp_tac >>
     simp[] >> disch_tac >>
     first_assum (qspec_then `0` mp_tac) >>
     first_assum (qspec_then `1` mp_tac) >>
     first_x_assum (qspec_then `2` mp_tac) >> simp[arithmeticTheory.ADD1]) >>
  `!D explicit. gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
     (t,G,tn) [] (OK (s1 with vs_inst_idx := SUC t.vs_inst_idx),G1,tn1)` by
    (rpt gen_tac >>
     `load.inst_opcode = MLOAD` by simp[Abbr `load`, venomInstTheory.mk_inst_def] >>
     `ptr_inst_ok D lo 0 ctx func G tn load t` by metis_tac[] >>
     `lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
      load.inst_opcode <> INVOKE` by simp[] >>
     drule_all fragGasSeqPtrTheory.straight_line_origin_ptr_edge >>
     simp[Abbr `G1`, Abbr `tn1`]) >>
  `!D explicit. gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
     (s1 with vs_inst_idx := SUC t.vs_inst_idx,G1,tn1) []
     (OK (s2 with vs_inst_idx := t.vs_inst_idx+2),G2,tn2)` by
    (rpt gen_tac >>
     `test.inst_opcode = LT` by simp[Abbr `test`, venomInstTheory.mk_inst_def] >>
     `ptr_inst_ok D lo 0 ctx func G1 tn1 test
       (s1 with vs_inst_idx := SUC t.vs_inst_idx)` by metis_tac[] >>
     `~(s1 with vs_inst_idx := SUC t.vs_inst_idx).vs_halted /\
      lookup_block (s1 with vs_inst_idx := SUC t.vs_inst_idx).vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb (s1 with vs_inst_idx := SUC t.vs_inst_idx).vs_inst_idx = SOME test /\
      test.inst_opcode <> INVOKE /\
      inst_mem_below_frontier test (s1 with vs_inst_idx := SUC t.vs_inst_idx) /\
      inst_dload_in_section test (s1 with vs_inst_idx := SUC t.vs_inst_idx) /\
      step_inst_base test (s1 with vs_inst_idx := SUC t.vs_inst_idx) =
        OK (s2 with vs_inst_idx := SUC t.vs_inst_idx)` by
       (simp[instIdxIndepTheory.step_inst_inst_idx_indep,
         instIdxIndepTheory.exec_result_map_def] >>
        qpat_assum `get_instruction bb (SUC t.vs_inst_idx) = _` mp_tac >>
        simp[Abbr `s1`, venomStateTheory.update_var_def] >> metis_tac[]) >>
     drule_all fragGasSeqPtrTheory.straight_line_origin_ptr_edge >>
     simp[Abbr `G2`, Abbr `tn2`, arithmeticTheory.ADD1]) >>
  qabbrev_tac `s3 = s2 with vs_inst_idx := t.vs_inst_idx+2` >>
  qabbrev_tac `ab = revert_state (set_returndata [] s3)` >>
  `!D explicit. gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
      (s3,G2,tn2) [] (Abort Revert_abort ab,G2,tn2)` by
    (rpt gen_tac >>
     `~s3.vs_halted /\ lookup_block s3.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb s3.vs_inst_idx = SOME assertinst /\
      step_inst_base assertinst s3 = Abort Revert_abort ab` by
       (simp[Abbr `s3`, Abbr `ab`, instIdxIndepTheory.step_inst_inst_idx_indep,
          instIdxIndepTheory.exec_result_map_def] >>
        simp[Abbr `s2`, Abbr `s1`, venomStateTheory.update_var_def,
          venomStateTheory.revert_state_def, venomStateTheory.set_returndata_def] >> metis_tac[]) >>
     simp[fragGasOriginPtrTheory.gas_origin_ptr_edge_def,
          fragGasOriginTheory.gas_origin_edge_def,
          fragGasPathPtrTheory.gas_path_ptr_edge_def] >>
     conj_tac >- (
     qexists_tac `0` >>
     simp[venomExecSemanticsTheory.step_inst_non_invoke,
          Abbr `assertinst`, venomInstTheory.mk_inst_def,
          gasEventsTheory.gas_events_step_def, gasCountTheory.gas_count_step_def,
          memSafeRunTheory.mem_safe_step_def, ptrSafeRunTheory.ptr_safe_step_def] >>
     simp[fragExecTheory.exit_result_def] >>
     (disj2_tac >>
       qpat_assum `inst_mem_below_frontier _ s2` mp_tac >>
       simp[Abbr `s3`, venomInstTheory.mk_inst_def,
            instMemFrontierTheory.inst_mem_below_frontier_inst_idx] >>
       metis_tac[venomInstTheory.mk_inst_def])) >>
     qexists_tac `0` >>
     simp[venomExecSemanticsTheory.step_inst_non_invoke,
          Abbr `assertinst`, venomInstTheory.mk_inst_def,
          gasEventsTheory.gas_events_step_def, gasCountTheory.gas_count_step_def,
          ptrSafeRunTheory.ptr_safe_step_def] >>
     simp[fragExecTheory.exit_result_def]) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (t,G,tn) [] (Abort Revert_abort ab,G2,tn2)` by
    (rpt gen_tac >>
     qpat_assum `!D explicit. gas_origin_ptr_edge _ (t,G,tn) _ _`
       (qspecl_then [`D`, `explicit`] mp_tac) >>
     qpat_assum `!D explicit. gas_origin_ptr_edge _ (_,G1,tn1) _ _`
       (qspecl_then [`D`, `explicit`] mp_tac) >>
     qpat_assum `!D explicit. gas_origin_ptr_edge _ (s3,G2,tn2) _ _`
       (qspecl_then [`D`, `explicit`] mp_tac) >>
     rpt (pop_assum kall_tac) >>
     rpt strip_tac >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s3,G2,tn2) [] (Abort Revert_abort ab,G2,tn2)` by
       (irule (cj 3 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >>
        simp[fragExecTheory.exit_result_def]) >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s1 with vs_inst_idx := SUC t.vs_inst_idx,G1,tn1) []
        (Abort Revert_abort ab,G2,tn2)` by
       (once_rewrite_tac[GSYM APPEND_NIL] >>
        irule (cj 2 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >>
        simp[] >> goal_assum (drule_at Any) >> simp[]) >>
     once_rewrite_tac[GSYM APPEND_NIL] >>
     irule (cj 2 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >>
     simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  simp[gasOutcomeFullTheory.gas_outcome_full_def] >>
  qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`INR (Error (RuntimeError "append overflow"))`, `mid`,
                `Abort Revert_abort ab`, `G2`, `tn2`] >>
  simp[gasSummaryTheory.gas_explicit_nil, fragExecTheory.exit_result_def] >>
  simp[bodyPtrDefsTheory.stmt_exit_ptr_def, exprSimDefsTheory.expr_exit_def,
       exprSimDefsTheory.halt_exit_def]

QED

Resume append_nested_memory_cont_full[success]:
  `!x. Var p = Var x \/ vop = Var x ==> not_fresh_at sm x` by (rpt strip_tac >> gvs[]) >>
  `eval_operand (Var p) t = SOME bp` by simp[venomStateTheory.eval_operand_def] >>
  `cap < dimword (:256) /\ w2n bp+32*(1+cap) <= dimword (:256)` by decide_tac >>
  drule_all appendMemoryPathTheory.append_memory_word_run_reserved >> strip_tac >>
  first_x_assum (qspec_then `LENGTH vs` mp_tac) >> simp[] >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sm sb) t` by
    (irule appendMemoryPathTheory.append_memory_word_mem_ok >>
     qpat_assum `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
     simp[venomStateTheory.eval_operand_def, arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
  `allocas_from lo t` by fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  `ptr_covers G tn p t (32*(1+cap))` by simp[arithmeticTheory.ADD_COMM] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by simp[] >>
  drule_all appendMemoryPtrTheory.append_memory_word_ptr >>
  disch_then (qspecl_then [`func`, `PG`, `DF (storage_trace_horizon mid.storage_trace)`]
    strip_assume_tac) >>
  `!D k. inst_seq_ptr D lo ctx func PG G tn
    (emitted_insts sm sb) (t with vs_inst_idx := k) Gf tnf` by
    (rpt gen_tac >>
     drule_all appendMemoryPtrTheory.append_memory_word_ptr >>
     disch_then (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
     qpat_x_assum `!k. inst_seq_ptr (DF _) _ _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_x_assum `!k. inst_seq_ptr D _ _ _ _ _ _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     metis_tac[fragGasSeqPtrTheory.inst_seq_ptr_ghost_unique]) >>
  drule appendMemoryPathTheory.append_memory_word_footprint >> strip_tac >>
  `sb.cs_current_bb = sm.cs_current_bb /\
   sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb` by
    (fs[exprLoweringPropsTheory.same_blocks_def,
        emitHelperPropsTheory.inst_extends_def,
        exprLoweringPropsTheory.emitted_insts_def] >>
     gvs[rich_listTheory.IS_PREFIX_APPEND]) >>
  drule_all fragExecTheory.fn_has_code_same_block >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sm sb)` by
    (qpat_assum `EVERY (\i. MEM i.inst_opcode _) _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[EVERY_MEM] >> rpt strip_tac >> res_tac >>
     gvs[venomInstTheory.is_terminator_def]) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (t,G,tn) [] (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tnf)` by
    (rpt gen_tac >>
     `inst_seq_ptr D lo ctx func PG G tn (emitted_insts sm sb) t Gf tnf` by
       (qpat_assum `!D k. inst_seq_ptr D _ _ _ _ _ _ _ _ _ _`
          (qspecl_then [`D`, `t.vs_inst_idx`] mp_tac) >>
        simp_tac (srw_ss()) []) >>
     `lookup_block t.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
     `isPREFIX (emitted_insts sm sb) (DROP t.vs_inst_idx bb.bb_instructions)` by
       (qpat_assum `fn_has_code sm sb func` mp_tac >>
        pure_rewrite_tac[fragExecTheory.fn_has_code_def] >> strip_tac >>
        gvs[] >> fs[rich_listTheory.IS_PREFIX_APPEND] >>
        pure_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
        simp_tac (srw_ss()) []) >>
     drule_all fragGasSeqPtrTheory.run_inst_seq_gas_origin_ptr_path >>
     disch_then (qspec_then `explicit` mp_tac) >>
     `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm sb) = []` by
       (qpat_assum `EVERY (\i. MEM i.inst_opcode _) _` mp_tac >>
        rpt (pop_assum kall_tac) >>
        simp[FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac >>
        first_x_assum drule >> strip_tac >> gvs[]) >>
     simp[]) >>
  `value_has_type entry.type entry.value /\ well_formed_type_value entry.type` by
    (fs[exprSimHypsDefsTheory.expr_sim_inv_def,
        vyperTypeInvariantsTheory.state_well_typed_def] >>
     metis_tac[bodySimAugPlaceLoadTheory.aug_place_lookup_typed]) >>
  `!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
     val_in_memory entry.type entry.value (w2n rootw) mem` by
    (fs[bodyPtrDefsTheory.ghost_inv_at_def] >> metis_tac[]) >>
  `w2n rootw + sz <= t.vs_alloca_next /\ type_memory_size entry.type <= sz` by
    (qpat_assum `stmt_state_rel (storage_trace_horizon _) _ _ _ _ _ _` mp_tac >>
     disch_then (mp_tac o cj 1 o MATCH_MP stmt_state_rel_local_ptrs_alloca) >>
     pure_rewrite_tac[loweringStateRelDefsTheory.local_ptrs_rel_def] >> strip_tac >>
     qpat_x_assum `!name en p sz. _ ==> ?w. _`
       (qspecl_then [`id`, `entry`, `rp`, `sz`] mp_tac) >> simp[] >>
     strip_tac >> gvs[]) >>
  `w2n bp = w2n rootw+k` by
    (qpat_assum `place_ptr_rel _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[loweringPostsTheory.place_ptr_rel_def] >> strip_tac >>
     `tv0 = entry.type` by
       metis_tac[bodySimAugPlaceLoadTheory.aug_place_entry_type_agrees,
                 optionTheory.SOME_11] >> gvs[] >>
     once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
     irule exprSimPropsTheory.buffer_offset_no_wrap >>
     qexists_tac `sz` >> decide_tac) >>
  `!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
     val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs))
       (w2n bp) mem` by
    (rpt strip_tac >> asm_rewrite_tac[] >>
     irule bodySimAugPlaceLoadTheory.aug_place_path_project >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  qabbrev_tac `slot = w2n bp+32*(1+LENGTH vs)` >>
  qabbrev_tac `stored = mstore slot (typed_val_to_w256 tv v) t` >>
  qabbrev_tac `out = mstore (w2n bp) (n2w (LENGTH vs+1)) stored` >>
  `u.vs_memory = out.vs_memory` by simp[Abbr `out`, Abbr `stored`, Abbr `slot`] >>
  `!mem. mem_agree_outside
      (tn.t_mem DIFF {i | slot <= i /\ i < slot+32}) stored.vs_memory mem ==>
      val_in_memory tv v slot mem` by
    (simp[Abbr `stored`] >> rpt strip_tac >>
     irule assignTuplePtrStoreWordTheory.typed_word_store_robust_ptr >>
     goal_assum (drule_at Any) >> simp[] >>
     conj_tac
     >- (qexistsl_tac [`get_tenv cx`, `elem`] >>
         simp[] >>
         fs[supportedTypesTheory.supported_full_word_type_def,
            compileEnvTheory.is_word_type_def]) >>
     qexistsl_tac [`tn.t_mem`, `t`] >> simp[]) >>
  `val_wf tv v /\ val_footprint tv v <= 32` by
    metis_tac[valueEncodingTypingTheory.value_has_type_val_wf,
              exprSimPropsTheory.val_footprint_le] >>
  `!mem. mem_agree_outside tnf.t_mem u.vs_memory mem ==>
      val_in_memory tv v slot mem` by
    (simp[Abbr `out`] >> rpt strip_tac >>
     irule rawCallBufferPtrTheory.robust_mstore_disjoint >>
     conj_tac >- simp[] >>
     qexistsl_tac [`w2n bp`,
       `tn.t_mem DIFF {i | slot <= i /\ i < slot+32}`,
       `stored`, `n2w (LENGTH vs+1)`] >>
     conj_tac >- asm_rewrite_tac[] >>
     conj_tac >- (simp[Abbr `slot`] >> decide_tac) >>
     simp[Abbr `slot`]) >>
  `tnf.t_mem = (tn.t_mem DIFF {i | slot <= i /\ i < slot+32})
       DIFF {i | w2n bp <= i /\ i < w2n bp+32}` by
    simp[Abbr `slot`] >>
  `!mem. mem_agree_outside tnf.t_mem u.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap))
      (ArrayV (DynArrayV (vs ++ [v]))) (w2n bp) mem` by
    (rpt strip_tac >>
     irule bodyFullAppendResolvedTheory.append_local_word_robust_array >>
     conj_tac
     >- (rpt strip_tac >>
         `value_has_type tv (EL j vs)` by
           fs[vyperTypingTheory.value_has_type_def,
              vyperTypingTheory.all_have_type_EVERY, EVERY_EL] >>
         metis_tac[valueEncodingTypingTheory.value_has_type_val_wf]) >>
     conj_tac >- simp[] >>
     qexistsl_tac [`u.vs_memory`, `tnf.t_mem`, `t.vs_memory`, `tn.t_mem`] >>
     simp[GSYM markerTheory.Abbrev_def] >>
     reverse conj_tac
     >- (conj_tac
         >- simp[Abbr `out`, Abbr `stored`, Abbr `slot`,
                 valueEncodingPropsTheory.mem_word_at_eq_mload,
                 venomMemPropsTheory.mload_mstore_same] >>
         simp[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
         metis_tac[]) >>
     rpt strip_tac >>
     simp[Abbr `out`, Abbr `stored`] >>
     dep_rewrite.DEP_REWRITE_TAC[valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint] >>
     simp[Abbr `slot`] >> decide_tac) >>
  drule vyperLookupTheory.lookup_scopes_find_containing_scope >> strip_tac >>
  `?updated. assign_subscripts entry.type entry.value path
       (Replace (ArrayV (DynArrayV (vs ++ [v])))) = INL updated` by
    (Cases_on `assign_subscripts entry.type entry.value path
       (Replace (ArrayV (DynArrayV (vs ++ [v]))))` >- metis_tac[] >>
     drule_all aug_place_replace_read_error >>
     strip_tac >>
     qpat_x_assum `_ = TypeError _` (fn th =>
       qpat_x_assum `assign_subscripts _ _ _ _ = INR _`
         (assume_tac o REWRITE_RULE [th])) >>
     `append_place cx (MemoryPlace id path) v (mid with gas_obs := []) =
        (INR (Error (TypeError msg)),mid with gas_obs := [])` by
       (qpat_assum `!st. st.scopes = mid.scopes ==> append_place _ _ _ _ = _`
          (qspec_then `mid with gas_obs := []` mp_tac) >>
        simp[vyperValueOperationTheory.append_element_def, compatible_bound_def,
             vyperTypingTheory.safe_cast_well_typed, SNOC_APPEND,
             write_place_def, bind_def, ignore_bind_def, get_scopes_def,
             lift_option_type_def, type_check_def, assert_def, lift_sum_def,
             replace_memory_entry_def, raise_def, return_def]) >>
     drule_all gasContextTheory.gas_admissible_result >>
     simp[stmtSimDefsTheory.stmt_res_ok_def]) >>
  `value_has_type (ArrayTV tv (Dynamic cap))
      (ArrayV (DynArrayV (vs ++ [v])))` by
    (fs[vyperTypingTheory.value_has_type_def,
        vyperTypingTheory.all_have_type_EVERY, EVERY_APPEND]) >>
  `!mem. mem_agree_outside tnf.t_mem u.vs_memory mem ==>
      val_in_memory entry.type updated (w2n rootw) mem` by
    (match_mp_tac (SRULE [] (Q.INST
       [`entry` |-> `entry`,
        `entry'` |-> `entry with <|value := updated; popped := []|>`,
        `path` |-> `path`, `k` |-> `k`,
        `ptv` |-> `ArrayTV tv (Dynamic cap)`,
        `off` |-> `w2n rootw`, `v` |-> `ArrayV (DynArrayV (vs ++ [v]))`,
        `tm` |-> `tn.t_mem`, `tm'` |-> `tnf.t_mem`,
        `mem` |-> `t.vs_memory`, `mem'` |-> `u.vs_memory`]
       memoryPlaceStorePostTheory.memory_place_replace_robust)) >>
     pure_rewrite_tac[arithmeticTheory.ADD_ASSOC] >>
     simp[replace_memory_entry_def, GSYM markerTheory.Abbrev_def] >>
     conj_tac
     >- (rpt strip_tac >> once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
         qpat_assum `w2n bp = _` (fn th => rewrite_tac[GSYM th]) >>
         qpat_assum `!mem. _ ==> val_in_memory (ArrayTV _ _) (ArrayV (DynArrayV (vs ++ [v]))) _ _` irule >>
         qpat_x_assum `mem_agree_outside _ _ m` mp_tac >>
         simp[arithmeticTheory.ADD_COMM]) >>
     rpt strip_tac >> simp[Abbr `out`, Abbr `stored`] >>
     dep_rewrite.DEP_REWRITE_TAC[valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint] >>
     fs[Abbr `slot`, valueEncodingTheory.type_memory_size_def] >>
     qpat_assum `type_memory_size tv = 32` (fn th =>
       qpat_x_assum `k + (_ + (_ * type_memory_size tv + 32)) <= q`
         (mp_tac o REWRITE_RULE [th])) >> decide_tac) >>
  rename1 `find_containing_scope id mid.scopes = SOME (pre,sc,entry,rest)` >>
  qabbrev_tac `ff = mid with scopes :=
       pre ++ (sc |+ (id,entry with <|value := updated; popped := []|>)) :: rest` >>
  `!tail. append_place cx (MemoryPlace id path) v (mid with gas_obs := tail) =
     (INL (), ff with gas_obs := tail)` by
    (gen_tac >> qpat_assum `!st. st.scopes = mid.scopes ==> append_place _ _ _ _ = _`
       (qspec_then `mid with gas_obs := tail` mp_tac) >>
     simp[vyperValueOperationTheory.append_element_def, compatible_bound_def,
          vyperTypingTheory.safe_cast_well_typed, SNOC_APPEND,
          write_place_def, bind_def, ignore_bind_def, get_scopes_def,
          lift_option_type_def, type_check_def, assert_def, lift_sum_def,
          replace_memory_entry_def, raise_def, return_def, set_scopes_def, Abbr `ff`]) >>
  `write_place cx (MemoryPlace id path) (ArrayV (DynArrayV (vs ++ [v]))) mid =
     (INL (), ff)` by
    simp[write_place_def, bind_def, ignore_bind_def, get_scopes_def,
         lift_option_type_def, type_check_def, assert_def, lift_sum_def,
         replace_memory_entry_def, return_def, set_scopes_def, Abbr `ff`] >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`Gf`, `ff`, `INL ()`,
    `u with vs_inst_idx := LENGTH sb.cs_current_insts`, `tnf`] >>
  conj_tac >- simp[] >>
  simp[GSYM markerTheory.Abbrev_def] >> rpt strip_tac >>
  all_tac >~ [`stmt_lands _ _ _ _`]
  >- simp[loweringPostsTheory.stmt_lands_def] >>
  all_tac >~ [`cenv_top_ext _ _ _`]
  >- simp[loweringPostsTheory.cenv_top_ext_def] >>
  all_tac >~ [`stmt_state_rel _ _ _ _ _ _ _`]
  >- (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
        (qspec_then `H` mp_tac) >>
      (impl_tac >- fs[Abbr `ff`]) >> strip_tac >>
      `stmt_state_rel H ctx func cenv cx ff out` by
        (qunabbrev_tac `out` >> qunabbrev_tac `stored` >> qunabbrev_tac `slot` >>
         irule appendMemoryRelTheory.append_memory_word_state >>
         goal_assum (drule_at (Pat `place_ptr_rel _ _ _ _ _ _ _`)) >>
         goal_assum (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
         qexistsl_tac [`cap`, `tv`, `v`] >>
         simp[] >> conj_tac
         >- (qpat_x_assum `place_ptr_rel _ _ _ _ _ _ _` mp_tac >>
             pure_rewrite_tac[loweringPostsTheory.place_ptr_rel_def] >> strip_tac >>
             `tv0 = entry.type` by
               metis_tac[bodySimAugPlaceLoadTheory.aug_place_entry_type_agrees,
                         optionTheory.SOME_11] >>
             FIRST [gvs[]]) >>
         conj_tac
         >- metis_tac[bodySimAugPlaceLoadTheory.aug_place_entry_type_agrees] >>
         irule (cj 1 stmtSimDeclStoreTheory.typed_word_store) >>
         simp[] >> qexistsl_tac [`elem`, `get_tenv cx`] >> simp[] >>
         fs[supportedTypesTheory.supported_full_word_type_def,
            compileEnvTheory.is_word_type_def]) >>
      pure_rewrite_tac[exprLoweringPropsTheory.stmt_state_rel_inst_idx] >>
      irule stmtSimAppendStorageComposeTheory.stmt_state_rel_reserved_frame >>
      goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ ff out`)) >>
      qexists_tac `sa` >> pure_asm_rewrite_tac[] >> reverse conj_tac
      >- simp[Abbr `out`, Abbr `stored`, Abbr `slot`,
              stateFrameTheory.state_frame_def,
              venomStateTheory.venom_state_component_equality] >>
      rpt strip_tac >>
      `not_fresh_at sm x` by (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >>
         simp[]) >>
      fs[Abbr `out`, Abbr `stored`] >> metis_tac[]) >>
  all_tac >~ [`storage_well_formed_on _ _ _`]
  >- (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
        (qspec_then `H` mp_tac) >>
      (impl_tac >- fs[Abbr `ff`]) >> strip_tac >>
      `storage_well_formed_on cx (ff with gas_obs := []) (FST H) <=>
       storage_well_formed_on cx mid (FST H)` by
        (irule vyperStorageFootprintTheory.storage_well_formed_on_backends >>
         simp[Abbr `ff`]) >> simp[]) >>
  all_tac >~ [`return_buf_frame _ _ _ _`]
  >- (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
      qexistsl_tac [`cenv`, `t`, `sm`] >>
      simp[venomStateTheory.lookup_var_def] >>
      qpat_x_assum `!x a. not_fresh_at sm x /\ lookup_var x t = SOME a ==> lookup_var x u = SOME a` mp_tac >>
      simp[venomStateTheory.lookup_var_def]) >>
  all_tac >~ [`alloca_history _ _`]
  >- (`alloca_inv t` by fs[exprLoweringPropsTheory.stmt_state_rel_def] >>
      `lookup_block t.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
      `?rest. DROP t.vs_inst_idx bb.bb_instructions = emitted_insts sm sb ++ rest` by
        (qpat_assum `t.vs_inst_idx = _` mp_tac >>
         qpat_assum `sb.cs_current_insts = _` mp_tac >>
         qpat_assum `sb.cs_current_bb = _` mp_tac >>
         qpat_assum `lookup_block sm.cs_current_bb _ = SOME bb` mp_tac >>
         qpat_assum `fn_has_code sm sb func` mp_tac >>
         rpt (pop_assum kall_tac) >>
         pure_rewrite_tac[fragExecTheory.fn_has_code_def] >> rpt strip_tac >>
         gvs[] >> fs[rich_listTheory.IS_PREFIX_APPEND] >>
         pure_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
         simp_tac (srw_ss()) []) >>
      `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
        (qpat_assum `EVERY (\i. i.inst_opcode <> INVOKE /\ _) _` mp_tac >>
         rpt (pop_assum kall_tac) >>
         simp[EVERY_MEM] >> metis_tac[]) >>
      drule_all allocaHistoryFragmentTheory.alloca_history_run_inst_seq >> simp[]) >>
  all_tac >~ [`ghost_inv_at (DF H) _ _ _ _ _ _ _ _`]
  >- (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
        (qspec_then `H` mp_tac) >>
      (impl_tac >- fs[Abbr `ff`]) >> strip_tac >>
      `local_ptrs_rel func cenv mid.scopes t` by
        metis_tac[stmt_state_rel_local_ptrs_alloca] >>
      `local_region cenv mid.scopes t id (w2n rootw) sz` by
        (simp[loweringStateRelDefsTheory.local_region_def] >> metis_tac[]) >>
      simp[Abbr `ff`] >>
      irule bodyFullMemoryFramesTheory.body_full_local_scope_ghost_post >>
      conj_tac >- fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
      conj_tac >- simp[] >>
      conj_tac >- (simp[ptrDisciplineTheory.allocas_from_def] >>
                    metis_tac[ptrDisciplineTheory.allocas_from_def]) >>
      conj_tac
      >- (qpat_assum `ghost_inv_at (DF H) _ _ _ _ _ _ _ _` mp_tac >>
          qpat_assum `u.vs_accounts = _` mp_tac >>
          qpat_assum `u.vs_transient = _` mp_tac >>
          qpat_assum `u.vs_immutables = _` mp_tac >>
          qpat_assum `u.vs_call_ctx = _` mp_tac >>
          qpat_assum `tnf.t_stor = _` mp_tac >>
          qpat_assum `tnf.t_trans = _` mp_tac >>
          qpat_assum `tnf.t_imm = _` mp_tac >>
          rpt (pop_assum kall_tac) >>
          pure_rewrite_tac[venomStateTheory.mstore_def, LET_THM] >>
          simp_tac (srw_ss()) [bodyPtrDefsTheory.ghost_inv_at_def,
                               bodyPtrDefsTheory.stor_taint_ok_at_def]) >>
      qexistsl_tac [`G`, `rootw`, `func`, `type_memory_size entry.type`,
                    `rp`, `t`, `sa`, `sz`, `tn`] >>
      simp[] >> conj_tac
      >- (rpt strip_tac >>
          `not_fresh_at sm x` by
            (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
          `lookup_var x u = lookup_var x t` by
            (drule_all append_nested_memory_reserved_lookup >>
             disch_then irule >> simp[]) >>
          qpat_x_assum `lookup_var x u = lookup_var x t` mp_tac >>
          qpat_assum `!x. not_fresh_at sm x ==> _` (qspec_then `x` mp_tac) >>
          simp[venomStateTheory.lookup_var_def]) >>
      conj_tac
      >- (gen_tac >> disch_tac >> conj_tac
          >- (simp[Abbr `out`, Abbr `stored`] >>
              dep_rewrite.DEP_REWRITE_TAC[valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint] >>
              fs[Abbr `slot`, valueEncodingTheory.type_memory_size_def] >>
              qpat_assum `type_memory_size tv = 32` (fn th =>
                qpat_x_assum `k + (_ * type_memory_size tv + 32) <= q`
                  (mp_tac o REWRITE_RULE [th])) >> decide_tac) >>
          fs[Abbr `slot`, valueEncodingTheory.type_memory_size_def] >>
          qpat_assum `type_memory_size tv = 32` (fn th =>
            qpat_x_assum `k + (_ * type_memory_size tv + 32) <= q`
              (mp_tac o REWRITE_RULE [th])) >> strip_tac >>
          `~(k + (w2n rootw + 32 * (LENGTH vs + 1)) <= i /\
              i < k + (w2n rootw + (32 * (LENGTH vs + 1) + 32)))` by decide_tac >>
          metis_tac[]) >>
      conj_tac
      >- (`0 < sz` by
            (qpat_x_assum `k + type_memory_size (ArrayTV tv (Dynamic cap)) <= _` mp_tac >>
             simp[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
          `lo <= w2n rootw` by
            (irule (INST_TYPE [alpha |-> ``:256``]
               bodyFullMemoryFramesTheory.body_full_local_region_lower_bound) >>
             goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
             goal_assum (drule_at (Pat `body_inv _ _ _ _`)) >>
             goal_assum (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
             qexistsl_tac [`DF H`, `H`, `func`] >> simp[]) >>
          simp[Abbr `out`, Abbr `stored`] >>
          dep_rewrite.DEP_REWRITE_TAC[valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint] >>
          fs[Abbr `slot`] >> decide_tac) >>
      qpat_x_assum `ghost_inv_at (DF H) lo d cenv cx mid G tn t` mp_tac >>
      simp_tac (srw_ss()) [ghost_inv_at_def] >>
      strip_tac >> simp[]) >>
  all_tac >~ [`lookup_var x _ = SOME w`]
  >- (`not_fresh_at sm x` by
        (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
      simp[venomStateTheory.lookup_var_def] >>
      metis_tac[venomStateTheory.lookup_var_def]) >>
  all_tac >~ [`FLOOKUP Gf x = FLOOKUP G0 x`]
  >- (`not_fresh_at sm x` by
       (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
      qpat_assum `!x. not_fresh_at sm x ==> _` (qspec_then `x` mp_tac) >>
      qpat_assum `!x. not_fresh_at sa x ==> _` (qspec_then `x` mp_tac) >> simp[]) >>
  all_tac >~ [`op_taint tnf (Var x) = op_taint tn0 (Var x)`]
  >- (`not_fresh_at sm x` by
       (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
      qpat_assum `!x. not_fresh_at sm x ==> _` (qspec_then `x` mp_tac) >>
      qpat_assum `!x. not_fresh_at sa x ==> _` (qspec_then `x` mp_tac) >> simp[]) >>
  all_tac >~ [`alloca_frame _ _ _ _ _ _ _`] >- suspend "alloca" >>
  simp[]
QED

Resume append_nested_memory_cont_full[alloca]:
  `local_ptrs_reserved cenv sm` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `local_region cenv mid.scopes t id (w2n rootw) sz` by
    (simp[loweringStateRelDefsTheory.local_region_def] >> metis_tac[]) >>
  `MAP FDOM ff.scopes = MAP FDOM mid.scopes` by
    (drule vyperLookupTheory.find_containing_scope_structure >> strip_tac >>
     simp[Abbr `ff`, MAP_APPEND, finite_mapTheory.FDOM_FUPDATE] >>
     qpat_x_assum `FLOOKUP sc id = SOME entry` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[finite_mapTheory.FLOOKUP_DEF, AllCaseEqs(), pred_setTheory.ABSORPTION]) >>
  irule (INST_TYPE [alpha |-> ``:256``] stmtSimDefsTheory.alloca_frame_local_store) >>
  simp[] >> reverse conj_tac
  >- (qexistsl_tac [`storage_trace_horizon mid.storage_trace`, `ctx`, `cx`, `func`] >>
      first_assum ACCEPT_TAC) >>
  qexistsl_tac [`w2n rootw`, `mid`, `id`, `sz`, `t`, `sz`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> simp[venomStateTheory.lookup_var_def] >>
      `not_fresh_at sm q` by
        (fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
      drule_all append_nested_memory_reserved_lookup >>
      simp[venomStateTheory.lookup_var_def]) >>
  reverse conj_tac
  >- (irule stmtSimDefsTheory.alloca_frame_same >> simp[]) >>
  rpt strip_tac >> simp[Abbr `out`, Abbr `stored`] >>
  dep_rewrite.DEP_REWRITE_TAC[valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint] >>
  fs[Abbr `slot`, valueEncodingTheory.type_memory_size_def] >>
  qpat_assum `type_memory_size tv = 32` (fn th =>
    qpat_x_assum `k + (_ * type_memory_size tv + 32) <= q`
      (mp_tac o REWRITE_RULE [th])) >> decide_tac
QED

Finalise append_nested_memory_cont_full[local]

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
    (irule fragGasCopyLoopTheory.inst_seq_ptr_lower_bound_transport >>
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
     irule fragGasCopyLoopTheory.inst_seq_ptr_lower_bound_transport >>
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
    (rpt gen_tac >> irule fragGasOriginPtrLoopTheory.emitted_origin_ptr_path >>
     conj_tac >- simp[] >> qexists_tac `sm` >>
     simp[] >> fs[EVERY_MEM]) >>
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
  first_x_assum (qspec_then `ctx` (qx_choose_then `jm` assume_tac)) >>
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

Theorem append_nested_storage_cont_full:
 !DF lo d ctx shadow_ctx PG func cx st0 lctx RetQ cenv env sa sm sb s0 G0 tn0
   mid t G tn tr slot tv v bop vop w elem src_ty cap.
  body_inv (cx_tops cx) ctx cenv cx /\
  gas_admissible (append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v)
    (stmt_res_ok lctx) mid /\
  expr_sim_inv cenv cx env mid /\ supported_full_word_type elem /\
  evaluate_type (get_tenv cx) elem = SOME tv /\
  value_has_type tv v /\ abi_tuple_word tv v /\
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
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\ ~ctx_has_dalloca ctx /\
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
         op_taint tf (Var x) = op_taint tn0 (Var x)))
    (\H res ee gt r. (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
      halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==>
        allocas_below_fmp s))
Proof
  rpt gen_tac >> strip_tac >>
  `is_word_type elem` by fs[supported_full_word_type_def, is_word_type_def] >>
  qspecl_then [`DF`,`lo`,`d`,`ctx`,`shadow_ctx`,`PG`,`func`,`cx`,`st0`,`lctx`,
    `RetQ`,`cenv`,`env`,`sa`,`sm`,`sb`,`s0`,`G0`,`tn0`,`mid`,`t`,`G`,`tn`,`tr`,
    `slot`,`tv`,`v`,`bop`,`vop`,`w`,`elem`,`src_ty`,`cap`] mp_tac
    append_nested_storage_cont_framed >>
  (impl_tac >- (asm_simp_tac bool_ss [] >> metis_tac[])) >> strip_tac >>
  irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
  goal_assum (drule_at (Pos last)) >> simp[] >>
  rpt gen_tac >> strip_tac >> qexists_tac `cenv''` >> simp[]
QED

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

(* GATE_ADMISSION: missing case, local Append with a nonword element; owner: log lane *)
Theorem body_append_local_nonword_frag_full:
  !cx id e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv
    env env' ret_ty lctx RetQ es elem cap.
  (!s p t. eval_target_place cx (NameTarget id) s = (INL p,t) ==>
     body_expr_full_ok cx e) /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (Append (NameTarget id) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Append (NameTarget id) e) ==> occurs_abi_decode_target target tops) /\
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
    (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Append (NameTarget id) e)))
    (eval_stmt cx (Append (NameTarget id) e)) es
Proof
  cheat
QED

(* GATE_ADMISSION: missing case, subscript Append; owner: log lane *)
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
    (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Append (SubscriptTarget base key) e)))
    (eval_stmt cx (Append (SubscriptTarget base key) e)) es
Proof
  cheat
QED

(* GATE_ADMISSION: missing case, attribute Append; owner: log lane *)
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
    (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Append (AttributeTarget base field) e)))
    (eval_stmt cx (Append (AttributeTarget base field) e)) es
Proof
  cheat
QED

(* GATE_ADMISSION: missing case, storage bytestring Append; owner: log lane *)
Theorem body_append_storage_bytestring_frag_full:
  !cx nid e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv
    env env' ret_ty lctx RetQ es elem cap.
  (!s p t. eval_target_place cx (TopLevelNameTarget nid) s = (INL p,t) ==>
     body_expr_full_ok cx e) /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (Append (TopLevelNameTarget nid) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Append (TopLevelNameTarget nid) e) ==> occurs_abi_decode_target target tops) /\
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
    (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Append (TopLevelNameTarget nid) e)))
    (eval_stmt cx (Append (TopLevelNameTarget nid) e)) es
Proof
  cheat
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
    (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Append (TopLevelNameTarget nid) e)))
    (eval_stmt cx (Append (TopLevelNameTarget nid) e)) es
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `type_place_target env (TopLevelNameTarget nid) =
    SOME (Type (ArrayT checked_elem (Dynamic checked_cap)))` >>
  PairCases_on `nid` >>
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
  metis_tac[bodyAppendStorageFactsTheory.supported_append_storage_decl]
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
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` mp_tac >>
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
  qpat_x_assum `!tail. INL place = res /\ _` kall_tac >>
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
     strip_tac >> fs[body_inv_def]) >>
  drule_all bodyAppendStorageFactsTheory.append_storage_compiler_location >> strip_tac >>
  `supported_pure_expr tops e` by
    (qpat_assum `supported_stmt _ _ _`
       (mp_tac o ONCE_REWRITE_RULE [supported_stmt_def]) >> simp[]) >>
  drule bodyAppendStorageFactsTheory.append_typing_target >> strip_tac >>
  `body_stmt_safe tops (Append (TopLevelNameTarget (nid0,nid1)) e)` by
    (drule bodyExprPreFactsTheory.supported_stmt_body_safe >> simp[]) >>
  `supported_expr tops e` by simp[supportedExprsTheory.supported_expr_def] >>
  drule_all bodyAppendStorageAdapterTheory.body_append_expr_pre >> strip_tac >>
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
  qpat_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _`
    (assume_tac o SRULE [gasShadowTheory.gas_shadow_stmt_def,
       gasShadowTheory.gas_shadow_expr_def]) >>
  `?vop raw_shadow sm shadow_sm. cenv' = cenv /\
     lower_value compile_expr cenv elem e sa = (vop,sm) /\
     lower_value compile_expr cenv elem (gas_shadow_expr e) shadow_sa = (raw_shadow,shadow_sm) /\
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
    (qspec_then `elem` mp_tac (Q.GEN `ty` gas_shadow_stmt_lower_value) >>
     rewrite_tac[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[]) >>
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
     `cx_tops cx = tops` by fs[body_inv_def,gasContextTheory.cx_tops_def] >> simp[]) >>
  rpt gen_tac >> disch_then (qx_choose_then `cenvf` strip_assume_tac) >>
  qexists_tac `cenvf` >> simp[] >>
  conj_tac >-
    (qpat_assum `stmt_state_rel H ctx func cenvf cx ee t'`
      (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  first_assum ACCEPT_TAC
QED

Finalise body_append_storage_word_frag_full

Theorem body_append_storage_nonbytes_frag_full[local]:
  !cx nid e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv
    env env' ret_ty lctx RetQ es elem cap.
  (!s p t. eval_target_place cx (TopLevelNameTarget nid) s = (INL p,t) ==>
     body_expr_full_ok cx e) /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (Append (TopLevelNameTarget nid) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Append (TopLevelNameTarget nid) e) ==> occurs_abi_decode_target target tops) /\
  expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
  locals_alloc_ok cenv env /\
  type_stmt env ret_ty (Append (TopLevelNameTarget nid) e) = SOME env' /\
  type_place_target env (TopLevelNameTarget nid) = SOME (Type (ArrayT elem (Dynamic cap))) /\
  ~is_word_type elem /\ ~is_bytestring_type elem /\
  stmt_exprs_ok cenv (Append (TopLevelNameTarget nid) e) /\
  call_evaluation_safe cx (int_calls_stmt (Append (TopLevelNameTarget nid) e)) /\
  frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ cenv ret_ty ==>
  stmt_frag_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (Append (TopLevelNameTarget nid) e))
    (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Append (TopLevelNameTarget nid) e)))
    (eval_stmt cx (Append (TopLevelNameTarget nid) e)) es
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `type_place_target env (TopLevelNameTarget nid) =
    SOME (Type (ArrayT checked_elem (Dynamic checked_cap)))` >>
  PairCases_on `nid` >>
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
  metis_tac[bodyAppendStorageFactsTheory.supported_append_storage_decl]
QED

Resume body_append_storage_nonbytes_frag_full[compose]:
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
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` mp_tac >>
  disch_then (fn th =>
    irule_at (Pos last) gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
    irule_at (Pos hd) th) >>
  qexists_tac `\H res ee G tn u. res = INL place /\ ee = observed with gas_obs := [] /\
        G = G0 /\ tn = tn0 /\ u = s0` >> simp[] >>
  suspend "after_root"
QED

Resume body_append_storage_nonbytes_frag_full[after_root]:
  rpt strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  disj1_tac >> qexists_tac `place` >> conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `!tail. INL place = res /\ _` kall_tac >>
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
     strip_tac >> fs[body_inv_def]) >>
  drule_all bodyAppendStorageFactsTheory.append_storage_compiler_location >> strip_tac >>
  `supported_pure_expr tops e` by
    (qpat_assum `supported_stmt _ _ _`
       (mp_tac o ONCE_REWRITE_RULE [supported_stmt_def]) >> simp[]) >>
  drule bodyAppendStorageFactsTheory.append_typing_target >> strip_tac >>
  `body_stmt_safe tops (Append (TopLevelNameTarget (nid0,nid1)) e)` by
    (drule bodyExprPreFactsTheory.supported_stmt_body_safe >> simp[]) >>
  `supported_expr tops e` by simp[supportedExprsTheory.supported_expr_def] >>
  drule_all bodyAppendStorageAdapterTheory.body_append_expr_pre >> strip_tac >>
  `expr_body_pre cenv cx env e mid` by simp[Abbr `observed`] >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  `find_var_decl_by_name nid1 tops <> NONE` by simp[] >>
  `~is_word_type elem /\ ~is_bytestring_type elem` by
    (drule_all bodyAppendStorageFactsTheory.append_typed_storage_target >>
     strip_tac >> fs[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s0` by
    metis_tac[bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp] >>
  suspend "rhs_code"
QED

Resume body_append_storage_nonbytes_frag_full[rhs_code]:
  qpat_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _`
    (assume_tac o SRULE [gasShadowTheory.gas_shadow_stmt_def,
       gasShadowTheory.gas_shadow_expr_def]) >>
  `?vop raw_shadow sm shadow_sm. cenv' = cenv /\
     lower_value compile_expr cenv elem e sa = (vop,sm) /\
     lower_value compile_expr cenv elem (gas_shadow_expr e) shadow_sa = (raw_shadow,shadow_sm) /\
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
    (qspec_then `elem` mp_tac (Q.GEN `ty` gas_shadow_stmt_lower_value) >>
     rewrite_tac[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[]) >>
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

Resume body_append_storage_nonbytes_frag_full[rhs_exit]:
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

Resume body_append_storage_nonbytes_frag_full[suffix]:
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

Resume body_append_storage_nonbytes_frag_full[aggregate]:
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

Resume body_append_storage_nonbytes_frag_full[aggregate_typed]:
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

Resume body_append_storage_nonbytes_frag_full[aggregate_rhs]:
  `type_widens_to env.type_defs (expr_type e) elem` by simp[] >>
  drule_all_then assume_tac immutableDeployPhysicalSourceTheory.immutable_rhs_physical_widens >>
  `~is_word_type (lowered_value_type cenv e) /\
    ~is_bytestring_type (lowered_value_type cenv e)` by
    metis_tac[typedMemoryCopyTheory.return_source_word_widens_eq,
              typedMemoryCopyTheory.type_widens_from_bytestring] >>
  `post_value_type cenv e = lowered_value_type cenv e` by
    metis_tac[immutableDeployPhysicalSourceTheory.immutable_rhs_post_physical_classify] >>
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
  `expr_val_at cenv cx (lowered_value_type cenv e) sa sm mid' v vop t` by metis_tac[] >>
  drule_all externalReturnBoundsTheory.expr_val_at_frontier >>
  disch_then (qx_choose_then `sw` (map_every assume_tac o CONJUNCTS)) >>
  `val_footprint stv v = type_memory_size stv` by
    metis_tac[annassignRelayoutSourceTheory.nonbytes_evaluated_val_footprint] >>
  `w2n sw + type_memory_size stv <= t.vs_alloca_next` by fs[] >>
  `t.vs_alloca_next < dimword (:256)` by
    (qpat_assum `stmt_state_rel (storage_trace_horizon mid'.storage_trace) ctx func cenv cx mid' t`
       (mp_then (Pos hd) assume_tac stateRelProjTheory.stmt_state_rel_alloca_room) >>
     drule exprLoweringPropsTheory.alloca_room_next_lt >> simp[]) >>
  `w2n sw + type_memory_size stv < dimword (:256)` by decide_tac >>
  `ptr_buf_ok cenv e vop G1 t` by
    (qpat_assum `~is_word_type _ ==> ptr_buf_ok cenv e vop G1 t` mp_tac >>
     simp[]) >>
  qpat_assum `ptr_val_ok cx (post_value_type cenv e) _ _ _ _ _`
    (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.ptr_val_ok_def]) >>
  simp[] >> strip_tac >>
  `?src. vop = Var src /\ ptr_covers G1 tn1 src t (type_memory_size stv)` by
    (irule assignBasePtrBoundaryTheory.ptr_buf_ok_read_covers >>
     simp[] >> qexistsl_tac [`cenv`,`e`] >> simp[]) >>
  `not_fresh_at sm src` by
    (drule_all exprOperandVarTheory.compile_lower_value_var >> simp[]) >>
  `lookup_var src t = SOME sw` by
    fs[venomStateTheory.eval_operand_def] >>
  `!mem. mem_agree_outside tn1.t_mem t.vs_memory mem ==>
     val_in_memory stv v (w2n sw) mem` by
    (qpat_assum `ptr_mem_ok cx (lowered_value_type cenv e) _ _ _ _ _`
       (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.ptr_mem_ok_def]) >>
     disch_then (qspecl_then [`stv`,`sw`] mp_tac) >> simp[]) >>
  qpat_x_assum `vop = Var src` SUBST_ALL_TAC >>
  suspend "aggregate_cont"
QED

Resume body_append_storage_nonbytes_frag_full[aggregate_cont]:
  `type_memory_bytes cenv elem < 2 ** 64` by
    (qpat_assum `cenv.ce_hashmap_info _ = NONE` (fn no_map =>
       qpat_assum `cenv.ce_module_var_type _ = SOME (ArrayT elem _)` (fn ty =>
         qpat_assum `~is_word_type elem` (fn nonword =>
           qpat_assum `stmt_exprs_ok cenv (Append (TopLevelNameTarget _) e)`
             (strip_assume_tac o SRULE [stmt_exprs_ok_def,
               allocLimitsTheory.alloc_limits_stmt_def,
               allocLimitsTheory.target_place_type_def,no_map,ty,nonword])))) >>
     simp[]) >>
  `32 * type_slot_size tv < dimword (:256)` by
    (qpat_assum `type_memory_bytes cenv elem = 32 * type_slot_size tv` (fn size =>
       qpat_assum `type_memory_bytes cenv elem < 2 ** 64`
         (mp_tac o PURE_REWRITE_RULE [size])) >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  qpat_x_assum `(type_memory_bytes cenv elem + 31) DIV 32 = type_slot_size tv`
    (fn slots => qpat_assum `type_memory_bytes cenv elem = type_memory_size tv`
      (fn bytes => RULE_ASSUM_TAC (PURE_REWRITE_RULE [slots,bytes]) >> assume_tac bytes)) >>
  irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
  irule_at (Pat `gas_outcome_full _ _ _ _ _ _ _ _`) append_storage_aggregate_cont_full >>
  qpat_assum `compile_dynarray_append cenv (Lit _) _ 1 _ elem elem _ F _ sd = ((),sb)`
    (irule_at Any) >>
  qpat_assum `compile_alloc_buffer (type_memory_size tv) sm = (tmp,sc)` (irule_at Any) >>
  qpat_assum `compile_store_memory cenv (Var src) tmp.buf_operand elem _ sc = ((),sd)` (irule_at Any) >>
  qpat_assum `lookup_var src t = SOME sw` (irule_at Any) >>
  qpat_assum `encode_value tv v = SOME writes` (irule_at Any) >>
  simp[] >>
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

Resume body_append_storage_nonbytes_frag_full[aggregate_post]:
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
     qpat_assum `!x. not_fresh_at sa x ==> FLOOKUP G1 x = _ /\ _`
       (qspec_then `x` mp_tac) >>
     qpat_assum `!x. not_fresh_at sm x ==> _` (qspec_then `x` mp_tac) >> simp[]) >>
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

Finalise body_append_storage_nonbytes_frag_full[local]

Theorem body_append_storage_flat_copy_frag_full:
  !cx nid e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv
    env env' ret_ty lctx RetQ es elem cap.
  (!s p t. eval_target_place cx (TopLevelNameTarget nid) s = (INL p,t) ==>
     body_expr_full_ok cx e) /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (Append (TopLevelNameTarget nid) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Append (TopLevelNameTarget nid) e) ==> occurs_abi_decode_target target tops) /\
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
    (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Append (TopLevelNameTarget nid) e)))
    (eval_stmt cx (Append (TopLevelNameTarget nid) e)) es
Proof
  rpt strip_tac >> irule body_append_storage_nonbytes_frag_full >> simp[] >>
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
    (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Append (TopLevelNameTarget nid) e)))
    (eval_stmt cx (Append (TopLevelNameTarget nid) e)) es
Proof
  rpt strip_tac >> irule body_append_storage_nonbytes_frag_full >> simp[] >>
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
    (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Append (TopLevelNameTarget nid) e)))
    (eval_stmt cx (Append (TopLevelNameTarget nid) e)) es
Proof
  rpt strip_tac >> irule body_append_storage_nonbytes_frag_full >> simp[] >>
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
