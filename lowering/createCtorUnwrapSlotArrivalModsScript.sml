(* The slot unwrap's own allocation and copy, in their emitted ID band. *)
Theory createCtorUnwrapSlotArrivalMods
Ancestors
  createCtorUnwrapSlotArrival createExprSizeExitDefsMods
  createCtorUnwrapSlotPostMods createCtorSlotLoopOriginBand createCtorStraightBand
  bodyFullUnwrapSlotOrigin exprPtrUnwrapLoopEntry exprPtrUnwrapEnsureShape
  exprPtrUnwrapSingleSegment abiBufferAllocationCode stmtReasonLitFragMemory
  exprPtrUnwrapStorage loweringPosts localPtrsProps vyperStorageFootprint
  fragGasOriginPtr ptrSafetyTransport bufferAllocationExecution venomMemProofs
  allocaHistory bodyBinopFragMemory copyExecution relation rich_list arithmetic
  venomExecSemantics venomInst venomState exprSimStorageCopy fragExec compileEnv
  exprLoweringProps exprLowering finite_map words emitHelper list ptrDiscipline
  loweringStateRelDefs venomMemDefs context bodyPtrDefs exprSimProps
  exprSimPtrTopLevelStorageCopy exprPtrUnwrapAllocSemantic abiPathAllocInv
  freshWrites valueEncodingProps exprSimFieldLayout gasOriginPtrLabels allocationPtr
  exprSimAlloc vyperStorageTrace bodyFullHashKeccakFixed loweringHalt exprPtrUnwrapAllocEntry
  createCtorSlotStraightBandMods

Theorem ctor_unwrap_slot_arrival_mods:
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\ ~is_word_type t /\
  compile_expr cenv ty e sa = (LocatedValue t p,sm) /\
  sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
  unwrap_value cenv (LocatedValue t p) sb = (op,sc) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  (!bb. lookup_block sc.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
  type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rty /\
  type_memory_size rty < 2**64 /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post_mods H ctx func cenv cx e es sa sm s0 ee tv (LocatedValue t p) s /\
     ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s) /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ptr_vv_ok cx (post_value_type cenv e) tv (LocatedValue t p) ee G tn s /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?v z G' tn'.
    read_result cx tv ee = (INL v,ee) /\
    RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
      sb.cs_next_id <= i.inst_id /\ i.inst_id < sc.cs_next_id /\
      i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v) s z /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,G',tn') /\
       expr_post_mods H ctx func cenv cx e es sa sc s0 ee v op z /\
       ghost_inv_at_mods (DF H) lo d cenv cx ee G' tn' z) /\
    vv_at cenv cx (post_value_type cenv e) sa sc ee tv
       (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z /\
    vv_own cenv cx (post_value_type cenv e) sb sc ee (Value v)
       (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z /\
    expr_store_bound cx (post_value_type cenv e) v op z /\
    ~z.vs_halted /\ z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
    s0.vs_alloca_next <= z.vs_alloca_next /\
    ptr_val_ok cx (post_value_type cenv e) v op G' tn' z /\
    ptr_buf_ok cenv e op G' z /\
    (!rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
            eval_operand op z = SOME w ==> w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    ghost_kept_at lo cenv es sa Gi ti s0 G' tn' /\
    (!x. not_fresh_at sb x ==>
         lookup_var x z = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)) /\
    wb_frame cenv ee ee sb s z /\ ghost_kept_at lo cenv ee sb G tn s G' tn'
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by fs[storage_trace_domain_def,Abbr `H0`] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  qpat_x_assum `vv_post_mods H0 _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[bodyFullPostsModsTheory.vv_post_mods_def]) >>
  `t = post_value_type cenv e /\ ?v a. read_result cx tv ee = (INL v,ee) /\
                                      eval_operand p.ptr_operand s = SOME a` by
    (qpat_assum `p.ptr_location = LocStorage \/ _` mp_tac >>
     qpat_assum `vv_holds_mods _ _ _ _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >> strip_tac >>
     gvs[bodyFullPostsModsTheory.vv_holds_mods_def,vv_holds_def,storage_holds_def,
         vyperStateTheory.read_result_def,vyperStateTheory.return_def] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by
    fs[bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s)` by
    (drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
  `op_taint tn p.ptr_operand = {}` by fs[ptr_vv_ok_def] >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sb x` by metis_tac[not_fresh_at_mono] >>
  qabbrev_tac `nb = type_memory_bytes cenv (post_value_type cenv e)` >>
  qabbrev_tac `n = type_slot_size rty` >>
  `nb = type_memory_size rty /\ nb = 32*n` by simp[Abbr `nb`,Abbr `n`,type_memory_size_slots] >>
  `nb < dimword(:256) /\ n < 2**256` by fs[dimword_def] >>
  `compile_ensure_in_memory p.ptr_operand p.ptr_location nb n
        cenv.ce_is_ctor cenv.ce_imm_alloca sb = (op,sc)` by
    (qpat_assum `unwrap_value _ _ _ = _` mp_tac >>
     qpat_assum `p.ptr_location = LocStorage \/ _` strip_assume_tac >>
     gvs[unwrap_value_def,slot_count_of_memory_size,Abbr `n`,Abbr `nb`]) >>
  drule_all ensure_slot_memory_split >> disch_then (qx_choosel_then [`buf`,`mid`] strip_assume_tac) >>
  `fn_has_code sb mid func /\ fn_has_code mid sc func` by suspend "registered" >>
  suspend "allocate"
QED

Resume ctor_unwrap_slot_arrival_mods[registered]:
  drule compile_alloc_buffer_extends >> strip_tac >>
  `cs_extends mid sc` by
    (Cases_on `n = 1`
     >- (qpat_x_assum `if n = 1 then _ else _` mp_tac >> simp[] >>
         disch_then (strip_assume_tac o MATCH_MP storage_copy_word_layout) >>
         fs[same_blocks_def,cs_extends_same_block]) >>
     qpat_x_assum `if n = 1 then _ else _` mp_tac >> simp[] >> strip_tac >>
     drule_all compile_slot_to_memory_boundary >> simp[]) >>
  drule_all fn_has_code_split >> simp[]
QED

Resume ctor_unwrap_slot_arrival_mods[allocate]:
  `32*n <= nb` by simp[] >>
  drule_all unwrap_alloc_loop_entry >>
  disch_then (qspecl_then [`PG`,`G`,
    `<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>`]
    (qx_choosel_then [`root`,`dst`,`allocated`,`G0`,`tn0`,`u`] strip_assume_tac)) >>
  drule_all unwrap_alloc_origin_path >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`,
    `<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>`]
    (qx_choosel_then [`out`,`u1`] strip_assume_tac)) >>
  `out = root` by fs[] >>
  qpat_x_assum `out = root` SUBST_ALL_TAC >>
  `u1 = u` by fs[] >> qpat_x_assum `u1 = u` SUBST_ALL_TAC >>
  `allocas_from lo allocated` by
    (qpat_assum `gas_origin_ptr_path _ (s,G,tn) _ _`
       (mp_then Any (qspec_then `lo` mp_tac) (Q.GEN `lower` member_origin_allocas_from)) >> simp[]) >>
  `alloca_history func allocated` by (drule_all unwrap_alloc_origin_history >> simp[]) >>
  `not_fresh_at mid root /\ sb.cs_next_id <= mid.cs_next_id` by
    (conj_tac
     >- (drule storage_copy_alloc_layout >> strip_tac >> metis_tac[]) >>
     drule compile_alloc_buffer_code >> simp[]) >>
  `op = Var root` by fs[] >>
  suspend "allocation_bounds"
QED

Resume ctor_unwrap_slot_arrival_mods[allocation_bounds]:
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists `sm` >> simp[]) >>
  drule_all unwrap_alloc_semantic_frames >> strip_tac >>
  `alloca_next_valid u` by fs[stmt_state_rel_def,alloca_inv_def] >>
  `w2n dst + nb <= u.vs_alloca_next` by
    (qpat_assum `alloca_next_valid u` (mp_tac o REWRITE_RULE[alloca_next_valid_def]) >>
     disch_then (drule_then ACCEPT_TAC)) >>
  `w2n dst + 32*n <= allocated.vs_alloca_next` by gvs[] >>
  `s.vs_alloca_next <= allocated.vs_alloca_next` by
    (qpat_assum `allocated = _` SUBST1_TAC >> qpat_assum `u = _` SUBST1_TAC >>
     simp[NoAsms,buffer_allocation_fields_def,update_var_def] >>
     Cases_on `FLOOKUP s.vs_allocas sb.cs_next_id` >> simp[]) >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at mid x` by
    (drule compile_alloc_buffer_code >> strip_tac >> metis_tac[not_fresh_at_mono,DECIDE ``x <= x+1``]) >>
  `RTC (\r t. ?i. ctor_segment_fetch func r = SOME i /\
       sb.cs_next_id <= i.inst_id /\ i.inst_id < mid.cs_next_id /\
       i.inst_opcode <> INVOKE /\ ctor_segment_next func r i = SOME t) s allocated` by
    (qpat_assum `allocated = _` SUBST1_TAC >> irule ctor_slot_alloc_band_mods >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
       qexistsl_tac [`buf`,`nb`,`root`] >> rpt conj_tac >> first_assum ACCEPT_TAC]) >>
  suspend "copy"
QED

Resume ctor_unwrap_slot_arrival_mods[copy]:
  `?z Gf tnf.
      gas_origin_ptr_path (<| d_stor := K (K {}); d_trans := K (K {});
        d_imm := K {}; d_ret := K {} |>,lo,explicit,ctx,func,PG)
        (allocated,G0,tn0) [] (OK z,Gf,tnf) /\
      RTC (\r t. ?i. ctor_segment_fetch func r = SOME i /\
        mid.cs_next_id <= i.inst_id /\ i.inst_id < sc.cs_next_id /\
        i.inst_opcode <> INVOKE /\ ctor_segment_next func r i = SOME t) allocated z /\
      mid.cs_next_id <= sc.cs_next_id /\
      ~z.vs_halted /\ z.vs_current_bb = sc.cs_current_bb /\
      z.vs_inst_idx = LENGTH sc.cs_current_insts /\ alloca_history func z /\
      z.vs_alloca_next = allocated.vs_alloca_next /\
      (n <> 1 ==> ?cv ds.
        toplevel_copy_inv cv ds root p.ptr_operand p.ptr_location a (w2n dst) n allocated G0 tn0 n Gf tnf z /\
        (!x. not_fresh_at mid x ==> ~MEM x ds) /\ ~z.vs_halted) /\
      (n = 1 ==>
        z = (mstore (w2n dst) (slot_copy_word (if p.ptr_location=LocStorage then SLOAD else TLOAD) allocated a)
          (update_var (STRING #"%" (toString mid.cs_next_var))
            (slot_copy_word (if p.ptr_location=LocStorage then SLOAD else TLOAD) allocated a) allocated)
              with vs_inst_idx := LENGTH sc.cs_current_insts) /\
        tnf.t_mem = (tn0.t_mem DIFF {j | w2n dst <= j /\ j < w2n dst+32}) UNION
          {w2n dst+b | b IN key_taint (if p.ptr_location=LocStorage then tn0.t_stor else tn0.t_trans) a} /\
        tnf.t_stor = tn0.t_stor /\ tnf.t_trans = tn0.t_trans /\ tnf.t_imm = tn0.t_imm /\
        (!x. x <> STRING #"%" (toString mid.cs_next_var) ==>
           FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tnf (Var x) = op_taint tn0 (Var x)))` by
    (Cases_on `n = 1` >- suspend "singleton" >> suspend "loop") >>
  suspend "join"
QED

Resume ctor_unwrap_slot_arrival_mods[singleton]:
  qpat_assum `n = 1` (fn nth =>
    qpat_assum `buf.buf_operand = Var root` (fn bth =>
      qpat_x_assum `if n = 1 then _ else _` (assume_tac o REWRITE_RULE[nth,bth]))) >>
  `32 <= nb /\ w2n dst + 32 <= allocated.vs_alloca_next` by fs[] >>
  Q.SUBGOAL_THEN
    `(if p.ptr_location = LocStorage then SLOAD else TLOAD) = SLOAD \/
     (if p.ptr_location = LocStorage then SLOAD else TLOAD) = TLOAD` assume_tac
  >- (Cases_on `p.ptr_location = LocStorage` >> simp[]) >>
  `ptr_covers G0 tn0 root allocated 32` by fs[] >>
  drule_all ctor_single_slot_band_mods >>
  disch_then (qspecl_then [`explicit`,`PG`,
    `<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>`]
    (qx_choosel_then [`Gf`,`tnf`,`z`] strip_assume_tac)) >>
  qexistsl_tac [`z`,`Gf`,`tnf`] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qpat_assum `n = 1` (fn th => simp[NoAsms,th])) >>
  disch_tac >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qpat_x_assum `tnf.t_mem = _` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
  Cases_on `p.ptr_location = LocStorage` >> simp[]
QED

Resume ctor_unwrap_slot_arrival_mods[loop]:
  qpat_assum `n <> 1` (fn nth =>
    qpat_assum `buf.buf_operand = Var root` (fn bth =>
      qpat_x_assum `if n = 1 then _ else _` (strip_assume_tac o REWRITE_RULE[nth,bth]))) >>
  drule_all compile_slot_to_memory_boundary >> strip_tac >>
  `compile_word_copy_loop p.ptr_operand (Var root) n p.ptr_location LocMemory F mid = (lab,sc)` by
    fs[compile_slot_to_memory_def] >>
  `?exitbb. lookup_block sc.cs_current_bb func.fn_blocks = SOME exitbb /\
     phi_prefix_length exitbb.bb_instructions = 0` by fs[fn_has_code_def] >>
  `lookup_var root allocated = SOME (n2w (w2n dst))` by simp[] >>
  drule_all ctor_slot_loop_origin_band >>
  disch_then (qspecl_then [`explicit`,`PG`,
    `<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>`]
    (qx_choosel_then [`z`,`Gf`,`tnf`,`cv`,`ds`] strip_assume_tac)) >>
  `copy_static z = copy_static allocated` by
    fs[toplevel_copy_inv_def,storage_copy_inv_def,copy_prefix_def,storage_copy_frame_def] >>
  drule copy_static_fields >> strip_tac >>
  `alloca_history func z` by
    (irule alloca_history_jump >> conj_tac >- simp[] >>
     qexists_tac `allocated` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`z`,`Gf`,`tnf`] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qpat_assum `sc.cs_next_id = _` (fn th => simp[NoAsms,th]))
  >- (strip_tac >> qexistsl_tac [`cv`,`ds`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `n <> 1` (fn th => simp[NoAsms,th])
QED

Resume ctor_unwrap_slot_arrival_mods[join]:
  qpat_assum `gas_origin_ptr_path _ (s,G,tn) _ _`
    (mp_then Any (assume_tac o SRULE []) gas_origin_ptr_path_append) >>
  `gas_origin_ptr_path (<| d_stor := K (K {}); d_trans := K (K {});
      d_imm := K {}; d_ret := K {} |>,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK z,Gf,tnf)` by
    (qpat_assum `!right r G' tn'. gas_origin_ptr_path _ _ right _ ==> _` irule >>
     qpat_assum `gas_origin_ptr_path _ (allocated,G0,tn0) [] _` mp_tac >>
     qpat_assum `allocated = _` (fn ath =>
       qpat_assum `G0 = _` (fn gth =>
         qpat_assum `tn0 = _` (fn tth => simp[NoAsms,ath,gth,tth])))) >>
  `nb = type_memory_bytes cenv (post_value_type cenv e) /\ n = type_slot_size rty` by
    simp[Abbr `nb`,Abbr `n`] >>
  `~is_word_type (post_value_type cenv e)` by metis_tac[] >>
  mp_tac ctor_unwrap_slot_endpoint_post_mods >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qexistsl_tac [`v`,`z`,`Gf`,`tnf`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (irule RTC_TRANS >> qexists_tac `allocated` >> conj_tac
      >- (irule RTC_MONOTONE >> goal_assum (drule_at Any) >> simp[] >>
          metis_tac[LESS_LESS_EQ_TRANS]) >>
      irule RTC_MONOTONE >> goal_assum (drule_at Any) >> simp[] >>
      metis_tac[LESS_EQ_TRANS]) >>
  qpat_assum `z.vs_alloca_next = allocated.vs_alloca_next` SUBST1_TAC >>
  TRY (first_assum ACCEPT_TAC) >> irule LESS_EQ_TRANS >>
  qexists_tac `s.vs_alloca_next` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise ctor_unwrap_slot_arrival_mods
