(* unwrap_value's storage and transient aggregates on one joint path: a
   fresh buffer, then one load and store or the word-copy loop. *)
Theory bodyFullUnwrapSlot
Ancestors
  exprPtrUnwrapMarked exprSimMemUnwrap fragGasOriginPtr fragGasSeqPtr
  bodyPtrEnvBuiltinsEdges bodyPtrDefs loweringPosts exprSimMemDefs
  exprLowering compileEnv context
  bodyFullUnwrapSlotOrigin bodyFullUnwrapSlotEndpoint bodyFullUnwrapSlotPost
  bodyFullUnwrapRun fragGasOriginPtrDead exprLoweringProps localPtrsProps
  exprSimProps loweringStateRelDefs ptrDiscipline finite_map pred_set
  vyperStorageFootprint exprSimFieldLayout valueEncodingProps words
  exprPtrUnwrapStorage exprSimMemorySource freshWrites
  bodyFullUnwrapSlotFrame exprPtrUnwrapAllocSemantic exprSimCopy
  exprSimPtrTopLevelStorageCopy exprSimStorageCopy venomState venomExecSemantics
  exprSimAbiEncodeMemoryLength arithmetic slotCopyExecution emitHelper
  assignTuplePtrAlloc bodyPtrBytestringBuiltinsAllocation bodyPtrMakeArrayExternalCaller

(* A storage or transient aggregate is copied into a fresh buffer. *)
Theorem unwrap_slot_copy_origin_ptr:
  vv = LocatedValue t p /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  ~is_word_type t /\
  compile_expr cenv ty e sa = (vv,sm) /\
  (is_word_type (post_value_type cenv e) ==> is_word_type (expr_type e)) /\
  sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
  unwrap_value cenv vv sb = (op,sc) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
    ~is_word_type (post_value_type cenv e) ==>
    type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
    type_memory_size rt < 2**64) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post H ctx func cenv cx e es sa sm s0 ee tv vv s /\
     ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
  vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
  (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type cenv e) ==>
    ptr_buf_ok cenv e op0 G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv e p.ptr_operand G s) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?val. read_result cx tv ee = (INL val, ee) /\
         !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                eval_operand (vv_operand vv) s = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
                       val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?v z G' tn'.
    read_result cx tv ee = (INL v, ee) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
         (s, G, tn) [] (OK z, G', tn') /\
       expr_post H ctx func cenv cx e es sa sc s0 ee v op z /\
       ghost_inv_at (DF H) lo d cenv cx ee G' tn' z) /\
    (~is_word_type (post_value_type cenv e) ==>
     vv_at cenv cx (post_value_type cenv e) sa sc ee tv
       (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z) /\
    expr_store_bound cx (expr_type e) v op z /\
    z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
    s0.vs_alloca_next <= z.vs_alloca_next /\
    ptr_val_ok cx (post_value_type cenv e) v op G' tn' z /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G' z) /\
    (~is_word_type (post_value_type cenv e) ==>
     !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
            eval_operand op z = SOME w ==>
            type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    ghost_kept_at lo cenv es sa Gi ti s0 G' tn' /\
    (!x. not_fresh_at sb x ==>
         lookup_var x z = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)) /\
    wb_frame cenv ee ee sb s z /\
    ghost_kept_at lo cenv ee sb G tn s G' tn'
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac strip_assume_tac)) >>
  qpat_x_assum `vv = _` SUBST_ALL_TAC >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
     ee.storage_trace` by fs[storage_trace_domain_def] >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `vv_post H0 ctx func cenv cx e es sa sm s0 ee tv (LocatedValue t p) s /\
   ghost_inv_at (DF H0) lo d cenv cx ee G tn s` by
    (first_x_assum drule >> simp[]) >>
  `t = post_value_type cenv e` by
    (drule vv_post_located_type >>
     qpat_assum `p.ptr_location = LocStorage \/ _` mp_tac >>
     Cases_on `p.ptr_location` >> gvs[]) >>
  `~is_word_type (post_value_type cenv e)` by metis_tac[] >>
  `type_memory_bytes cenv t = type_memory_size rty /\
   type_memory_size rty < 2**64` by metis_tac[] >>
  `compile_ensure_in_memory p.ptr_operand p.ptr_location
     (type_memory_bytes cenv t) ((type_memory_bytes cenv t+31) DIV 32)
     cenv.ce_is_ctor cenv.ce_imm_alloca sb = (op,sc)` by
    (qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
     qpat_assum `p.ptr_location = LocStorage \/ _` mp_tac >>
     Cases_on `p.ptr_location` >> gvs[unwrap_value_def]) >>
  `((type_memory_bytes cenv t+31) DIV 32) = type_slot_size rty /\
   32 * type_slot_size rty = type_memory_bytes cenv t` by
    simp[slot_count_of_memory_size, type_memory_size_slots] >>
  `type_memory_bytes cenv t < dimword (:256) /\ type_slot_size rty < 2**256` by
    (fs[dimword_def] >> decide_tac) >>
  qabbrev_tac `tr = (p.ptr_location = LocTransient)` >>
  `p.ptr_location = slot_loc tr` by
    (qpat_assum `p.ptr_location = LocStorage \/ _` mp_tac >>
     Cases_on `p.ptr_location` >> gvs[Abbr `tr`, slot_loc_def]) >>
  drule_all vv_post_storage_source >> strip_tac >>
  `stmt_state_rel H0 ctx func cenv cx ee s` by fs[vv_post_def] >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `op_taint tn p.ptr_operand = {}` by fs[ptr_vv_ok_def] >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sb x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists `sm` >>
     fs[vv_operand_def]) >>
  qunabbrev_tac `tr` >>
  `32 * ((type_memory_bytes cenv t+31) DIV 32) <= type_memory_bytes cenv t /\
   ((type_memory_bytes cenv t+31) DIV 32) < 2**256` by gvs[] >>
  drule_all unwrap_ensure_slot_origin_execution >>
  disch_then (qspecl_then [`explicit`, `PG`, `G`]
    (qx_choosel_then [`root`, `dstword`, `allocated`, `G0`, `tn0`, `Gf`, `tnf`,
       `z`, `mid`, `buf`, `u`] strip_assume_tac)) >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists `sm` >> simp[]) >>
  drule_all unwrap_alloc_semantic_frames >> strip_tac >>
  `copy_static z = copy_static allocated /\
   LENGTH allocated.vs_memory <= LENGTH z.vs_memory /\
   (!off len. off+len <= w2n dstword \/
     w2n dstword+type_memory_bytes cenv t <= off ==>
     mem_bytes_at off len z.vs_memory = mem_bytes_at off len allocated.vs_memory) /\
   (!x. not_fresh_at mid x ==>
     lookup_var x z = lookup_var x allocated /\ FLOOKUP Gf x = FLOOKUP G0 x /\
     op_taint tnf (Var x) = op_taint tn0 (Var x))` by
    (Cases_on `((type_memory_bytes cenv t+31) DIV 32) = 1`
     >- suspend "single_physical"
     >> suspend "loop_physical") >>
  suspend "finish"
QED

Resume unwrap_slot_copy_origin_ptr[loop_physical]:
  qpat_x_assum `(_ <> 1 ==> _)` (drule_then strip_assume_tac) >>
  gvs[toplevel_copy_inv_def, storage_copy_inv_def, copy_prefix_def,
      storage_copy_frame_def] >> metis_tac[]
QED
Resume unwrap_slot_copy_origin_ptr[single_physical]:
  `type_memory_bytes cenv t = 32` by decide_tac >>
  `!x. not_fresh_at mid x ==> x <> STRING #"%" (toString mid.cs_next_var)` by
    (rpt strip_tac >> gvs[not_fresh_at_def]) >>
  qpat_x_assum `(_ = 1 ==> _)` (drule_then strip_assume_tac) >>
  rpt conj_tac
  >- (qpat_x_assum `z = _` SUBST1_TAC >>
      simp[copy_static_def, mstore_def, write_memory_with_expansion_def, update_var_def])
  >- (qpat_x_assum `z = _` SUBST1_TAC >>
      simp[] >> irule LESS_EQ_TRANS >>
      qexists `LENGTH (update_var (STRING #"%" (toString mid.cs_next_var))
        (slot_copy_word (if p.ptr_location = LocStorage then SLOAD else TLOAD) allocated a)
        allocated).vs_memory` >>
      conj_tac >- simp[update_var_def] >> simp[abi_encode_mstore_memory_length])
  >- (rpt strip_tac >> qpat_x_assum `z = _` SUBST1_TAC >>
      simp_tac (srw_ss()) [] >>
      dep_rewrite.DEP_REWRITE_TAC [mstore_mem_bytes_at_disjoint] >>
      (conj_tac >- metis_tac[] >>
       simp[update_var_def]))
  >> rpt strip_tac >>
  qpat_x_assum `z = _` SUBST1_TAC >>
  simp[mstore_def, write_memory_with_expansion_def, update_var_def, lookup_var_def,
       FLOOKUP_UPDATE] >> metis_tac[]
QED
Resume unwrap_slot_copy_origin_ptr[finish]:
  `(!j. j < type_slot_size rty ==>
      mem_word_at (w2n dstword+32*j) z.vs_memory =
      slot_copy_word (if p.ptr_location=LocStorage then SLOAD else TLOAD)
        allocated (a+n2w j)) /\
   (!j k. j < type_slot_size rty /\ k < 32 /\
      w2n dstword+32*j+k IN tnf.t_mem ==>
      k IN key_taint (if p.ptr_location=LocStorage then tn0.t_stor else tn0.t_trans)
        (a+n2w j)) /\
   (!q. ~(w2n dstword <= q /\ q < w2n dstword+type_memory_bytes cenv t) /\
      q IN tnf.t_mem ==> q IN tn0.t_mem) /\
   tnf.t_stor = tn0.t_stor /\ tnf.t_trans = tn0.t_trans /\ tnf.t_imm = tn0.t_imm` by
    (Cases_on `((type_memory_bytes cenv t+31) DIV 32) = 1`
     >- suspend "single_content"
     >> suspend "loop_content") >>
  suspend "join"
QED
Resume unwrap_slot_copy_origin_ptr[loop_content]:
  qpat_x_assum `(_ <> 1 ==> _)` (drule_then strip_assume_tac) >>
  drule toplevel_copy_inv_content >>
  disch_then (strip_assume_tac o REWRITE_RULE [storage_copy_inv_def, copy_prefix_def]) >>
  rpt conj_tac
  >- (rpt strip_tac >>
      `mem_word_at (w2n dstword+32*j) z.vs_memory =
       copy_runtime_word p.ptr_location allocated (a+n2w j)` by metis_tac[] >>
      Cases_on `p.ptr_location=LocStorage` >>
      gvs[copy_runtime_word_def, slot_copy_word_def])
  >- suspend "loop_taint"
  >- suspend "loop_outside"
  >> fs[toplevel_copy_inv_def]
QED
Resume unwrap_slot_copy_origin_ptr[loop_taint]:
  rpt strip_tac >> drule toplevel_copy_inv_memory_taint >>
  simp[toplevel_copy_taint_bound_def, toplevel_copy_region_def,
       toplevel_copy_translated_taint_def, pred_setTheory.SUBSET_DEF] >>
  disch_then (qspec_then `w2n dstword+32*j+k` mp_tac) >>
  `w2n dstword <= w2n dstword+32*j+k /\
   w2n dstword+32*j+k < w2n dstword+32*((type_memory_bytes cenv t+31) DIV 32)` by
    (qpat_x_assum `_ DIV 32 = type_slot_size rty` (fn th => rewrite_tac[th]) >> decide_tac) >>
  simp[] >> strip_tac >>
  rename1 `(a+n2w i,r) IN toplevel_copy_source_taint loc ts` >>
  `i = j /\ r = k` by intLib.COOPER_TAC >>
  qpat_x_assum `(a+n2w i,r) IN _` mp_tac >>
  simp[key_taint_def, toplevel_copy_source_taint_def]
QED
Resume unwrap_slot_copy_origin_ptr[loop_outside]:
  rpt strip_tac >> drule toplevel_copy_inv_memory_taint >>
  simp[toplevel_copy_taint_bound_def, toplevel_copy_region_def,
       toplevel_copy_translated_taint_def, pred_setTheory.SUBSET_DEF] >>
  disch_then (qspec_then `q` mp_tac) >> simp[] >>
  strip_tac >> gvs[]
QED
Resume unwrap_slot_copy_origin_ptr[single_content]:
  `type_slot_size rty = 1 /\ type_memory_bytes cenv t = 32` by decide_tac >>
  qpat_x_assum `(_ = 1 ==> _)` (drule_then strip_assume_tac) >>
  rpt conj_tac
  >- (rpt strip_tac >> `j = 0` by decide_tac >>
      qpat_x_assum `z = _` SUBST1_TAC >>
      simp_tac (srw_ss()) [mstore_mem_word_at_same] >>
      simp[] >> simp[mstore_mem_word_at_same, WORD_ADD_0])
  >- suspend "single_taint"
  >- suspend "single_outside"
  >> asm_rewrite_tac[]
QED
Resume unwrap_slot_copy_origin_ptr[single_taint]:
  rpt strip_tac >> `j = 0` by decide_tac >>
  qpat_x_assum `tnf.t_mem = _` (fn th => fs[th]) >>
  gvs[WORD_ADD_0, slot_loc_def]
QED
Resume unwrap_slot_copy_origin_ptr[single_outside]:
  rpt strip_tac >>
  qpat_x_assum `tnf.t_mem = _` (fn th => fs[th]) >>
  gvs[key_taint_def] >> decide_tac
QED
Resume unwrap_slot_copy_origin_ptr[join]:
  `allocated.vs_accounts = s.vs_accounts /\
   allocated.vs_transient = s.vs_transient /\
   allocated.vs_call_ctx = s.vs_call_ctx /\
   tn0.t_stor = tn.t_stor /\ tn0.t_trans = tn.t_trans /\
   tn0.t_imm = tn.t_imm` by
    simp[bufferAllocationExecutionTheory.buffer_allocation_fields_frame, update_var_def,
         storageNormalizationOwnershipPtrTheory.normalization_alloca_key_taints] >>
  `!mem. mem_agree_outside tnf.t_mem z.vs_memory mem ==>
     val_in_memory rty v (w2n dstword) mem` by
    (`?v'. read_result cx tv ee = (INL v',ee) /\
       !mem. mem_agree_outside tnf.t_mem z.vs_memory mem ==>
         val_in_memory rty v' (w2n dstword) mem` by
      (irule exprPtrUnwrapStoragePostTheory.unwrap_storage_copied_robust >>
       goal_assum (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >>
       qexistsl [`p.ptr_location = LocTransient`, `a`] >> simp[] >>
       conj_tac
       >- (rpt strip_tac >>
           qpat_x_assum `!j k. _ ==> k IN _` drule >> simp[] >>
           qpat_assum `p.ptr_location = LocStorage \/ _` mp_tac >>
           Cases_on `p.ptr_location` >> gvs[slot_loc_def]) >>
       conj_tac
       >- (rpt strip_tac >>
           qpat_assum `p.ptr_location = LocStorage \/ _` mp_tac >>
           Cases_on `p.ptr_location` >>
           gvs[slot_copy_word_def, sload_def, tload_def,
               contract_storage_def, contract_transient_def]) >>
       gvs[storage_holds_def, vyperStateTheory.read_result_def, vyperStateTheory.return_def]) >>
     gvs[]) >>
  `ptr_covers G0 tn0 root allocated (type_memory_bytes cenv t)` by
    (drule_all exprPtrUnwrapAllocationFrameTheory.unwrap_alloc_output_coverage >>
     simp[]) >>
  `not_fresh_at mid root` by
    (qpat_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     qpat_assum `buf.buf_operand = Var root` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def] >>
     rpt strip_tac >> gvs[not_fresh_at_def]) >>
  `ptr_covers Gf tnf root z (type_memory_bytes cenv t)` by
    (fs[ptr_covers_def] >> metis_tac[]) >>
  `lookup_var root z = SOME dstword /\ eval_operand op z = SOME dstword` by
    (`lookup_var root allocated = SOME dstword` by
       (qpat_x_assum `allocated = _` SUBST1_TAC >>
        qpat_x_assum `u = _` SUBST1_TAC >> simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
     metis_tac[eval_operand_def]) >>
  `w2n dstword + type_memory_bytes cenv t < dimword (:256)` by
    (qpat_x_assum `stmt_state_rel _ _ _ _ _ _ u` kall_tac >>
     drule_all exprPtrUnwrapAllocSeparationTheory.unwrap_alloc_site_bound >>
     qpat_x_assum `dstword = _` SUBST1_TAC >>
     strip_tac >> `buffer_allocation_base s sb.cs_next_id < dimword (:256)` by decide_tac >>
     simp[w2n_n2w]) >>
  `sb.cs_next_var <= mid.cs_next_var /\ sb.cs_next_id < mid.cs_next_id` by
    (qpat_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def] >> rpt strip_tac >> gvs[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     expr_post H ctx func cenv cx e es sa sc s0 ee v op z` by
    suspend "semantic" >>
  suspend "final_join"
QED
Resume unwrap_slot_copy_origin_ptr[semantic]:
  rpt strip_tac >>
  `vv_post H ctx func cenv cx e es sa sm s0 ee tv (LocatedValue t p) s` by metis_tac[] >>
  `vv_post H ctx func cenv cx e es sa sm s0 ee (Value v) (LocatedValue t p) s` by
    metis_tac[exprSimUnwrapPropsTheory.vv_post_read_result] >>
  `vv_post H ctx func cenv cx e es sa sb s0 ee (Value v) (LocatedValue t p) s` by
    (qpat_assum `vv_post H _ _ _ _ _ _ _ sm _ _ (Value v) _ _` mp_tac >>
     qpat_assum `p.ptr_location = LocStorage \/ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `p.ptr_location` >> simp[vv_post_def, vv_at_def, vv_own_def] >> metis_tac[]) >>
  `stmt_state_rel H ctx func cenv cx ee s` by fs[vv_post_def] >>
  qpat_x_assum `stmt_state_rel H0 _ _ _ _ _ u` kall_tac >>
  drule_all unwrap_alloc_semantic_frames >> strip_tac >>
  `copy_static allocated = copy_static u /\ allocated.vs_memory = u.vs_memory /\
   (!x. lookup_var x allocated = lookup_var x u)` by
    simp[copy_static_def, lookup_var_def, update_var_def,
         bufferAllocationExecutionTheory.buffer_allocation_fields_frame] >>
  qpat_x_assum `allocated = _` kall_tac >>
  qpat_x_assum `u = _` kall_tac >>
  qpat_x_assum `dstword = _` kall_tac >>
  qpat_assum `vv_post H _ _ _ _ _ _ _ sb _ _ (Value v) _ _`
    (mp_then Any mp_tac copy_buffer_post_transport_physical) >>
  disch_then irule >>
  simp[] >> conj_tac
  >- (qpat_assum `compile_ensure_in_memory _ _ _ _ _ _ _ = _` mp_tac >>
      qpat_assum `p.ptr_location = LocStorage \/ _` mp_tac >>
      qpat_assum `compile_alloc_buffer _ _ = _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      Cases_on `p.ptr_location` >>
      simp[compile_ensure_in_memory_def, comp_bind_def, comp_ignore_bind_def,
           comp_return_def] >> rpt strip_tac >> gvs[] >>
      Cases_on `(type_memory_bytes cenv t + 31) DIV 32 = 1` >>
      gvs[compile_storage_to_memory_def, compile_transient_to_memory_def,
          GSYM compile_slot_to_memory_def, copyExecutionTheory.compile_slot_to_memory_shape,
          copyExecutionTheory.slot_copy_final_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
          emit_op_def, emit_void_def, emit_def, fresh_var_def, fresh_id_def,
          compile_alloc_buffer_def] >> pairarg_tac >> gvs[]) >>
  conj_tac
  >- (qexists `mk_inst sb.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv t))] [root]` >>
      simp[GSYM venomInstTheory.mk_inst_def] >>
      drule exprPtrUnwrapAllocationTheory.unwrap_alloc_generated_code >> strip_tac >>
      `root = STRING #"%" (toString sb.cs_next_var)` by fs[] >>
      simp[venomInstTheory.mk_inst_def] >>
      drule_all exprSimAllocTheory.buffer_alloc_code >>
      simp[venomInstTheory.mk_inst_def]) >>
  qexistsl [`mid`, `type_memory_bytes cenv t`, `u`] >>
  gvs[] >>
  `val_wf rty v` by metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
  simp[exprSimPropsTheory.val_footprint_le] >>
  metis_tac[mem_agree_outside_def, ADD_COMM]
QED
Resume unwrap_slot_copy_origin_ptr[final_join]:
  `root = STRING #"%" (toString sb.cs_next_var)` by
    (drule exprPtrUnwrapAllocationTheory.unwrap_alloc_generated_code >> fs[]) >>
  `!x. not_fresh_at sb x ==> x <> root /\ not_fresh_at mid x` by
    (rpt strip_tac >> fs[not_fresh_at_def] >> decide_tac) >>
  `!x. not_fresh_at sb x ==>
     lookup_var x z = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
     op_taint tnf (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     `FLOOKUP G0 x = FLOOKUP G x /\ op_taint tn0 (Var x) = op_taint tn (Var x)` by
       (qpat_x_assum `G0 = _` SUBST1_TAC >> qpat_x_assum `tn0 = _` SUBST1_TAC >>
        irule bodyPtrBytestringBuiltinsAllocationTheory.alloca_old_register_ghost_frame >>
        metis_tac[]) >>
     `lookup_var x allocated = lookup_var x s` by
       (qpat_x_assum `allocated = _` SUBST1_TAC >>
        simp[lookup_var_def, update_var_def,
          bufferAllocationExecutionTheory.buffer_allocation_fields_frame, FLOOKUP_UPDATE] >>
        metis_tac[]) >>
     metis_tac[]) >>
  `MEM (mk_inst sb.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv t))] [root])
     (fn_insts func)` by
    (drule_all exprSimAllocTheory.buffer_alloc_code >> simp[]) >>
  drule_all assignTuplePtrAllocTheory.alloca_step_exterior_ghost_ptr >> strip_tac >>
  `!q. ~(w2n dstword <= q /\ q < w2n dstword + type_memory_bytes cenv t) /\
     q IN tnf.t_mem ==> q IN tn.t_mem` by metis_tac[] >>
  `buffer_allocation_base s sb.cs_next_id = w2n dstword` by
    (qpat_x_assum `stmt_state_rel _ _ _ _ _ _ u` kall_tac >>
     drule_all exprPtrUnwrapAllocSeparationTheory.unwrap_alloc_site_bound >>
     strip_tac >>
     `buffer_allocation_base s sb.cs_next_id < dimword (:256)` by decide_tac >>
     simp[w2n_n2w]) >>
  `!name b len. local_region cenv ee.scopes s name b len ==>
     w2n dstword + type_memory_bytes cenv t <= b \/ b+len <= w2n dstword` by
    (rpt strip_tac >>
     qpat_x_assum `stmt_state_rel _ _ _ _ _ _ u` kall_tac >>
     drule_all exprPtrUnwrapRetainedTheory.unwrap_alloc_local_separation >>
     (intLib.COOPER_TAC)) >>
  `!off len. off+len <= w2n dstword \/ w2n dstword+type_memory_bytes cenv t <= off ==>
     mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory` by
    (rpt strip_tac >>
     `allocated.vs_memory = s.vs_memory` by
       (qpat_x_assum `allocated = _` SUBST1_TAC >>
        qpat_x_assum `u = _` SUBST1_TAC >>
        simp[NoAsms, update_var_def, bufferAllocationExecutionTheory.buffer_allocation_fields_frame]) >>
     metis_tac[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     ghost_inv_at (DF H) lo d cenv cx ee Gf tnf z` by
    suspend "ghost_final" >>
  suspend "remaining"
QED
Resume unwrap_slot_copy_origin_ptr[ghost_final]:
  rpt strip_tac >>
  `ghost_inv_at (DF H) lo d cenv cx ee G tn s` by metis_tac[] >>
  `local_ptrs_rel func cenv ee.scopes s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `lo <= buffer_allocation_base s sb.cs_next_id` by
    (qpat_assum `allocas_from lo s` mp_tac >>
     qpat_assum `lo <= s.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[bufferAllocationExecutionTheory.buffer_allocation_base_def, allocas_from_def] >>
     Cases_on `FLOOKUP s.vs_allocas sb.cs_next_id` >> simp[] >>
     rename1 `SOME site` >> PairCases_on `site` >> simp[] >> metis_tac[]) >>
  drule copy_static_fields >> strip_tac >>
  irule bodyFullUnwrapSlotFrameTheory.unwrap_slot_copy_ghost_inv_at_mono >>
  conj_tac >- decide_tac >>
  conj_tac >-
    (qpat_assum `z.vs_allocas = allocated.vs_allocas` mp_tac >>
     qpat_assum `u = _` mp_tac >>
     qpat_assum `allocated = _` mp_tac >>
     qpat_assum `allocas_from lo s` mp_tac >>
     qpat_assum `lo <= buffer_allocation_base s sb.cs_next_id` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[copy_static_def, allocas_from_def, update_var_def,
       bufferAllocationExecutionTheory.buffer_allocation_fields_def, FLOOKUP_UPDATE] >>
     rpt strip_tac >>
     Cases_on `FLOOKUP s.vs_allocas sb.cs_next_id` >>
     gvs[FLOOKUP_UPDATE, bufferAllocationExecutionTheory.buffer_allocation_base_def,
       AllCaseEqs()] >> metis_tac[]) >>
  conj_tac >-
    (`stor_taint_ok_at (DF H) tn s` by
       (qpat_assum `ghost_inv_at (DF H) _ _ _ _ _ _ _ _` mp_tac >>
        simp[NoAsms, ghost_inv_at_def]) >>
     qpat_assum `stor_taint_ok_at (DF H) tn s` mp_tac >>
     `z.vs_immutables = allocated.vs_immutables` by
       (qpat_assum `copy_static z = _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[copy_static_def, venom_state_component_equality]) >>
     qpat_assum `z.vs_immutables = _` mp_tac >>
     qpat_assum `z.vs_accounts = _` mp_tac >>
     qpat_assum `z.vs_transient = _` mp_tac >>
     qpat_assum `z.vs_call_ctx = _` mp_tac >>
     qpat_assum `allocated = _` mp_tac >>
     qpat_assum `u = _` mp_tac >>
     qpat_assum `tnf.t_stor = _` mp_tac >>
     qpat_assum `tnf.t_trans = _` mp_tac >>
     qpat_assum `tnf.t_imm = _` mp_tac >>
     qpat_assum `tn0.t_stor = _` mp_tac >>
     qpat_assum `tn0.t_trans = _` mp_tac >>
     qpat_assum `tn0.t_imm = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[stor_taint_ok_at_def, update_var_def,
       bufferAllocationExecutionTheory.buffer_allocation_fields_frame] >>
     rpt strip_tac >>
     gvs[bufferAllocationExecutionTheory.buffer_allocation_fields_def, AllCaseEqs()] >>
     Cases_on `FLOOKUP s.vs_allocas sb.cs_next_id` >> gvs[]) >>
  qexistsl [`G`, `func`, `type_memory_bytes cenv t`, `s`, `sa`, `w2n dstword`, `tn`] >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >-
    (rpt strip_tac >>
     `not_fresh_at sb x` by (fs[not_fresh_at_def] >> decide_tac) >>
     metis_tac[]) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >-
    (qpat_assum `!q. ~(_ <= q /\ _) /\ _ ==> _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[NOT_LESS, NOT_LESS_EQUAL]) >>
  conj_tac >- metis_tac[] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Resume unwrap_slot_copy_origin_ptr[remaining]:
  `p.ptr_location <> LocMemory` by
    (qpat_assum `p.ptr_location = LocStorage \/ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `p.ptr_location` >> simp[]) >>
  `post_value_type cenv e = expr_type e /\
   lowered_value_type cenv e = expr_type e` by
    metis_tac[external_located_post_type, external_located_lowered_type] >>
  `val_wf rty v` by metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
  `stmt_state_rel H0 ctx func cenv cx ee z` by metis_tac[expr_post_def] >>
  `FLOOKUP z.vs_allocas sb.cs_next_id = SOME (w2n dstword,type_memory_bytes cenv t)` by
    (drule copy_static_fields >> strip_tac >>
     qpat_assum `FLOOKUP u.vs_allocas _ = _` mp_tac >>
     qpat_assum `allocated = _` mp_tac >>
     qpat_assum `z.vs_allocas = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  `w2n dstword + type_memory_bytes cenv t <= z.vs_alloca_next` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _ z` mp_tac >>
     qpat_assum `FLOOKUP z.vs_allocas _ = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.alloca_next_valid_def] >> metis_tac[]) >>
  `ptr_val_ok cx (post_value_type cenv e) v (Var root) Gf tnf z /\
   ptr_buf_ok cenv e (Var root) Gf z` by
    (irule exprPtrUnwrapStoragePostTheory.unwrap_storage_pointer_posts >>
     metis_tac[]) >>
  qexistsl [`v`, `z`, `Gf`, `tnf`] >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >-
    (gen_tac >> disch_tac >>
     conj_tac >-
       (irule fragGasOriginPtrDeadTheory.gas_origin_ptr_path_from_no_dead >>
        first_assum ACCEPT_TAC) >>
     metis_tac[]) >>
  conj_tac >- suspend "memory_vv" >>
  conj_tac >- suspend "store_bound" >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- decide_tac >>
  conj_tac >- suspend "ptr_value" >>
  conj_tac >- suspend "ptr_buffer" >>
  conj_tac >- suspend "lowered_bound" >>
  conj_tac >- suspend "kept_original" >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- suspend "writeback" >>
  suspend "kept_current"
QED
Resume unwrap_slot_copy_origin_ptr[memory_vv]:
  disch_tac >>
  `FLOOKUP z.vs_allocas sb.cs_next_id = SOME (w2n dstword,type_memory_bytes cenv t)` by
    (drule copy_static_fields >> strip_tac >>
     qpat_assum `FLOOKUP u.vs_allocas _ = _` mp_tac >>
     qpat_assum `allocated = _` mp_tac >>
     qpat_assum `z.vs_allocas = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  `sb.cs_next_id < sc.cs_next_id` by
    (qpat_assum `compile_ensure_in_memory _ _ _ _ _ _ _ = _` mp_tac >>
     qpat_assum `p.ptr_location = LocStorage \/ _` mp_tac >>
     qpat_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `p.ptr_location` >>
     simp[compile_ensure_in_memory_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def] >> rpt strip_tac >> gvs[] >>
     Cases_on `(type_memory_bytes cenv t + 31) DIV 32 = 1` >>
     gvs[compile_storage_to_memory_def, compile_transient_to_memory_def,
       GSYM compile_slot_to_memory_def, copyExecutionTheory.compile_slot_to_memory_shape,
       copyExecutionTheory.slot_copy_final_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, emit_void_def, emit_def, fresh_var_def, fresh_id_def,
       compile_alloc_buffer_def] >> pairarg_tac >> gvs[]) >>
  `!name b len. local_region cenv ee.scopes z name b len ==>
     w2n dstword + type_memory_bytes cenv t <= b \/ b+len <= w2n dstword` by
    (rpt strip_tac >>
     `local_region cenv ee.scopes s name b len` by
       (irule (iffLR (SPEC_ALL exprSimCopyTheory.copy_buffer_local_region_frame)) >>
        qexistsl [`sb`, `z`] >> metis_tac[]) >> metis_tac[]) >>
  `val_wf rty v` by metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
  `val_footprint rty v <= type_memory_bytes cenv t` by
    metis_tac[exprSimPropsTheory.val_footprint_le] >>
  qpat_assum `read_result _ _ _ = _` mp_tac >>
  qpat_assum `evaluate_type _ _ = SOME rty` mp_tac >>
  qpat_assum `FLOOKUP z.vs_allocas _ = _` mp_tac >>
  qpat_assum `!name b len. local_region _ _ z _ _ _ ==> _` mp_tac >>
  qpat_assum `eval_operand op z = _` mp_tac >>
  qpat_assum `val_wf rty v` mp_tac >>
  qpat_assum `val_footprint rty v <= _` mp_tac >>
  qpat_assum `sa.cs_next_id <= sm.cs_next_id` mp_tac >>
  qpat_assum `sm.cs_next_id <= sb.cs_next_id` mp_tac >>
  qpat_assum `sb.cs_next_id < sc.cs_next_id` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp[vv_at_def, mk_ptr_def] >> rpt strip_tac >>
  disj1_tac >>
  qexistsl [`sb.cs_next_id`, `w2n dstword`, `type_memory_bytes cenv t`] >>
  simp[] >> metis_tac[]

QED
Resume unwrap_slot_copy_origin_ptr[store_bound]:
  `val_store_size rty v <= type_memory_bytes cenv t` by
    metis_tac[exprSimPropsTheory.val_store_size_le] >>
  qpat_assum `post_value_type cenv e = expr_type e` mp_tac >>
  qpat_assum `evaluate_type _ _ = SOME rty` mp_tac >>
  qpat_assum `eval_operand op z = SOME dstword` mp_tac >>
  qpat_assum `val_store_size rty v <= _` mp_tac >>
  qpat_assum `w2n dstword + type_memory_bytes cenv t <= z.vs_alloca_next` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp[expr_store_bound_def] >> rpt strip_tac >> gvs[] >> decide_tac
QED
Resume unwrap_slot_copy_origin_ptr[ptr_value]:
  metis_tac[]
QED
Resume unwrap_slot_copy_origin_ptr[ptr_buffer]:
  metis_tac[]
QED
Resume unwrap_slot_copy_origin_ptr[lowered_bound]:
  qpat_assum `lowered_value_type cenv e = expr_type e` mp_tac >>
  qpat_assum `post_value_type cenv e = expr_type e` mp_tac >>
  qpat_assum `evaluate_type _ _ = SOME rty` mp_tac >>
  qpat_assum `eval_operand op z = SOME dstword` mp_tac >>
  qpat_assum `type_memory_bytes cenv t = type_memory_size rty` mp_tac >>
  qpat_assum `t = post_value_type cenv e` mp_tac >>
  qpat_assum `w2n dstword + type_memory_bytes cenv t <= z.vs_alloca_next` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> gvs[]
QED
Resume unwrap_slot_copy_origin_ptr[kept_original]:
  `vv_post H0 ctx func cenv cx e es sa sb s0 ee tv (LocatedValue t p) s` by
    (qpat_assum `vv_post H0 _ _ _ _ _ _ _ sm _ _ _ _ _` mp_tac >>
     qpat_assum `p.ptr_location = LocStorage \/ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `p.ptr_location` >>
     simp[vv_post_def, vv_at_def, vv_own_def] >> metis_tac[]) >>
  `sa.cs_next_id <= sb.cs_next_id` by decide_tac >>
  `!aid off len. FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id ==>
     w2n dstword + type_memory_bytes cenv t <= off \/ off+len <= w2n dstword` by
    (rpt strip_tac >> drule_all exprPtrUnwrapAllocSeparationTheory.unwrap_alloc_old_entry_separation >> decide_tac) >>
  `!name off len. local_region cenv es.scopes s0 name off len ==>
     w2n dstword + type_memory_bytes cenv t <= off \/ off+len <= w2n dstword` by
    (rpt strip_tac >> drule_all exprPtrUnwrapRetainedTheory.unwrap_alloc_entry_local_separation >> decide_tac) >>
  `lo <= buffer_allocation_base s sb.cs_next_id` by
    (qpat_assum `allocas_from lo s` mp_tac >>
     qpat_assum `lo <= s.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[bufferAllocationExecutionTheory.buffer_allocation_base_def, allocas_from_def] >>
     Cases_on `FLOOKUP s.vs_allocas sb.cs_next_id` >> simp[] >>
     rename1 `SOME site` >> PairCases_on `site` >> simp[] >> metis_tac[]) >>
  irule unwrap_slot_copy_ghost_kept_at >> qexistsl [`G`, `tn`] >>
  rpt conj_tac
  >- (rpt strip_tac >>
      `~(w2n dstword <= i /\ i < w2n dstword+type_memory_bytes cenv t)` by
        (first_x_assum drule >> decide_tac) >> metis_tac[])
  >- (rpt strip_tac >>
      `not_fresh_at sb x` by (fs[not_fresh_at_def] >> decide_tac) >> metis_tac[])
  >- (rpt strip_tac >>
   `~(w2n dstword <= i /\ i < w2n dstword+type_memory_bytes cenv t)` by
     (qpat_x_assum `!aid off len. _` drule >> strip_tac >> decide_tac) >>
   metis_tac[])
  >- (rpt strip_tac >>
      `lo <= w2n dstword` by metis_tac[] >>
      `~(w2n dstword <= i /\ i < w2n dstword+type_memory_bytes cenv t)` by decide_tac >>
      metis_tac[]) >>
  metis_tac[]
QED
Resume unwrap_slot_copy_origin_ptr[writeback]:
  drule copy_static_fields >> strip_tac >>
  irule unwrap_slot_copy_wb_frame >>
  conj_tac >- metis_tac[] >>
  conj_tac >-
    (qexistsl [`type_memory_bytes cenv t`, `w2n dstword`] >>
     rpt conj_tac >- metis_tac[]
     >- (rpt strip_tac >>
         `alloca_inv s` by fs[stmt_state_rel_def] >>
         `sb.cs_next_id <> aid` by decide_tac >>
         `!offset stored. FLOOKUP s.vs_allocas sb.cs_next_id = SOME (offset,stored) ==>
            stored = type_memory_bytes cenv t` by
           (rpt strip_tac >>
            qpat_x_assum `stmt_state_rel _ _ _ _ _ _ u` kall_tac >>
            qpat_x_assum `stmt_state_rel _ _ _ _ _ _ z` kall_tac >>
            drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
            drule_all allocationPtrTheory.stmt_state_rel_alloca_site_bound >> simp[]) >>
         drule_all bufferAllocationExecutionTheory.buffer_allocation_disjoint >> decide_tac) >>
     metis_tac[]) >>
  (rpt strip_tac >>
      qpat_assum `z.vs_allocas = allocated.vs_allocas` mp_tac >>
      qpat_assum `allocated = _` mp_tac >> qpat_assum `u = _` mp_tac >>
      qpat_assum `FLOOKUP s.vs_allocas aid = _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
      gvs[update_var_def, bufferAllocationExecutionTheory.buffer_allocation_fields_def] >>
      Cases_on `FLOOKUP s.vs_allocas sb.cs_next_id` >> gvs[FLOOKUP_UPDATE] >>
      Cases_on `sb.cs_next_id = aid` >> gvs[])
QED
Resume unwrap_slot_copy_origin_ptr[kept_current]:
  `lo <= w2n dstword` by
    (qpat_assum `allocas_from lo s` mp_tac >>
     qpat_assum `lo <= s.vs_alloca_next` mp_tac >>
     qpat_assum `buffer_allocation_base s sb.cs_next_id = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[bufferAllocationExecutionTheory.buffer_allocation_base_def, allocas_from_def] >>
     Cases_on `FLOOKUP s.vs_allocas sb.cs_next_id` >> simp[] >>
     rename1 `SOME site` >> PairCases_on `site` >> simp[] >> metis_tac[]) >>
  pure_rewrite_tac[ghost_kept_at_def, ghost_kept_def] >> rpt conj_tac
  >- metis_tac[]
  >- (rpt strip_tac >>
      `alloca_inv s` by fs[stmt_state_rel_def] >>
      `sb.cs_next_id <> aid` by decide_tac >>
      `!offset stored. FLOOKUP s.vs_allocas sb.cs_next_id = SOME (offset,stored) ==>
         stored = type_memory_bytes cenv t` by
        (rpt strip_tac >>
         qpat_x_assum `stmt_state_rel _ _ _ _ _ _ u` kall_tac >>
         qpat_x_assum `stmt_state_rel _ _ _ _ _ _ z` kall_tac >>
         drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
         drule_all allocationPtrTheory.stmt_state_rel_alloca_site_bound >> simp[]) >>
      `off+sz <= w2n dstword \/ w2n dstword+type_memory_bytes cenv t <= off` by
        (drule_all bufferAllocationExecutionTheory.buffer_allocation_disjoint >> decide_tac) >>
      `~(w2n dstword <= i /\ i < w2n dstword+type_memory_bytes cenv t)` by decide_tac >>
      metis_tac[])
  >- (rpt strip_tac >>
      `~(w2n dstword <= i /\ i < w2n dstword+type_memory_bytes cenv t)` by
        (qpat_x_assum `!name b len. local_region cenv ee.scopes s name b len ==> _` drule >>
         decide_tac) >> metis_tac[]) >>
  rpt strip_tac >>
  `~(w2n dstword <= i /\ i < w2n dstword+type_memory_bytes cenv t)` by decide_tac >>
  metis_tac[]
QED
Finalise unwrap_slot_copy_origin_ptr
