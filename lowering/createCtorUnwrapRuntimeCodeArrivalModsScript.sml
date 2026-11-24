(* A runtime immutable copy reaches the semantic endpoint along its own instructions. *)
Theory createCtorUnwrapRuntimeCodeArrivalMods
Ancestors
  createCtorUnwrapRuntimeCodeArrival createExprSizeExitDefsMods
  createCtorStraightBand createCtorImmutableCopyBand exprSimAbiEncodeObliviousCode exprSimAbiGasBridge
  bodyFullUnwrapCodeRuntimeRun bodyFullUnwrapCodeRuntimeFrame
  exprPtrUnwrapCodeCopyShape exprPtrUnwrapCodeCopySemantic exprPtrUnwrapCode
  exprPtrUnwrapAllocation exprPtrUnwrapAllocSeparation exprPtrUnwrapAllocationFrame
  exprPtrCleanBufferPost exprSimCopy exprSimStorageCopy exprSimAlloc
  exprSimUnwrapProps
  fragGasOriginPtrDead bodyFieldMemoryProps loweringPosts loweringStateRelDefs
  bodyPtrDefs freshWrites context compileEnv exprLowering exprLoweringProps
  venomState venomInst venomExecSemantics instIdxIndep fragExec abiBufferAllocationCode bufferAllocationExecution
  ptrDiscipline finite_map relation words arithmetic list rich_list
  vyperStorageFootprint bodyFullHashKeccakFixed valueEncodingProps bodyImmutableUnwrapMemory
  exprPtrUnwrapStorageShape exprSimMemDefs allocaHistory
  bodyFullPostsMods bodyInvSplit bodyFullShadowBodyInv valueEncodingTyping
  exprPtrUnwrapAllocSemantic immutableCopyExecution exprSimProps
  bodyFullUnwrapSlotPost exprPtrCodeCopyPost valueEncodingDefs
  exprPtrUnwrapAllocEntry exprBopSimProps loweringHalt exprPtrUnwrapRetained

Theorem runtime_loccode_source_mods[local]:
  vv_post_mods H ctx func cenv cx e es sa sm s0 ee tv (LocatedValue t p) s /\
  p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty ==>
  t = post_value_type cenv e /\ ?v a.
    read_result cx tv ee = (INL v,ee) /\
    eval_operand p.ptr_operand s = SOME a /\
    val_wf rty v /\ val_in_memory rty v (w2n a) s.vs_data_section /\
    w2n a + type_memory_size rty <= LENGTH s.vs_data_section /\
    w2n a + type_memory_size rty < dimword(:256)
Proof
  strip_tac >>
  gvs[vv_post_mods_def, vv_holds_mods_def, immutable_holds_mods_def,
      immutable_frame_mods_def, immutables_rel_mods_def] >>
  first_x_assum drule >> simp[immutables_rel_def] >> disch_tac >>
  qpat_x_assum `immutable_holds _ _ _ _ _ _ _` mp_tac >>
  simp[immutable_holds_def] >> strip_tac >> gvs[sub_layout_def] >>
  first_x_assum drule_all >> strip_tac >>
  `off + k < dimword (:256)` by decide_tac >>
  simp[] >> rpt conj_tac >> TRY decide_tac >>
  metis_tac[value_has_type_val_wf, ADD_COMM]
QED

Theorem runtime_loccode_copy_contents[local]:
  val_wf rty v /\ val_in_memory rty v (w2n a) s.vs_data_section /\
  w2n a + type_memory_size rty < dimword(:256) /\
  w2n w + type_memory_size rty < dimword(:256) /\
  z.vs_memory = (immutable_transfers F F a w (type_slot_size rty) 0 s).vs_memory ==>
  val_in_memory rty v (w2n w) z.vs_memory
Proof
  strip_tac >> irule valueEncodingPropsTheory.val_in_memory_relocate >> simp[] >>
  qexistsl_tac [`s.vs_data_section`, `type_memory_size rty`, `w2n a`] >> simp[] >>
  Cases_on `type_slot_size rty = 0`
  >- gvs[type_memory_size_slots, mem_bytes_at_def] >>
  `immutable_transfers F F a w (type_slot_size rty) 0 s =
    write_memory_with_expansion (w2n w)
      (mem_bytes_at (w2n a) (type_memory_size rty) s.vs_data_section) s` by
    (qspecl_then [`type_slot_size rty`, `w2n a`, `w2n w`, `0`, `s`] mp_tac
      immutable_runtime_transfers_snapshot >>
     simp[mem_bytes_at_def, type_memory_size_slots] >> gvs[type_memory_size_slots]) >>
  qspec_then `w2n w` mp_tac write_memory_mem_bytes_at_same >>
  disch_then (qspecl_then
    [`mem_bytes_at (w2n a) (type_memory_size rty) s.vs_data_section`, `s`] mp_tac) >>
  simp[]
QED

(* Use the active-frame ghost transport at floor zero, then restore the
   linked immutable-prefix clause by the exterior memory and taint frames. *)

Theorem runtime_loccode_ghost_frame[local]:
  ghost_inv_at_mods D lo d cenv cx ee G tn s /\ local_ptrs_reserved cenv sb /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x) /\
  local_ptrs_rel func cenv ee.scopes s /\
  (!name b len. local_region cenv ee.scopes s name b len ==>
    start+nb <= b \/ b+len <= start) /\
  (!x. not_fresh_at sb x ==> lookup_var x q = lookup_var x s /\
    FLOOKUP HG x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  (!a k. a+k <= start \/ start+nb <= a ==>
    mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) /\
  (!j. j < start \/ start+nb <= j ==> (j IN tf.t_mem <=> j IN tn.t_mem)) /\
  lo <= start /\ stor_taint_ok_at D tf q /\ allocas_from lo q /\ lo <= q.vs_alloca_next ==>
  ghost_inv_at_mods D lo d cenv cx ee HG tf q
Proof
  strip_tac >>
  `ghost_inv_at D 0 d cenv cx ee G tn s` by
    (fs[ghost_inv_at_mods_def, ghost_inv_at_def, allocas_from_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ghost_inv_at D 0 d cenv cx ee HG tf q` by
    (irule unwrap_slot_copy_ghost_inv_at >> simp[allocas_from_def] >>
     qexistsl_tac [`G`, `func`, `nb`, `s`, `sb`, `start`, `tn`] >> gvs[] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `mem_bytes_at 0 lo q.vs_memory = mem_bytes_at 0 lo s.vs_memory` by simp[] >>
  fs[ghost_inv_at_def, ghost_inv_at_mods_def] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >> conj_tac
  >- (rpt strip_tac >> `i < start` by decide_tac >> metis_tac[]) >>
  rpt strip_tac >> `not_fresh_at sb x` by metis_tac[local_ptrs_reserved_imm_base] >>
  metis_tac[]
QED

Theorem ctor_unwrap_runtime_code_arrival_strong_mods:
  ~cenv.ce_is_ctor /\
  vv = LocatedValue t p /\ p.ptr_location = LocCode /\ ~is_word_type t /\
  compile_expr cenv ty e sa = (vv,sm) /\
  sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
  unwrap_value cenv vv sb = (op,sc) /\
  local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
  type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rty /\
  type_memory_size rty < 2**64 /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post_mods H ctx func cenv cx e es sa sm s0 ee tv vv s /\
     ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s) /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?v z G' tn'.
    read_result cx tv ee = (INL v, ee) /\
    RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
                    sb.cs_next_id <= i.inst_id /\ i.inst_id < sc.cs_next_id /\
                    i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v) s z /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
         (s, G, tn) [] (OK z, G', tn') /\
       expr_post_mods H ctx func cenv cx e es sa sc s0 ee v op z /\
       ghost_inv_at_mods (DF H) lo d cenv cx ee G' tn' z) /\
    expr_store_bound cx (post_value_type cenv e) v op z /\
    ~z.vs_halted /\ z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
    s0.vs_alloca_next <= z.vs_alloca_next /\
    ptr_val_ok cx (post_value_type cenv e) v op G' tn' z /\
    ptr_buf_ok cenv e op G' z /\
    (!rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
            eval_operand op z = SOME w ==>
            type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    ghost_kept_at lo cenv es sa Gi ti s0 G' tn' /\
    (!x. not_fresh_at sb x ==>
         lookup_var x z = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)) /\
    wb_frame cenv ee ee sb s z /\ ghost_kept_at lo cenv ee sb G tn s G' tn' /\
    pure_frame cenv func ee sb s z /\
    expr_val_at cenv cx (post_value_type cenv e) sb sc ee v op z /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
           (s,G,tn) [] (OK z,G',tn'))
Proof
  strip_tac >> gvs[] >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  drule_all runtime_loccode_source_mods >> strip_tac >> gvs[] >>
  `sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id` by decide_tac >>
  `local_ptrs_reserved cenv sb` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sb x` by
    (fs[vv_operand_def] >> metis_tac[not_fresh_at_mono]) >>
  `stmt_state_rel H0 ctx func cenv cx ee s` by fs[vv_post_mods_def] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s)` by
    metis_tac[stmt_state_rel_allocas_below_fmp] >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
       (qspec_then `H0` (drule_then strip_assume_tac)) >> fs[ghost_inv_at_mods_def]) >>
  `op_taint tn p.ptr_operand = {}` by fs[ptr_vv_ok_def,vv_operand_def] >>
  `compile_ensure_in_memory p.ptr_operand LocCode
    (type_memory_bytes cenv (post_value_type cenv e))
    ((type_memory_bytes cenv (post_value_type cenv e) + 31) DIV 32)
    F cenv.ce_imm_alloca sb = (op,sc)` by gvs[unwrap_value_def] >>
  drule_all ensure_runtime_code_layout >> strip_tac >>
  `(type_memory_size rty + 31) DIV 32 = type_slot_size rty` by
    simp[type_memory_size_slots,ADD_DIV_ADD_DIV] >>
  `compile_alloc_buffer (type_memory_size rty) sb = (buf,mid) /\
   compile_imm_copy_to_memory F cenv.ce_imm_alloca p.ptr_operand buf.buf_operand
     (type_slot_size rty) 0 mid = ((),sc)` by metis_tac[] >>
  `type_memory_size rty = 32 * type_slot_size rty` by simp[type_memory_size_slots] >>
  `w2n a + 32 * type_slot_size rty <= LENGTH s.vs_data_section /\
   w2n a + 32 * type_slot_size rty < dimword(:256)` by decide_tac >>
  `type_memory_size rty < dimword(:256)` by decide_tac >>
  drule_all runtime_code_copy_origin_execution >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`,
    `<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>`]
    strip_assume_tac) >>
  rename1 `copy_runtime_frame mid allocst sc z` >>
  rename1 `lookup_var root allocst = SOME dst` >>
  `allocst.vs_memory = s.vs_memory /\ allocst.vs_accounts = s.vs_accounts /\
   allocst.vs_transient = s.vs_transient /\ allocst.vs_call_ctx = s.vs_call_ctx /\
   allocst.vs_immutables = s.vs_immutables` by
    (drule unwrap_alloc_runtime_frame >> simp[] >> metis_tac[]) >>
  `buffer_allocation_base s sb.cs_next_id < dimword(:256)` by
    (drule_all unwrap_alloc_site_bound >> decide_tac) >>
  `lo <= w2n dst` by
    (simp[] >> Cases_on `FLOOKUP s.vs_allocas sb.cs_next_id` >>
     fs[buffer_allocation_base_def,allocas_from_def] >> PairCases_on `x` >> fs[] >> metis_tac[]) >>
  `MEM (mk_inst sb.cs_next_id ALLOCA [Lit (n2w (type_memory_size rty))] [root])
     (fn_insts func)` by
    (drule unwrap_alloc_generated_code >> strip_tac >> drule_all buffer_alloc_code >> gvs[]) >>
  `tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm` by
    fs[step_taint_def,mk_inst_def,adopt_reset_def,store_taint_def,imm_taint_def] >>
  `!i. i < buffer_allocation_base s sb.cs_next_id \/
       buffer_allocation_base s sb.cs_next_id + type_memory_size rty <= i ==>
       (i IN tm.t_mem <=> i IN tn.t_mem)` by
    (drule_all unwrap_alloc_taint_frame >> simp[] >> metis_tac[]) >>
  `tf.t_mem SUBSET tn.t_mem` by
    (fs[pred_setTheory.SUBSET_DEF] >> rpt strip_tac >>
     `w2n dst = buffer_allocation_base s sb.cs_next_id` by simp[] >>
     metis_tac[NOT_LESS_EQUAL]) >>
  `!off len. off+len <= w2n dst \/ w2n dst+type_memory_size rty <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory` by metis_tac[] >>
  `u = update_var root dst (buffer_allocation_fields s sb.cs_next_id (type_memory_size rty))` by simp[] >>
  drule_all runtime_code_copy_retained_frames_pure >> strip_tac >>
  drule_all immutable_copy_band >> disch_tac >>
  qabbrev_tac `q = z with vs_inst_idx := LENGTH sc.cs_current_insts` >>
  `lookup_var root z = SOME dst` by
    (fs[copy_runtime_frame_def,lookup_var_def] >> metis_tac[allocated_copy_operands_old]) >>
  `eval_operand (Var root) q = SOME dst` by fs[Abbr `q`,eval_operand_def,lookup_var_def] >>
  `ptr_covers HG tf root q (type_memory_size rty)` by
    (qpat_assum `ptr_covers HG tf root z _` mp_tac >>
     simp[Abbr `q`,ptr_covers_def,lookup_var_def]) >>
  `!i. w2n dst <= i /\ i < w2n dst + type_memory_size rty ==> i NOTIN tf.t_mem` by
    (fs[pred_setTheory.IN_DIFF,pred_setTheory.GSPECIFICATION] >> decide_tac) >>
  `lowered_value_type cenv e = expr_type e` by
    (drule compile_nonmemory_lowered_value_type >> simp[]) >>
  `post_value_type cenv e = expr_type e` by metis_tac[post_value_type_lowered] >>
  `type_memory_bytes cenv (lowered_value_type cenv e) <= type_memory_size rty` by fs[] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK q,HG,tf)` by
    (gen_tac >> irule gas_origin_ptr_path_from_no_dead >> first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK q,HG,tf)` by simp[] >>
  suspend "linked_posts"
QED

Resume ctor_unwrap_runtime_code_arrival_strong_mods[linked_posts]:
  markerLib.RESUME_TAC >>
  `!x. p.ptr_operand = Var x ==> x <> root` by
    metis_tac[unwrap_alloc_old_operand_distinct] >>
  `eval_operand p.ptr_operand allocst = SOME a` by
    (drule_all unwrap_alloc_old_operand_ghost >> simp[]) >>
  `copy_old_operand mid p.ptr_operand /\ copy_old_operand mid (Var root)` by
    (drule_all allocated_copy_operands_old >> simp[copy_old_operand_def]) >>
  `eval_operand (Var root) allocst = SOME dst` by simp[eval_operand_def] >>
  `compile_imm_copy_to_memory F cenv.ce_imm_alloca p.ptr_operand (Var root)
     (type_slot_size rty) 0 mid = ((),sc)` by metis_tac[] >>
  `z.vs_memory = (immutable_transfers F F a dst (type_slot_size rty) 0 allocst).vs_memory` by
    (drule_all code_copy_same_endpoint_memory >> simp[]) >>
  `copy_static z = copy_static allocst /\
    (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x allocst)` by
    fs[copy_runtime_frame_def] >>
  `z.vs_data_section = allocst.vs_data_section /\
    z.vs_accounts = allocst.vs_accounts /\ z.vs_transient = allocst.vs_transient /\
    z.vs_call_ctx = allocst.vs_call_ctx /\ z.vs_allocas = allocst.vs_allocas` by
    (drule copy_static_fields >> simp[]) >>
  `z.vs_immutables = allocst.vs_immutables` by
    (qpat_assum `copy_static z = copy_static allocst` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[copy_static_def, venom_state_component_equality]) >>
  `allocst.vs_data_section = s.vs_data_section` by
    (Cases_on `FLOOKUP s.vs_allocas sb.cs_next_id` >>
     simp[buffer_allocation_fields_def, update_var_def]) >>
  `w2n a + type_memory_size rty < dimword(:256)` by decide_tac >>
  `val_in_memory rty v (w2n dst) z.vs_memory` by
    (irule runtime_loccode_copy_contents >> simp[] >>
     qexistsl_tac [`a`,`allocst`] >> simp[]) >>
  `val_footprint rty v <= type_memory_size rty` by simp[val_footprint_le] >>
  `LENGTH allocst.vs_memory <= LENGTH z.vs_memory` by
    (drule_all runtime_code_copy_memory_frame >> simp[]) >>
  `!j. j < w2n dst \/ w2n dst+type_memory_size rty <= j ==>
     (j IN tf.t_mem <=> j IN tn.t_mem)` by
    (rpt strip_tac >>
     `w2n dst = buffer_allocation_base s sb.cs_next_id` by simp[] >>
     fs[pred_setTheory.IN_DIFF, pred_setTheory.GSPECIFICATION] >>
     metis_tac[NOT_LESS, NOT_LESS_EQUAL]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
      ghost_inv_at_mods (DF H) lo d cenv cx ee HG tf q` by
    suspend "linked_ghost" >>
  `ci_mono mid sc` by
    (qpat_assum `compile_imm_copy_to_memory F _ _ (Var root) _ _ mid = ((),sc)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[ci_mono_compile_imm_copy_to_memory, pairTheory.SND]) >>
  `sb.cs_next_id < sc.cs_next_id` by
    (drule compile_alloc_buffer_parts >> strip_tac >> fs[ci_mono_def] >> decide_tac) >>
  `FLOOKUP q.vs_allocas sb.cs_next_id = SOME (w2n dst,type_memory_size rty)` by
    (drule_all unwrap_alloc_semantic_frames >> strip_tac >>
     `q.vs_allocas = u.vs_allocas` by
       (qpat_assum `z.vs_allocas = allocst.vs_allocas` (fn th =>
          simp_tac (srw_ss()) [Abbr `q`, th]) >>
        qpat_assum `allocst = u with vs_inst_idx := _` (fn th =>
          simp_tac (srw_ss()) [th])) >>
     qpat_assum `q.vs_allocas = u.vs_allocas` (fn th => pure_rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `!name b len. local_region cenv ee.scopes q name b len ==>
     w2n dst + type_memory_size rty <= b \/ b+len <= w2n dst` by
    (rpt strip_tac >>
     `!x. not_fresh_at sb x ==> lookup_var x q = lookup_var x s` by
       (qpat_assum `!x. not_fresh_at sb x ==> lookup_var x z = _ /\ _` mp_tac >>
        UNABBREV_ALL_TAC >> POP_ASSUM_LIST (K ALL_TAC) >>
        simp[lookup_var_def]) >>
     `local_region cenv ee.scopes s name b len` by
       (qpat_assum `!x. not_fresh_at sb x ==> lookup_var x q = _` mp_tac >>
        qpat_assum `local_ptrs_reserved cenv sb` mp_tac >>
        qpat_assum `local_region cenv ee.scopes q name b len` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[copy_buffer_local_region_frame]) >>
     drule_all unwrap_alloc_local_separation >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
      expr_post_mods H ctx func cenv cx e es sa sc s0 ee v (Var root) q` by
    suspend "linked_expr_post" >>
  suspend "runtime_value"
QED

Resume ctor_unwrap_runtime_code_arrival_strong_mods[linked_ghost]:
  markerLib.RESUME_TAC >>
  rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
    (drule_then strip_assume_tac) >>
  `local_ptrs_rel func cenv ee.scopes s` by
    fs[vv_post_mods_def, stmt_state_rel_def, state_rel_def] >>
  `!name off len. local_region cenv ee.scopes s name off len ==>
    w2n dst+type_memory_size rty <= off \/ off+len <= w2n dst` by
    (rpt strip_tac >> drule_all unwrap_alloc_local_separation >> simp[]) >>
  `stor_taint_ok_at (DF H) tf q` by
    fs[Abbr `q`, ghost_inv_at_mods_def, stor_taint_ok_at_def] >>
  `allocas_from lo q /\ lo <= q.vs_alloca_next` by
    (conj_tac
     >- (qpat_assum `allocas_from lo z` mp_tac >>
         UNABBREV_ALL_TAC >> POP_ASSUM_LIST (K ALL_TAC) >> simp[allocas_from_def]) >>
     fs[Abbr `q`] >> decide_tac) >>
  irule runtime_loccode_ghost_frame >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`G`, `func`, `type_memory_size rty`, `s`, `sb`, `w2n dst`, `tn`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (rpt strip_tac >> qpat_assum `!x sz. cenv.ce_return_buf = _ ==> _` drule >>
      strip_tac >> drule_all not_fresh_at_mono >> simp[])
  >- (rpt strip_tac >> qpat_assum `!x sz. cenv.ce_return_pc = _ ==> _` drule >>
      strip_tac >> drule_all not_fresh_at_mono >> simp[])
  >- (qpat_assum `!x. not_fresh_at sb x ==> lookup_var x z = _ /\ _` mp_tac >>
      UNABBREV_ALL_TAC >> POP_ASSUM_LIST (K ALL_TAC) >> simp[lookup_var_def]) >>
  qpat_assum `!off len. _ ==> mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory`
    mp_tac >>
  UNABBREV_ALL_TAC >> POP_ASSUM_LIST (K ALL_TAC) >> simp[] >>
  strip_tac >> rpt gen_tac >> strip_tac >> first_x_assum irule >> decide_tac
QED

Resume ctor_unwrap_runtime_code_arrival_strong_mods[linked_expr_post]:
  markerLib.RESUME_TAC >>
  rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
    (drule_then strip_assume_tac) >>
  `stmt_state_rel H ctx func cenv cx ee s` by fs[vv_post_mods_def] >>
  drule_all unwrap_alloc_semantic_frames >> strip_tac >>
  `stmt_state_rel H ctx func cenv cx ee allocst` by
    (qpat_assum `allocst = u with vs_inst_idx := _`
      (fn th => pure_rewrite_tac[th, stmt_state_rel_inst_idx]) >> first_assum ACCEPT_TAC) >>
  `FLOOKUP allocst.vs_allocas sb.cs_next_id = SOME (w2n dst,type_memory_size rty)` by
    (qpat_assum `FLOOKUP u.vs_allocas sb.cs_next_id = SOME _` mp_tac >>
     qpat_assum `allocst = u with vs_inst_idx := _`
       (fn th => simp_tac (srw_ss()) [th])) >>
  `!name b len. local_region cenv ee.scopes allocst name b len ==>
     w2n dst + type_memory_size rty <= b \/ b+len <= w2n dst` by
    (qpat_assum `!name b len. local_region cenv ee.scopes u name b len ==> _` mp_tac >>
     qpat_assum `allocst = u with vs_inst_idx := _`
       (fn th => simp_tac (srw_ss()) [th, local_region_def, lookup_var_def, regions_disjoint_def])) >>
  `local_ptrs_reserved cenv mid` by metis_tac[local_ptrs_reserved_next_var] >>
  `stmt_state_rel H ctx func cenv cx ee z` by
    (irule copy_buffer_state_rel_frame >>
     qexistsl_tac [`w2n dst`,
      `mk_inst sb.cs_next_id ALLOCA [Lit (n2w (type_memory_size rty))] [root]`,
      `allocst`, `mid`, `type_memory_size rty`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     simp_tac (srw_ss()) [mk_inst_def]
     >- (rpt gen_tac >> strip_tac >>
         qpat_assum `!off len. _ ==> mem_bytes_at off len z.vs_memory = mem_bytes_at off len allocst.vs_memory`
           irule >> decide_tac) >>
     first_assum ACCEPT_TAC) >>
  `wb_frame cenv es ee sa s0 s` by
    (qpat_assum `vv_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ s`
       (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
     rewrite_tac[wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `wb_frame cenv es ee sa s0 q` by suspend "compose_wb" >>
  `(~expr_has_effect e ==> pure_frame cenv func es sa s0 q)` by
    (strip_tac >> irule pure_frame_trans >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`ee`,`sb`,`s`] >>
     qpat_assum `vv_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ s`
       (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
     qpat_assum `wb_frame cenv ee ee sb s q`
       (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE (first_x_assum irule >> first_assum ACCEPT_TAC))) >>
  simp[expr_post_mods_def] >> conj_tac
  >- (qpat_assum `wb_frame cenv es ee sa s0 q`
        (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
      qpat_assum `vv_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ s`
        (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
      irule copy_buffer_expr_post >>
      `(q:venom_state).vs_memory = z.vs_memory` by simp[Abbr `q`] >>
      `stmt_state_rel H ctx func cenv cx ee q` by
        (qpat_assum `Abbrev(q = _)` (fn th => pure_rewrite_tac[REWRITE_RULE [markerTheory.Abbrev_def] th, stmt_state_rel_inst_idx]) >>
         first_assum ACCEPT_TAC) >>
      `~is_word_type (expr_type e)` by
        (qpat_assum `~is_word_type (post_value_type cenv e)` mp_tac >>
         qpat_assum `post_value_type cenv e = expr_type e` (fn th => pure_rewrite_tac[th]) >>
         disch_then ACCEPT_TAC) >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qexistsl_tac [`sb.cs_next_id`, `type_memory_size rty`,`rty`,`dst`] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      (first_assum (fn th => pure_rewrite_tac[th] >> first_assum ACCEPT_TAC) ORELSE
       metis_tac[])) >>
  qpat_assum `vv_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ s`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  qpat_assum `immutable_frame_mods func cenv cx ee s` mp_tac >>
  `q.vs_data_section = s.vs_data_section` by
    (qpat_assum `Abbrev(q = _)` (fn th => simp_tac (srw_ss()) [REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
     metis_tac[]) >>
  qpat_assum `~cenv.ce_is_ctor` mp_tac >>
  qpat_assum `q.vs_data_section = s.vs_data_section` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp[immutable_frame_mods_def, immutables_rel_mods_def, immutables_rel_def,
       immutable_alloca_sep_mods_def, immutable_alloca_sep_def, immutable_decl_sep_def]
QED

Resume ctor_unwrap_runtime_code_arrival_strong_mods[compose_wb]:
  markerLib.RESUME_TAC >>
  qpat_assum `wb_frame cenv es ee sa s0 s` (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
  qpat_assum `wb_frame cenv ee ee sb s q` (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
  rewrite_tac[wb_frame_def] >> conj_tac
  >- (rpt strip_tac >> metis_tac[not_fresh_at_mono]) >>
  conj_tac >- metis_tac[] >>
  reverse conj_tac
  >- (irule locals_kept_trans >> qexistsl_tac [`ee`, `sa`, `s`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  `mem_bytes_at off sz s.vs_memory = mem_bytes_at off sz s0.vs_memory` by metis_tac[] >>
  `FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ aid < sb.cs_next_id` by
    (conj_tac >- metis_tac[] >> decide_tac) >>
  `regions_disjoint (w2n dst) (type_memory_size rty) off sz` by metis_tac[] >>
  fs[Abbr `q`, regions_disjoint_def] >> metis_tac[]
QED

Resume ctor_unwrap_runtime_code_arrival_strong_mods[runtime_value]:
  markerLib.RESUME_TAC >>
  `expr_post H0 ctx func cenv cx e es sa sc s0 ee v (Var root) q` by
    fs[expr_post_mods_def] >>
  `type_memory_size rty <= type_memory_size rty` by simp[] >>
  drule_all clean_buffer_pointer_posts >> strip_tac >>
  `expr_store_bound cx (post_value_type cenv e) v (Var root) q` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ q`
       (mp_then (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`) mp_tac
          expr_store_bound_capacity) >>
     simp[] >> disch_then irule >> rpt strip_tac >> gvs[Abbr `q`]) >>
  `expr_val_at cenv cx (post_value_type cenv e) sb sc ee v (Var root) q` by
    (simp[expr_val_at_def] >>
     disj1_tac >> qexistsl_tac [`sb.cs_next_id`, `w2n dst`, `type_memory_size rty`] >>
     simp[] >>
     qpat_assum `!n b len. local_region cenv ee.scopes q n b len ==> _` mp_tac >>
     simp[] >> strip_tac >> rpt gen_tac >> strip_tac >>
     first_x_assum drule >> decide_tac) >>
  qexistsl_tac [`q`,`HG`,`tf`] >>
  gvs[Abbr `q`,eval_operand_def,lookup_var_def] >> decide_tac
QED

Finalise ctor_unwrap_runtime_code_arrival_strong_mods

(* The ordinary interface forgets only the extra endpoint projections. *)
Theorem ctor_unwrap_runtime_code_arrival_mods:
  ~cenv.ce_is_ctor /\
  vv = LocatedValue t p /\ p.ptr_location = LocCode /\ ~is_word_type t /\
  compile_expr cenv ty e sa = (vv,sm) /\
  sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
  unwrap_value cenv vv sb = (op,sc) /\
  local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
  type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rty /\
  type_memory_size rty < 2**64 /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post_mods H ctx func cenv cx e es sa sm s0 ee tv vv s /\
     ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s) /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?v z G' tn'.
    read_result cx tv ee = (INL v, ee) /\
    RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
                    sb.cs_next_id <= i.inst_id /\ i.inst_id < sc.cs_next_id /\
                    i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v) s z /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
         (s, G, tn) [] (OK z, G', tn') /\
       expr_post_mods H ctx func cenv cx e es sa sc s0 ee v op z /\
       ghost_inv_at_mods (DF H) lo d cenv cx ee G' tn' z) /\
    expr_store_bound cx (post_value_type cenv e) v op z /\
    ~z.vs_halted /\ z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
    s0.vs_alloca_next <= z.vs_alloca_next /\
    ptr_val_ok cx (post_value_type cenv e) v op G' tn' z /\
    ptr_buf_ok cenv e op G' z /\
    (!rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
            eval_operand op z = SOME w ==>
            type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    ghost_kept_at lo cenv es sa Gi ti s0 G' tn' /\
    (!x. not_fresh_at sb x ==>
         lookup_var x z = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)) /\
    wb_frame cenv ee ee sb s z /\ ghost_kept_at lo cenv ee sb G tn s G' tn'
Proof
  strip_tac >> drule_all ctor_unwrap_runtime_code_arrival_strong_mods >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`v`,`z`,`G'`,`tn'`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
