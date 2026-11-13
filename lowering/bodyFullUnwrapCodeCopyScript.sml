(* unwrap_value's immutable aggregates on one joint path: a fresh buffer
   and the unrolled word copy from the data section, or in a constructor
   from the immutables region of memory. *)
Theory bodyFullUnwrapCodeCopy
Ancestors
  exprPtrUnwrapMarked exprSimMemUnwrap fragGasOriginPtr fragGasSeqPtr
  bodyPtrEnvBuiltinsEdges bodyPtrDefs loweringPosts exprSimMemDefs
  exprLowering compileEnv context bodyFullUnwrapRun exprPtrCtorCodeLoad
  exprSimCopy exprLoweringProps venomState venomInst entrySinkExtraction list
  vyperStorageFootprint exprPtrUnwrapCode exprPtrUnwrapCodeCopySemantic freshWrites
  exprSimUnwrapProps bodyFullUnwrapCodeRuntimeRun bodyFullUnwrapCodeRuntimeFrame
  bodyImmutableUnwrapMemory valueEncodingProps fragExec
  exprPtrUnwrapAllocationFrame exprPtrUnwrapAllocSeparation
  bufferAllocationExecution ptrDiscipline exprPtrUnwrapAllocation exprSimAlloc
  fragGasOriginPtrDead bodyFieldMemoryProps logTupleOwnershipPtr exprPtrUnwrapStorageShape
  exprPtrUnwrapCodeCopyShape exprPtrCleanBufferPost bodyFullUnwrapCodeCtorRun
  bodyFullUnwrapCodeCtorSemantic bodyFullUnwrapCodeCtorFrame loweringStateRelDefs


(* Runtime data-section branch. *)
Theorem unwrap_code_copy_runtime_origin_ptr:
  ~cenv.ce_is_ctor /\
  vv = LocatedValue t p /\ p.ptr_location = LocCode /\ ~is_word_type t /\
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
  strip_tac >> gvs[] >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
     ee.storage_trace` by fs[storage_trace_domain_def] >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `H0` mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  drule_all vv_post_code_source >> strip_tac >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post H ctx func cenv cx e es sa sb s0 ee tv (LocatedValue t p) s` by
    (rpt strip_tac >>
     qpat_x_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
       (drule_then strip_assume_tac) >>
     gvs[vv_post_def, vv_at_def, vv_own_def] >> metis_tac[]) >>
  `sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id` by
    decide_tac >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sb x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists `sm` >>
     fs[vv_operand_def]) >>
  `vv_post H0 ctx func cenv cx e es sa sb s0 ee (Value v) (LocatedValue t p) s` by
    (irule vv_post_read_result >> qexists `tv` >> simp[] >>
     first_x_assum irule >> simp[]) >>
  `type_memory_bytes cenv t = type_memory_size rty /\
   type_memory_size rty < 2**64` by fs[] >>
  qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  simp[unwrap_value_def, compile_ensure_in_memory_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  gvs[] >> rename1 `compile_alloc_buffer _ sb = (buf,mid)` >>
  `stmt_state_rel H0 ctx func cenv cx ee s` by fs[vv_post_def] >>
  `type_memory_size rty = 32 * type_slot_size rty` by
    simp[type_memory_size_slots] >>
  `(type_memory_size rty + 31) DIV 32 = type_slot_size rty` by
    simp[type_memory_size_slots, arithmeticTheory.ADD_DIV_ADD_DIV] >>
  `w2n a + type_memory_size rty < dimword(:256)` by
    metis_tac[immutable_holds_bounds] >>
  `w2n a + type_memory_size rty <= LENGTH s.vs_data_section` by
    metis_tac[runtime_immutable_data_section] >>
  `ci_mono sb mid` by
    (qspecl_then [`type_memory_size rty`, `sb`] mp_tac
      ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono mid cs''` by
    (qpat_assum `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     metis_tac[ci_mono_compile_imm_copy_to_memory, pairTheory.SND]) >>
  `fn_has_code sb mid func /\ fn_has_code mid cs'' func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split]) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by
    (qpat_x_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
      (qspec_then `H0` mp_tac) >> simp[ghost_inv_at_def] >> metis_tac[]) >>
  `op_taint tn p.ptr_operand = {}` by
    fs[ptr_vv_ok_def, vv_operand_def] >>
  `type_memory_size rty < dimword(:256)` by
    (simp[wordsTheory.dimword_def] >> decide_tac) >>
  `compile_imm_copy_to_memory F cenv.ce_imm_alloca p.ptr_operand buf.buf_operand
      (type_slot_size rty) 0 mid = ((),cs'')` by metis_tac[] >>
  `w2n a + 32 * type_slot_size rty <= LENGTH s.vs_data_section /\
   w2n a + 32 * type_slot_size rty < dimword(:256)` by metis_tac[] >>
  drule_all runtime_code_copy_origin_execution >>
  disch_then (qspecl_then [`explicit`, `PG`, `G`,
    `<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>`]
    strip_assume_tac) >>
  rename1 `copy_runtime_frame mid allocst cs'' z` >>
  rename1 `lookup_var root allocst = SOME dst` >>
  `unwrap_value cenv (LocatedValue (post_value_type cenv e) p) sb =
     (buf.buf_operand,cs'')` by
    (simp[unwrap_value_def, compile_ensure_in_memory_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >> gvs[]) >>
  `sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id` by decide_tac >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post H ctx func cenv cx e es sa cs'' s0 ee v buf.buf_operand z` by
    (rpt strip_tac >>
     `vv_post H ctx func cenv cx e es sa sb s0 ee (Value v)
       (LocatedValue (post_value_type cenv e) p) s` by
       (irule vv_post_read_result >> qexists `tv` >> simp[]) >>
     `!ty. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ty ==>
       type_memory_bytes cenv (post_value_type cenv e) = type_memory_size ty` by simp[] >>
     drule_all unwrap_code_copy_endpoint_post >> simp[]) >>
  `allocst.vs_memory = s.vs_memory /\
   allocst.vs_accounts = s.vs_accounts /\
   allocst.vs_transient = s.vs_transient /\
   allocst.vs_call_ctx = s.vs_call_ctx /\
   allocst.vs_immutables = s.vs_immutables` by
    (drule unwrap_alloc_runtime_frame >> simp[] >> metis_tac[]) >>
  `buffer_allocation_base s sb.cs_next_id < dimword(:256)` by
    (drule_all unwrap_alloc_site_bound >> decide_tac) >>
  `lo <= w2n dst` by
    (simp[] >> Cases_on `FLOOKUP s.vs_allocas sb.cs_next_id` >>
     fs[buffer_allocation_base_def, allocas_from_def] >>
     PairCases_on `x` >> fs[] >> metis_tac[]) >>
  `local_ptrs_reserved cenv sb` by metis_tac[local_ptrs_reserved_next_var] >>
  `sb.cs_next_var <= mid.cs_next_var` by fs[ci_mono_def] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    ghost_inv_at (DF H) lo d cenv cx ee HG tf
      (z with vs_inst_idx := LENGTH cs''.cs_current_insts)` by
    (rpt strip_tac >>
     `stmt_state_rel H ctx func cenv cx ee s /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn s` by
       (fs[vv_post_def] >> metis_tac[]) >>
     `tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm` by
       (fs[step_taint_def, mk_inst_def, adopt_reset_def, store_taint_def, imm_taint_def]) >>
     `32 * type_slot_size rty <= type_memory_size rty /\ lo <= z.vs_alloca_next` by decide_tac >>
     drule_all runtime_code_copy_ghost_inv_at >> simp[]) >>
  `MEM (mk_inst sb.cs_next_id ALLOCA [Lit (n2w (type_memory_size rty))] [root])
    (fn_insts func)` by
    (drule unwrap_alloc_generated_code >> strip_tac >>
     drule_all exprSimAllocTheory.buffer_alloc_code >> gvs[]) >>
  `!i. i < buffer_allocation_base s sb.cs_next_id \/
       buffer_allocation_base s sb.cs_next_id + type_memory_size rty <= i ==>
       (i IN tm.t_mem <=> i IN tn.t_mem)` by
    (drule_all unwrap_alloc_taint_frame >> simp[] >> metis_tac[]) >>
  `tf.t_mem SUBSET tn.t_mem` by
    (fs[pred_setTheory.SUBSET_DEF] >> rpt strip_tac >>
     `w2n dst = buffer_allocation_base s sb.cs_next_id` by simp[] >>
     metis_tac[arithmeticTheory.NOT_LESS_EQUAL]) >>
  `!off len. off+len <= w2n dst \/ w2n dst+type_memory_size rty <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory` by metis_tac[] >>
  `u = update_var root dst
    (buffer_allocation_fields s sb.cs_next_id (type_memory_size rty))` by simp[] >>
  drule_all runtime_code_copy_retained_frames >> strip_tac >>
  qexistsl [`z with vs_inst_idx := LENGTH cs''.cs_current_insts`, `HG`, `tf`] >>
  simp[] >>
  conj_tac >-
    (rpt strip_tac >> irule gas_origin_ptr_path_from_no_dead >> first_assum ACCEPT_TAC) >>
  `expr_post H0 ctx func cenv cx e es sa cs'' s0 ee v (Var root)
    (z with vs_inst_idx := LENGTH cs''.cs_current_insts)` by
    (pure_rewrite_tac[body_field_expr_post_inst_idx] >> metis_tac[]) >>
  conj_tac >-
    (qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `H0` mp_tac) >> (impl_tac >- simp[]) >>
     qpat_x_assum `expr_post H0 _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `read_result _ _ _ = _` mp_tac >>
     qpat_assum `~is_word_type _` mp_tac >>
     qpat_assum `p.ptr_location = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[expr_post_def, vv_post_def, vv_at_def, expr_val_at_def,
       mk_ptr_def, local_place_at_def, eval_operand_def,
       log_local_region_inst_idx] >> rpt strip_tac >> metis_tac[]) >>
  `lowered_value_type cenv e = expr_type e` by
    (drule compile_nonmemory_lowered_value_type >> simp[]) >>
  `post_value_type cenv e = expr_type e` by metis_tac[post_value_type_lowered] >>
  `not_fresh_at mid root` by
    (drule_all allocated_copy_operands_old >> simp[]) >>
  `lookup_var root z = SOME dst` by
    (fs[copy_runtime_frame_def] >> metis_tac[]) >>
  conj_tac >-
    (fs[expr_post_def, expr_val_at_def] >>
     simp[expr_store_bound_def, eval_operand_def] >> rpt strip_tac >>
     `val_wf rty v` by metis_tac[] >>
     drule exprSimPropsTheory.val_store_size_le >>
     gvs[lookup_var_def] >> decide_tac) >>
  `ptr_covers HG tf root (z with vs_inst_idx := LENGTH cs''.cs_current_insts)
     (type_memory_size rty)` by
    (qpat_x_assum `ptr_covers HG tf root z _` mp_tac >>
     simp[ptr_covers_def, lookup_var_def]) >>
  `eval_operand (Var root) (z with vs_inst_idx := LENGTH cs''.cs_current_insts) = SOME dst` by
    (qpat_assum `lookup_var root z = SOME dst` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[eval_operand_def, lookup_var_def]) >>
  `val_wf rty v` by
    (fs[expr_post_def, expr_val_at_def] >> metis_tac[]) >>
  `type_memory_bytes cenv (lowered_value_type cenv e) <= type_memory_size rty` by fs[] >>
  `!i. w2n dst <= i /\ i < w2n dst + type_memory_size rty ==> i NOTIN tf.t_mem` by
    (fs[pred_setTheory.IN_DIFF, pred_setTheory.GSPECIFICATION] >> decide_tac) >>
  `type_memory_size rty <= type_memory_size rty` by simp[] >>
  drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`) clean_buffer_pointer_posts >>
  simp[] >> disch_then drule >> simp[] >>
  gvs[] >> strip_tac >> rpt strip_tac >>
  simp[lookup_var_def] >> metis_tac[lookup_var_def]
QED

(* Constructor immutable-memory branch, with a single execution endpoint. *)
Theorem unwrap_code_copy_ctor_origin_ptr:
  cenv.ce_is_ctor /\
  vv = LocatedValue t p /\ p.ptr_location = LocCode /\ ~is_word_type t /\
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
  strip_tac >> gvs[] >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
     ee.storage_trace` by fs[storage_trace_domain_def] >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `H0` mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  drule_all vv_post_code_source >> strip_tac >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post H ctx func cenv cx e es sa sb s0 ee tv (LocatedValue t p) s` by
    (rpt strip_tac >>
     qpat_x_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
       (drule_then strip_assume_tac) >>
     gvs[vv_post_def, vv_at_def, vv_own_def] >> metis_tac[]) >>
  `sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id` by decide_tac >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sb x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists `sm` >> fs[vv_operand_def]) >>
  `vv_post H0 ctx func cenv cx e es sa sb s0 ee (Value v) (LocatedValue t p) s` by
    (irule vv_post_read_result >> qexists `tv` >> simp[] >>
     first_x_assum irule >> simp[]) >>
  `type_memory_bytes cenv t = type_memory_size rty /\ type_memory_size rty < 2**64` by fs[] >>
  `w2n a + type_memory_size rty <= lo /\
   (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory rty v (w2n a) mem)` by fs[vv_location_def, vv_operand_def] >>
  qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  simp[unwrap_value_def, compile_ensure_in_memory_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  gvs[] >> rename1 `compile_alloc_buffer _ sb = (buf,mid)` >>
  `stmt_state_rel H0 ctx func cenv cx ee s` by fs[vv_post_def] >>
  `type_memory_size rty = 32 * type_slot_size rty` by simp[type_memory_size_slots] >>
  `(type_memory_size rty + 31) DIV 32 = type_slot_size rty` by
    simp[type_memory_size_slots, arithmeticTheory.ADD_DIV_ADD_DIV] >>
  `ci_mono sb mid` by
    (qspecl_then [`type_memory_size rty`, `sb`] mp_tac ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono mid cs''` by
    (qpat_assum `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     metis_tac[ci_mono_compile_imm_copy_to_memory, pairTheory.SND]) >>
  `fn_has_code sb mid func /\ fn_has_code mid cs'' func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split]) >>
  `ghost_inv_at (DF H0) lo d cenv cx ee G tn s` by metis_tac[] >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `op_taint tn p.ptr_operand = {} /\ op_prov G p.ptr_operand = NONE` by
    fs[ptr_vv_ok_def, vv_operand_def] >>
  `type_memory_size rty < dimword(:256)` by
    (simp[wordsTheory.dimword_def] >> decide_tac) >>
  `local_ptrs_reserved cenv sb` by metis_tac[local_ptrs_reserved_next_var] >>
  `type_slot_size rty <> 0 ==> !region. cenv.ce_imm_alloca = SOME region ==>
    eval_operand region s = SOME 0w /\ copy_old_operand sb region /\
    op_taint tn region = {} /\ op_prov G region = NONE` by
    (rpt strip_tac >>
     `lo <> 0` by decide_tac >>
     Cases_on `region` >>
     fs[copy_old_operand_def, op_taint_def, op_prov_def,
        ghost_inv_at_def, local_ptrs_reserved_imm_base,
        stmt_state_rel_def, state_rel_def, immutables_rel_def, immutable_base_zero_def] >>
     metis_tac[local_ptrs_reserved_imm_base]) >>
  `compile_imm_copy_to_memory T cenv.ce_imm_alloca p.ptr_operand buf.buf_operand
      (type_slot_size rty) 0 mid = ((),cs'')` by metis_tac[] >>
  `w2n a + 32 * type_slot_size rty <= lo` by decide_tac >>
  drule_all ctor_code_copy_origin_execution >>
  disch_then (qspecl_then [`explicit`, `PG`,
    `<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>`]
    strip_assume_tac) >>
  rename1 `copy_runtime_frame mid allocst cs'' z` >>
  rename1 `lookup_var root allocst = SOME dst` >>
  `unwrap_value cenv (LocatedValue (post_value_type cenv e) p) sb =
     (buf.buf_operand,cs'')` by
    (simp[unwrap_value_def, compile_ensure_in_memory_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >> gvs[]) >>
  `sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id` by decide_tac >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post H ctx func cenv cx e es sa cs'' s0 ee v buf.buf_operand z` by
    (rpt strip_tac >>
     `vv_post H ctx func cenv cx e es sa sb s0 ee (Value v)
       (LocatedValue (post_value_type cenv e) p) s` by
       (irule vv_post_read_result >> qexists `tv` >> simp[]) >>
     `!ty. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ty ==>
       type_memory_bytes cenv (post_value_type cenv e) = type_memory_size ty` by simp[] >>
     drule_all ctor_code_copy_endpoint_post >> simp[]) >>
  `allocst.vs_memory = s.vs_memory /\
   allocst.vs_accounts = s.vs_accounts /\ allocst.vs_transient = s.vs_transient /\
   allocst.vs_call_ctx = s.vs_call_ctx /\ allocst.vs_immutables = s.vs_immutables` by
    (drule unwrap_alloc_runtime_frame >> simp[] >> metis_tac[]) >>
  `buffer_allocation_base s sb.cs_next_id < dimword(:256)` by
    (drule_all unwrap_alloc_site_bound >> decide_tac) >>
  `lo <= w2n dst` by
    (simp[] >> Cases_on `FLOOKUP s.vs_allocas sb.cs_next_id` >>
     fs[buffer_allocation_base_def, allocas_from_def] >>
     PairCases_on `x` >> fs[] >> metis_tac[]) >>
  `sb.cs_next_var <= mid.cs_next_var` by fs[ci_mono_def] >>
  `tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm` by
    fs[step_taint_def, mk_inst_def, adopt_reset_def, store_taint_def, imm_taint_def] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    ghost_inv_at (DF H) lo d cenv cx ee HG tf
      (z with vs_inst_idx := LENGTH cs''.cs_current_insts)` by
    (rpt strip_tac >>
     `stmt_state_rel H ctx func cenv cx ee s /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn s` by
       (fs[vv_post_def] >> metis_tac[]) >>
     `32 * type_slot_size rty <= type_memory_size rty /\ lo <= z.vs_alloca_next` by decide_tac >>
     drule_all ctor_code_copy_ghost_inv_at >> simp[]) >>
  `32 * type_slot_size rty <= type_memory_size rty` by decide_tac >>
  drule_all ctor_code_copy_exterior_frames >> strip_tac >>
  `wb_frame cenv es ee sa s0 s` by
    (qpat_assum `vv_post H0 _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[vv_post_def, wb_frame_def] >> metis_tac[]) >>
  `u = update_var root dst
    (buffer_allocation_fields s sb.cs_next_id (type_memory_size rty))` by simp[] >>
  drule_all ctor_code_copy_retained_frames >> strip_tac >>
  `not_fresh_at mid root` by
    (drule_all allocated_copy_operands_old >> simp[]) >>
  `lookup_var root z = SOME dst` by
    (fs[copy_runtime_frame_def] >> metis_tac[]) >>
  `w2n a + type_memory_size rty < dimword(:256)` by metis_tac[immutable_holds_bounds] >>
  `regions_disjoint (w2n a) (type_memory_size rty) (w2n dst) (type_memory_size rty)` by
    (gvs[regions_disjoint_def] >> decide_tac) >>
  `z.vs_memory = (immutable_transfers F T a dst (type_slot_size rty) 0 allocst).vs_memory` by
    (Cases_on `type_slot_size rty = 0`
     >- (gvs[compile_imm_copy_to_memory_def, comp_return_def,
          copy_runtime_frame_def, immutableCopyExecutionTheory.immutable_transfers_def,
          run_inst_seq_def]) >>
     `!region. cenv.ce_imm_alloca = SOME region ==>
       eval_operand region allocst = SOME 0w /\ copy_old_operand mid region` by
       (gen_tac >> disch_tac >>
        `eval_operand region s = SOME 0w /\ copy_old_operand sb region` by metis_tac[] >>
        `!x. region = Var x ==> x <> root` by
          (fs[copy_old_operand_def] >> metis_tac[exprPtrUnwrapAllocEntryTheory.unwrap_alloc_old_operand_distinct]) >>
        conj_tac >- (drule_all unwrap_alloc_operand_frame >> simp[] >> metis_tac[]) >>
        metis_tac[copy_old_operand_mono, ci_mono_def]) >>
     drule_all allocated_copy_operands_old >> strip_tac >>
     `!x. p.ptr_operand = Var x ==> x <> root` by
       metis_tac[exprPtrUnwrapAllocEntryTheory.unwrap_alloc_old_operand_distinct] >>
     `eval_operand p.ptr_operand allocst = SOME a` by
       (drule_all unwrap_alloc_operand_frame >> simp[] >> metis_tac[]) >>
     `eval_operand buf.buf_operand allocst = SOME dst` by
       (qpat_assum `lookup_var root allocst = SOME dst` mp_tac >>
        simp[eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
     `copy_old_operand mid buf.buf_operand` by simp[copy_old_operand_def] >>
     drule_all copy_ctor_run >> strip_tac >>
     `zz = z` by fs[copy_runtime_frame_def] >> gvs[]) >>
  `MEM (mk_inst sb.cs_next_id ALLOCA [Lit (n2w (type_memory_size rty))] [root])
    (fn_insts func)` by
    (drule unwrap_alloc_generated_code >> strip_tac >>
     drule_all exprSimAllocTheory.buffer_alloc_code >> gvs[]) >>
  `!i. i < buffer_allocation_base s sb.cs_next_id \/
       buffer_allocation_base s sb.cs_next_id + type_memory_size rty <= i ==>
       (i IN tm.t_mem <=> i IN tn.t_mem)` by
    (drule_all unwrap_alloc_taint_frame >> simp[] >> metis_tac[]) >>
  `!i. i < type_memory_size rty ==>
     (w2n dst+i IN tf.t_mem <=> w2n a+i IN tn.t_mem)` by
    (rpt strip_tac >>
     `w2n dst <= w2n dst+i /\ w2n dst+i < w2n dst+32*type_slot_size rty /\
      w2n a+i < buffer_allocation_base s sb.cs_next_id` by
       (gvs[] >> decide_tac) >>
     `w2n dst+i-w2n dst = i` by decide_tac >> metis_tac[]) >>
  `lowered_value_type cenv e = expr_type e` by
    (drule compile_nonmemory_lowered_value_type >> simp[]) >>
  `post_value_type cenv e = expr_type e` by metis_tac[post_value_type_lowered] >>
  `expr_post H0 ctx func cenv cx e es sa cs'' s0 ee v (Var root)
    (z with vs_inst_idx := LENGTH cs''.cs_current_insts)` by
    (pure_rewrite_tac[body_field_expr_post_inst_idx] >> metis_tac[]) >>
  `val_wf rty v /\ val_footprint rty v <= type_memory_size rty /\
   val_store_size rty v <= type_memory_size rty` by
    (fs[expr_post_def, expr_val_at_def] >>
     metis_tac[exprSimPropsTheory.val_store_size_le, exprSimPropsTheory.val_footprint_le]) >>
  `ptr_val_ok cx (post_value_type cenv e) v (Var root) HG tf
    (z with vs_inst_idx := LENGTH cs''.cs_current_insts)` by
    (irule ctor_code_copy_ptr_val_ok >>
     metis_tac[]) >>
  qexistsl [`z with vs_inst_idx := LENGTH cs''.cs_current_insts`, `HG`, `tf`] >>
  simp[] >>
  conj_tac >-
    (gen_tac >> disch_tac >>
     pure_rewrite_tac[body_field_expr_post_inst_idx] >> simp[] >>
     irule gas_origin_ptr_path_from_no_dead >> first_assum ACCEPT_TAC) >>
  conj_tac >-
    (qpat_assum `post_value_type cenv e = expr_type e` mp_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `H0` mp_tac) >> (impl_tac >- simp[]) >>
     qpat_x_assum `expr_post H0 _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `read_result _ _ _ = _` mp_tac >>
     qpat_assum `~is_word_type _` mp_tac >>
     qpat_assum `p.ptr_location = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[expr_post_def, vv_post_def, vv_at_def, expr_val_at_def,
       mk_ptr_def, local_place_at_def, eval_operand_def,
       log_local_region_inst_idx] >> rpt strip_tac >> metis_tac[]) >>
  conj_tac >-
    (simp[expr_store_bound_def, eval_operand_def] >> rpt strip_tac >>
     gvs[lookup_var_def] >> decide_tac) >>
  conj_tac >- metis_tac[] >>
  conj_tac >-
    (`type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size rty` by fs[] >>
     pop_assum mp_tac >>
     qpat_assum `ptr_covers HG tf root z _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[ptr_covers_def, ptr_buf_ok_def, eval_operand_def, lookup_var_def] >>
     rpt strip_tac >> gvs[] >> metis_tac[]) >>
  conj_tac >-
    (rpt strip_tac >> gvs[eval_operand_def, lookup_var_def] >> decide_tac) >>
  simp[lookup_var_def] >> metis_tac[lookup_var_def]
QED

(* An immutable aggregate is copied into a fresh buffer. *)
Theorem unwrap_code_copy_origin_ptr:
  vv = LocatedValue t p /\ p.ptr_location = LocCode /\ ~is_word_type t /\
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
  cheat
QED
