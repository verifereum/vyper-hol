Theory createCtorEncoderDelayedCtorMods
Ancestors
  bodyFullPostsMods bodyFullShadowBodyInv bodyInvSplit bodyFullUnwrapCodeCtorRun
  bodyFullHashKeccakFixed exprSimWordArgs exprPtrUnwrapAllocation
  bodyFullUnwrapCodeCtorFrame bodyFullUnwrapSlotPost exprPtrUnwrapAllocSemantic
  exprPtrUnwrapAllocEntry exprPtrUnwrapAllocSeparation exprPtrUnwrapAllocationFrame
  exprPtrUnwrapCodeCopyShape exprPtrUnwrapCodeCopySemantic exprPtrUnwrapRetained
  bodyPtrMakeArrayMemoryFrame stateRelProj bodyPtrEnvBuiltinsBoundary
  exprLowering exprLoweringProps exprOperandVar exprSimCopy exprSimStorageCopy
  exprSimAlloc exprSimProps exprSimUnwrapProps localPtrsProps loweringSlice
  fragGasOriginPtrDead fragGasOriginPtrExec gasOriginPtrLabels fragExec
  immutableCopyExecution bufferAllocationExecution bodyPtrDefs loweringPosts
  loweringStateRelDefs compileEnv context freshWrites venomState venomInst
  venomExecSemantics ptrDiscipline valueEncodingTyping valueEncodingProps
  loweringHalt exprSimMemDefs bodyPtrIfExpAllocSource immutableBytestringFootprint
  vyperStorageFootprint vyperStorageTrace words finite_map arithmetic

Theorem delayed_ctor_ptr_read[local]:
  ptr_val_ok cx ty v op G tn s /\ ~is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME rt /\ eval_operand op s = SOME w ==>
  val_in_memory rt v (w2n w) s.vs_memory
Proof
  simp[ptr_val_ok_def,ptr_mem_ok_def] >> rpt strip_tac >>
  `mem_agree_outside tn.t_mem s.vs_memory s.vs_memory` by simp[mem_agree_outside_def] >>
  metis_tac[]
QED

(* The read contract holds at the delayed cut, before allocating the copy. *)
Theorem ctor_encoder_delayed_ctor_mods:
  p.ptr_location = LocCode /\ ce.ce_is_ctor /\
  lowered_value_type ce e = expr_type e /\ ~is_word_type (expr_type e) /\
  compile_expr ce (expr_type e) e si = (LocatedValue (expr_type e) p,sm) /\
  sm.cs_next_var <= su.cs_next_var /\ sm.cs_next_id <= su.cs_next_id /\
  unwrap_value ce (LocatedValue (expr_type e) p) su = (src,sb) /\
  local_ptrs_reserved ce si /\ local_ptrs_reserved ce sm /\
  si.cs_next_var <= sm.cs_next_var /\ si.cs_next_id <= sm.cs_next_id /\
  fn_has_code su sb fn /\ fn_inst_ids_distinct fn /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME rt /\
  type_memory_bytes ce (expr_type e) = type_memory_size rt /\
  type_memory_size rt < 2**64 /\ value_has_type rt v /\
  storage_trace_domain cx st0 ee.storage_trace /\
  read_result cx raw ee = (INL v,ee) /\
  vv_holds_mods ce cx (expr_type e) raw (LocatedValue (expr_type e) p) ee t /\
  ptr_vv_ok cx (expr_type e) raw (LocatedValue (expr_type e) p) ee G tn t /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx fn ce cx ee t /\ immutable_frame_mods fn ce cx ee t /\
     storage_well_formed_on cx ee (FST H) /\
     vv_storage_live H cx (LocatedValue (expr_type e) p) ee t /\
     ghost_inv_at_mods (DF H) lo d ce cx ee G tn t) /\
  alloca_history fn t /\ ~t.vs_halted /\ t.vs_current_bb = su.cs_current_bb /\
  t.vs_inst_idx = LENGTH su.cs_current_insts /\
  (!w. eval_operand p.ptr_operand t = SOME w ==>
     w2n w + type_memory_size rt <= lo /\
     (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
            val_in_memory rt v (w2n w) mem)) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) ==>
  ?q HG tf.
    pure_frame ce fn ee su t q /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx fn ce cx ee q /\ immutable_frame_mods fn ce cx ee q /\
       storage_well_formed_on cx ee (FST H) /\
       ghost_inv_at_mods (DF H) lo d ce cx ee HG tf q) /\
    expr_val_rel cx (expr_type e) v src q /\ ptr_val_ok cx (expr_type e) v src HG tf q /\
    expr_store_bound cx (expr_type e) v src q /\ ptr_buf_ok ce e src HG q /\
    (!w. eval_operand src q = SOME w ==> w2n w + type_memory_size rt <= q.vs_alloca_next) /\
    alloca_history fn q /\ t.vs_alloca_next <= q.vs_alloca_next /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\ q.vs_labels = t.vs_labels /\
    (!x. not_fresh_at su x ==> lookup_var x q = lookup_var x t /\
       FLOOKUP HG x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    wb_frame ce ee ee su t q /\ ghost_kept_at lo ce ee su G tn t HG tf /\
    (!x. src = Var x ==> not_fresh_at sb x) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (t,G,tn) [] (OK q,HG,tf)) /\
    expr_val_at ce cx (expr_type e) su sb ee v src q
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by fs[Abbr `H0`,storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  `?w. eval_operand p.ptr_operand t = SOME w` by
    (qpat_assum `vv_holds_mods _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `p.ptr_location = LocCode` (fn th => simp[NoAsms, th, vv_holds_mods_def]) >>
     disch_then (qx_choose_then `w` (assume_tac o CONJUNCT1)) >> qexists_tac `w` >> simp[]) >>
  rename1 `eval_operand p.ptr_operand t = SOME w` >>
  qpat_assum `!w. eval_operand p.ptr_operand t = SOME w ==> _` (drule_then strip_assume_tac) >>
  `local_ptrs_reserved ce su` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at su x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp t)` by
    metis_tac[stmt_state_rel_allocas_below_fmp] >>
  `op_taint tn p.ptr_operand = {} /\ op_prov G p.ptr_operand = NONE` by
    fs[ptr_vv_ok_def, vv_operand_def] >>
  qabbrev_tac `nb = type_memory_size rt` >>
  qabbrev_tac `n = type_slot_size rt` >>
  `nb = 32*n /\ (nb+31) DIV 32 = n` by
    simp[Abbr `nb`, Abbr `n`, type_memory_size_slots, ADD_DIV_ADD_DIV] >>
  `nb < dimword (:256)` by (fs[dimword_def] >> decide_tac) >>
  `?buf mid. compile_alloc_buffer nb su = (buf,mid) /\
     compile_imm_copy_to_memory T ce.ce_imm_alloca p.ptr_operand buf.buf_operand n 0 mid = ((),sb) /\
     src = buf.buf_operand` by
    (qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
     simp[unwrap_value_def,compile_ensure_in_memory_def,comp_bind_def,
          comp_ignore_bind_def,comp_return_def] >>
     pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[]) >>
  `ci_mono su mid /\ ci_mono mid sb` by
    metis_tac[ci_mono_compile_alloc_buffer,ci_mono_compile_imm_copy_to_memory,pairTheory.SND] >>
  `fn_has_code su mid fn /\ fn_has_code mid sb fn` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split]) >>
  `(n <> 0 ==> !region. ce.ce_imm_alloca = SOME region ==>
      eval_operand region t = SOME 0w /\ copy_old_operand su region /\
      op_taint tn region = {} /\ op_prov G region = NONE)` by suspend "imm_base" >>
  `w2n w + 32*n <= lo` by decide_tac >>
  drule_all ctor_code_copy_origin_execution >>
  disch_then (qspecl_then [`explicit`,`PG`,
      `<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`]
    (qx_choosel_then [`root`,`u`,`a`,`Gm`,`tm`,`HG`,`tf`,`z`,`dst`]
      (REPEAT_TCL CONJUNCTS_THEN assume_tac))) >>
  suspend "frames"
QED

Resume ctor_encoder_delayed_ctor_mods[imm_base]:
  disch_tac >> gen_tac >> disch_tac >> `lo <> 0` by decide_tac >>
  drule_then assume_tac stmt_state_rel_immutable_base_zero >>
  conj_tac >- fs[immutable_base_zero_def] >>
  Cases_on `region` >>
  fs[copy_old_operand_def, op_taint_def, op_prov_def, ghost_inv_at_mods_def] >>
  metis_tac[local_ptrs_reserved_imm_base]
QED

Resume ctor_encoder_delayed_ctor_mods[frames]:
  `a.vs_memory = t.vs_memory /\ a.vs_accounts = t.vs_accounts /\
   a.vs_transient = t.vs_transient /\ a.vs_call_ctx = t.vs_call_ctx /\
   a.vs_immutables = t.vs_immutables` by
    (drule unwrap_alloc_runtime_frame >> simp[] >> metis_tac[]) >>
  `buffer_allocation_base t su.cs_next_id < dimword (:256)` by
    (drule_all unwrap_alloc_site_bound >> decide_tac) >>
  `w2n dst = buffer_allocation_base t su.cs_next_id` by simp[w2n_n2w] >>
  `lo <= w2n dst` by
    (simp[] >> Cases_on `FLOOKUP t.vs_allocas su.cs_next_id` >>
     fs[buffer_allocation_base_def, allocas_from_def] >>
     PairCases_on `x` >> fs[] >> metis_tac[]) >>
  `32*n <= nb` by simp[] >>
  drule_all ctor_code_copy_exterior_frames >> strip_tac >>
  `si.cs_next_var <= su.cs_next_var /\ si.cs_next_id <= su.cs_next_id` by decide_tac >>
  `u = update_var root dst (buffer_allocation_fields t su.cs_next_id nb)` by simp[] >>
  `wb_frame ce ee ee si t t /\ ghost_kept_at lo ce ee si G tn t G tn` by
    simp[wb_frame_refl,ghost_kept_at_def] >>
  `MAP FDOM ee.scopes = MAP FDOM ee.scopes` by simp[] >>
  drule_all ctor_code_copy_retained_frames_pure >> strip_tac >>
  `not_fresh_at mid root` by (drule_all allocated_copy_operands_old >> simp[]) >>
  `lookup_var root z = SOME dst` by fs[copy_runtime_frame_def] >>
  `src = Var root` by metis_tac[] >>
  `MEM (mk_inst su.cs_next_id ALLOCA [Lit (n2w nb)] [root]) (fn_insts fn)` by
    (drule unwrap_alloc_generated_code >> strip_tac >> drule_all buffer_alloc_code >> gvs[]) >>
  `copy_static z = copy_static a /\
   (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x a)` by fs[copy_runtime_frame_def] >>
  qabbrev_tac `q = z with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `q.vs_memory = z.vs_memory /\ q.vs_allocas = u.vs_allocas /\
    q.vs_alloca_next = z.vs_alloca_next /\ q.vs_labels = t.vs_labels /\
    q.vs_accounts = t.vs_accounts /\ q.vs_transient = t.vs_transient /\
    q.vs_call_ctx = t.vs_call_ctx /\ q.vs_immutables = t.vs_immutables` by suspend "static_fields" >>
  `z.vs_memory = (immutable_transfers F T w dst n 0 a).vs_memory` by suspend "raw_memory" >>
  suspend "copied_value"
QED

Resume ctor_encoder_delayed_ctor_mods[static_fields]:
  drule_then strip_assume_tac copy_static_fields >>
  `z.vs_immutables = a.vs_immutables` by
    (qpat_assum `copy_static z = copy_static a`
       (mp_tac o Q.AP_TERM `\s. s.vs_immutables`) >> simp[NoAsms, copy_static_def]) >>
  `a.vs_labels = t.vs_labels` by
    (qpat_assum `a = u with vs_inst_idx := _` SUBST1_TAC >>
     qpat_assum `u = update_var root dst _` SUBST1_TAC >>
     Cases_on `FLOOKUP t.vs_allocas su.cs_next_id` >> simp[update_var_def,buffer_allocation_fields_def]) >>
  `a.vs_allocas = u.vs_allocas` by simp[] >>
  simp[Abbr `q`]
QED

Resume ctor_encoder_delayed_ctor_mods[raw_memory]:
  Cases_on `n = 0`
  >- gvs[compile_imm_copy_to_memory_def,comp_return_def,copy_runtime_frame_def,
         immutable_transfers_def,run_inst_seq_def] >>
  `!op. (!x. op = Var x ==> x <> root) ==>
        eval_operand op a = eval_operand op t` by
    (gen_tac >> strip_tac >> qpat_assum `a = _` SUBST1_TAC >>
     irule unwrap_alloc_operand_frame >> metis_tac[]) >>
  `!region. ce.ce_imm_alloca = SOME region ==>
      eval_operand region a = SOME 0w /\ copy_old_operand mid region` by
    (gen_tac >> disch_tac >>
     `eval_operand region t = SOME 0w /\ copy_old_operand su region` by metis_tac[] >>
     `!x. region = Var x ==> x <> root` by
       (fs[copy_old_operand_def] >> metis_tac[unwrap_alloc_old_operand_distinct]) >>
     conj_tac >- metis_tac[] >>
     metis_tac[copy_old_operand_mono,ci_mono_def]) >>
  `copy_old_operand mid p.ptr_operand` by metis_tac[allocated_copy_operands_old] >>
  `!x. p.ptr_operand = Var x ==> x <> root` by metis_tac[unwrap_alloc_old_operand_distinct] >>
  `eval_operand p.ptr_operand a = SOME w` by metis_tac[] >>
  `eval_operand buf.buf_operand a = SOME dst /\ copy_old_operand mid buf.buf_operand` by
    gvs[eval_operand_def,copy_old_operand_def,operand_11,lookup_var_def] >>
  drule_all copy_ctor_run >> strip_tac >> fs[copy_runtime_frame_def] >> metis_tac[]
QED

Resume ctor_encoder_delayed_ctor_mods[copied_value]:
  `val_wf rt v` by (irule (cj 1 value_has_type_val_wf) >> first_assum ACCEPT_TAC) >>
  `val_footprint rt v <= nb /\ val_store_size rt v <= nb` by
    simp[Abbr `nb`, val_footprint_le, val_store_size_le] >>
  `regions_disjoint (w2n w) nb (w2n dst) nb` by (simp[regions_disjoint_def] >> decide_tac) >>
  `w2n w + nb < dimword (:256)` by decide_tac >>
  `!i. i < nb ==> (w2n dst+i IN tf.t_mem <=> w2n w+i IN tm.t_mem)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!j. j IN tf.t_mem <=> _` (qspec_then `w2n dst+i` SUBST1_TAC) >>
     `w2n dst <= w2n dst+i /\ w2n dst+i < w2n dst+32*n /\ w2n dst+i-w2n dst = i` by
       decide_tac >> simp[]) >>
  `!mem. mem_agree_outside tm.t_mem a.vs_memory mem ==> val_in_memory rt v (w2n w) mem` by
    suspend "robust_source" >>
  `ptr_val_ok cx (expr_type e) v (Var root) HG tf q` by
    (qpat_assum `Abbrev(q = _)` (fn th => pure_rewrite_tac[REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
     irule ctor_code_copy_ptr_val_ok >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`a`,`dst`,`nb`,`w`,`tm`,`rt`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     fs[Abbr `nb`, Abbr `n`]) >>
  `eval_operand src q = SOME dst` by
    simp[Abbr `q`,eval_operand_def,lookup_var_def] >>
  `ptr_val_ok cx (expr_type e) v src HG tf q` by metis_tac[] >>
  `val_in_memory rt v (w2n dst) q.vs_memory` by
    (drule_all delayed_ctor_ptr_read >> first_assum ACCEPT_TAC ORELSE
     metis_tac[delayed_ctor_ptr_read]) >>
  suspend "assemble"
QED

Resume ctor_encoder_delayed_ctor_mods[robust_source]:
  `!i. i < w2n dst ==> (i IN tm.t_mem <=> i IN tn.t_mem)` by
    (drule_all unwrap_alloc_taint_frame >>
     disch_then (qspec_then `tn` strip_assume_tac) >> gen_tac >> disch_tac >>
     qpat_assum `!i. (i < buffer_allocation_base _ _ \/ _ <= i) ==> _`
       (qspec_then `i` mp_tac) >>
     (impl_tac >- (disj1_tac >> qpat_assum `w2n dst = _`
       (fn th => once_rewrite_tac[GSYM th]) >> first_assum ACCEPT_TAC)) >>
     qpat_assum `tm = _` (fn th => pure_rewrite_tac[th]) >> simp[NoAsms]) >>
  gen_tac >> disch_tac >> irule robust_val_in_memory_shrinking_frame >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`tn.t_mem`,`tm.t_mem`,`t.vs_memory`,`a.vs_memory`,`nb`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (qpat_assum `a.vs_memory = t.vs_memory` (fn th => rewrite_tac[th]) >> REFL_TAC) >>
  qx_gen_tac `i` >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `i < w2n dst` by decide_tac >>
  qpat_assum `!i. i < w2n dst ==> _` (drule_then (fn th => fs[th]))
QED

Resume ctor_encoder_delayed_ctor_mods[assemble]:
  `!x. not_fresh_at su x ==> lookup_var x q = lookup_var x t /\
     FLOOKUP HG x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by
    (qpat_assum `!x. not_fresh_at su x ==> lookup_var x z = _ /\ _` mp_tac >>
     simp[NoAsms, Abbr `q`,lookup_var_def]) >>
  `!name b len. local_region ce ee.scopes q name b len <=> local_region ce ee.scopes t name b len` by
    (rpt gen_tac >> irule copy_buffer_local_region_frame >> qexists_tac `su` >> simp[]) >>
  `!name b len. local_region ce ee.scopes t name b len ==>
     w2n dst + nb <= b \/ b+len <= w2n dst` by
    (rpt strip_tac >> drule_all unwrap_alloc_local_separation >> simp[]) >>
  drule_all unwrap_alloc_semantic_frames >> strip_tac >>
  `FLOOKUP q.vs_allocas su.cs_next_id = SOME (w2n dst,nb)` by
    (qpat_assum `q.vs_allocas = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `su.cs_next_id < sb.cs_next_id` by
    (drule compile_alloc_buffer_parts >> strip_tac >> fs[ci_mono_def] >> decide_tac) >>
  `!off len. off+len <= w2n dst \/ w2n dst+nb <= off ==>
     mem_bytes_at off len q.vs_memory = mem_bytes_at off len t.vs_memory` by
    (qpat_assum `q.vs_memory = _` (fn th => pure_rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx fn ce cx ee q /\ immutable_frame_mods fn ce cx ee q /\
       storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee HG tf q` by
    suspend "horizons" >>
  qexistsl_tac [`q`,`HG`,`tf`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (simp[expr_val_rel_def] >> (metis_tac[]))
  >- (simp[expr_store_bound_def] >> decide_tac)
  >- (simp[Abbr `q`,ptr_buf_ok_inst_idx] >> irule ptr_covers_buf_ok >>
      qexistsl_tac [`nb`,`tf`] >> simp[])
  >- (simp[] >> decide_tac)
  >- decide_tac
  >- simp[Abbr `q`]
  >- simp[Abbr `q`]
  >- simp[Abbr `q`]
  >- (drule compiler_unwrap_value_var >> simp[])
  >- (gen_tac >> irule gas_origin_ptr_path_from_no_dead >> first_assum ACCEPT_TAC) >>
  suspend "ownership"
QED

Resume ctor_encoder_delayed_ctor_mods[ownership]:
  rewrite_tac[expr_val_at_def] >> qx_gen_tac `rt'` >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `rt' = rt` by metis_tac[optionTheory.SOME_11] >>
  pop_assum SUBST1_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `dst` >> conj_tac >- first_assum ACCEPT_TAC >>
  disj1_tac >> qexistsl_tac [`su.cs_next_id`,`w2n dst`,`nb`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY decide_tac >>
  rpt strip_tac >>
  qpat_assum `!name b len. local_region ce ee.scopes q name b len <=> _`
    (fn th => fs[th]) >> metis_tac[]
QED

Resume ctor_encoder_delayed_ctor_mods[horizons]:
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  conj_tac >- suspend "state_rel" >>
  conj_tac >- suspend "immutable_frame" >>
  conj_tac >- first_assum ACCEPT_TAC >>
  suspend "ghost_frame"
QED

Resume ctor_encoder_delayed_ctor_mods[state_rel]:
  `stmt_state_rel H ctx fn ce cx ee a` by
    (drule_all unwrap_alloc_semantic_frames >> strip_tac >>
     qpat_assum `a = u with vs_inst_idx := _`
       (fn th => pure_rewrite_tac[th,stmt_state_rel_inst_idx]) >> first_assum ACCEPT_TAC) >>
  `FLOOKUP a.vs_allocas su.cs_next_id = SOME (w2n dst,nb)` by
    (qpat_assum `a = u with vs_inst_idx := _` (fn th => simp[NoAsms,th]) >> first_assum ACCEPT_TAC) >>
  `!name b len. local_region ce ee.scopes a name b len ==>
     w2n dst + nb <= b \/ b+len <= w2n dst` by
    (qpat_assum `!name b len. local_region ce ee.scopes u name b len ==> _` mp_tac >>
     qpat_assum `a = u with vs_inst_idx := _`
       (fn th => simp[NoAsms,th,local_region_def,lookup_var_def,regions_disjoint_def])) >>
  `LENGTH a.vs_memory <= LENGTH z.vs_memory` by
    (qpat_assum `z.vs_memory = _` (fn th => pure_rewrite_tac[th]) >>
     irule immutable_transfers_memory_nondecreasing) >>
  `local_ptrs_reserved ce mid` by metis_tac[local_ptrs_reserved_next_var,ci_mono_def] >>
  qpat_assum `Abbrev(q = _)`
    (fn th => pure_rewrite_tac[REWRITE_RULE [markerTheory.Abbrev_def] th,stmt_state_rel_inst_idx]) >>
  irule copy_buffer_state_rel_frame >>
  qexistsl_tac [`w2n dst`,`mk_inst su.cs_next_id ALLOCA [Lit (n2w nb)] [root]`,`a`,`mid`,`nb`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (simp[NoAsms,mk_inst_def] >> TRY (first_assum ACCEPT_TAC) >> NO_TAC) >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!off len. _ ==> mem_bytes_at off len z.vs_memory = mem_bytes_at off len a.vs_memory`
    irule >> decide_tac
QED

Resume ctor_encoder_delayed_ctor_mods[immutable_frame]:
  qpat_assum `immutable_frame_mods fn ce cx ee t`
    (strip_assume_tac o REWRITE_RULE [immutable_frame_mods_def,
       immutables_rel_mods_def,immutable_alloca_sep_mods_def]) >>
  rewrite_tac[immutable_frame_mods_def,immutable_alloca_sep_mods_def,immutables_rel_mods_def] >>
  reverse conj_tac >- suspend "immutable_allocas" >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!src tops. ALOOKUP ce.ce_modules src = SOME tops ==> immutables_rel _ _ _ _ _ _`
    (drule_then mp_tac) >>
  qpat_assum `ce.ce_is_ctor` (fn th => simp[NoAsms,th,immutables_rel_def]) >>
  disch_tac >> rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `!name tv v off. _ /\ _ ==> immutable_value_admissible _ _ /\ _`
    (drule_all_then strip_assume_tac) >>
  rename1 `val_in_memory vt value off t.vs_memory` >>
  `mem_bytes_at off (type_memory_size vt) q.vs_memory =
   mem_bytes_at off (type_memory_size vt) t.vs_memory` by suspend "immutable_bytes" >>
  asm_rewrite_tac[] >> irule val_in_memory_mem_agree >>
  conj_tac >- (irule (cj 1 immutable_admissible_val_wf) >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`type_memory_size vt`,`t.vs_memory`] >>
  simp[NoAsms] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  sym_tac >> (metis_tac[])
QED

Resume ctor_encoder_delayed_ctor_mods[immutable_allocas]:
  `!id b sz. FLOOKUP q.vs_allocas id = SOME (b,sz) ==>
      FLOOKUP t.vs_allocas id = SOME (b,sz) \/ t.vs_alloca_next <= b` by
    (qpat_assum `q.vs_allocas = u.vs_allocas` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `u = update_var root dst _` (fn th => pure_rewrite_tac[th]) >>
     Cases_on `FLOOKUP t.vs_allocas su.cs_next_id` >>
     pop_assum (fn th => simp[NoAsms,th,buffer_allocation_fields_def,update_var_def,FLOOKUP_UPDATE]) >>
     qx_genl_tac [`id`,`b`,`sz`] >> Cases_on `su.cs_next_id = id` >> simp[]) >>
  qx_genl_tac [`md`,`tops`] >> disch_tac >> irule immutable_alloca_sep_frame >>
  qexistsl_tac [`t`,`ee`] >>
  `t.vs_alloca_next <= q.vs_alloca_next` by decide_tac >>
  `immutable_alloca_sep fn (ce with ce_module := md) cx ee t` by
    (qpat_assum `!src tops. ALOOKUP ce.ce_modules src = SOME tops ==> immutable_alloca_sep _ _ _ _ _`
       (drule_then ACCEPT_TAC)) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY REFL_TAC >>
  qx_genl_tac [`id`,`b`,`sz`] >> disch_tac >> disj1_tac >> qexists_tac `id` >>
  pop_assum mp_tac >> qpat_assum `!name b sz. local_region ce ee.scopes q name b sz <=> _`
    (qspecl_then [`id`,`b`,`sz`] mp_tac) >> simp[NoAsms,local_region_def]
QED

Resume ctor_encoder_delayed_ctor_mods[immutable_bytes]:
  qpat_assum `!off len. _ \/ _ ==> mem_bytes_at off len q.vs_memory = _` irule >>
  qpat_assum `!src tops. ALOOKUP ce.ce_modules src = SOME tops ==> immutable_alloca_sep _ _ _ _ _`
    (drule_then mp_tac) >>
  qpat_assum `ce.ce_is_ctor`
    (fn th => simp[NoAsms,th,immutable_alloca_sep_def]) >>
  disch_then (CONJUNCTS_THEN2 (K ALL_TAC) assume_tac) >>
  qpat_assum `!name tv v off. _ /\ _ ==> off + type_memory_size tv <= _ /\ _`
    (drule_all_then strip_assume_tac) >>
  qpat_assum `w2n dst = _` SUBST1_TAC >>
  Cases_on `FLOOKUP t.vs_allocas su.cs_next_id`
  >- fs[buffer_allocation_base_def] >>
  rename1 `FLOOKUP t.vs_allocas su.cs_next_id = SOME row` >> PairCases_on `row` >>
  `row1 = nb` by
    (qpat_assum `FLOOKUP u.vs_allocas su.cs_next_id = SOME _` mp_tac >>
     qpat_assum `u = update_var root dst _` (fn th => pure_rewrite_tac[th]) >>
     simp[buffer_allocation_fields_def,update_var_def]) >>
  `regions_disjoint off (type_memory_size vt) row0 row1` by
    (qpat_assum `!inst b sz. MEM inst (fn_insts fn) /\ _ ==> regions_disjoint off (type_memory_size vt) b sz` irule >>
     qexists_tac `mk_inst su.cs_next_id ALLOCA [Lit (n2w nb)] [root]` >> simp[mk_inst_def]) >>
  fs[regions_disjoint_def,buffer_allocation_base_def]
QED

Resume ctor_encoder_delayed_ctor_mods[ghost_frame]:
  `tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm` by
    fs[step_taint_def,mk_inst_def,adopt_reset_def,store_taint_def,imm_taint_def] >>
  `stor_taint_ok_at (DF H) tf q` by
    (qpat_assum `ghost_inv_at_mods (DF H) lo d ce cx ee G tn t`
       (strip_assume_tac o REWRITE_RULE[ghost_inv_at_mods_def]) >>
     qpat_assum `stor_taint_ok_at (DF H) tn t`
       (assume_tac o REWRITE_RULE[stor_taint_ok_at_def]) >>
     simp[stor_taint_ok_at_def]) >>
  `local_ptrs_rel fn ce ee.scopes t` by
    (drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >> first_assum ACCEPT_TAC) >>
  `ghost_inv_at (DF H) 0 d ce cx ee G tn t` by
    (qpat_assum `ghost_inv_at_mods (DF H) lo d ce cx ee G tn t`
       (strip_assume_tac o REWRITE_RULE[ghost_inv_at_mods_def]) >>
     simp[NoAsms,ghost_inv_at_def,allocas_from_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ghost_inv_at (DF H) 0 d ce cx ee HG tf q` by suspend "ordinary_ghost" >>
  `mem_bytes_at 0 lo q.vs_memory = mem_bytes_at 0 lo t.vs_memory` by
    (qpat_assum `!off len. _ ==> mem_bytes_at off len q.vs_memory = _` irule >>
     disj1_tac >> simp[]) >>
  `allocas_from lo q` by
    (qpat_assum `allocas_from lo z` mp_tac >> simp[NoAsms,Abbr `q`,allocas_from_def]) >>
  `lo <= q.vs_alloca_next` by decide_tac >>
  qpat_assum `ghost_inv_at (DF H) 0 d ce cx ee HG tf q`
    (strip_assume_tac o REWRITE_RULE[ghost_inv_at_def]) >>
  qpat_assum `ghost_inv_at_mods (DF H) lo d ce cx ee G tn t`
    (strip_assume_tac o REWRITE_RULE[ghost_inv_at_mods_def]) >>
  rewrite_tac[ghost_inv_at_mods_def] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (rpt strip_tac >> `i < w2n dst` by decide_tac >> metis_tac[]) >>
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `not_fresh_at su x` by (irule local_ptrs_reserved_imm_base >> goal_assum drule >> simp[]) >>
  qpat_assum `!x. not_fresh_at su x ==> lookup_var x q = _ /\ _` (drule_then strip_assume_tac) >>
  qpat_assum `!x. lo <> 0 /\ ce.ce_imm_alloca = _ ==> _` (drule_all_then strip_assume_tac) >>
  simp[]
QED

Resume ctor_encoder_delayed_ctor_mods[ordinary_ghost]:
  `allocas_from 0 q /\ 0 <= q.vs_alloca_next /\ 0 <= w2n dst` by simp[allocas_from_def] >>
  irule unwrap_slot_copy_ghost_inv_at >> rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`G`,`fn`,`nb`,`t`,`su`,`w2n dst`,`tn`] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `si` >> simp[])
  >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `si` >> simp[])
  >> simp[]
QED

Finalise ctor_encoder_delayed_ctor_mods
