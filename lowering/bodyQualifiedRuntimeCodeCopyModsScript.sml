(* Force a qualified runtime immutable at the raw lookup's code cursor. *)
Theory bodyQualifiedRuntimeCodeCopyMods
Ancestors
  bodyFullPostsMods bodyFullShadowBodyInv bodyFullUnwrapCodeRuntimeRun
  bodyFullUnwrapCodeRuntimeFrame vyperStorageFootprint ptrDiscipline
  exprPtrUnwrapCodeCopyShape exprPtrCodeCopyPost exprPtrCleanBufferPost
  exprPtrUnwrapAllocSemantic exprPtrUnwrapRetained exprPtrUnwrapAllocationFrame
  exprPtrUnwrapAllocation exprPtrUnwrapAllocSeparation bodyFullUnwrapCodePureFrame
  bufferAllocationExecution valueEncodingProofs
  exprSimCopy exprSimStorageCopy exprSimMemDefs bodyFieldMemoryProps
  fragGasOriginPtrDead bodyFullHashKeccakFixed immutableCopyExecution
  valueEncodingProps valueEncodingDefs exprSimProps bodyInvSplit
  loweringPosts loweringStateRelDefs bodyPtrDefs exprLowering exprLoweringProps
  compileEnv context venomInst venomState exprSimAlloc freshWrites words arithmetic pred_set

Theorem runtime_copy_data_value[local]:
  val_wf rt v /\ val_in_memory rt v (w2n src) u.vs_data_section /\
  w2n src + type_memory_size rt < dimword(:256) /\
  w2n dst + type_memory_size rt < dimword(:256) /\
  z.vs_memory = (immutable_transfers F F src dst (type_slot_size rt) 0 u).vs_memory ==>
  val_in_memory rt v (w2n dst) z.vs_memory
Proof
  strip_tac >> irule val_in_memory_relocate >> simp[] >>
  qexistsl_tac [`u.vs_data_section`, `type_memory_size rt`, `w2n src`] >> simp[] >>
  Cases_on `type_slot_size rt = 0`
  >- gvs[type_memory_size_slots, mem_bytes_at_def] >>
  `immutable_transfers F F src dst (type_slot_size rt) 0 u =
   write_memory_with_expansion (w2n dst)
     (mem_bytes_at (w2n src) (type_memory_size rt) u.vs_data_section) u` by
    (qspecl_then [`type_slot_size rt`, `w2n src`, `w2n dst`, `0`, `u`] mp_tac
       immutable_runtime_transfers_snapshot >>
     simp[mem_bytes_at_def, type_memory_size_slots] >> gvs[type_memory_size_slots]) >>
  qspec_then `w2n dst` mp_tac write_memory_mem_bytes_at_same >>
  disch_then (qspecl_then
    [`mem_bytes_at (w2n src) (type_memory_size rt) u.vs_data_section`, `u`] mp_tac) >>
  simp[]
QED

Theorem runtime_copy_immutable_frame[local]:
  ~cenv.ce_is_ctor /\ z.vs_data_section = s.vs_data_section /\
  immutable_frame_mods func cenv cx es s ==>
  immutable_frame_mods func cenv cx es z
Proof
  strip_tac >> gvs[immutable_frame_mods_def, immutables_rel_mods_def, immutables_rel_def,
                   immutable_alloca_sep_mods_def, immutable_alloca_sep_def, immutable_decl_sep_def] >>
  first_assum ACCEPT_TAC
QED

Theorem runtime_copy_ghost_bridge[local]:
  ghost_inv_at_mods D 0 d cenv cx es G tn s <=> ghost_inv_at D 0 d cenv cx es G tn s
Proof
  simp[ghost_inv_at_mods_def, ghost_inv_at_def]
QED

(* The raw qualified lookup emits no instructions. The source bytes are the
   selected owner's runtime data, while the locals still belong to cenv. *)
Theorem qualified_runtime_code_copy_read_mods:
  ~cenv.ce_is_ctor /\
  unwrap_value cenv (LocatedValue (post_value_type cenv e)
                         (mk_ptr (Lit src) LocCode)) sa = (op,sb) /\
  post_value_type cenv e = expr_type e /\
  lowered_value_type cenv e = expr_type e /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME rt /\
  type_memory_bytes cenv (expr_type e) = type_memory_size rt /\
  val_wf rt v /\ val_in_memory rt v (w2n src) s.vs_data_section /\
  w2n src + type_memory_size rt <= LENGTH s.vs_data_section /\
  w2n src + type_memory_size rt < dimword(:256) /\
  ee.scopes = es.scopes /\ fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  alloca_history func s /\ ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s /\
    immutable_frame_mods func cenv cx ee s /\
    storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods (DF H) 0 d cenv cx ee G tn s) ==>
  ?z G' tn'. !H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,0,explicit,ctx,func,PG) (s,G,tn) [] (OK z,G',tn') /\
    expr_post_mods H ctx func cenv cx e es sa sb s ee v op z /\
    expr_store_bound cx (post_value_type cenv e) v op z /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    s.vs_alloca_next <= z.vs_alloca_next /\
    ghost_inv_at_mods (DF H) 0 d cenv cx ee G' tn' z /\
    ptr_val_ok cx (post_value_type cenv e) v op G' tn' z /\
    ptr_buf_ok cenv e op G' z /\ ghost_kept_at 0 cenv es sa G tn s G' tn'
Proof
  strip_tac >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  qabbrev_tac `nb = type_memory_size rt` >>
  `(nb + 31) DIV 32 = type_slot_size rt` by
    simp[Abbr `nb`, type_memory_size_slots, ADD_DIV_ADD_DIV] >>
  `compile_ensure_in_memory (Lit src) LocCode nb (type_slot_size rt)
    F cenv.ce_imm_alloca sa = (op,sb)` by gvs[unwrap_value_def, mk_ptr_def] >>
  drule_all ensure_runtime_code_layout >> simp[] >> strip_tac >>
  `nb = 32 * type_slot_size rt` by simp[Abbr `nb`, type_memory_size_slots] >>
  `nb < dimword(:256)` by decide_tac >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s)` by
    drule_then ACCEPT_TAC stmt_state_rel_allocas_below_fmp >>
  `allocas_from 0 s` by fs[ghost_inv_at_mods_def] >>
  `eval_operand (Lit src) s = SOME src /\ op_taint tn (Lit src) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  `w2n src + 32 * type_slot_size rt <= LENGTH s.vs_data_section /\
   w2n src + 32 * type_slot_size rt < dimword(:256)` by decide_tac >>
  `0 <= s.vs_alloca_next` by simp[] >>
  `!x. Lit src = Var x ==> not_fresh_at sa x` by simp[] >>
  drule_all (Q.INST [`lo` |-> `0`, `src` |-> `Lit srcword`] runtime_code_copy_origin_execution) >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`,
    `<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`]
    strip_assume_tac) >>
  rename1 `copy_runtime_frame mid a sb z` >>
  rename1 `lookup_var root a = SOME dst` >>
  suspend "physical"
QED

Resume qualified_runtime_code_copy_read_mods[physical]:
  `copy_old_operand mid (Lit src) /\ copy_old_operand mid (Var root)` by
    (drule_all allocated_copy_operands_old >> simp[copy_old_operand_def]) >>
  `eval_operand (Lit src) a = SOME src /\ eval_operand (Var root) a = SOME dst` by
    simp[eval_operand_def] >>
  `compile_imm_copy_to_memory F cenv.ce_imm_alloca (Lit src) (Var root)
    (type_slot_size rt) 0 mid = ((),sb)` by
    (qpat_assum `buf.buf_operand = Var root` (fn th =>
       qpat_assum `compile_imm_copy_to_memory _ _ _ buf.buf_operand _ _ _ = _`
         (ACCEPT_TAC o REWRITE_RULE [th]))) >>
  drule_all code_copy_same_endpoint_memory >> disch_tac >>
  `a.vs_data_section = s.vs_data_section` by
    (Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id` >>
     simp[bufferAllocationExecutionTheory.buffer_allocation_fields_def, update_var_def]) >>
  qpat_assum `copy_runtime_frame _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [copy_runtime_frame_def]) >>
  drule copy_static_fields >> strip_tac >>
  `z.vs_data_section = s.vs_data_section` by simp[] >>
  `w2n dst + type_memory_size rt < dimword(:256)` by
    (qpat_assum `w2n dst + nb < _` mp_tac >> simp[Abbr `nb`]) >>
  `w2n src + type_memory_size rt < dimword(:256)` by
    (qpat_assum `w2n src + nb < _` mp_tac >> simp[Abbr `nb`]) >>
  `val_in_memory rt v (w2n src) a.vs_data_section` by simp[] >>
  drule_all runtime_copy_data_value >> disch_tac >>
  drule_all runtime_code_copy_memory_frame >> strip_tac >>
  `LENGTH a.vs_memory <= LENGTH z.vs_memory` by simp[] >>
  `a.vs_memory = s.vs_memory /\ a.vs_accounts = s.vs_accounts /\
   a.vs_transient = s.vs_transient /\ a.vs_call_ctx = s.vs_call_ctx /\
   a.vs_immutables = s.vs_immutables` by (drule unwrap_alloc_runtime_frame >> simp[]) >>
  `op = Var root` by simp[] >>
  `eval_operand (Var root) z = SOME dst` by
    (drule_all copy_runtime_frame_operand >> disch_then (fn th => simp[th])) >>
  suspend "frames"
QED

Resume qualified_runtime_code_copy_read_mods[frames]:
  `u = update_var root dst (buffer_allocation_fields s sa.cs_next_id nb)` by
    asm_rewrite_tac[] >>
  drule_all unwrap_alloc_semantic_frames >> strip_tac >>
  `a.vs_allocas = u.vs_allocas` by
    (qpat_assum `a = u with vs_inst_idx := _` (fn th => rewrite_tac[th]) >> simp[]) >>
  `z.vs_allocas = u.vs_allocas` by
    (qpat_assum `z.vs_allocas = a.vs_allocas` (fn th => rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `FLOOKUP z.vs_allocas sa.cs_next_id = SOME (w2n dst,nb)` by
    (qpat_assum `z.vs_allocas = u.vs_allocas` (fn th => rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
     FLOOKUP z.vs_allocas aid = SOME entry` by
    (qpat_assum `z.vs_allocas = u.vs_allocas` (fn th => rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) (fn_insts func)` by
    (drule unwrap_alloc_generated_code >> strip_tac >> drule_all buffer_alloc_code >> gvs[]) >>
  `sa.cs_next_id < sb.cs_next_id` by
    (drule loweringHaltTheory.compile_alloc_buffer_parts >> strip_tac >>
     `ci_mono mid sb` by
       (qpat_assum `compile_imm_copy_to_memory _ _ _ (Var root) _ _ _ = _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> strip_tac >>
        metis_tac[ci_mono_compile_imm_copy_to_memory, pairTheory.SND]) >>
     qpat_assum `ci_mono mid sb` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
     decide_tac) >>
  `!off len. off+len <= w2n dst \/ w2n dst+nb <= off ==>
     mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory` by
    (rpt strip_tac >> qpat_assum `a.vs_memory = s.vs_memory` (fn th => rewrite_tac[GSYM th]) >>
     qpat_assum `!at len. _ ==> _ = mem_bytes_at at len a.vs_memory`
       (qspecl_then [`off`,`len`] mp_tac) >>
     (impl_tac >- (qpat_assum `Abbrev (nb = _)`
        (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >> decide_tac)) >>
     disch_then ACCEPT_TAC) >>
  `buffer_allocation_base s sa.cs_next_id < dimword (:256)` by
    (qpat_x_assum `stmt_state_rel _ _ _ _ _ _ u` kall_tac >>
     drule_all unwrap_alloc_site_bound >> decide_tac) >>
  `w2n dst = buffer_allocation_base s sa.cs_next_id` by simp[] >>
  `!name b len. local_region cenv ee.scopes s name b len ==>
     w2n dst+nb <= b \/ b+len <= w2n dst` by
    (rpt strip_tac >> drule_all unwrap_alloc_local_separation >> asm_rewrite_tac[]) >>
  `!name b len. local_region cenv ee.scopes z name b len ==>
     w2n dst+nb <= b \/ b+len <= w2n dst` by
    (rpt strip_tac >>
     `!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s` by
       (rpt strip_tac >> qpat_assum `!x. not_fresh_at sa x ==> lookup_var x z = _ /\ _`
          drule >> simp[]) >>
     qpat_x_assum `!x. not_fresh_at sa x ==> lookup_var x u = _` kall_tac >>
     drule_all copy_buffer_local_region_frame >>
     disch_then (qspecl_then [`ee.scopes`,`name`,`b`,`len`]
       (fn th => qpat_assum `local_region cenv ee.scopes z name b len`
          (assume_tac o REWRITE_RULE [th]))) >>
     qpat_assum `!name b len. local_region cenv ee.scopes s name b len ==> _`
       irule >> qexists_tac `name` >> first_assum ACCEPT_TAC) >>
  `pure_frame cenv func es sa s z` by
    (irule unwrap_alloc_copy_pure_frame >>
     goal_assum (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
     qexistsl_tac [`w2n dst`,`root`,`u`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     rpt strip_tac >>
     `local_region cenv ee.scopes s name b len` by
       (qpat_assum `ee.scopes = es.scopes` (fn th => rewrite_tac[th]) >>
        first_assum ACCEPT_TAC) >>
     qpat_assum `!name b len. local_region cenv ee.scopes s name b len ==> _` drule >>
     tautLib.TAUT_TAC) >>
  suspend "posts"
QED

Resume qualified_runtime_code_copy_read_mods[posts]:
  `local_ptrs_reserved cenv mid` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func cenv cx ee z` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
     `stmt_state_rel H ctx func cenv cx ee a` by
       (qpat_assum `a = u with vs_inst_idx := _` (fn th => rewrite_tac[th]) >>
        simp[stmt_state_rel_inst_idx] >>
        qpat_x_assum `stmt_state_rel H0 _ _ _ _ _ u` kall_tac >>
        drule_all unwrap_alloc_semantic_frames >> simp[]) >>
     irule copy_buffer_state_rel_frame >>
     goal_assum (drule_at (Pat `copy_static z = copy_static a`)) >>
     goal_assum (drule_at (Pat `MEM _ (fn_insts _)`)) >>
     qexistsl_tac [`w2n dst`,`mid`,`nb`] >>
     simp_tac (srw_ss()) [mk_inst_def] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
     >- (rpt strip_tac >>
         `local_region cenv ee.scopes u name lb len` by
           (qpat_assum `a = u with vs_inst_idx := _`
              (fn th => qpat_assum `local_region cenv ee.scopes a _ _ _`
                 (mp_tac o REWRITE_RULE [th])) >>
            rewrite_tac[logTupleOwnershipPtrTheory.log_local_region_inst_idx]) >>
         qpat_assum `!name b len. local_region cenv ee.scopes u name b len ==> _` drule >>
         rewrite_tac[regions_disjoint_def])
     >- (rpt gen_tac >> disch_tac >>
         qpat_assum `a.vs_memory = s.vs_memory` (fn th => rewrite_tac[th]) >>
         qpat_assum `!off len. _ ==> _ = mem_bytes_at off len s.vs_memory` irule >>
         first_assum ACCEPT_TAC)
     >> (qpat_assum `a.vs_allocas = u.vs_allocas` (fn th => rewrite_tac[th]) >>
         first_assum ACCEPT_TAC)) >>
  suspend "value"
QED

Resume qualified_runtime_code_copy_read_mods[value]:
  `!n b len. local_region cenv es.scopes s n b len ==>
    mem_bytes_at b len z.vs_memory = mem_bytes_at b len s.vs_memory` by
    (qpat_assum `pure_frame cenv func es sa s z`
       (strip_assume_tac o REWRITE_RULE [pure_frame_def]) >> first_assum ACCEPT_TAC) >>
  `locals_kept cenv es ee s z` by
    (irule locals_kept_regions_tail >> qexists_tac `s` >>
     conj_tac >- first_assum ACCEPT_TAC >> simp[locals_kept_refl]) >>
  `val_footprint rt v <= nb` by simp[Abbr `nb`, val_footprint_le] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> expr_post H ctx func cenv cx e es sa sb s ee v (Var root) z` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ s /\ _`
       (drule_then strip_assume_tac) >>
     irule copy_buffer_expr_post >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
     >- (rpt strip_tac >>
         qpat_assum `!x. not_fresh_at _ x ==> lookup_var x z = _ /\ _`
           (drule_then strip_assume_tac) >> asm_rewrite_tac[])
     >- (rpt strip_tac >>
         qpat_assum `!off len. _ ==> _ = mem_bytes_at off len s.vs_memory` irule >>
         `regions_disjoint (w2n dst) nb off len` by
           (qpat_assum `!id b len. id < _ /\ _ ==> regions_disjoint _ _ _ _` irule >>
            qexists_tac `id` >> asm_rewrite_tac[]) >>
         pop_assum (mp_tac o REWRITE_RULE [loweringStateRelDefsTheory.regions_disjoint_def]) >>
         rpt (pop_assum kall_tac) >> decide_tac)
     >- (strip_tac >> first_assum ACCEPT_TAC)
     >- (qexistsl_tac [`sa.cs_next_id`,`nb`,`rt`,`dst`] >>
         rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >> decide_tac)
     >> qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ z` irule >>
     first_assum ACCEPT_TAC) >>
  suspend "ghosts"
QED

Resume qualified_runtime_code_copy_read_mods[ghosts]:
  `tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
   (!i. i < buffer_allocation_base s sa.cs_next_id \/
        buffer_allocation_base s sa.cs_next_id + nb <= i ==>
        (i IN tm.t_mem <=> i IN tn.t_mem))` by
    (qpat_x_assum `stmt_state_rel H0 _ _ _ _ _ u` kall_tac >>
     drule_all unwrap_alloc_taint_frame >>
     disch_then (qspec_then `tn` mp_tac) >>
     qpat_assum `tm = step_taint _ _ _ tn` (fn th => rewrite_tac[GSYM th])) >>
  `tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm` by
    (qpat_assum `tf.t_stor = tm.t_stor` (fn s =>
       qpat_assum `tf.t_trans = tm.t_trans` (fn t =>
         qpat_assum `tf.t_imm = tm.t_imm` (fn i => rewrite_tac[s,t,i]))) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `sa.cs_next_var <= sa.cs_next_var /\ 32 * type_slot_size rt <= nb /\
   0 <= w2n dst /\ 0 <= z.vs_alloca_next` by asm_rewrite_tac[LESS_EQ_REFL, ZERO_LESS_EQ] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       ghost_inv_at_mods (DF H) 0 d cenv cx ee HG tf
         (z with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (gen_tac >> disch_tac >>
     qpat_x_assum `stmt_state_rel H0 _ _ _ _ _ s` kall_tac >>
     qpat_x_assum `stmt_state_rel H0 _ _ _ _ _ u` kall_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ s /\ _`
       (drule_then strip_assume_tac) >>
     qpat_x_assum `ghost_inv_at_mods (DF H) _ _ _ _ _ G tn s`
       (assume_tac o REWRITE_RULE [runtime_copy_ghost_bridge]) >>
     rewrite_tac[runtime_copy_ghost_bridge] >>
     drule_all (Q.INST [`lo` |-> `0`] runtime_code_copy_ghost_inv_at) >>
     disch_then ACCEPT_TAC) >>
  suspend "retained"
QED

Resume qualified_runtime_code_copy_read_mods[retained]:
  `!i. i IN tf.t_mem <=> i IN tm.t_mem /\ ~(w2n dst <= i /\ i < w2n dst + nb)` by
    (qpat_assum `tf.t_mem = _ DIFF _` (fn th => rewrite_tac[th, IN_DIFF]) >>
     qpat_assum `nb = 32 * type_slot_size rt` (fn th => simp_tac (srw_ss()) [th])) >>
  `!i. w2n dst <= i /\ i < w2n dst + nb ==> i NOTIN tf.t_mem` by
    (pop_assum (fn th => simp_tac (srw_ss()) [th])) >>
  `tf.t_mem SUBSET tn.t_mem` by
    (rewrite_tac[SUBSET_DEF] >> gen_tac >>
     qpat_assum `!i. i IN tf.t_mem <=> _` (fn th => rewrite_tac[th]) >>
     strip_tac >>
     qpat_assum `!i. i < _ \/ _ <= i ==> (i IN tm.t_mem <=> i IN tn.t_mem)`
       (qspec_then `x` mp_tac) >>
     qpat_assum `w2n dst = buffer_allocation_base _ _` (fn th => rewrite_tac[GSYM th]) >>
     impl_tac >- (qpat_assum `~(_ <= _ /\ _ < _)` mp_tac >>
                  rpt (pop_assum kall_tac) >> decide_tac) >>
     disch_then (fn th => rewrite_tac[GSYM th]) >> first_assum ACCEPT_TAC) >>
  `ghost_kept_at 0 cenv es sa G tn s HG tf` by
    (rewrite_tac[ghost_kept_at_def] >> conj_tac
     >- (rpt strip_tac >>
         qpat_assum `!x. not_fresh_at _ x ==> lookup_var x z = _ /\ _`
           (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
     qpat_assum `tf.t_mem SUBSET tn.t_mem` (assume_tac o REWRITE_RULE [SUBSET_DEF]) >>
     conj_tac >> rpt strip_tac >> first_x_assum irule >> first_assum ACCEPT_TAC) >>
  suspend "landing"
QED

Resume qualified_runtime_code_copy_read_mods[landing]:
  qabbrev_tac `q = z with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `eval_operand (Var root) q = SOME dst` by
    (qpat_assum `eval_operand (Var root) z = SOME dst` mp_tac >>
     simp_tac (srw_ss()) [Abbr `q`,eval_operand_def,lookup_var_def]) >>
  `ptr_covers HG tf root q nb` by
    (qpat_assum `ptr_covers HG tf root z nb` mp_tac >>
     simp_tac (srw_ss()) [Abbr `q`,ptr_covers_def,lookup_var_def]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       expr_post H ctx func cenv cx e es sa sb s ee v (Var root) q` by
    (simp_tac (srw_ss()) [Abbr `q`,body_field_expr_post_inst_idx] >>
     first_assum ACCEPT_TAC) >>
  `expr_post H0 ctx func cenv cx e es sa sb s ee v (Var root) q` by
    (first_x_assum irule >> first_assum ACCEPT_TAC) >>
  `type_memory_bytes cenv (lowered_value_type cenv e) <= nb /\
   type_memory_size rt <= nb` by
    (conj_tac >- (qpat_assum `lowered_value_type cenv e = expr_type e`
                    (fn ty => qpat_assum `type_memory_bytes cenv (expr_type e) = nb`
                      (fn sz => rewrite_tac[ty,sz,LESS_EQ_REFL]))) >>
     simp_tac (srw_ss()) [Abbr `nb`]) >>
  `ptr_val_ok cx (expr_type e) v (Var root) HG tf q /\
   ptr_buf_ok cenv e (Var root) HG q` by
    (qpat_assum `post_value_type cenv e = expr_type e` (fn th => rewrite_tac[GSYM th]) >>
     `~is_word_type (post_value_type cenv e) /\
      evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt` by asm_rewrite_tac[] >>
     qpat_x_assum `expr_post H0 _ _ _ _ _ _ _ _ _ _ _ _ q`
       (mp_then (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`) mp_tac clean_buffer_pointer_posts) >>
     disch_then irule >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`nb`,`rt`,`dst`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `expr_store_bound cx (expr_type e) v (Var root) q` by
    (qpat_assum `expr_post H0 _ _ _ _ _ _ _ _ _ _ _ _ q`
       (mp_then (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`) mp_tac expr_store_bound_capacity) >>
     disch_then irule >> conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     qx_gen_tac `tv` >>
     qpat_assum `evaluate_type _ (expr_type e) = SOME rt`
       (fn th => simp_tac (srw_ss()) [th]) >>
     disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC assume_tac) >> qexists_tac `dst` >>
     conj_tac >- first_assum ACCEPT_TAC >> disj2_tac >>
     qpat_assum `w2n dst + nb <= z.vs_alloca_next` mp_tac >>
     simp_tac (srw_ss()) [Abbr `q`, Abbr `nb`]) >>
  suspend "finish"
QED

Resume qualified_runtime_code_copy_read_mods[finish]:
  `q.vs_data_section = s.vs_data_section /\ q.vs_current_bb = sb.cs_current_bb /\
   q.vs_inst_idx = LENGTH sb.cs_current_insts /\ s.vs_alloca_next <= q.vs_alloca_next` by
    (simp_tac (srw_ss()) [Abbr `q`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `immutable_frame_mods func cenv cx ee q` by
    (irule runtime_copy_immutable_frame >> conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `s` >> conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`q`,`HG`,`tf`] >> gen_tac >> disch_tac >>
  qpat_assum `op = Var root` (fn th => rewrite_tac[th,expr_post_mods_def]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
  >- (irule gas_origin_ptr_path_from_no_dead >> first_assum ACCEPT_TAC)
  >- (qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post H _ _ _ _ _ _ _ _ _ _ _ _ q`
        irule >> first_assum ACCEPT_TAC)
  >- (`stmt_state_rel H ctx func cenv cx ee q` by
        (simp_tac (srw_ss()) [Abbr `q`, stmt_state_rel_inst_idx] >>
         qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ z` irule >>
         first_assum ACCEPT_TAC) >>
      pop_assum (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) ACCEPT_TAC
                   stmt_state_rel_allocas_below_fmp)) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> ghost_inv_at_mods _ _ _ _ _ _ _ _ q` irule >>
  first_assum ACCEPT_TAC
QED

Finalise qualified_runtime_code_copy_read_mods
