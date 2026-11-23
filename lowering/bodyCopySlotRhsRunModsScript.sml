(* The no-GAS materialization suffix, starting at the reached slot operand. *)
Theory bodyCopySlotRhsRunMods
Ancestors
  bodyFullPostsMods bodyFullUnwrapSlotOrigin exprPtrUnwrapAllocSemantic
  exprPtrUnwrapAllocationFrame exprPtrUnwrapAllocSeparation exprPtrUnwrapRetained
  exprPtrUnwrapStoragePost exprPtrUnwrapEnsureShape exprSimProps
  exprSimPtrTopLevelStorageCopy exprSimStorageCopy exprSimAbiEncodeMemoryLength
  fragGasOriginPtrDead assignTuplePtrAlloc storageNormalizationOwnershipPtr
  exprSimAlloc exprLoweringProps localPtrsProps bufferAllocationExecution
  slotCopyExecution freshWrites exprLowering loweringPosts ptrDiscipline
  venomState venomExecSemantics arithmetic words finite_map pred_set
  loweringStateRelDefs valueEncodingProps copyExecution emitHelper compileEnv
  bodyFullHashKeccakFixed bodyFullShadowBodyInv
  bodyPtrDefs vyperStorageFootprint venomMemDefs context exprSimFieldLayout
  abiBufferAllocationCode venomInst exprPtrUnwrapStorageSource bodyFullAbiEncodeOriginFloor

(* Flatten the single-slot and loop endpoints to the same physical frame.
   Neither branch depends on the expression which produced src. *)
Theorem copy_slot_suffix_effects:
  (loc = LocStorage \/ loc = LocTransient) /\
  (n <> 1 ==> ?cv ds.
     toplevel_copy_inv cv ds root src loc key (w2n dst) n allocated G0 tn0 n Gf tnf z /\
     (!x. not_fresh_at mid x ==> ~MEM x ds)) /\
  (n = 1 ==>
     z = (mstore (w2n dst) (slot_copy_word (if loc=LocStorage then SLOAD else TLOAD) allocated key)
       (update_var (STRING #"%" (toString mid.cs_next_var))
         (slot_copy_word (if loc=LocStorage then SLOAD else TLOAD) allocated key) allocated)
           with vs_inst_idx := k) /\
     tnf.t_mem = (tn0.t_mem DIFF {j | w2n dst <= j /\ j < w2n dst+32}) UNION
       {w2n dst+b | b IN key_taint (if loc=LocStorage then tn0.t_stor else tn0.t_trans) key} /\
     tnf.t_stor = tn0.t_stor /\ tnf.t_trans = tn0.t_trans /\ tnf.t_imm = tn0.t_imm /\
     (!x. x <> STRING #"%" (toString mid.cs_next_var) ==>
        FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tnf (Var x) = op_taint tn0 (Var x))) ==>
  copy_static z = copy_static allocated /\
  LENGTH allocated.vs_memory <= LENGTH z.vs_memory /\
  (!off len. off+len <= w2n dst \/ w2n dst+32*n <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len allocated.vs_memory) /\
  (!x. not_fresh_at mid x ==>
    lookup_var x z = lookup_var x allocated /\ FLOOKUP Gf x = FLOOKUP G0 x /\
    op_taint tnf (Var x) = op_taint tn0 (Var x)) /\
  (!j. j < n ==> mem_word_at (w2n dst+32*j) z.vs_memory =
    slot_copy_word (if loc=LocStorage then SLOAD else TLOAD) allocated (key+n2w j)) /\
  (!j b. j < n /\ b < 32 /\ w2n dst+32*j+b IN tnf.t_mem ==>
    b IN key_taint (if loc=LocStorage then tn0.t_stor else tn0.t_trans) (key+n2w j)) /\
  (!q. ~(w2n dst <= q /\ q < w2n dst+32*n) /\ q IN tnf.t_mem ==> q IN tn0.t_mem) /\
  tnf.t_stor = tn0.t_stor /\ tnf.t_trans = tn0.t_trans /\ tnf.t_imm = tn0.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> Cases_on `n = 1`
  >- suspend "single" >> suspend "loop"
QED

Resume copy_slot_suffix_effects[single]:
  qpat_x_assum `loc = LocStorage \/ loc = LocTransient` kall_tac >>
  qpat_x_assum `(_ = 1 ==> _)` (drule_then strip_assume_tac) >> gvs[] >>
  `!x. not_fresh_at mid x ==> x <> STRING #"%" (toString mid.cs_next_var)` by
    simp[not_fresh_at_def] >>
  rpt conj_tac
  >- simp[copy_static_def, mstore_def, write_memory_with_expansion_def, update_var_def]
  >- (qmatch_goalsub_abbrev_tac `mstore off w r` >>
      mp_tac (Q.INST [`s` |-> `r`, `off` |-> `off`, `w` |-> `w`]
        abi_encode_mstore_memory_length) >> simp[Abbr `r`, update_var_def])
  >- (rpt gen_tac >> disch_tac >> dep_rewrite.DEP_REWRITE_TAC [mstore_mem_bytes_at_disjoint] >>
      conj_tac >- decide_tac >> simp[update_var_def])
  >- (rpt strip_tac >>
      simp[mstore_def, write_memory_with_expansion_def, update_var_def, lookup_var_def,
           FLOOKUP_UPDATE] >> metis_tac[])
  >- simp[mstore_mem_word_at_same, WORD_ADD_0]
  >- (simp[WORD_ADD_0] >> metis_tac[]) >>
  rpt strip_tac >> gvs[key_taint_def] >> decide_tac
QED

Resume copy_slot_suffix_effects[loop]:
  qpat_x_assum `(_ <> 1 ==> _)` (drule_then strip_assume_tac) >>
  drule toplevel_copy_inv_content >>
  disch_then (strip_assume_tac o REWRITE_RULE [storage_copy_inv_def, copy_prefix_def]) >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (fs[toplevel_copy_inv_def, storage_copy_frame_def] >> metis_tac[])
  >- (rpt strip_tac >>
      `mem_word_at (w2n dst+32*j) z.vs_memory =
       copy_runtime_word loc allocated (key+n2w j)` by metis_tac[] >>
      Cases_on `loc=LocStorage` >> gvs[copy_runtime_word_def, slot_copy_word_def])
  >- suspend "loop_taint"
  >- (rpt strip_tac >> drule toplevel_copy_inv_memory_taint >>
      simp[toplevel_copy_taint_bound_def, toplevel_copy_region_def,
           toplevel_copy_translated_taint_def, SUBSET_DEF] >>
      disch_then (qspec_then `q` mp_tac) >> simp[] >> strip_tac >> gvs[]) >>
  fs[toplevel_copy_inv_def]
QED

Resume copy_slot_suffix_effects[loop_taint]:
  rpt strip_tac >> drule toplevel_copy_inv_memory_taint >>
  simp[toplevel_copy_taint_bound_def, toplevel_copy_region_def,
       toplevel_copy_translated_taint_def, SUBSET_DEF] >>
  disch_then (qspec_then `w2n dst+32*j+b` mp_tac) >>
  `w2n dst <= w2n dst+32*j+b /\ w2n dst+32*j+b < w2n dst+32*n` by decide_tac >>
  simp[] >> strip_tac >>
  rename1 `(key+n2w i,r) IN toplevel_copy_source_taint loc ts` >>
  `i = j /\ r = b` by intLib.COOPER_TAC >>
  qpat_x_assum `(key+n2w i,r) IN _` mp_tac >>
  simp[key_taint_def, toplevel_copy_source_taint_def]
QED

Finalise copy_slot_suffix_effects[local]

Theorem copy_slot_layout[local]:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_ensure_in_memory src loc nb n ctor imm sm = (op,sc) /\
  compile_alloc_buffer nb sm = (buf,mid) ==>
  sm.cs_next_id < sc.cs_next_id
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> drule_all ensure_slot_memory_split >>
  disch_then (strip_assume_tac o SRULE []) >>
  Cases_on `n = 1` >>
  gvs[compile_slot_to_memory_shape, slot_copy_final_def,
      emit_op_def, emit_void_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def, emit_def, fresh_var_def, fresh_id_def,
      compile_alloc_buffer_def]
QED

Theorem copy_slot_source_mods[local]:
  vv_post_mods H ctx func ce cx e es sa sm entry ee tv (LocatedValue t p) s /\
  p.ptr_location = slot_loc tr ==>
  t = post_value_type ce e /\
  ?key. eval_operand p.ptr_operand s = SOME key /\
    storage_holds cx tr t tv key ee s
Proof
  strip_tac >> qpat_x_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_post_mods_def] >> Cases_on `tr` >>
  gvs[slot_loc_def, vv_holds_mods_def, vv_holds_def]
QED

(* The allocation endpoint u and the final copy endpoint z are chosen once.
   The former has the input bytes, the latter the represented source value. *)
Theorem copy_slot_rhs_run_mods:
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\ ~is_word_type t /\
  unwrap_value ce (LocatedValue t p) sm = (op,sc) /\ fn_has_code sm sc func /\
  local_ptrs_reserved ce sm /\ fn_inst_ids_distinct func /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
  type_memory_bytes ce (post_value_type ce e) = type_memory_size rt /\
  type_memory_size rt < 2**64 /\ read_result cx tv ee = (INL v,ee) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es sa sm entry ee tv (LocatedValue t p) s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  ptr_vv_ok cx (post_value_type ce e) tv (LocatedValue t p) ee G tn s ==>
  ?root dst mid buf u z Gf tnf.
    op = Var root /\ not_fresh_at mid root /\
    compile_alloc_buffer (type_memory_size rt) sm = (buf,mid) /\
    buf.buf_operand = Var root /\ fn_has_code sm mid func /\
    MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_size rt))] [root]) (fn_insts func) /\
    sm.cs_next_var <= mid.cs_next_var /\ sm.cs_next_id < sc.cs_next_id /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gf,tnf)) /\
    ~z.vs_halted /\ z.vs_current_bb = sc.cs_current_bb /\ z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\ allocas_from lo z /\
    eval_operand op z = SOME dst /\ ptr_covers Gf tnf root z (type_memory_size rt) /\
    lo <= w2n dst /\ w2n dst + type_memory_size rt < dimword (:256) /\
    w2n dst + type_memory_size rt <= z.vs_alloca_next /\
    val_wf rt v /\
    (!mem. mem_agree_outside tnf.t_mem z.vs_memory mem ==> val_in_memory rt v (w2n dst) mem) /\
    FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n dst,type_memory_size rt) /\
    FLOOKUP z.vs_allocas sm.cs_next_id = SOME (w2n dst,type_memory_size rt) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee u) /\
    u.vs_memory = s.vs_memory /\ copy_static z = copy_static u /\
    copy_static z = copy_static (buffer_allocation_fields s sm.cs_next_id (type_memory_size rt)) /\
    (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
    (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x u) /\
    (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
    (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==>
      FLOOKUP u.vs_allocas aid = SOME ent /\ FLOOKUP z.vs_allocas aid = SOME ent) /\
    (!aid b len. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n dst) (type_memory_size rt) b len) /\
    (!name b len. local_region ce ee.scopes u name b len ==>
      regions_disjoint (w2n dst) (type_memory_size rt) b len) /\
    (!name b len. local_region ce ee.scopes s name b len ==>
      regions_disjoint (w2n dst) (type_memory_size rt) b len) /\
    LENGTH s.vs_memory <= LENGTH z.vs_memory /\
    (!off len. off+len <= w2n dst \/ w2n dst+type_memory_size rt <= off ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
    (!i. ~(w2n dst <= i /\ i < w2n dst+type_memory_size rt) /\ i IN tnf.t_mem ==> i IN tn.t_mem) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  `stmt_state_rel H0 ctx func ce cx ee s` by fs[vv_post_mods_def] >>
  `p.ptr_location = slot_loc (p.ptr_location = LocTransient)` by
    (qpat_assum `p.ptr_location = LocStorage \/ _` strip_assume_tac >>
     simp[slot_loc_def]) >>
  drule_all copy_slot_source_mods >> strip_tac >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `op_taint tn p.ptr_operand = {}` by fs[ptr_vv_ok_def] >>
  drule stmt_state_rel_allocas_below_fmp >> strip_tac >>
  qabbrev_tac `nb = type_memory_size rt` >>
  qabbrev_tac `n = type_slot_size rt` >>
  `nb = 32*n /\ (nb+31) DIV 32 = n` by
    simp[Abbr `nb`, Abbr `n`, type_memory_size_slots, slot_count_of_memory_size] >>
  `nb < dimword (:256) /\ n < 2**256` by fs[dimword_def] >>
  `compile_ensure_in_memory p.ptr_operand p.ptr_location nb n
      ce.ce_is_ctor ce.ce_imm_alloca sm = (op,sc)` by
    (qpat_x_assum `nb = 32*n` kall_tac >>
     qpat_assum `unwrap_value _ _ _ = _` mp_tac >>
     Cases_on `p.ptr_location` >> gvs[unwrap_value_def, slot_loc_def]) >>
  `32*n <= nb` by simp[] >>
  drule_all unwrap_ensure_slot_origin_execution >>
  disch_then (qspecl_then [`explicit`, `PG`, `G`] (qx_choosel_then
     [`root`, `dst`, `allocated`, `G0`, `tn0`, `Gf`, `tnf`, `z`, `mid`, `buf`, `u`]
     (map_every assume_tac o CONJUNCTS))) >>
  suspend "effects"
QED

Resume copy_slot_rhs_run_mods[effects]:
  `copy_static z = copy_static allocated /\
   LENGTH allocated.vs_memory <= LENGTH z.vs_memory /\
   (!off len. off+len <= w2n dst \/ w2n dst+32*n <= off ==>
     mem_bytes_at off len z.vs_memory = mem_bytes_at off len allocated.vs_memory) /\
   (!x. not_fresh_at mid x ==>
      lookup_var x z = lookup_var x allocated /\ FLOOKUP Gf x = FLOOKUP G0 x /\
      op_taint tnf (Var x) = op_taint tn0 (Var x)) /\
   (!j. j < n ==> mem_word_at (w2n dst+32*j) z.vs_memory =
     slot_copy_word (if p.ptr_location=LocStorage then SLOAD else TLOAD) allocated (key+n2w j)) /\
   (!j b. j < n /\ b < 32 /\ w2n dst+32*j+b IN tnf.t_mem ==>
     b IN key_taint (if p.ptr_location=LocStorage then tn0.t_stor else tn0.t_trans) (key+n2w j)) /\
   (!q. ~(w2n dst <= q /\ q < w2n dst+32*n) /\ q IN tnf.t_mem ==> q IN tn0.t_mem) /\
   tnf.t_stor = tn0.t_stor /\ tnf.t_trans = tn0.t_trans /\ tnf.t_imm = tn0.t_imm` by
    (irule copy_slot_suffix_effects >>
     conj_tac >- (qexistsl [`root`, `p.ptr_operand`] >>
       disch_tac >> qpat_assum `n <> 1 ==> _` (drule_then strip_assume_tac) >>
       qexistsl [`cv`, `ds`] >> asm_rewrite_tac[]) >>
     conj_tac >- (qexists `LENGTH sc.cs_current_insts` >> first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC) >>
  suspend "allocation"
QED

Resume copy_slot_rhs_run_mods[allocation]:
  drule_all unwrap_alloc_semantic_frames >> strip_tac >>
  drule compile_alloc_buffer_code >> strip_tac >>
  `root = STRING #"%" (toString sm.cs_next_var)` by fs[] >>
  `not_fresh_at mid root` by simp[not_fresh_at_def] >>
  `!x. not_fresh_at sm x ==> x <> root /\ not_fresh_at mid x` by
    (rpt strip_tac >> fs[not_fresh_at_def] >> decide_tac) >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) (fn_insts func)` by
    (drule_all buffer_alloc_code >> simp[]) >>
  drule_all alloca_step_exterior_ghost_ptr >>
  qpat_assum `G0 = _` (fn gth =>
    qpat_assum `tn0 = _` (fn tth =>
      disch_then (qspecl_then [`tn`, `PG`, `G`]
        (strip_assume_tac o REWRITE_RULE [GSYM gth, GSYM tth])))) >>
  `sm.cs_next_id < sc.cs_next_id` by (drule_all copy_slot_layout >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee u` by
    (rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (drule_then strip_assume_tac) >>
     qpat_x_assum `stmt_state_rel H0 _ _ _ _ _ s` kall_tac >>
     `stmt_state_rel H ctx func ce cx ee s` by fs[vv_post_mods_def] >>
     drule_all unwrap_alloc_semantic_frames >> simp[]) >>
  suspend "copy_frame"
QED

Resume copy_slot_rhs_run_mods[copy_frame]:
  `copy_static allocated = copy_static u /\ allocated.vs_memory = u.vs_memory /\
   (!x. lookup_var x allocated = lookup_var x u)` by
    (qpat_assum `allocated = _` SUBST1_TAC >> simp[copy_static_def, lookup_var_def]) >>
  `copy_static u = copy_static (buffer_allocation_fields s sm.cs_next_id nb)` by
    (qpat_assum `u = _` SUBST1_TAC >> simp[copy_static_def, update_var_def]) >>
  `copy_static z = copy_static u` by
    (qpat_assum `copy_static z = copy_static allocated` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  qpat_assum `copy_static z = copy_static u` (mp_then Any strip_assume_tac copy_static_fields) >>
  `!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x s /\
       FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     `x <> root /\ not_fresh_at mid x` by
       (qpat_assum `!x. not_fresh_at sm x ==> _ /\ _` (drule_then ACCEPT_TAC)) >>
     qpat_assum `!x. not_fresh_at mid x ==> _` (drule_then strip_assume_tac) >>
     qpat_assum `!x. x <> root ==> _` (drule_then strip_assume_tac) >>
     simp[Once (GSYM EQ_IMP_THM)]) >>
  `!off len. off+len <= w2n dst \/ w2n dst+nb <= off ==>
     mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!off len. _ ==> mem_bytes_at off len z.vs_memory = _`
       (qspecl_then [`off`, `len`] mp_tac) >>
     (impl_tac >- (qpat_assum `nb = 32*n` (fn th => pure_rewrite_tac[GSYM th]) >>
       first_assum ACCEPT_TAC)) >>
     asm_rewrite_tac[]) >>
  `!q. ~(w2n dst <= q /\ q < w2n dst+nb) /\ q IN tnf.t_mem ==> q IN tn.t_mem` by
    (gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
     `q IN tn0.t_mem` by
       (qpat_assum `!q. _ /\ q IN tnf.t_mem ==> _` (qspec_then `q` mp_tac) >>
        qpat_assum `nb = 32*n` (fn th => pure_rewrite_tac[GSYM th]) >>
        asm_rewrite_tac[]) >>
     qpat_assum `!i. ~(_ <= i /\ _) ==> _` (drule_then mp_tac) >>
     asm_rewrite_tac[]) >>
  `allocated.vs_accounts = s.vs_accounts /\ allocated.vs_transient = s.vs_transient /\
   allocated.vs_call_ctx = s.vs_call_ctx` by
    (qpat_assum `allocated = _` SUBST1_TAC >> qpat_assum `u = _` SUBST1_TAC >>
     simp[update_var_def]) >>
  `tn0.t_stor = tn.t_stor /\ tn0.t_trans = tn.t_trans /\ tn0.t_imm = tn.t_imm` by
    (qpat_assum `tn0 = _` SUBST1_TAC >> simp[normalization_alloca_key_taints]) >>
  suspend "source_value"
QED

Resume copy_slot_rhs_run_mods[source_value]:
  qpat_x_assum `t = post_value_type ce e` SUBST_ALL_TAC >>
  `val_wf rt v` by (drule_all storage_holds_value_bounds >> simp[]) >>
  `!load k. slot_copy_word load allocated k = slot_copy_word load s k` by
    (rpt gen_tac >> irule slot_copy_word_sources >> asm_rewrite_tac[]) >>
  `?v'. read_result cx tv ee = (INL v',ee) /\
      !mem. mem_agree_outside tnf.t_mem z.vs_memory mem ==>
        val_in_memory rt v' (w2n dst) mem` by
    (irule unwrap_storage_copied_robust >>
     goal_assum (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >>
     qexistsl [`p.ptr_location = LocTransient`, `key`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (qpat_assum `!j b. _ ==> b IN key_taint _ _` mp_tac >>
         qpat_assum `tn0.t_stor = tn.t_stor` (fn th => pure_rewrite_tac[th]) >>
         qpat_assum `tn0.t_trans = tn.t_trans` (fn th => pure_rewrite_tac[th]) >>
         qpat_assum `p.ptr_location = LocStorage \/ _` strip_assume_tac >>
         simp[Abbr `n`]) >>
     qpat_assum `!j. j < n ==> mem_word_at _ _ = _` mp_tac >>
     qpat_assum `p.ptr_location = LocStorage \/ _` strip_assume_tac >>
     simp[Abbr `n`]) >>
  pop_assum strip_assume_tac >>
  `v' = v` by fs[] >>
  qpat_x_assum `v' = v` SUBST_ALL_TAC >>
  suspend "destination"
QED

Resume copy_slot_rhs_run_mods[destination]:
  `lookup_var root u = SOME dst` by
    (qpat_assum `u = _` SUBST1_TAC >> simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `lookup_var root z = lookup_var root allocated /\ FLOOKUP Gf root = FLOOKUP G0 root /\
   op_taint tnf (Var root) = op_taint tn0 (Var root)` by
    (qpat_assum `!x. not_fresh_at mid x ==> _` (drule_then ACCEPT_TAC)) >>
  `eval_operand op z = SOME dst` by
    (qpat_assum `op = Var root` SUBST1_TAC >> rewrite_tac[eval_operand_def] >>
     qpat_assum `lookup_var root z = _` SUBST1_TAC >>
     qpat_assum `!x. lookup_var x allocated = _` (fn th => rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `ptr_covers G0 tn0 root allocated nb` by (drule_all unwrap_alloc_output_coverage >> simp[]) >>
  `ptr_covers Gf tnf root z nb` by
    (qpat_assum `lookup_var root z = _` (fn vth =>
       qpat_assum `FLOOKUP Gf root = _` (fn gth =>
         qpat_assum `op_taint tnf (Var root) = _` (fn tth =>
           pure_rewrite_tac[ptr_covers_def, vth, gth, tth]))) >>
     qpat_assum `ptr_covers G0 tn0 root allocated nb`
       (ACCEPT_TAC o REWRITE_RULE[ptr_covers_def])) >>
  `buffer_allocation_base s sm.cs_next_id + nb < dimword (:256)` by
    (qpat_x_assum `stmt_state_rel _ _ _ _ _ _ u` kall_tac >>
     drule_all unwrap_alloc_site_bound >> disch_then ACCEPT_TAC) >>
  `w2n dst = buffer_allocation_base s sm.cs_next_id` by
    (`buffer_allocation_base s sm.cs_next_id < dimword (:256)` by decide_tac >>
     qpat_assum `dst = n2w _` SUBST1_TAC >> simp[w2n_n2w]) >>
  `lo <= buffer_allocation_base s sm.cs_next_id` by
    (qpat_assum `allocas_from lo s` mp_tac >>
     qpat_assum `lo <= s.vs_alloca_next` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp[allocas_from_def, buffer_allocation_base_def] >>
     Cases_on `FLOOKUP s.vs_allocas sm.cs_next_id` >> simp[] >>
     rename1 `SOME ent` >> PairCases_on `ent` >> simp[] >> metis_tac[]) >>
  `alloca_next_valid u` by
    fs[stmt_state_rel_def, alloca_inv_def] >>
  `w2n dst + nb <= z.vs_alloca_next` by
    (qpat_assum `z.vs_alloca_next = u.vs_alloca_next` SUBST1_TAC >>
     irule instMemFrontierTheory.alloca_region_below_frontier >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl [`sm.cs_next_id`, `w2n dst`, `nb`] >>
     asm_rewrite_tac[LESS_EQ_REFL]) >>
  `!name b len. local_region ce ee.scopes s name b len ==>
     regions_disjoint (w2n dst) nb b len` by
    (rpt strip_tac >>
     qpat_x_assum `stmt_state_rel _ _ _ _ _ _ u` kall_tac >>
     drule_all unwrap_alloc_local_separation >>
     qpat_assum `w2n dst = _` (fn th => rewrite_tac[th, loweringStateRelDefsTheory.regions_disjoint_def])) >>
  suspend "join"
QED

Resume copy_slot_rhs_run_mods[join]:
  qpat_assum `copy_static u = copy_static _` (mp_then Any strip_assume_tac copy_static_fields) >>
  `~z.vs_halted` by
    (qpat_assum `z.vs_halted = _` SUBST1_TAC >>
     qpat_assum `u.vs_halted = _` SUBST1_TAC >>
     Cases_on `FLOOKUP s.vs_allocas sm.cs_next_id` >>
     simp[buffer_allocation_fields_def]) >>
  `allocas_from lo z` by
    (qpat_assum `gas_origin_ptr_path _ (s,G,tn) [] (OK z,_,_)`
       (mp_then Any (qspec_then `lo` mp_tac) abi_encode_origin_path_allocas_from) >>
     asm_rewrite_tac[] >> disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  qexistsl [`root`, `dst`, `mid`, `buf`, `u`, `z`, `Gf`, `tnf`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qpat_assum `mid.cs_next_var = _` SUBST1_TAC >> simp[])
  >- (gen_tac >> irule gas_origin_ptr_path_from_no_dead >> first_assum ACCEPT_TAC)
  >- (qpat_assum `w2n dst = _` SUBST1_TAC >> first_assum ACCEPT_TAC)
  >- (qpat_assum `w2n dst = _` SUBST1_TAC >> first_assum ACCEPT_TAC)
  >- (qpat_assum `z.vs_allocas = _` SUBST1_TAC >> first_assum ACCEPT_TAC)
  >- (qpat_assum `copy_static z = copy_static u` SUBST1_TAC >> first_assum ACCEPT_TAC)
  >- (rpt strip_tac >>
      qpat_assum `!x. not_fresh_at mid x ==> _` (drule_then strip_assume_tac) >>
      qpat_assum `!x. lookup_var x allocated = _` (fn th => pure_rewrite_tac[GSYM th]) >>
      first_assum ACCEPT_TAC)
  >- (qpat_assum `z.vs_allocas = _` SUBST1_TAC >> simp[] >>
      rpt strip_tac >>
      qpat_assum `!id entry. FLOOKUP s.vs_allocas id = SOME entry ==> _`
        (drule_then ACCEPT_TAC))
  >- (qpat_assum `allocated.vs_memory = _` (fn ath =>
        qpat_assum `u.vs_memory = _` (fn uth =>
          qpat_assum `LENGTH allocated.vs_memory <= _`
            (ACCEPT_TAC o REWRITE_RULE[ath, uth])))) >>
  asm_rewrite_tac[]
QED

Finalise copy_slot_rhs_run_mods
