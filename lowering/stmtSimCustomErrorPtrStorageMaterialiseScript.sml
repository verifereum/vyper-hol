Theory stmtSimCustomErrorPtrStorageMaterialise
Ancestors
  exprSimPtrTopLevelStorageSemantic exprSimPtrTopLevelStorageDecode
  exprSimPtrTopLevelStorageEnsure exprSimPtrTopLevelStorageAlloc
  exprSimPtrTopLevelStoragePost exprSimPtrTopLevelStorageCopy exprSimCopy exprSimStorageCopy exprSimAlloc
  exprSimUnwrap exprSimUnwrapProps exprLowering exprLoweringProps loweringPosts compileEnv loweringStateRelDefs
  context venomState venomInst words ptrDiscipline fragGasPathPtr
  ghostPcTransportPtr loweringHalt fragExec pred_set bodyPtrDefs
  exprSimPtrTopLevelStorageBranch exprSimPtrTopLevelStorageFrame
  accountsRelProps valueEncodingProps storageDecodeMemory vyperStorageBackend
  vyperTypeValues vyperValue vyperStorage vyperState exprSimProps

(* The source is an old operand, not necessarily a literal.  Allocation
   preserves its value and its scalar taint before either copy suffix. *)
Theorem custom_error_storage_ensure_effects[local]:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_ensure_in_memory src loc nb n ctor imm sa = (op,sb) /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  fn_has_code sa sb fn /\ stmt_state_rel ctx fn cenv cx es s /\
  fn_inst_ids_distinct fn /\ local_ptrs_reserved cenv sa /\
  nb = 32*n /\ nb < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf p.
    op = Var p /\ gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK t) /\
    ptr_covers Gf tnf p t nb /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ?u w.
      stmt_state_rel ctx fn cenv cx es u /\ u.vs_memory = s.vs_memory /\
      lookup_var p u = SOME w /\ lookup_var p t = SOME w /\
      copy_prefix loc a (w2n w) n u n t /\ copy_static t = copy_static u /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
      tnf.t_mem SUBSET toplevel_copy_taint_bound loc a (w2n w) tn n /\
      (!aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
        regions_disjoint (w2n w) nb b len) /\
      (!name b len. local_region cenv es.scopes u name b len ==>
        regions_disjoint (w2n w) nb b len) /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
      u.vs_call_ctx = s.vs_call_ctx /\ u.vs_accounts = s.vs_accounts /\
      u.vs_transient = s.vs_transient /\
      t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
      t.vs_transient = s.vs_transient /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry) /\
      FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,nb) /\
      sa.cs_next_id < sb.cs_next_id /\
      LENGTH u.vs_memory <= LENGTH t.vs_memory /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP u.vs_allocas aid = SOME entry) /\
      FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,nb) /\
      (?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
        inst.inst_id = sa.cs_next_id)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `compile_ensure_in_memory src loc nb n ctor imm =
    do buf <- compile_alloc_buffer nb;
       (if n = 1 then
          do v <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
             emit_void MSTORE [buf.buf_operand;v] od
        else do compile_word_copy_loop src buf.buf_operand n loc LocMemory F;
                return () od);
       return buf.buf_operand od` by
    (irule ensure_storage_memory_layout >> simp[]) >>
  qpat_x_assum `compile_ensure_in_memory _ _ _ _ _ _ sa = _` mp_tac >>
  asm_rewrite_tac[] >>
  Cases_on `compile_alloc_buffer (32*n) sa` >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gnvs[] >>
  drule_all (SRULE[comp_ignore_bind_def] storage_copy_suffix_extends) >> strip_tac >>
  drule compile_alloc_buffer_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all toplevel_alloc_buffer_ptr_run >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  qpat_x_assum `q.buf_operand = op /\ _` strip_assume_tac >> gnvs[] >>
  `n < 2**256` by (fs[dimword_def] >> decide_tac) >>
  qabbrev_tac `s1 = u with vs_inst_idx := LENGTH r.cs_current_insts` >>
  `u.vs_labels = s.vs_labels` by metis_tac[hash_alloc_buffer_labels] >>
  `eval_operand src s1 = SOME a /\ op_taint tnf src = {}` by
    (Cases_on `src` >> gvs[eval_operand_def, op_taint_def, Abbr `s1`, lookup_var_def] >>
     metis_tac[]) >>
  `lookup_var p s1 = SOME w /\ ptr_covers Gf tnf p s1 (32*n) /\
   w2n w+32*n < 2**256 /\ w2n w+32*n <= s1.vs_alloca_next /\
   ~s1.vs_halted /\ s1.vs_current_bb = r.cs_current_bb /\
   s1.vs_inst_idx = LENGTH r.cs_current_insts` by
    fs[Abbr `s1`, eval_operand_def, lookup_var_def, op_taint_def, dimword_def] >>
  `w = n2w (w2n w)` by simp[] >>
  `lookup_var p s1 = SOME (n2w (w2n w))` by metis_tac[] >>
  `!x. not_fresh_at sa x ==> not_fresh_at r x` by
    (qpat_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     strip_tac >> drule storage_copy_alloc_layout >>
     simp[not_fresh_at_def] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  `32*n <= 32*n /\ (!x. src = Var x ==> not_fresh_at r x)` by (simp[] >> metis_tac[]) >>
  drule_all (REWRITE_RULE[comp_ignore_bind_def] toplevel_copy_suffix_post_effects) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  drule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  `copy_prefix loc a (w2n w) n u n t /\ copy_static t = copy_static u` by
    (`copy_static s1 = copy_static u` by simp[Abbr `s1`, copy_static_def] >>
     `!z. copy_runtime_word loc s1 z = copy_runtime_word loc u z` by
       metis_tac[copy_runtime_word_static] >>
     qpat_x_assum `copy_prefix _ _ _ _ _ _ _` mp_tac >>
     simp[copy_prefix_def, Abbr `s1`] >> metis_tac[]) >>
  `lookup_var p t = SOME w` by
    (qpat_x_assum `!x. not_fresh_at r x ==> _` drule >>
     simp[Abbr `s1`, lookup_var_def]) >>
  `toplevel_copy_taint_bound loc a (w2n w) tnf n SUBSET
    toplevel_copy_taint_bound loc a (w2n w) tn n` by
    (irule toplevel_copy_alloc_taint_bound >>
     simp[toplevel_copy_region_def]) >>
  `tnf'.t_mem SUBSET toplevel_copy_taint_bound loc a (w2n w) tn n` by
    metis_tac[SUBSET_TRANS] >>
  `u.vs_call_ctx = s.vs_call_ctx /\ u.vs_accounts = s.vs_accounts /\
   u.vs_transient = s.vs_transient /\
   (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
     FLOOKUP u.vs_allocas aid = SOME entry)` by
    (drule_all toplevel_alloc_buffer_static_effects >> simp[]) >>
  `t.vs_call_ctx = u.vs_call_ctx /\ t.vs_accounts = u.vs_accounts /\
   t.vs_transient = u.vs_transient /\ t.vs_allocas = u.vs_allocas` by
    metis_tac[copy_static_fields] >>
  `LENGTH u.vs_memory <= LENGTH t.vs_memory` by fs[Abbr `s1`] >>
  `?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = sa.cs_next_id` by
    (drule_all buffer_alloc_code >> strip_tac >>
     goal_assum (drule_at Any) >> simp[mk_inst_def]) >>
  `sa.cs_next_id < cs'.cs_next_id` by
    (`32*n < dimword (:256)` by decide_tac >>
     drule_all (REWRITE_RULE[comp_ignore_bind_def] storage_copy_suffix_ci_mono) >> strip_tac >>
     drule_all buffer_alloc_code >> strip_tac >>
     drule_all literal_alloc_buffer_run >> strip_tac >>
     fs[ci_mono_def] >> decide_tac) >>
  qexistsl_tac [`t`, `Gf'`, `tnf'`] >> simp[] >>
  qexists_tac `u` >> simp[] >>
  rpt conj_tac
  >- fs[eval_operand_def, lookup_var_def]
  >- (rpt strip_tac >> first_x_assum drule >> strip_tac >>
      fs[Abbr `s1`, lookup_var_def] >> metis_tac[]) >>
  metis_tac[]
QED

(* Unlike the top-level-name wrapper, use the located value's own dead-byte
   invariant; no global storage-read liveness premise is needed. *)
Theorem custom_error_storage_copy_robust[local]:
  well_formed_type_value tv /\ slots_in_range st (w2n a) tv /\
  decode_value st (w2n a) tv = SOME v /\
  storage_range_agree st (if tr then contract_transient u else contract_storage u) a tv /\
  copy_prefix (if tr then LocTransient else LocStorage)
    a b (type_slot_size tv) u (type_slot_size tv) t /\
  tnf.t_mem SUBSET toplevel_copy_taint_bound
    (if tr then LocTransient else LocStorage) a b tn (type_slot_size tv) /\
  (!i j. i < type_slot_size tv /\ j < 32 /\
    (a+n2w i,j) IN toplevel_copy_source_taint
      (if tr then LocTransient else LocStorage) tn ==>
    dead_bytes (if tr then contract_transient u else contract_storage u)
      (w2n a) tv (w2n a+i) j) ==>
  !mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
    val_in_memory tv v b mem
Proof
  strip_tac >>
  `w2n a+type_slot_size tv <= dimword (:256)` by fs[storage_range_agree_def] >>
  `!i. i < type_slot_size tv ==> w2n (a+n2w i) = w2n a+i` by
    (rpt strip_tac >>
     `w2n a+i < dimword (:256)` by simp[] >>
     `a+n2w i = n2w (w2n a+i)` by metis_tac[word_add_n2w, n2w_w2n] >>
     asm_rewrite_tac[w2n_n2w] >> simp[]) >>
  `storage_live_memory (if tr then contract_transient u else contract_storage u)
    (w2n a) tv b t.vs_memory` by
    (irule toplevel_copy_prefix_live_memory >>
     rpt (goal_assum (drule_at Any)) >> simp[] >> Cases_on `tr` >>
     gvs[copy_runtime_word_def, read_slot_def,
         tload_def, sload_def, contract_transient_def, contract_storage_def,
         vfmStateTheory.lookup_account_def] >> rpt strip_tac >>
     `a+n2w i = n2w (i+w2n a)` by metis_tac[word_add_n2w, n2w_w2n,
       arithmeticTheory.ADD_COMM] >> simp[]) >>
  `storage_live_memory st (w2n a) tv b t.vs_memory` by
    metis_tac[toplevel_storage_live_memory_range] >>
  `!i j. i < type_slot_size tv /\ j < 32 /\
    (a+n2w i,j) IN toplevel_copy_source_taint
      (if tr then LocTransient else LocStorage) tn ==>
    dead_bytes st (w2n a) tv (w2n a+i) j` by
    metis_tac[toplevel_storage_range_dead_bytes] >>
  `!i j. i < type_slot_size tv /\ j < 32 /\ b+32*i+j IN tnf.t_mem ==>
    dead_bytes st (w2n a) tv (w2n a+i) j` by
    metis_tac[toplevel_copy_taint_dead_bytes] >>
  rpt strip_tac >> irule toplevel_storage_decode_robust >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  metis_tac[arithmeticTheory.ADD_COMM, arithmeticTheory.ADD_ASSOC]
QED

Theorem custom_error_storage_unwrap_ptr:
  unwrap_value ce (LocatedValue ty place) sm = (op,sb) /\
  (place.ptr_location = LocStorage \/ place.ptr_location = LocTransient) /\
  ~is_word_type (post_value_type ce e) /\
  vv_post ctx func ce cx e es sa sm s0 ee raw (LocatedValue ty place) s /\
  ptr_vv_ok cx (post_value_type ce e) raw (LocatedValue ty place) ee G tn s /\
  read_result cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tv /\
  post_value_type ce e = expr_type e /\
  nb = type_memory_bytes ce ty /\ nb = type_memory_size tv /\
  nb < dimword (:256) /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!x. place.ptr_operand = Var x ==> not_fresh_at sm x) /\
  ghost_inv d ce cx ee G tn s /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  !D PG. ?G' tn' t p w.
    op = Var p /\ lookup_var p t = SOME w /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK t) /\
    expr_post ctx func ce cx e es sa sb s0 ee v op t /\
    ptr_val_ok cx (post_value_type ce e) v op G' tn' t /\
    ptr_covers G' tn' p t nb /\
    ghost_inv d ce cx ee G' tn' t /\ ghost_kept ce ee sm G tn s G' tn' /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    FLOOKUP t.vs_allocas sm.cs_next_id = SOME (w2n w,nb) /\
    sm.cs_next_id < sb.cs_next_id /\
    (!aid b len. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n w) nb b len) /\
    (!i. i NOTIN toplevel_copy_region (w2n w) (type_slot_size tv) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
    (!i. i NOTIN toplevel_copy_region (w2n w) (type_slot_size tv) /\
      i IN tn'.t_mem ==> i IN tn.t_mem)
Proof
  strip_tac >> rpt gen_tac >>
  `vv_post ctx func ce cx e es sa sm s0 ee (Value v) (LocatedValue ty place) s` by
    metis_tac[vv_post_read_result] >>
  `ty = expr_type e /\ ?a. eval_operand place.ptr_operand s = SOME a /\
    storage_holds cx (place.ptr_location = LocTransient) (expr_type e) (Value v) a ee s` by
    (gvs[vv_post_def, vv_holds_def] >>
     Cases_on `place.ptr_location` >> gvs[]) >>
  `nb = 32 * type_slot_size tv /\
    (nb+31) DIV 32 = type_slot_size tv` by
    (simp[type_memory_size_slots] >> decide_tac) >>
  `compile_ensure_in_memory place.ptr_operand place.ptr_location nb
     (type_slot_size tv) ce.ce_is_ctor ce.ce_imm_alloca sm = (op,sb)` by
    (qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
     simp[unwrap_value_def] >> Cases_on `place.ptr_location` >> gvs[]) >>
  `stmt_state_rel ctx func ce cx ee s /\ op_taint tn place.ptr_operand = {}` by
    gvs[vv_post_def, ptr_vv_ok_def] >>
  drule_at (Pat `compile_ensure_in_memory _ _ _ _ _ _ _ = _`)
    custom_error_storage_ensure_effects >> simp[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  `storage_holds cx (place.ptr_location = LocTransient) (expr_type e) (Value v) a ee u` by
    gvs[storage_holds_def, contract_storage_def, contract_transient_def] >>
  `place.ptr_location = if place.ptr_location = LocTransient then LocTransient else LocStorage` by
    metis_tac[] >>
  `val_wf tv v /\ val_in_memory tv v (w2n w) t.vs_memory /\
    val_footprint tv v <= type_memory_size tv` by
    (irule copy_buffer_storage_contents >>
     rpt (goal_assum (drule_at Any)) >> metis_tac[]) >>
  `~is_word_type (expr_type e) /\
   evaluate_type (get_tenv cx) (expr_type e) = SOME tv` by metis_tac[] >>
  `expr_post ctx func ce cx e es sa sb s0 ee v op t` by
    (irule copy_buffer_post_transport >> simp[] >>
     qrefinel [`_`, `sm`, `_`, `_`, `nb`] >>
     rpt (goal_assum (drule_at Any)) >>
     gvs[copy_prefix_def, eval_operand_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
    val_in_memory tv v (w2n w) mem` by suspend "robust" >>
  `val_store_size tv v <= type_memory_size tv` by metis_tac[val_store_size_le] >>
  `ptr_val_ok cx (post_value_type ce e) v op Gf tnf t` by
    (gvs[ptr_val_ok_def, ptr_mem_ok_def, ptr_covers_def, eval_operand_def] >>
     decide_tac) >>
  `!name b len. local_region ce ee.scopes s name b len ==>
    local_region ce ee.scopes u name b len` by
    (simp[local_region_def] >> rpt strip_tac >>
     `not_fresh_at sm p'` by metis_tac[local_ptrs_reserved_def] >> metis_tac[]) >>
  `!name b len i. local_region ce ee.scopes s name b len /\
    b <= i /\ i < b+len ==> i NOTIN toplevel_copy_region (w2n w) (type_slot_size tv)` by
    (simp[toplevel_copy_region_def] >> rpt strip_tac >>
     `regions_disjoint (w2n w) (32*type_slot_size tv) b len` by metis_tac[] >>
     fs[regions_disjoint_def] >> decide_tac) >>
  `!i. i NOTIN toplevel_copy_region (w2n w) (type_slot_size tv) ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory` by
    (gvs[copy_prefix_def, toplevel_copy_region_def] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  `!i. i NOTIN toplevel_copy_region (w2n w) (type_slot_size tv) /\
    i IN tnf.t_mem ==> i IN tn.t_mem` by
    (fs[SUBSET_DEF, toplevel_copy_taint_bound_def, toplevel_copy_region_def,
        toplevel_copy_translated_taint_def] >> rpt strip_tac >>
     first_x_assum drule >> simp[] >> rpt strip_tac >> gvs[] >> decide_tac) >>
  `ghost_inv d ce cx ee Gf tnf t /\ ghost_kept ce ee sm G tn s Gf tnf` by
    suspend "ghost" >>
  qexistsl_tac [`Gf`, `tnf`, `t`, `p`, `w`] >> simp[] >> metis_tac[]
QED

Resume custom_error_storage_unwrap_ptr[robust]:
  markerLib.RESUME_TAC >>
  `!i. i < type_slot_size tv ==> w2n (a+n2w i) = w2n a+i` by
    (fs[storage_holds_def, storage_range_agree_def] >> rpt strip_tac >>
     `w2n a+i < dimword (:256)` by simp[] >>
     `a+n2w i = n2w (w2n a+i)` by metis_tac[word_add_n2w,n2w_w2n] >>
     asm_rewrite_tac[w2n_n2w] >> simp[]) >>
  rpt gen_tac >> disch_tac >>
  irule custom_error_storage_copy_robust >>
  (conj_tac >- metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value]) >>
  qexistsl_tac [`a`, `get_storage cx ee (place.ptr_location = LocTransient)`,
    `t`, `tn`, `tnf`, `place.ptr_location = LocTransient`, `u`] >>
  gvs[storage_holds_def, read_storage_slot_eq, read_result_def,
      return_def, AllCaseEqs()] >>
  gvs[ptr_vv_ok_def, toplevel_copy_source_taint_def,
      contract_storage_def, contract_transient_def,
      vfmStateTheory.lookup_account_def] >> rpt strip_tac >>
  qpat_x_assum `!k b. _` (qspecl_then [`a+n2w i`, `j`] mp_tac) >> simp[]
QED

Resume custom_error_storage_unwrap_ptr[ghost]:
  markerLib.RESUME_TAC >> (
  `!name entry p sz z. lookup_scopes name ee.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME z ==>
    val_wf entry.type entry.value /\
    (!i. w2n z <= i /\ i < w2n z+val_footprint entry.type entry.value ==>
      i NOTIN toplevel_copy_region (w2n w) (type_slot_size tv))` by
    (qpat_assum `stmt_state_rel _ _ _ _ ee s` (fn sr =>
      qpat_assum `!name b len i. local_region _ _ s _ _ _ /\ _ ==> _` (fn ex =>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[sr,ex,toplevel_local_footprint_disjoint]))) >>
  conj_tac
  >- (irule toplevel_ghost_inv_memory_frame >>
      qexistsl_tac [`G`, `ee`, `s`, `sm`, `tn`,
        `toplevel_copy_region (w2n w) (type_slot_size tv)`] >>
      simp[] >>
      qpat_assum `!name entry p sz w. _` (fn fp =>
        qpat_assum `!name b len i. local_region _ _ s _ _ _ /\ _ ==> _` (fn ex =>
          POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[fp,ex]))) >>
  irule toplevel_ghost_kept_memory_frame >>
  (conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[])) >>
  qexists_tac `toplevel_copy_region (w2n w) (type_slot_size tv)` >>
  simp[] >> (conj_tac >- first_assum MATCH_ACCEPT_TAC) >>
  rpt strip_tac >>
  `regions_disjoint (w2n w) (32*type_slot_size tv) off sz` by metis_tac[] >>
  fs[regions_disjoint_def, toplevel_copy_region_def] >> decide_tac)
QED

Finalise custom_error_storage_unwrap_ptr
