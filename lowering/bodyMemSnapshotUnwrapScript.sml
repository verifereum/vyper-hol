(* Framed counted materialisation of non-memory aggregate values. *)
Theory bodyMemSnapshotUnwrap
Ancestors
  bodyMemSnapshotCodeCtor bodyMemSnapshotCodeRuntime
  bodyMemAggregateMaterialise exprSimMemUnwrap exprSimStorageCopy exprSimCopy
  exprSimProps exprSimUnwrapProps exprSimUnwrap
  exprSimMemDefs exprLoweringProps freshWrites valueEncodingProps
  loweringPosts fragGasPathMem exprLowering context compileEnv
  loweringStateRelDefs exprSimAlloc fragExec bodyImmutableUnwrapMemory
  venomExecSemantics venomInst venomState

Theorem snapshot_copy_frame[local]:
  !cenv func ee sm s u z b sz ops outs.
    local_ptrs_reserved cenv sm /\
    (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
    u.vs_memory = s.vs_memory /\ copy_static z = copy_static u /\
    FLOOKUP u.vs_allocas sm.cs_next_id = SOME (b,sz) /\
    MEM (mk_inst sm.cs_next_id ALLOCA ops outs) (fn_insts func) /\
    (!n lb len. local_region cenv ee.scopes u n lb len ==>
       regions_disjoint b sz lb len) /\
    (!off len. off + len <= b \/ b + sz <= off ==>
       mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory) ==>
    pure_frame cenv func ee sm s z
Proof
  rpt gen_tac >> strip_tac >> drule copy_static_fields >> strip_tac >>
  irule pure_frame_fresh_alloca >>
  reverse conj_tac
  >- (qexistsl_tac [`b`, `sm.cs_next_id`, `ops`, `outs`, `sz`] >>
      simp[regions_disjoint_def] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  rpt strip_tac >>
      `local_region cenv ee.scopes u n lb lsz` by
        metis_tac[copy_buffer_local_region_frame] >>
      `regions_disjoint b sz lb lsz` by metis_tac[] >>
      fs[regions_disjoint_def] >> metis_tac[]
QED

Theorem snapshot_storage_unwrap_mem[local]:
  !ctx func cenv cx e es sa sm sb s0 ee v t p op s.
    post_value_type cenv e = expr_type e /\
    unwrap_value cenv (LocatedValue t p) sm = (op,sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
    ~is_word_type t /\ local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) t = SOME tvt ==>
       type_memory_bytes cenv t = type_memory_size tvt /\
       type_memory_size tvt < 2 ** 64) /\
    vv_post ctx func cenv cx e es sa sm s0 ee (Value v) (LocatedValue t p) s /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?z w tvt. gas_path_mem ctx func s 0 (OK z) /\
      expr_post ctx func cenv cx e es sa sb s0 ee v op z /\
      evaluate_type (get_tenv cx) t = SOME tvt /\ eval_operand op z = SOME w /\
      w2n w + type_memory_size tvt <= z.vs_alloca_next /\
      (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
         FLOOKUP z.vs_allocas aid = SOME entry) /\
      pure_frame cenv func ee sm s z /\ alloca_history func z /\
      s.vs_alloca_next <= z.vs_alloca_next /\ ~z.vs_halted /\
      z.vs_current_bb = sb.cs_current_bb /\
      z.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all storage_unwrap_layout_facts >> strip_tac >>
  drule_all storage_unwrap_type_facts >> strip_tac >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  drule_all alloc_buffer_source_path_mem >> strip_tac >>
  `storage_holds cx (p.ptr_location = LocTransient) t (Value v) a ee u` by
    (qpat_x_assum `storage_holds _ _ _ _ _ _ s` mp_tac >> simp[storage_holds_def]) >>
  `!x. p.ptr_operand = Var x \/ buf.buf_operand = Var x ==> not_fresh_at mid x` by
    (gen_tac >> strip_tac
     >- (irule not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >> fs[]) >>
  `w2n w + 32 * type_slot_size tv < 2**256 /\
   w2n w + 32 * type_slot_size tv <= u.vs_alloca_next` by
    fs[type_memory_size_slots, wordsTheory.dimword_def] >>
  qpat_x_assum `(_ + 31) DIV 32 = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  drule_all storage_unwrap_typed_suffix_path_mem >> strip_tac >>
  `expr_post ctx func cenv cx e es sa sb s0 ee v buf.buf_operand z` by
    (irule buffer_post_transport >> simp[] >>
     qexistsl_tac [`mid`, `p`, `s`, `sm`, `tv`, `u`] >>
     qpat_assum `t = expr_type e` (fn th => rewrite_tac[GSYM th]) >>
     simp[arithmeticTheory.ADD_COMM] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  `pure_frame cenv func ee sm s z` by
    (drule_all buffer_alloc_code >> strip_tac >>
     irule snapshot_copy_frame >>
     conj_tac
     >- (qexistsl_tac [`w2n w`, `type_memory_bytes cenv t`, `u`] >>
         simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
     metis_tac[]) >>
  drule copy_static_fields >> strip_tac >>
  qexistsl_tac [`z`, `w`, `tv`] >> simp[] >>
  conj_tac
  >- (`0 = 0 + 0` by simp[] >> pop_assum SUBST1_TAC >>
      irule gas_path_mem_then >> qexists_tac `u` >> simp[]) >>
  rpt strip_tac >> metis_tac[not_fresh_at_mono]
QED

Theorem snapshot_code_layout[local]:
  unwrap_value ce (LocatedValue ty p) sm = (op,sb) /\
  p.ptr_location = LocCode /\ ~is_word_type ty /\ fn_has_code sm sb func ==>
  ?buf mid. compile_alloc_buffer (type_memory_bytes ce ty) sm = (buf,mid) /\
    compile_imm_copy_to_memory ce.ce_is_ctor ce.ce_imm_alloca p.ptr_operand
      buf.buf_operand ((type_memory_bytes ce ty + 31) DIV 32) 0 mid = ((),sb) /\
    op = buf.buf_operand /\ fn_has_code sm mid func /\ fn_has_code mid sb func /\
    sm.cs_next_var <= mid.cs_next_var /\ mid.cs_next_id <= sb.cs_next_id
Proof
  strip_tac >> qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  simp[unwrap_value_def, compile_ensure_in_memory_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  gvs[] >> rename1 `compile_alloc_buffer _ sm = (buf,mid)` >>
  `ci_mono sm mid` by
    (qspecl_then [`type_memory_bytes ce ty`, `sm`] mp_tac
      ci_mono_compile_alloc_buffer >> simp[]) >>
  rename1 `compile_imm_copy_to_memory _ _ _ _ _ _ mid = ((),sc)` >>
  `ci_mono mid sc` by
    metis_tac[ci_mono_compile_imm_copy_to_memory, pairTheory.SND] >>
  gvs[ci_mono_def] >> metis_tac[fn_has_code_split]
QED

Theorem snapshot_code_type_facts[local]:
  post_value_type ce e = expr_type e /\ p.ptr_location = LocCode /\
  vv_post ctx func ce cx e es sa sm s0 ee (Value v) (LocatedValue ty p) s /\
  (!tvt. evaluate_type (get_tenv cx) ty = SOME tvt ==>
    type_memory_bytes ce ty = type_memory_size tvt /\
    type_memory_size tvt < 2**64) ==>
  ty = expr_type e /\ stmt_state_rel ctx func ce cx ee s /\
  ?a tv. eval_operand p.ptr_operand s = SOME a /\
    immutable_holds ce cx ty (Value v) a ee s /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ val_wf tv v /\
    type_memory_bytes ce ty = type_memory_size tv /\
    type_memory_bytes ce ty < dimword (:256) /\
    w2n a + type_memory_size tv < dimword (:256) /\
    (type_memory_bytes ce ty + 31) DIV 32 = type_slot_size tv
Proof
  strip_tac >>
  `ty = expr_type e /\ stmt_state_rel ctx func ce cx ee s /\
   ?a. eval_operand p.ptr_operand s = SOME a /\
     immutable_holds ce cx ty (Value v) a ee s` by
    gvs[vv_post_def, vv_holds_def] >> simp[] >>
  `?tv. evaluate_type (get_tenv cx) ty = SOME tv` by
    (gvs[immutable_holds_def] >> metis_tac[]) >>
  drule_all immutable_holds_bounds >> strip_tac >>
  qexists_tac `tv` >> gvs[arithmeticTheory.ADD_COMM] >>
  gvs[type_memory_size_slots] >> decide_tac
QED

Theorem snapshot_code_unwrap_mem[local]:
  !ctx func cenv cx e es sa sm sb s0 ee v t p op s.
    post_value_type cenv e = expr_type e /\
    unwrap_value cenv (LocatedValue t p) sm = (op,sb) /\
    p.ptr_location = LocCode /\ ~is_word_type t /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) t = SOME tvt ==>
       type_memory_bytes cenv t = type_memory_size tvt /\
       type_memory_size tvt < 2**64) /\
    vv_post ctx func cenv cx e es sa sm s0 ee (Value v) (LocatedValue t p) s /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?z w tvt. gas_path_mem ctx func s 0 (OK z) /\
      expr_post ctx func cenv cx e es sa sb s0 ee v op z /\
      evaluate_type (get_tenv cx) t = SOME tvt /\ eval_operand op z = SOME w /\
      w2n w + type_memory_size tvt <= z.vs_alloca_next /\
      (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
         FLOOKUP z.vs_allocas aid = SOME entry) /\
      pure_frame cenv func ee sm s z /\ alloca_history func z /\
      s.vs_alloca_next <= z.vs_alloca_next /\ ~z.vs_halted /\
      z.vs_current_bb = sb.cs_current_bb /\
      z.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all snapshot_code_layout >> strip_tac >>
  drule_all snapshot_code_type_facts >> strip_tac >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  drule_all alloc_buffer_source_path_mem >> strip_tac >>
  `copy_old_operand mid p.ptr_operand /\ copy_old_operand mid buf.buf_operand` by
    (rw[copy_old_operand_def] >> gvs[] >> metis_tac[not_fresh_at_mono]) >>
  qpat_x_assum `(_ + 31) DIV 32 = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  `immutable_holds cenv cx t (Value v) a ee u` by
    (qpat_x_assum `immutable_holds _ _ _ _ _ _ s` mp_tac >>
     simp[immutable_holds_def]) >>
  `?z. gas_path_mem ctx func u 0 (OK z) /\ copy_static z = copy_static u /\
       (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x u) /\
       z.vs_current_bb = sb.cs_current_bb /\
       z.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func z /\
       LENGTH u.vs_memory <= LENGTH z.vs_memory /\
       (!off len. off + len <= w2n w \/ w2n w + type_memory_size tv <= off ==>
          mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory) /\
       val_in_memory tv v (w2n w) z.vs_memory /\
       val_footprint tv v <= type_memory_size tv` by
    (Cases_on `cenv.ce_is_ctor` >- suspend "ctor" >> suspend "runtime") >>
  `eval_operand buf.buf_operand z = SOME w` by
    (qsuff_tac `eval_operand buf.buf_operand z = eval_operand buf.buf_operand u`
     >- gvs[] >> irule storage_copy_operand_preserved >> simp[] >>
     qexists_tac `mid` >> simp[]) >>
  `expr_post ctx func cenv cx e es sa sb s0 ee v buf.buf_operand z` by
    (irule buffer_post_transport >> simp[] >>
     qexistsl_tac [`mid`, `p`, `s`, `sm`, `tv`, `u`] >>
     qpat_assum `t = expr_type e` (fn th => rewrite_tac[GSYM th]) >>
     gvs[arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
  `pure_frame cenv func ee sm s z` by
    (drule_all buffer_alloc_code >> strip_tac >> irule snapshot_copy_frame >>
     conj_tac >- (qexistsl_tac [`w2n w`, `type_memory_bytes cenv t`, `u`] >>
       simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >> metis_tac[]) >>
  drule copy_static_fields >> strip_tac >>
  qexistsl_tac [`z`, `w`, `tv`] >> simp[] >>
  conj_tac >- (`0 = 0 + 0` by simp[] >> pop_assum SUBST1_TAC >>
    irule gas_path_mem_then >> qexists_tac `u` >> simp[]) >>
  rpt strip_tac >> metis_tac[not_fresh_at_mono]
QED

Resume snapshot_code_unwrap_mem[ctor]:
  `alloca_inv u` by gvs[stmt_state_rel_def] >>
  `immutable_base_zero cenv s` by gvs[stmt_state_rel_def] >>
  `!region. cenv.ce_imm_alloca = SOME region ==>
    eval_operand region u = SOME 0w /\ copy_old_operand mid region` by
    (rpt strip_tac >>
     `eval_operand region s = SOME 0w` by gvs[immutable_base_zero_def] >>
     `!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x` by
       metis_tac[local_ptrs_reserved_imm_base] >>
     `copy_old_operand sa region` by
       (simp[copy_old_operand_def] >> rpt strip_tac >> gvs[]) >>
     `copy_old_operand sm region` by
       (irule copy_old_operand_mono >> qexists_tac `sa` >> gvs[]) >>
     `copy_old_operand mid region` by
       (irule copy_old_operand_mono >> qexists_tac `sm` >> gvs[]) >>
     Cases_on `region` >> gvs[eval_operand_def, copy_old_operand_def]) >>
  `w2n a + type_memory_size tv <= s.vs_alloca_next` by
    metis_tac[ctor_immutable_frontier] >>
  `regions_disjoint (w2n a) (type_memory_size tv)
    (w2n w) (type_memory_size tv)` by
    (irule immutable_holds_alloca_disjoint >>
     qexistsl_tac [`cenv`, `ctx`, `cx`, `ee`, `func`] >>
     goal_assum (drule_at Any) >> simp[mk_inst_def] >>
     drule_all buffer_alloc_code >> strip_tac >>
     goal_assum (drule_at Any) >> gvs[mk_inst_def] >>
     qexistsl_tac [`expr_type e`, `u`, `v`] >> simp[]) >>
  `w2n a + type_memory_size tv <= u.vs_alloca_next` by decide_tac >>
  gvs[] >> drule snapshot_ctor_copy_typed_mem >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `immutable_holds _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand (Var p') _ = _`)) >>
  (impl_tac >- (simp[] >> decide_tac)) >>
  strip_tac >> qexists_tac `z` >> gvs[arithmeticTheory.ADD_COMM] >> metis_tac[]
QED
Resume snapshot_code_unwrap_mem[runtime]:
  `alloca_inv u` by gvs[stmt_state_rel_def] >>
  `w2n a + type_memory_size tv <= LENGTH u.vs_data_section` by
    (irule runtime_immutable_data_section >> metis_tac[]) >>
  gvs[] >> drule snapshot_runtime_copy_typed_mem >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `immutable_holds _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand (Var p') _ = _`)) >>
  (impl_tac >- (simp[] >> decide_tac)) >>
  strip_tac >> qexists_tac `z` >> gvs[arithmeticTheory.ADD_COMM] >> metis_tac[]
QED
Finalise snapshot_code_unwrap_mem

Theorem snapshot_nonmemory_unwrap_mem:
  !ctx func cenv cx e es sa sm sb s0 ee raw v t p op s.
    post_value_type cenv e = expr_type e /\
    unwrap_value cenv (LocatedValue t p) sm = (op,sb) /\
    p.ptr_location <> LocMemory /\ ~is_word_type t /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) t = SOME tvt ==>
       type_memory_bytes cenv t = type_memory_size tvt /\
       type_memory_size tvt < 2**64) /\
    read_result cx raw ee = (INL v,ee) /\
    vv_post ctx func cenv cx e es sa sm s0 ee raw (LocatedValue t p) s /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?z w tvt. gas_path_mem ctx func s 0 (OK z) /\
      expr_post ctx func cenv cx e es sa sb s0 ee v op z /\
      evaluate_type (get_tenv cx) t = SOME tvt /\ eval_operand op z = SOME w /\
      w2n w + type_memory_size tvt <= z.vs_alloca_next /\
      (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
         FLOOKUP z.vs_allocas aid = SOME entry) /\
      pure_frame cenv func ee sm s z /\ alloca_history func z /\
      s.vs_alloca_next <= z.vs_alloca_next /\ ~z.vs_halted /\
      z.vs_current_bb = sb.cs_current_bb /\
      z.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >> drule_all vv_post_read_result >> strip_tac >>
  Cases_on `p.ptr_location` >> gvs[]
  >- (irule (SRULE [arithmeticTheory.ADD_COMM] snapshot_storage_unwrap_mem) >> simp[] >> metis_tac[])
  >- (irule (SRULE [arithmeticTheory.ADD_COMM] snapshot_storage_unwrap_mem) >> simp[] >> metis_tac[])
  >- (irule (SRULE [arithmeticTheory.ADD_COMM] snapshot_code_unwrap_mem) >> simp[] >> metis_tac[]) >>
  metis_tac[vv_post_calldata]
QED
