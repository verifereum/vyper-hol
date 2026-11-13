(* Snapshot frames retain the actual lowered representation, even when an
   internal call's annotation describes a wider aggregate. *)
Theory bodyMemLoweredSnapshot
Ancestors
  bodyMemSnapshotStages bodyMemSnapshotStore bodyMemSnapshotResult
  exprSimVVFrame exprSimCalldataSlice exprSimCopy exprSimStorageCopy exprSimProps
  exprSimMemDefs loweringPosts loweringStateRelDefs freshWrites
  exprLoweringProps exprLowering context compileEnv venomState venomInst
  venomExecSemantics fragGasPathMem

Theorem lowered_snapshot_store_frame[local]:
  vv_post ctx func ce cx e es sa sc s0 ee raw source s /\
  local_ptrs_reserved ce sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  copy_static z = copy_static s /\
  (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s) /\
  LENGTH s.vs_memory <= LENGTH z.vs_memory /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  sa.cs_next_id <= inst.inst_id /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  (!n lb len. local_region ce ee.scopes s n lb len ==>
    regions_disjoint b sz lb len) /\
  (!aid off len. FLOOKUP s0.vs_allocas aid = SOME (off,len) /\
    aid < sa.cs_next_id ==> regions_disjoint b sz off len) /\
  (!off len. off + len <= b \/ b + sz <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
  vv_holds ce cx (post_value_type ce e) raw saved ee z /\
  vv_at ce cx (post_value_type ce e) sa sb ee raw saved z /\
  vv_own ce cx (post_value_type ce e) sa sb ee raw saved z /\
  vv_storage_live cx saved ee z ==>
  vv_post ctx func ce cx e es sa sb s0 ee raw saved z
Proof
  strip_tac >>
  `!n lb len. local_region ce es.scopes s0 n lb len ==>
    regions_disjoint b sz lb len` by
    (rpt strip_tac >>
     `local_region ce ee.scopes s n lb len` by
       (irule local_region_frame_fwd >>
        qexistsl_tac [`s0`, `sa`, `es.scopes`] >> gvs[vv_post_def]) >>
     metis_tac[]) >>
  `stmt_state_rel ctx func ce cx ee z` by
    (irule copy_buffer_state_rel_frame >>
     qexistsl_tac [`b`, `inst`, `s`, `sa`, `sz`] >>
     gvs[vv_post_def, regions_disjoint_def] >> metis_tac[]) >>
  `locals_kept ce es ee s0 z` by
    (irule copy_buffer_locals_kept_frame >>
     qexistsl_tac [`b`, `s`, `sz`] >>
     gvs[vv_post_def, regions_disjoint_def] >> metis_tac[]) >>
  drule copy_static_fields >> strip_tac >>
  `~expr_has_effect e ==> pure_frame ce func es sa s0 z` by
    (strip_tac >> irule pure_frame_buffer_tail >>
     qexistsl_tac [`b`, `sz`, `inst`, `s`] >>
     gvs[vv_post_def, regions_disjoint_def] >> metis_tac[]) >>
  simp[vv_post_def] >> gvs[vv_post_def] >>
  rpt strip_tac >>
  rename1 `FLOOKUP s0.vs_allocas aid = SOME (off,len)` >>
  `mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory` by
    (qpat_x_assum `!off len. _ ==> mem_bytes_at _ _ z.vs_memory = _` irule >>
     `regions_disjoint b sz off len` by metis_tac[] >>
     gvs[regions_disjoint_def] >> decide_tac) >>
  qpat_x_assum `!aid off sz. _ ==> mem_bytes_at _ _ s.vs_memory = _` drule >>
  simp[] >> (impl_tac >- (rpt strip_tac >>
    qpat_x_assum `!n b sz'. local_region _ _ _ _ _ _ ==> _` drule >>
    simp[arithmeticTheory.ADD_COMM])) >> simp[]
QED

Theorem lowered_snapshot_store_mem[local]:
  compile_store_memory ce src dst lt lt sc = ((),sb) /\
  post_value_type ce e = lt /\ ~is_word_type lt /\
  evaluate_type (get_tenv cx) lt = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  val_in_memory tv v (w2n w) s.vs_memory /\
  type_memory_bytes ce lt = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  eval_operand src s = SOME w /\ eval_operand dst s = SOME d /\
  w2n w + type_memory_size tv <= s.vs_alloca_next /\
  w2n d + type_memory_size tv <= s.vs_alloca_next /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sc x) /\
  fn_has_code sc sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  vv_post ctx func ce cx e es sa sc s0 ee raw source s /\
  read_result cx raw ee = (INL v,ee) /\
  local_ptrs_reserved ce sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sc.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id <= inst.inst_id /\
  inst.inst_id < sb.cs_next_id /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n d,type_memory_size tv) /\
  (!n b len. local_region ce ee.scopes s n b len ==>
    regions_disjoint (w2n d) (type_memory_size tv) b len) /\
  (!aid off len. FLOOKUP s0.vs_allocas aid = SOME (off,len) /\
    aid < sa.cs_next_id ==>
    regions_disjoint (w2n d) (type_memory_size tv) off len) ==>
  ?z. gas_path_mem ctx func s 0 (OK z) /\
    vv_post ctx func ce cx e es sa sb s0 ee raw
      (LocatedValue lt (mk_ptr dst LocMemory)) z /\
    vv_own ce cx lt sm sb ee raw (LocatedValue lt (mk_ptr dst LocMemory)) z /\
    vv_store_bound cx lt lt ee raw (LocatedValue lt (mk_ptr dst LocMemory)) z /\
    val_in_memory tv v (w2n d) z.vs_memory /\
    eval_operand dst z = SOME d /\
    FLOOKUP z.vs_allocas inst.inst_id = SOME (w2n d,type_memory_size tv) /\
    (!n b len. local_region ce ee.scopes z n b len ==>
      regions_disjoint (w2n d) (type_memory_size tv) b len) /\
    alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
    z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all snapshot_nonword_store_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `copy_static z = copy_static s` by
    (qpat_x_assum `_ with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|> = s`
      mp_tac >> simp[copy_static_def, venom_state_component_equality] >>
     rpt strip_tac >> simp[]) >>
  drule copy_static_fields >> strip_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s` by
    metis_tac[not_fresh_at_mono] >>
  `eval_operand dst z = SOME d` by
    (Cases_on `dst` >> gvs[eval_operand_def]) >>
  `!n b len. local_region ce ee.scopes z n b len ==>
    regions_disjoint (w2n d) (type_memory_size tv) b len` by
    (rpt strip_tac >>
     `local_region ce ee.scopes s n b len` by
       metis_tac[copy_buffer_local_region_frame] >> metis_tac[]) >>
  `vv_holds ce cx lt raw (LocatedValue lt (mk_ptr dst LocMemory)) ee z /\
   vv_at ce cx lt sa sb ee raw (LocatedValue lt (mk_ptr dst LocMemory)) z /\
   vv_own ce cx lt sm sb ee raw (LocatedValue lt (mk_ptr dst LocMemory)) z /\
   vv_store_bound cx lt lt ee raw (LocatedValue lt (mk_ptr dst LocMemory)) z` by
    (`vv_holds ce cx lt raw
        (LocatedValue lt <|ptr_location := LocMemory; ptr_operand := dst|>) ee z /\
      vv_at ce cx lt sa sb ee raw
        (LocatedValue lt <|ptr_location := LocMemory; ptr_operand := dst|>) z /\
      vv_own ce cx lt sm sb ee raw
        (LocatedValue lt <|ptr_location := LocMemory; ptr_operand := dst|>) z /\
      vv_store_bound cx lt lt ee raw
        (LocatedValue lt <|ptr_location := LocMemory; ptr_operand := dst|>) z` by
       (irule snapshot_located_result_facts >> simp[] >>
        qexists_tac `inst.inst_id` >> simp[regions_disjoint_def] >>
        metis_tac[regions_disjoint_def, arithmeticTheory.ADD_COMM]) >>
     gvs[mk_ptr_def, vv_holds_def, vv_at_def, vv_own_def, vv_store_bound_def] >>
     metis_tac[]) >>
  `vv_own ce cx lt sa sb ee raw (LocatedValue lt (mk_ptr dst LocMemory)) z` by
    (irule vv_own_start_mono >> qexists_tac `sm` >> simp[]) >>
  `vv_storage_live cx (LocatedValue lt (mk_ptr dst LocMemory)) ee z` by
    simp[mk_ptr_def] >>
  `vv_post ctx func ce cx e es sa sb s0 ee raw
     (LocatedValue lt (mk_ptr dst LocMemory)) z` by
    (irule lowered_snapshot_store_frame >> simp[] >>
     qexistsl_tac [`w2n d`, `inst`, `s`, `sc`, `source`, `type_memory_size tv`] >> simp[] >>
     conj_tac >- (rpt strip_tac >>
       qpat_x_assum `!n b len. local_region _ _ s _ _ _ ==> _` drule >> simp[]) >>
     conj_tac >- (rpt strip_tac >>
       qpat_x_assum `!aid off len. _ /\ aid < sa.cs_next_id ==> _` drule_all >> simp[]) >>
     rpt strip_tac >>
     qpat_x_assum `!a k. _ ==> mem_bytes_at _ _ z.vs_memory = _`
       (qspecl_then [`off`, `len`] mp_tac) >> simp[arithmeticTheory.ADD_COMM]) >>
  qexists_tac `z` >> simp[] >> first_assum ACCEPT_TAC
QED

(* The capacity premise concerns the lowered layout, never the annotation. *)
Theorem snapshot_lowered_located_mem:
  post_value_type ce e = lowered_value_type ce e /\
  ~is_word_type (lowered_value_type ce e) /\ p.ptr_location = LocMemory /\
  compile_snapshot_vv ce T
    (vv_with_type (lowered_value_type ce e) (LocatedValue declared p)) sm = (saved,sb) /\
  vv_post ctx func ce cx e es sa sm s0 ee raw (LocatedValue declared p) s /\
  read_result cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
  value_has_type tv v /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  (!w. eval_operand p.ptr_operand s = SOME w ==>
    w2n w + type_memory_size tv <= s.vs_alloca_next) /\
  local_ptrs_reserved ce sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?z dst d. gas_path_mem ctx func s 0 (OK z) /\
    saved = LocatedValue (lowered_value_type ce e) (mk_ptr dst LocMemory) /\
    vv_post ctx func ce cx e es sa sb s0 ee raw saved z /\
    vv_own ce cx (lowered_value_type ce e) sm sb ee raw saved z /\
    vv_store_bound cx (lowered_value_type ce e) (lowered_value_type ce e)
      ee raw saved z /\
    val_in_memory tv v (w2n d) z.vs_memory /\ eval_operand dst z = SOME d /\
    FLOOKUP z.vs_allocas sm.cs_next_id = SOME (w2n d,type_memory_size tv) /\
    (!n b len. local_region ce ee.scopes z n b len ==>
      regions_disjoint (w2n d) (type_memory_size tv) b len) /\
    alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
    z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all snapshot_nonword_slices >> strip_tac >>
  `sc = mid /\ src = p.ptr_operand` by
    gvs[vv_with_type_def, unwrap_value_def, comp_return_def] >>
  gvs[] >>
  `local_ptrs_reserved ce sm` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `?u d. gas_path_mem ctx func s 0 (OK u) /\
    vv_post ctx func ce cx e es sa mid s0 ee raw (LocatedValue declared p) u /\
    eval_operand buf.buf_operand u = SOME d /\
    FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n d,type_memory_size tv) /\
    w2n d + type_memory_size tv <= u.vs_alloca_next /\
    u.vs_memory = s.vs_memory /\ u.vs_labels = s.vs_labels /\
    sm.cs_next_id < mid.cs_next_id /\
    (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
    (!aid b len. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       regions_disjoint (w2n d) (type_memory_size tv) b len) /\
    (!n b len. local_region ce ee.scopes u n b len ==>
       regions_disjoint (w2n d) (type_memory_size tv) b len) /\
    (?x. buf.buf_operand = Var x /\ not_fresh_at mid x) /\
    s.vs_alloca_next <= u.vs_alloca_next /\ alloca_history func u /\
    ~u.vs_halted /\ u.vs_current_bb = mid.cs_current_bb /\
    u.vs_inst_idx = LENGTH mid.cs_current_insts` by suspend "allocation" >>
  suspend "store"
QED

Resume snapshot_lowered_located_mem[allocation]:
  `stmt_state_rel ctx func ce cx ee s` by fs[vv_post_def] >>
  `eval_operand (Lit 0w) s = SOME 0w` by simp[eval_operand_def] >>
  `!x. Lit 0w = Var x ==> not_fresh_at sm x` by simp[] >>
  drule_all exprSimMemUnwrapTheory.alloc_buffer_source_path_mem_endpoint >> strip_tac >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  `!x. vv_operand (LocatedValue declared p) = Var x ==> not_fresh_at sm x` by
    simp[vv_operand_def] >>
  drule_all exprSimIfExpTheory.ifexp_alloc_preserves_post >> strip_tac >>
  gvs[] >>
  qexistsl_tac [`q with vs_inst_idx := LENGTH mid.cs_current_insts`, `w`] >>
  simp[] >> metis_tac[]
QED

Resume snapshot_lowered_located_mem[store]:
  `val_wf tv v` by metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  `?w. eval_operand p.ptr_operand u = SOME w /\
    val_in_memory tv v (w2n w) u.vs_memory` by
    (`vv_holds ce cx (lowered_value_type ce e) raw (LocatedValue declared p) ee u` by
       gvs[vv_post_def] >>
     pop_assum mp_tac >> simp[vv_holds_def] >> strip_tac >>
     gvs[] >> metis_tac[]) >>
  `eval_operand p.ptr_operand s = SOME w` by
    (Cases_on `p.ptr_operand` >> gvs[eval_operand_def]) >>
  `w2n w + type_memory_size tv <= u.vs_alloca_next` by
    (first_x_assum drule >> decide_tac) >>
  `!q. p.ptr_operand = Var q \/ buf.buf_operand = Var q ==> not_fresh_at mid q` by
    (rpt strip_tac >> gvs[] >> irule not_fresh_at_mono >>
     qexists_tac `sm` >> fs[ci_mono_def]) >>
  `alloca_inv u` by fs[vv_post_def, stmt_state_rel_def] >>
  `sa.cs_next_var <= mid.cs_next_var` by (fs[ci_mono_def] >> decide_tac) >>
  `!aid off len. FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id ==>
    regions_disjoint (w2n d) (type_memory_size tv) off len` by
    (rpt strip_tac >>
     qpat_x_assum `!aid b len. aid < sm.cs_next_id /\ _ ==> _` irule >>
     qexists_tac `aid` >> conj_tac >- decide_tac >> fs[vv_post_def] >> metis_tac[]) >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  qabbrev_tac `inst = mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_size tv))]
    [STRING #"%" (toString sm.cs_next_var)]` >>
  `inst.inst_id = sm.cs_next_id /\ inst.inst_opcode = ALLOCA /\
    MEM inst (fn_insts func)` by simp[Abbr `inst`, mk_inst_def] >>
  `inst.inst_id < sb.cs_next_id` by (fs[ci_mono_def] >> decide_tac) >>
  drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`) lowered_snapshot_store_mem >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `read_result _ _ _ = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand p.ptr_operand _ = _`)) >>
  disch_then (qspecl_then [`sm`, `inst`, `d`] mp_tac) >>
  (impl_tac >- (gvs[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qexistsl_tac [`z`, `buf.buf_operand`, `d`] >> simp[] >>
  conj_tac >- metis_tac[gas_path_mem_then, arithmeticTheory.ADD_0] >>
  gvs[] >> first_assum ACCEPT_TAC
QED
Finalise snapshot_lowered_located_mem
